import CertifiedConsensus

/-!
# `certify` — an exact epipolar certificate checker

Reads a camera pair or a fundamental matrix, together with correspondences, and checks
the certificate of `CertifiedConsensus.Checker` over the rationals.

Input format (whitespace separated, `#` starts a comment):

```
A                     -- or `F`
a11 a12 a13
a21 a22 a23
a31 a32 a33
b                     -- only in `A` mode
b1 b2 b3
n
u1 v1 u1' v1'
...
```

Numbers may be integers, decimals, or exact fractions `p/q`.
-/

open CertifiedConsensus

namespace CLI

def mat3 (l : List Rat) : Matrix (Fin 3) (Fin 3) Rat :=
  Matrix.of fun i j => l.getD (i.val * 3 + j.val) 0

def vec3 (l : List Rat) : Fin 3 → Rat := fun i => l.getD i.val 0

def showMat (M : Matrix (Fin 3) (Fin 3) Rat) : String :=
  String.join <| (List.finRange 3).map (fun i =>
    String.join ((List.finRange 3).map (fun j => toString (M i j) ++ "  ")) ++ "\n")

/-- The first nonvanishing `2 × 2` minor, as a rank-two witness. -/
def rankWitness (F : Matrix (Fin 3) (Fin 3) Rat) : Option (Rat × Fin 3 × Fin 3 × Fin 3 × Fin 3) :=
  let idx : List (Fin 3 × Fin 3 × Fin 3 × Fin 3) :=
    [(0,1,0,1), (0,1,0,2), (0,1,1,2), (0,2,0,1), (0,2,0,2),
     (0,2,1,2), (1,2,0,1), (1,2,0,2), (1,2,1,2)]
  idx.findSome? fun (i, j, k, l) =>
    let m := minor2 F i j k l
    if m ≠ 0 then some (m, i, j, k, l) else none

end CLI

open CLI

def main (args : List String) : IO UInt32 := do
  let path := args.head?.getD "data/stereo_certificate.txt"
  let content ← IO.FS.readFile path
  let toks := tokenize content
  match toks with
  | [] => IO.println "empty input"; return 1
  | mode :: rest₀ =>
    -- Optional tolerance: `tol <rat>` immediately after the mode token.
    let (tol?, rest) : Option Rat × List String :=
      match rest₀ with
      | "tol" :: d :: tl => (parseRat? d, tl)
      | _ => (none, rest₀)
    let nums := rest.filterMap parseRat?
    let nNums := nums.length
    let (F?, pts) ←
      if mode == "A" then
        if nNums < 13 then
          IO.println "error: `A` mode needs 9 matrix entries, 3 baseline entries and a count"
          return 1
        let A := mat3 nums
        let b := vec3 (nums.drop 9)
        let cnt := ratToNat (nums.getD 12 0)
        let coords := nums.drop 13
        let pts := (List.range cnt).map fun t =>
          let g k := coords.getD (4 * t + k) 0
          (homog (g 0) (g 1), homog (g 2) (g 3))
        pure (crossMatrix b * A, pts)
      else
        if nNums < 10 then
          IO.println "error: `F` mode needs 9 matrix entries and a point count"
          return 1
        let F := mat3 nums
        let cnt := ratToNat (nums.getD 9 0)
        let coords := nums.drop 10
        let pts := (List.range cnt).map fun t =>
          let g k := coords.getD (4 * t + k) 0
          (homog (g 0) (g 1), homog (g 2) (g 3))
        pure (F, pts)
    let F := F?
    IO.println "certified-consensus — exact rational certificate"
    IO.println s!"input: {path}"
    IO.println "fundamental matrix F ="
    IO.println (showMat F)
    IO.println ""
    IO.println s!"points: {pts.length}"
    let maxRes := (pts.map fun p => epipolarResidual F p.1 p.2).foldl max 0
    let ok := match tol? with
      | some δ => checkEpipolarTol δ pts F
      | none => checkEpipolar F pts
    match tol? with
    | some δ =>
      IO.println s!"tolerance: δ = {δ}"
      IO.println s!"max |residual| = {maxRes}"
      IO.println s!"exact check (δ = 0) accepts: {checkEpipolar F pts}"
    | none =>
      let bad := pts.filter (fun p => epipolarResidual F p.1 p.2 ≠ 0)
      IO.println s!"epipolar residuals: {pts.length - bad.length}/{pts.length} exactly zero"
    match rankWitness F with
    | some (m, i, j, k, l) =>
      IO.println s!"rank two: det F = 0, minor rows ({i.val},{j.val}) cols ({k.val},{l.val}) = {m} ≠ 0"
    | none => IO.println "rank two: FAILED (all 2×2 minors vanish)"
    if ok then
      match tol? with
      | some δ =>
        IO.println "\nCERTIFIED within tolerance — rank and residuals verified"
        IO.println s!"tightening δ to {maxRes / 2} is rejected: {!(checkEpipolarTol (maxRes / 2) pts F)}"
        IO.println s!"max residual {maxRes} ≤ δ: {decide (maxRes ≤ δ)}"
      | none =>
        IO.println "\nCERTIFIED — every check passed exactly"
        match pts with
        | (x, _) :: _ =>
          let x' : Point := fun i => if i = 0 then x 0 + (1 : Rat) / 1000 else x i
          let pts' := (x, x') :: pts.tail
          IO.println s!"negative control: perturbing u by 1/1000 is rejected: {!checkEpipolar F pts'}"
        | [] => pure ()
      return 0
    else
      IO.println "\nREJECTED — at least one check failed"
      return 1
