import CertifiedConsensus.Parse
import Lean

/-!
# `#certify_epipolar`

Checks an epipolar certificate **at elaboration time**. The fundamental matrix is
evaluated from the term the user wrote; the correspondences come from a file. If
any residual is nonzero, or the matrix is not rank two, the command throws and the
file does not compile.

```
#certify_epipolar
  !![0, 0, 1/10; 0, 0, -1/2; 1/2, 1/10, 0]
  from "data/stereo_points.txt"
```

With an explicit tolerance:

```
#certify_epipolar F from "data/noisy_points.txt" tol 3/500
```

Relative paths are resolved against the directory of the file containing the command,
not against the process working directory.

## Trust boundary

`Meta.evalExpr` is `unsafe`: it evaluates the elaborated term with compiled code, the
same mechanism `#eval` and `native_decide` use. The command is therefore an `unsafe`
implementation behind an `@[implemented_by] opaque` wrapper, mirroring
`Lean.Elab.Command.elabEvalCore` in the Lean sources. The *statement* being checked is
still the kernel-checked `checkEpipolar_sound`; only the computation of the `Bool` is
delegated to compiled evaluation.
-/

open Lean Elab Command Meta

namespace CertifiedConsensus

/-- Render a `3 × 3` rational matrix. -/
def renderMat (M : Matrix (Fin 3) (Fin 3) Rat) : String :=
  String.join <| (List.finRange 3).map (fun i =>
    String.join ((List.finRange 3).map (fun j => toString (M i j) ++ "  ")) ++ "\n")

/-- Evaluate a term of the given type at elaboration time. -/
unsafe def evalTermUnsafe (stx : Syntax) (expected : Expr) (hostType : Type) : CommandElabM hostType :=
  liftTermElabM do
    let e ← Term.elabTermAndSynthesize stx (some expected)
    Meta.evalExpr hostType expected e

/-- Resolve a path relative to the file currently being elaborated. -/
def resolvePath (p : String) : CommandElabM System.FilePath := do
  let raw := System.FilePath.mk p
  if raw.isAbsolute then return raw
  let here := System.FilePath.mk (← getFileName)
  return (here.parent.map (·.join raw)).getD raw

/-- The first correspondence violating the tolerance, with its index and residual. -/
def firstViolation (F : Matrix (Fin 3) (Fin 3) Rat) (pts : List (Point × Point))
    (δ : Rat) : Option (Nat × Rat) :=
  let rec go (i : Nat) : List (Point × Point) → Option (Nat × Rat)
    | [] => none
    | p :: ps =>
      if residualWithin F p δ then go (i + 1) ps
      else some (i, epipolarResidual F p.1 p.2)
  go 0 pts

unsafe def certifyEpipolarCore (F : Syntax) (file : Syntax) (δ? : Option Syntax) :
    CommandElabM Unit := do
  let rawPath ← match file.isStrLit? with
    | some p => pure p
    | none => throwError "expected a string literal file name"
  let path ← resolvePath rawPath
  -- Read the matrix type off the quoted type rather than reconstructing it by hand:
  -- `Matrix` carries a universe level, and hand-built `Expr`s are easy to get wrong.
  let matTy ← liftTermElabM <| Term.elabTermAndSynthesize
    (← `(Matrix (Fin 3) (Fin 3) Rat)) (some (.sort .zero))
  let Fv ← evalTermUnsafe F matTy (Matrix (Fin 3) (Fin 3) Rat)
  let δv? ← match δ? with
    | none => pure none
    | some t => some <$> evalTermUnsafe t (mkConst ``Rat) Rat
  let content ← liftIO <| IO.FS.readFile path
  let pts ← match parsePoints (tokenize content) with
    | .ok pts => pure pts
    | .error msg => throwError "certificate parse error in {path}: {msg}"
  let δ := δv?.getD 0
  let bad := firstViolation Fv pts δ
  let zeroRes := (pts.filter fun p => epipolarResidual Fv p.1 p.2 == 0).length
  let maxRes := (pts.map fun p => epipolarResidual Fv p.1 p.2).foldl max 0
  let report := match δv? with
    | some δ => s!"tolerance δ = {δ}\nmax |residual| = {maxRes}"
    | none => s!"residuals exactly zero: {zeroRes}/{pts.length}"
  logInfo m!"certified-consensus — kernel-time certificate\n\
    file: {path}\nF =\n{renderMat Fv}\npoints: {pts.length}\n\
    rank two: {IsRankTwo Fv}\n{report}"
  if !IsRankTwo Fv then
    throwError "REJECTED — F is not rank two (det = {Fv.det})"
  match bad with
  | some (i, r) =>
    throwError "REJECTED — correspondence {i} has residual {r}, outside tolerance {δ}"
  | none => pure ()

@[implemented_by certifyEpipolarCore]
opaque certifyEpipolar (F : Syntax) (file : Syntax) (δ? : Option Syntax) : CommandElabM Unit

/-- Check an epipolar certificate at elaboration time. Compilation fails if the
certificate is invalid. -/
elab "#certify_epipolar" F:term "from" f:str : command =>
  certifyEpipolar F f none

/-- Check an epipolar certificate against an explicit rational tolerance. -/
elab "#certify_epipolar" F:term "from" f:str "tol" d:term : command =>
  certifyEpipolar F f (some d)

end CertifiedConsensus
