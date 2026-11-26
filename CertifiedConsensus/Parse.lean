import CertifiedConsensus.Checker

/-!
# Parsing certificates

Shared tokenizer and rational parser for the command-line checker and the
`#certify_epipolar` command. All numbers are parsed as exact rationals: decimals
become `p / 10^k`, so no rounding ever enters the verification path.
-/

namespace CertifiedConsensus

/-- Parse an exact rational from `p/q`, `-p/q`, `12.5`, or `-3`. -/
def parseRat? (s : String) : Option Rat :=
  match s.splitOn "/" with
  | [a, b] =>
      match a.toInt?, b.toInt? with
      | some n, some d => if d = 0 then none else some (Rat.divInt n d)
      | _, _ => none
  | [a] =>
      let neg := a.startsWith "-"
      let a := if neg then (a.drop 1).toString else a
      let mk (v : Rat) : Rat := if neg then -v else v
      match a.splitOn "." with
      | [ip, fp] =>
          let i := ip.toNat?.getD 0
          let f := fp.toNat?.getD 0
          let den : Rat := (10 : Rat) ^ fp.length
          some (mk (((i : Rat) * den + f) / den))
      | [_] =>
          match a.toNat? with
          | some n => some (mk n)
          | none => none
      | _ => none
  | _ => none

/-- Split input into whitespace-separated tokens, dropping `#` comments. -/
def tokenize (content : String) : List String :=
  content.splitOn "\n" |>.flatMap (fun line =>
    let code := (line.splitOn "#").headD line
    (code.splitOn " ").filter (fun t => !t.isEmpty))

/-- Parse a list of tokens as rationals, failing on the first non-numeric token. -/
def parseRatList : List String → Except String (List Rat)
  | [] => .ok []
  | t :: ts =>
      match parseRat? t with
      | none => .error s!"not a rational: {t}"
      | some r =>
          match parseRatList ts with
          | .ok rs => .ok (r :: rs)
          | .error e => .error e

/-- Interpret a nonnegative rational as a natural number. -/
def ratToNat (r : Rat) : Nat := r.num.toNat

/-- Build the `i`-th correspondence from a flat coordinate list. -/
def pointAt (coords : List Rat) (t : Nat) : Point × Point :=
  let g (k : Nat) : Rat := coords.getD (4 * t + k) 0
  (homog (g 0) (g 1), homog (g 2) (g 3))

/-- Parse a points-only certificate: a count `n` followed by `4n` rationals. -/
def parsePoints (toks : List String) : Except String (List (Point × Point)) :=
  match parseRatList toks with
  | .error e => .error e
  | .ok [] => .error "empty certificate"
  | .ok (n :: coords) =>
      let cnt := ratToNat n
      if coords.length < 4 * cnt then
        .error s!"truncated certificate: expected {4 * cnt} coordinates, found {coords.length}"
      else
        .ok ((List.range cnt).map (pointAt coords))

end CertifiedConsensus
