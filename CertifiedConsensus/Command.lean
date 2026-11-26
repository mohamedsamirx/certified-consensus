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
    let e ← Term.elabTerm stx (some expected)
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    Meta.evalExpr hostType expected e

unsafe def certifyEpipolarCore (F : Syntax) (file : Syntax) (δ? : Option Syntax) :
    CommandElabM Unit := do
  let path ← match file.isStrLit? with
    | some p => pure p
    | none => throwError "expected a string literal file name"
  let matTy ← liftTermElabM do
    let ty ← inferType (mkConst ``checkEpipolar)
    pure ty.bindingDomain!
  let Fv ← evalTermUnsafe F matTy (Matrix (Fin 3) (Fin 3) Rat)
  let δv? ← match δ? with
    | none => pure none
    | some t => some <$> evalTermUnsafe t (mkConst ``Rat) Rat
  let content ← liftIO <| IO.FS.readFile path
  let pts ← match parsePoints (tokenize content) with
    | .ok pts => pure pts
    | .error msg => throwError "certificate parse error: {msg}"
  let ok := match δv? with
    | some δ => checkEpipolarTol δ pts Fv
    | none => checkEpipolar Fv pts
  let maxRes := (pts.map fun p => epipolarResidual Fv p.1 p.2).foldl max 0
  let zeroRes := (pts.filter fun p => epipolarResidual Fv p.1 p.2 == 0).length
  let body := match δv? with
    | some δ => s!"tolerance δ = {δ}\nmax |residual| = {maxRes}"
    | none => s!"residuals exactly zero: {zeroRes}/{pts.length}"
  logInfo m!"certified-consensus — kernel-time certificate\n\
    file: {path}\nF =\n{renderMat Fv}\npoints: {pts.length}\n\
    rank two: {IsRankTwo Fv}\n{body}"
  unless ok do
    throwError "REJECTED — rank or residual check failed"

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
