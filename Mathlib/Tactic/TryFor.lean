import Lean
open Lean
open Meta
open Elab
    open Tactic
open Core

syntax (name := tryFor) "try_for " term:max tacticSeq : tactic


#check checkMaxHeartbeats
#check withCurrHeartbeats

/-
https://github.com/leanprover/lean4/blob/20d6b9c4aaeb6263f903838c46b6343fe7814654/src/Lean/Parser/Term.lean#L34-L39
def tacticSeq1Indented : Parser :=
  leading_parser many1Indent (group (ppLine >> tacticParser >> optional ";"))
def tacticSeqBracketed : Parser :=
  leading_parser "{" >> many (group (ppLine >> tacticParser >> optional ";")) >> ppDedent (ppLine >> "}")
def tacticSeq :=
  leading_parser tacticSeqBracketed <|> tacticSeq1Indented
-/

-- for each tactic in `ts`, check heartbeats, then run the tactic?
-- I don't think this ensures that a tactic that takes a long time will be guarded?
#check maxHeartbeats
#check TacticM
#check ReaderT

-- def liftCoreM (x: CoreM α): TacticM α := do 
--   withReader (fun ctx => {} ) x

-- def setMaxHeartbeatsCore (max : Nat) (x: CoreM α): CoreM α := do
--   modifyMCtx (fun mctx => 
--    withReader (fun ctx => { ctx with maxHeartbeats := max }) x

-- abbrev TacticM := ReaderT Context $ StateRefT State TermElabM
-- abbrev TermElabM := ReaderT Context $ StateRefT State MetaM
-- abbrev MetaM  := ReaderT Context $ StateRefT State CoreM
-- abbrev CoreM := ReaderT Context <| StateRefT State (EIO Exception)
-- structure Context where
--   fileName       : String
--   fileMap        : FileMap
--   options        : Options := {}
--   currRecDepth   : Nat := 0
--   maxRecDepth    : Nat := 1000
--   ref            : Syntax := Syntax.missing
--   currNamespace  : Name := Name.anonymous
--   openDecls      : List OpenDecl := []
--   initHeartbeats : Nat := 0
--   maxHeartbeats  : Nat := getMaxHeartbeats options
--   currMacroScope : MacroScope := firstFrontendMacroScope
#check CoreM
#check MetaM
#check TermElabM
#check TacticM


private def startTryForCoreM (max: Nat) (x : CoreM α) : CoreM α := do
  let heartbeats ← IO.getNumHeartbeats
  withReader (fun ctx => { ctx with initHeartbeats := heartbeats, maxHeartbeats := max }) x

#check controlAt
def withStartTryForCoreM [Monad m] [MonadControlT CoreM m] (max: Nat) (x : m α) : m α :=
  controlAt CoreM fun runInBase => startTryForCoreM max (runInBase x)
  


/-
instance : MonadCoreCtx MetaM where 
  withCoreCtx k := do
    s <- StateT.get 
-/

-- def modifyCoreContext (ctx: Core.Context -> Core.Context) (t: TacticM Unit): TacticM Unit := 
--   modifyMCtx

-- | Changed type of time from `term` to `num` because all uses use
--   numeric literals.
-- elab "try_for " time:term  ts:tacticSeq : tactic => do
elab "try_for " timeStx:num  ts:tacticSeq : tactic => do
  let time := timeStx.getNat
  withStartTryForCoreM (time*1000) (do
    -- checkMaxHeartbeatsCore "Mathlib.Tactic.Tryfor" `maxHeartbeats (time*1000)
    evalTactic ts
  )


def ackermann: Nat -> Nat -> Nat
| 0, n => n + 1
| (m+1),  0 => m + 1
| (m+1),  (n+1) => ackermann m (ackermann (m+1) n)
termination_by _ m n => (m, n)

def thm_success : ackermann 4 5 = 211 := by {
  try_for 2 rfl;
}
#print thm_success

def thm1 : ackermann 4 1 = 11 := by {
  try_for 1 rfl;
}

def thm2 : ackermann 4 1 = 11 := by {
  try_for 50 rfl;
}

def thm3 : ackermann 4 1 = 11 := by {
  try_for 51 rfl; -- succeeds with 51 heartbeats
}

