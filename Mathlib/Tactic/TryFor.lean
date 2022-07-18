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
-- | Changed type of time from `term` to `num` because all uses use
--   numeric literals.
-- elab "try_for " time:term  ts:tacticSeq : tactic => do
elab "try_for " timeStx:num  ts:tacticSeq : tactic => do
  let time := timeStx.getNat
  withCurrHeartbeats (do
    -- multiply time by 1000 because Lean internally divides by 
    -- 1000 to report error messages
    checkMaxHeartbeatsCore "Mathlib.Tactic.Tryfor" `maxHeartbeats (time*1000)
    evalTactic ts
  )


def ackermann: Nat -> Nat -> Nat
| 0, n => n + 1
| (m+1),  0 => m + 1
| (m+1),  (n+1) => ackermann m (ackermann (m+1) n)
termination_by _ m n => (m, n)

def thm_success : ackermann 4 5 = 211 := by {
  rfl;
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

