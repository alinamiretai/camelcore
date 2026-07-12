import Camelcore.Model

/-!
# Camelcore.Plan — operations, the tool-call gate (as a proposition), execution

The gate `Admits` is a PROPOSITION, not a Bool: this makes the noninterference
theorem hold for arbitrary capability lattices (even infinite principal spaces),
since the theorem is a hyperproperty and never needs to execute the gate. A
decidable checker for the finite case is layered on later (Checker.lean), proved
sound and complete against `Admits` — the strongest architecture: maximal
generality in the core, executability as a verified add-on.
-/

namespace Camelcore

abbrev Recipients := Cap

inductive Stmt where
  | assign   (x : Var) (n : Nat) (c : Cap)
  | compute  (dst : Var) (srcs : List Var)
  | toolCall (tool : Nat) (args : List Var) (rcpt : Recipients)

structure State where
  store : Store
  out   : List (Nat × List Nat × Cap)

def lookupAll (σ : Store) : List Var → Option (List (Nat × Cap))
  | [] => some []
  | x :: xs =>
    match lookup σ x, lookupAll σ xs with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- The gate as a PROPOSITION: a tool call is admitted iff the arguments are all
    defined and every argument's capability flows to the recipients. -/
def Admits (σ : Store) (args : List Var) (rcpt : Recipients) : Prop :=
  ∃ vs, lookupAll σ args = some vs ∧ ∀ vc ∈ vs, Cap.flows vc.2 rcpt

end Camelcore

namespace Camelcore

open Classical

/-- Apply one statement.
    - `assign`: bind x to (n, c).
    - `compute`: bind dst to a value whose capability is the MEET of the srcs'
      caps (dependency-graph taint). Undefined src ⇒ no-op.
    - `toolCall`: if admitted (args' caps flow to recipients), log (tool, values)
      to the observable output; else no-op. The `if` is on a Prop, made total by
      classical decidability — caps stay arbitrary (strongest theorem). -/
noncomputable def step (s : State) (st : Stmt) : State :=
  match st with
  | .assign x n c => { s with store := (x, n, c) :: s.store }
  | .compute dst srcs =>
      match lookupAll s.store srcs with
      | some vs =>
          let cap := Cap.meetList (vs.map (·.2))
          let val := (vs.map (·.1)).foldl (· + ·) 0
          { s with store := (dst, val, cap) :: s.store }
      | none => s
  | .toolCall tool args rcpt =>
      if Admits s.store args rcpt then
        match lookupAll s.store args with
        | some vs => { s with out := s.out ++ [(tool, vs.map (·.1), rcpt)] }
        | none => s
      else s

/-- Run a plan: fold step over the statements. -/
noncomputable def run (s : State) (prog : List Stmt) : State :=
  prog.foldl step s

end Camelcore
