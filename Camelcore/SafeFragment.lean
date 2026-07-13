import Camelcore.Model
import Camelcore.Plan
import Camelcore.Control
import Camelcore.Noninterference
import Camelcore.Leak

/-!
# Camelcore.SafeFragment — a deployer-checkable safe fragment (Layer 3)

The leak (`Leak.lean`) shows plain noninterference is false for STRICT-mode
control flow. This file identifies a DECIDABLE, statically-checkable fragment of
plans on which noninterference is RECOVERED — the safe-usage boundary a deployer
can enforce on the *current* interpreter without any changes to CaMeL itself.

## The analysis

A forward dataflow pass computes the set of "branch-tainted" variables:

- Everything assigned inside ANY `ite` branch is branch-tainted (it may carry
  the control-flow taint of the branch condition).
- Taint launders through `compute`: if any source of a `compute` is tainted, its
  destination is tainted too. (This closes the `y := compute[x]` hole that a
  naive "only branch-assigned vars" predicate would miss — that naive predicate
  is UNSOUND, which is itself worth stating.)
- A plan is in the safe fragment iff no tool call ever takes a branch-tainted
  variable as an argument.

This is sound (a tainted var never reaches a tool call, so control-flow taint
never influences an admitted call's recipients) and decidable (a single forward
pass over the plan). It is deliberately conservative: it may reject some safe
plans, but it never accepts an unsafe one.

## Roadmap
1. Taint analysis + `SafeFragment` predicate + the unsoundness note (this file).
2. `safeFragment_NI`: noninterference holds on the safe fragment, in STRICT
    mode, for the same faithful semantics where the leak exists.   [next layer]
-/

namespace Camelcore

/-- Membership test on the tainted-variable list (Var = String has DecidableEq). -/
def tainted (T : List Var) (x : Var) : Bool := T.contains x

/-- All variables that a plan assigns to (targets of `assign`/`compute`, and
    recursively inside `ite` branches). These become branch-tainted when the
    plan appears inside an `ite`. -/
def assignedVars : List CStmt → List Var
  | [] => []
  | .assign x _ _ :: rest => x :: assignedVars rest
  | .compute dst _ :: rest => dst :: assignedVars rest
  | .toolCall dst _ _ _ :: rest => dst :: assignedVars rest
  | .ite _ thenB elseB :: rest =>
      assignedVars thenB ++ assignedVars elseB ++ assignedVars rest

/-- One statement's effect on the branch-tainted set, given the CURRENT tainted
    set `T`. `assign` outside a branch clears taint on its target (a fresh public
    literal); `compute` taints its target iff any source is tainted; `ite` taints
    everything assigned anywhere in either branch; `toolCall` does not change the
    set (its result var is tool-sourced, not control-flow-tainted).

    IMPORTANT (soundness): taint is never CLEARED. A static pass cannot see the
    runtime pc, so it cannot tell whether an `assign`/`compute` happens under a
    non-empty (branch) pc — where the assigned value would carry control-flow
    taint. We therefore keep any already-tainted variable tainted. This is
    conservative (a variable reassigned a public literal at top level stays
    flagged) but sound: it never treats a control-flow-tainted variable as
    clean. A fresh variable (not yet tainted) assigned a literal stays clean. -/
def taintStep (T : List Var) : CStmt → List Var
  | .assign _ _ _ => T                            -- monotone: never clear taint
  | .compute dst srcs =>
      if srcs.any (fun s => T.contains s) then dst :: T
      else T                                       -- monotone: never clear taint
  | .toolCall _ _ _ _ => T
  | .ite _ thenB elseB => assignedVars thenB ++ assignedVars elseB ++ T

/-- Fold the taint analysis across a plan, returning the tainted set after the
    whole plan (used compositionally by the safety predicate below). -/
def taintFold (T : List Var) : List CStmt → List Var
  | [] => T
  | st :: rest => taintFold (taintStep T st) rest

end Camelcore

namespace Camelcore

/-- A single statement is SAFE given tainted set `T` iff, when it is a tool call,
    none of its arguments is tainted. Other statements impose no condition here
    (their contribution to taint is handled by `taintStep`). -/
def stmtSafe (T : List Var) : CStmt → Prop
  | .toolCall _ _ args _ => ∀ a ∈ args, tainted T a = false
  | _ => True

mutual

/-- Branch-safety obligation for a statement: for an `ite`, both branches are
    recursively in the safe fragment under the branch-entered tainted set; for
    any other statement, vacuous. Named (not an inline `match`) so its type is
    stable across the definition and the paired-step lemma. -/
def branchSafe (Tset : List Var) : CStmt → Prop
  | .ite _ thenB elseB =>
      SafeFragmentFrom (assignedVars thenB ++ assignedVars elseB ++ Tset) thenB ∧
      SafeFragmentFrom (assignedVars thenB ++ assignedVars elseB ++ Tset) elseB
  | _ => True

/-- A plan is in the SAFE FRAGMENT given an initial tainted set: each statement
    is safe under the tainted set accumulated up to that point, and (for `ite`)
    both branches are recursively safe under the branch-entered tainted set. -/
def SafeFragmentFrom (T : List Var) : List CStmt → Prop
  | [] => True
  | st :: rest =>
      stmtSafe T st ∧ branchSafe T st ∧ SafeFragmentFrom (taintStep T st) rest

end

/-- A closed plan is in the safe fragment iff it is safe from the empty tainted
    set. This is the predicate a deployer checks. -/
def SafeFragment (prog : List CStmt) : Prop := SafeFragmentFrom [] prog

end Camelcore

namespace Camelcore

/-! ### The unsoundness of the naive predicate (a documented finding)

The naive "no variable assigned *directly* inside a branch is a tool arg"
predicate — which does NOT track laundering through `compute` — accepts the
plan `if secret: x := 1  ;  y := compute[x]  ;  send(y)`, because `y` is not
branch-assigned. But `y` carries `x`'s taint, so the send leaks. Our
`SafeFragment` rejects this plan (via `taintStep`'s `compute` case), which is
why the laundering-aware analysis is the sound choice. The witness plan itself
is deferred to the proof layer, where the machinery to evaluate `taintFold` on a
concrete plan is available. -/

end Camelcore

-- (Path 1 taint-relative machinery removed; Option A appears after the frame lemma.)

namespace Camelcore

open Classical

/-! ### Frame lemma: a plan only affects the variables it assigns

The linchpin for the `ite` case: variables NOT in `assignedVars prog` have
unchanged lookups after running `prog`. Since `cstep` prepends store entries
only for assigned variables and `lookup` takes the first match, an unassigned
variable's binding is never shadowed. This is what lets two runs take DIFFERENT
branches yet still agree on every non-tainted (hence unassigned-by-the-branch)
variable. -/

mutual

/-- One `cstep` only changes the lookup of variables it assigns. -/
theorem cstep_frame (Tenv : ToolEnv) (P : Policy) (m : Mode) (s : CState)
    (st : CStmt) (y : Var)
    (hy : y ∉ assignedVars [st]) (hnh : s.halted = false) :
    lookup (cstep Tenv P m s st).store y = lookup s.store y := by
  unfold cstep
  rw [if_neg (by rw [hnh]; decide : ¬ (s.halted = true))]
  cases st with
  | assign x n c =>
    -- assignedVars [assign x ..] = [x]; hy : y ∉ [x] ⇒ y ≠ x
    simp only [assignedVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    simp only [lookup, List.find?_cons]
    have : (x == y) = false := by
      rw [beq_eq_false_iff_ne]; exact fun h => hy h.symm
    rw [this]
  | compute dst srcs =>
    simp only [assignedVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    cases hla : lookupAll s.store srcs with
    | none => simp only [hla]
    | some vs =>
      simp only [hla, lookup, List.find?_cons]
      have : (dst == y) = false := by
        rw [beq_eq_false_iff_ne]; exact fun h => hy h.symm
      rw [this]
  | toolCall dst tool args rcpt =>
    simp only [assignedVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    cases hla : lookupAll s.store args with
    | none => simp only [hla]
    | some vs =>
      by_cases hadm : CAdmits P s.store s.pc tool args rcpt
      · simp only [hla, if_pos hadm, lookup, List.find?_cons]
        have : (dst == y) = false := by
          rw [beq_eq_false_iff_ne]; exact fun h => hy h.symm
        rw [this]
      · simp only [hla, if_neg hadm]
  | ite cond thenB elseB =>
    -- assignedVars [ite ..] = assignedVars thenB ++ assignedVars elseB
    simp only [assignedVars, List.append_nil, List.mem_append] at hy
    rw [not_or] at hy
    obtain ⟨hyT, hyE⟩ := hy
    cases hlc : lookup s.store cond with
    | none => simp only [hlc]
    | some p =>
      obtain ⟨v, c⟩ := p
      simp only [hlc]
      by_cases hv : v ≠ 0
      · simp only [if_pos hv]
        rw [cstepList_frame Tenv P m thenB _ y hyT]
      · simp only [if_neg hv]
        rw [cstepList_frame Tenv P m elseB _ y hyE]
  termination_by sizeOf st

/-- A plan only changes the lookup of variables it assigns. -/
theorem cstepList_frame (Tenv : ToolEnv) (P : Policy) (m : Mode)
    (prog : List CStmt) (s : CState) (y : Var)
    (hy : y ∉ assignedVars prog) :
    lookup (cstepList Tenv P m s prog).store y = lookup s.store y := by
  match prog with
  | [] => rfl
  | st :: rest =>
    have hsplit : y ∉ assignedVars [st] ∧ y ∉ assignedVars rest := by
      constructor
      · intro hmem
        apply hy
        cases st <;>
          simp_all [assignedVars, List.mem_append, List.mem_cons]
      · intro hmem; apply hy
        cases st <;>
          simp_all [assignedVars, List.mem_append, List.mem_cons]
    simp only [cstepList]
    rw [cstepList_frame Tenv P m rest (cstep Tenv P m s st) y hsplit.2]
    by_cases hnh : s.halted = true
    · unfold cstep; rw [if_pos hnh]
    · exact cstep_frame Tenv P m s st y hsplit.1 (by
        cases hh : s.halted with
        | false => rfl
        | true => exact absurd hh hnh)
  termination_by sizeOf prog

end

end Camelcore
