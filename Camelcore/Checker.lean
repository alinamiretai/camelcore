import Camelcore.Model
import Camelcore.Plan

/-!
# Camelcore.Checker (v2) — a decidable admission checker for the base policy

`Admits` is a Prop over an arbitrary policy. For the practical finite case with
the base policy (every argument flows to the recipients — the generalization of
`security_policy.py:base_security_policy`), we give a Bool checker
parameterized by a decidable flows-test and prove it sound and complete
against `Admits basePolicy`. Architecture unchanged from v1: maximal
generality in the core theorem, executable enforcement as a verified add-on.
-/

namespace Camelcore

/-- A decidable flows-test: a Bool function that correctly decides `Cap.flows`.
    In the finite-reader case (frozensets / `Public`, as in `readers.py`) this
    is implementable as a superset test with `Public` as top. -/
structure FlowsDec where
  test : Cap → Cap → Bool
  correct : ∀ a b, test a b = true ↔ Cap.flows a b

/-- The Bool admission checker: all args defined, and each arg's cap passes the
    decidable flows-test against the recipients. -/
def admitCheck (fd : FlowsDec) (σ : Store) (args : List Var) (rcpt : Recipients) : Bool :=
  match lookupAll σ args with
  | some vs => vs.all (fun vc => fd.test vc.2 rcpt)
  | none    => false

end Camelcore

namespace Camelcore

/-- **Checker correctness.** The Bool `admitCheck` returns true iff the base-
    policy gate admits: sound (true ⇒ admitted) and complete (admitted ⇒
    true). So the finite-case checker exactly implements the gate the
    noninterference theorem reasons about (via `basePolicySound`). -/
theorem admitCheck_correct (fd : FlowsDec) (σ : Store) (tool : Nat)
    (args : List Var) (rcpt : Recipients) :
    admitCheck fd σ args rcpt = true ↔ Admits basePolicy σ tool args rcpt := by
  unfold admitCheck Admits basePolicy
  cases hla : lookupAll σ args with
  | none =>
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨vs, hvs, _⟩
    exact absurd hvs (by simp)
  | some vs =>
    simp only [List.all_eq_true]
    constructor
    · intro h
      refine ⟨vs, rfl, ?_⟩
      intro c hc
      obtain ⟨vc, hvcmem, hvceq⟩ := List.mem_map.mp hc
      rw [← hvceq]
      exact (fd.correct vc.2 rcpt).mp (h vc hvcmem)
    · rintro ⟨vs', hvs', hflow⟩
      simp only [Option.some.injEq] at hvs'
      subst hvs'
      intro vc hvc
      exact (fd.correct vc.2 rcpt).mpr (hflow vc.2 (List.mem_map_of_mem hvc))

end Camelcore

#print axioms Camelcore.admitCheck_correct
