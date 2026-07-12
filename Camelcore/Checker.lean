import Camelcore.Model
import Camelcore.Plan

/-!
# Camelcore.Checker — a decidable admission checker

`Admits` is a Prop (undecidable over arbitrary/infinite principal sets). For the
practical finite case, we give a Bool checker parameterized by a decidable test for
`flows`, and prove it sound and complete against `Admits`. This mirrors AttnNI's
`wellMaskedCheck` + correctness bridge: maximal generality in the core theorem,
executable enforcement as a verified add-on.
-/

namespace Camelcore

/-- A decidable flows-test: a Bool function that correctly decides `Cap.flows`.
    In the finite-reader case this is implementable (superset of finite sets). -/
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

/-- **Checker correctness.** The Bool `admitCheck` returns true iff the proposition
    `Admits` holds: sound (true ⇒ admitted) and complete (admitted ⇒ true). So the
    finite-case checker exactly implements the gate the noninterference theorem
    reasons about. -/
theorem admitCheck_correct (fd : FlowsDec) (σ : Store) (args : List Var)
    (rcpt : Recipients) :
    admitCheck fd σ args rcpt = true ↔ Admits σ args rcpt := by
  unfold admitCheck Admits
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
      intro vc hvc
      exact (fd.correct vc.2 rcpt).mp (h vc hvc)
    · rintro ⟨vs', hvs', hflow⟩
      simp only [Option.some.injEq] at hvs'
      subst hvs'
      intro vc hvc
      exact (fd.correct vc.2 rcpt).mpr (hflow vc hvc)

end Camelcore

#print axioms Camelcore.admitCheck_correct
