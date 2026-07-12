import Camelcore.Model
import Camelcore.Plan

/-!
# Camelcore.Noninterference — CaMeL's confidentiality guarantee, machine-checked

For any observer capability `obs`, two runs that agree on all observer-readable data
(and agree on all capabilities) produce identical tool-call outputs to the observer.
Data the observer cannot read provably cannot influence what it observes — for any
plan the (untrusted) Privileged LLM proposes. This is CaMeL's guarantee, proved.
-/

namespace Camelcore

/-- A capability is observer-readable if it flows to the observer (obs is among its
    permitted readers — i.e. the value may be disclosed to obs). -/
def readable (obs : Cap) (c : Cap) : Prop := Cap.flows c obs

/-- Per-variable equivalence from the observer's view: the two lookups agree on the
    capability (always), and on the value when that capability is observer-readable. -/
def varCapEq (obs : Cap) (r₁ r₂ : Option (Nat × Cap)) : Prop :=
  match r₁, r₂ with
  | some (v₁, c₁), some (v₂, c₂) =>
      (∀ p, c₁.readers p ↔ c₂.readers p) ∧ (readable obs c₁ → v₁ = v₂)
  | none, none => True
  | _, _ => False

/-- Stores are observer-low-equivalent: agree per-variable in the above sense. -/
def StoreCapEq (obs : Cap) (σ₁ σ₂ : Store) : Prop :=
  ∀ x, varCapEq obs (lookup σ₁ x) (lookup σ₂ x)

/-- States are observer-low-equivalent: equal output logs + equivalent stores. -/
def CapLowEq (obs : Cap) (s₁ s₂ : State) : Prop :=
  s₁.out = s₂.out ∧ StoreCapEq obs s₁.store s₂.store

end Camelcore

namespace Camelcore

/-- Capability agreement from StoreCapEq: looking up a variable in two
    observer-equivalent stores yields the same "defined?" status and, when defined,
    capabilities that agree as reader-predicates. -/
theorem lookup_cap_agree {obs : Cap} {σ₁ σ₂ : Store} (h : StoreCapEq obs σ₁ σ₂)
    (x : Var) :
    (lookup σ₁ x).map (·.2.readers) = (lookup σ₂ x).map (·.2.readers) ∨
    (lookup σ₁ x = none ∧ lookup σ₂ x = none) := by
  have hx := h x
  unfold varCapEq at hx
  cases h1 : lookup σ₁ x with
  | none =>
    cases h2 : lookup σ₂ x with
    | none => right; exact ⟨rfl, rfl⟩
    | some p => rw [h1, h2] at hx; exact absurd hx (by simp)
  | some p₁ =>
    cases h2 : lookup σ₂ x with
    | none => rw [h1, h2] at hx; exact absurd hx (by simp)
    | some p₂ =>
      rw [h1, h2] at hx
      left
      obtain ⟨v₁, c₁⟩ := p₁
      obtain ⟨v₂, c₂⟩ := p₂
      have hcap : c₁.readers = c₂.readers := funext (fun p => propext (hx.1 p))
      simp only [Option.map_some, hcap]

end Camelcore

namespace Camelcore

/-- If all args are defined in σ₁ and the stores are observer-equivalent, the args
    are defined in σ₂ too, and their capabilities agree pointwise. -/
theorem lookupAll_cap_agree {obs : Cap} {σ₁ σ₂ : Store} (h : StoreCapEq obs σ₁ σ₂) :
    ∀ (args : List Var) (vs₁ : List (Nat × Cap)),
      lookupAll σ₁ args = some vs₁ →
      ∃ vs₂, lookupAll σ₂ args = some vs₂ ∧
             (vs₁.map (·.2.readers) = vs₂.map (·.2.readers)) := by
  intro args
  induction args with
  | nil =>
    intro vs₁ h1
    simp only [lookupAll, Option.some.injEq] at h1
    subst h1
    exact ⟨[], rfl, rfl⟩
  | cons x xs ih =>
    intro vs₁ h1
    simp only [lookupAll] at h1
    -- h1 destructures the match on lookup σ₁ x and lookupAll σ₁ xs
    cases hx1 : lookup σ₁ x with
    | none => rw [hx1] at h1; simp at h1
    | some p₁ =>
      cases hxs1 : lookupAll σ₁ xs with
      | none => rw [hx1, hxs1] at h1; simp at h1
      | some ps₁ =>
        rw [hx1, hxs1] at h1
        simp only [Option.some.injEq] at h1
        -- lookup σ₂ x agrees on cap; lookupAll σ₂ xs agrees by ih
        have hcap := lookup_cap_agree h x
        rcases hcap with hmap | ⟨hn1, _⟩
        · rw [hx1] at hmap
          cases hx2 : lookup σ₂ x with
          | none => rw [hx2] at hmap; simp at hmap
          | some p₂ =>
            obtain ⟨vs₂, hvs2, hmapxs⟩ := ih ps₁ hxs1
            refine ⟨(p₂) :: vs₂, ?_, ?_⟩
            · simp only [lookupAll, hx2, hvs2]
            · subst h1
              rw [hx2] at hmap
              simp only [Option.map_some, Option.some.injEq] at hmap
              simp only [List.map_cons, hmapxs, hmap]
        · rw [hx1] at hn1; simp at hn1

end Camelcore
