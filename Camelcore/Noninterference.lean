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

/-- The observer-visible projection of an output log: keep only the tool-call
    entries whose recipients the observer can read (readable obs entry.recipients).
    An observer sees exactly the calls disclosed to it. -/
noncomputable def visLog (obs : Cap) (log : List (Nat × List Nat × Cap)) :
    List (Nat × List Nat × Cap) :=
  log.filter (fun e => @decide (readable obs e.2.2) (Classical.propDecidable _))

/-- States are observer-low-equivalent: equal output logs + equivalent stores. -/
def CapLowEq (obs : Cap) (s₁ s₂ : State) : Prop :=
  visLog obs s₁.out = visLog obs s₂.out ∧ StoreCapEq obs s₁.store s₂.store

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

namespace Camelcore

/-- If two capabilities have the same readers (as predicates), one flows to a
    target iff the other does. -/
theorem flows_congr {c₁ c₂ t : Cap} (hc : c₁.readers = c₂.readers) :
    Cap.flows c₁ t ↔ Cap.flows c₂ t := by
  unfold Cap.flows
  rw [hc]

/-- Observer-equivalence of stores is symmetric. -/
theorem StoreCapEq.symm {obs : Cap} {σ₁ σ₂ : Store} (h : StoreCapEq obs σ₁ σ₂) :
    StoreCapEq obs σ₂ σ₁ := by
  intro x
  have hx := h x
  unfold varCapEq at hx ⊢
  cases h1 : lookup σ₁ x with
  | none =>
    cases h2 : lookup σ₂ x with
    | none => trivial
    | some p => rw [h1, h2] at hx; exact hx.elim
  | some p₁ =>
    cases h2 : lookup σ₂ x with
    | none => rw [h1, h2] at hx; exact hx.elim
    | some p₂ =>
      rw [h1, h2] at hx
      obtain ⟨v₁, c₁⟩ := p₁
      obtain ⟨v₂, c₂⟩ := p₂
      refine ⟨fun p => (hx.1 p).symm, fun hr => ?_⟩
      -- readable obs c₂ → v₂ = v₁; from cap-agreement, readable obs c₂ ↔ readable obs c₁
      have hcapeq : c₁.readers = c₂.readers := funext (fun p => propext (hx.1 p))
      have : readable obs c₁ := by unfold readable Cap.flows at hr ⊢; rw [hcapeq]; exact hr
      exact (hx.2 this).symm

/-- **Gate agreement.** On observer-equivalent stores, the gate admits a tool call
    in one run iff it admits it in the other: `Admits` inspects only capabilities,
    which agree. -/
theorem admits_agree {obs : Cap} {σ₁ σ₂ : Store} (h : StoreCapEq obs σ₁ σ₂)
    (args : List Var) (rcpt : Recipients) :
    Admits σ₁ args rcpt ↔ Admits σ₂ args rcpt := by
  unfold Admits
  constructor
  · rintro ⟨vs₁, hlk₁, hflow₁⟩
    obtain ⟨vs₂, hlk₂, hmap⟩ := lookupAll_cap_agree h args vs₁ hlk₁
    refine ⟨vs₂, hlk₂, ?_⟩
    -- caps of vs₂ match caps of vs₁ (via hmap on readers); flows transfers
    intro vc₂ hvc₂
    -- find the corresponding vc₁ with the same readers
    have : vc₂.2.readers ∈ vs₂.map (·.2.readers) := List.mem_map_of_mem hvc₂
    rw [← hmap] at this
    obtain ⟨vc₁, hvc₁mem, hreadeq⟩ := List.mem_map.mp this
    have := hflow₁ vc₁ hvc₁mem
    exact (flows_congr hreadeq).mp this
  · rintro ⟨vs₂, hlk₂, hflow₂⟩
    -- symmetric: use StoreCapEq symmetry
    have hsym : StoreCapEq obs σ₂ σ₁ := StoreCapEq.symm h
    obtain ⟨vs₁, hlk₁, hmap⟩ := lookupAll_cap_agree hsym args vs₂ hlk₂
    refine ⟨vs₁, hlk₁, ?_⟩
    intro vc₁ hvc₁
    have : vc₁.2.readers ∈ vs₁.map (·.2.readers) := List.mem_map_of_mem hvc₁
    rw [← hmap] at this
    obtain ⟨vc₂, hvc₂mem, hreadeq⟩ := List.mem_map.mp this
    have := hflow₂ vc₂ hvc₂mem
    exact (flows_congr hreadeq).mp this

end Camelcore

namespace Camelcore

/-- If the meet of a list of caps is observer-readable, then every cap in the list
    is observer-readable. (readable obs (meet cs) → ∀ c ∈ cs, readable obs c.)
    This is why `compute` is safe: a readable result had only readable sources. -/
theorem readable_meetList {obs : Cap} :
    ∀ (cs : List Cap), readable obs (Cap.meetList cs) → ∀ c ∈ cs, readable obs c := by
  intro cs
  induction cs with
  | nil => intro _ c hc; simp at hc
  | cons d ds ih =>
    intro hmeet c hc
    -- meetList (d :: ds) = meet d (meetList ds); readable of meet → readable of both
    unfold Cap.meetList at hmeet
    unfold readable Cap.flows Cap.meet at hmeet
    -- hmeet : ∀ p, obs.readers p → d.readers p ∧ (meetList ds).readers p
    rcases List.mem_cons.mp hc with hcd | hcds
    · subst hcd
      unfold readable Cap.flows
      intro p hp
      exact (hmeet p hp).1
    · have hds : readable obs (Cap.meetList ds) := by
        unfold readable Cap.flows
        intro p hp
        exact (hmeet p hp).2
      exact ih hds c hcds

end Camelcore

namespace Camelcore

open Classical

/-- If two cap-lists have equal readers pointwise (equal readers-maps), their
    meetLists have equal readers. Needed so  produces agreeing caps. -/
theorem meetList_readers_eq :
    ∀ (cs ds : List Cap), cs.map (·.readers) = ds.map (·.readers) →
      (Cap.meetList cs).readers = (Cap.meetList ds).readers := by
  intro cs
  induction cs with
  | nil =>
    intro ds hd
    cases ds with
    | nil => rfl
    | cons e es => simp at hd
  | cons c cs ih =>
    intro ds hd
    cases ds with
    | nil => simp at hd
    | cons e es =>
      simp only [List.map_cons, List.cons.injEq] at hd
      obtain ⟨hce, hrest⟩ := hd
      simp only [Cap.meetList, Cap.meet]
      funext p
      rw [hce, ih es hrest]

/-- If two stores are observer-equivalent and lookupAll succeeds on both with all
    result caps observer-readable, the looked-up VALUES agree. (Companion to
    lookupAll_cap_agree, for the value half under a readability condition.) -/
theorem lookupAll_val_agree {obs : Cap} {σ₁ σ₂ : Store} (h : StoreCapEq obs σ₁ σ₂) :
    ∀ (args : List Var) (vs₁ vs₂ : List (Nat × Cap)),
      lookupAll σ₁ args = some vs₁ → lookupAll σ₂ args = some vs₂ →
      (∀ c ∈ vs₁.map (·.2), readable obs c) →
      vs₁.map (·.1) = vs₂.map (·.1) := by
  intro args
  induction args with
  | nil =>
    intro vs₁ vs₂ h1 h2 _
    simp only [lookupAll, Option.some.injEq] at h1 h2
    subst h1; subst h2; rfl
  | cons x xs ih =>
    intro vs₁ vs₂ h1 h2 hread
    simp only [lookupAll] at h1 h2
    cases hx1 : lookup σ₁ x with
    | none => rw [hx1] at h1; simp at h1
    | some p₁ =>
      cases hxs1 : lookupAll σ₁ xs with
      | none => rw [hx1, hxs1] at h1; simp at h1
      | some ps₁ =>
        cases hx2 : lookup σ₂ x with
        | none => rw [hx2] at h2; simp at h2
        | some p₂ =>
          cases hxs2 : lookupAll σ₂ xs with
          | none => rw [hx2, hxs2] at h2; simp at h2
          | some ps₂ =>
            rw [hx1, hxs1] at h1; rw [hx2, hxs2] at h2
            simp only [Option.some.injEq] at h1 h2
            subst h1; subst h2
            -- head values agree (x readable via hread), tail by ih
            have hvx := h x
            unfold varCapEq at hvx
            rw [hx1, hx2] at hvx
            obtain ⟨v₁, c₁⟩ := p₁; obtain ⟨v₂, c₂⟩ := p₂
            have hreadhd : readable obs c₁ := by
              apply hread; simp [List.map_cons]
            have hveq : v₁ = v₂ := hvx.2 hreadhd
            have htail : ps₁.map (·.1) = ps₂.map (·.1) := by
              apply ih ps₁ ps₂ hxs1 hxs2
              intro c hc; apply hread; simp only [List.map_cons]; exact List.mem_cons_of_mem _ hc
            simp only [List.map_cons, hveq, htail]

/-- **The paired-step lemma (the heart).** One statement, executed on two
    observer-equivalent states, yields observer-equivalent states. The three cases:
    - `assign`: same literal + cap added to both; trivially preserved.
    - `compute`: the result cap is the meet of sources; if readable, all sources
      were readable (readable_meetList) so their values agreed, so the result
      agrees. Caps agree because source caps agree.
    - `toolCall`: both runs admit-or-block identically (admits_agree); when both
      admit and log, the logged values agree because an admitted call's args all
      flow to the recipients — and this is where CaMeL's security becomes a theorem.
    -/
theorem step_preserves_capLowEq {obs : Cap} (st : Stmt) {s₁ s₂ : State}
    (h : CapLowEq obs s₁ s₂) : CapLowEq obs (step s₁ st) (step s₂ st) := by
  obtain ⟨hout, hstore⟩ := h
  cases st with
  | assign x n c =>
    -- both prepend (x, n, c) to their stores; out unchanged
    refine ⟨hout, ?_⟩
    intro y
    have hs := hstore y
    simp only [step, lookup, List.find?_cons] at hs ⊢
    cases hxy : (x == y) with
    | true => simp only [hxy]; unfold varCapEq; exact ⟨fun p => Iff.rfl, fun _ => rfl⟩
    | false => simp only [hxy] at hs ⊢; exact hs
  | compute dst srcs =>
    refine ⟨?_, ?_⟩
    · simp only [step]; cases lookupAll s₁.store srcs <;> cases lookupAll s₂.store srcs <;> exact hout
    intro y
    simp only [step]
    cases hla1 : lookupAll s₁.store srcs with
    | none =>
      cases hla2 : lookupAll s₂.store srcs with
      | none => simp only [hla1, hla2]; exact hstore y
      | some vs2 =>
        obtain ⟨vs1, hla1', _⟩ := lookupAll_cap_agree hstore.symm srcs vs2 hla2
        rw [hla1] at hla1'; exact absurd hla1' (by simp)
    | some vs1 =>
      obtain ⟨vs2, hla2, hmapread⟩ := lookupAll_cap_agree hstore srcs vs1 hla1
      simp only [hla1, hla2, lookup, List.find?_cons]
      cases hdy : (dst == y) with
      | true =>
        simp only [hdy]
        unfold varCapEq
        have hmapread' : (vs1.map (·.2)).map (·.readers) = (vs2.map (·.2)).map (·.readers) := by
          simp only [List.map_map]; exact hmapread
        refine ⟨fun p => by rw [meetList_readers_eq _ _ hmapread'], fun hread => ?_⟩
        -- result readable ⇒ all source caps readable ⇒ source values agree ⇒ sums agree
        have hallread : ∀ c ∈ vs1.map (·.2), readable obs c := by
          apply readable_meetList
          simpa using hread
        -- each source value agrees, so the folded sums agree
        have hvaleq : vs1.map (·.1) = vs2.map (·.1) :=
          lookupAll_val_agree hstore srcs vs1 vs2 hla1 hla2 hallread
        rw [hvaleq]
      | false =>
        simp only [hdy]
        exact hstore y
  | toolCall tool args rcpt =>
    -- store unchanged by toolCall; all content is in the visLog
    have hstore' : StoreCapEq obs (step s₁ (Stmt.toolCall tool args rcpt)).store
                                   (step s₂ (Stmt.toolCall tool args rcpt)).store := by
      simp only [step]
      by_cases ha : Admits s₁.store args rcpt <;>
        (by_cases ha2 : Admits s₂.store args rcpt <;>
          · simp only [ha, ha2, if_true, if_false] <;>
            (cases lookupAll s₁.store args <;> cases lookupAll s₂.store args <;>
              simp_all [hstore]))
    refine ⟨?_, hstore'⟩
    -- visLog agreement
    simp only [step]
    by_cases ha : Admits s₁.store args rcpt
    · have ha2 : Admits s₂.store args rcpt := (admits_agree hstore args rcpt).mp ha
      simp only [ha, ha2, if_true]
      -- both admit; sub-case on lookupAll (defined by admits) and readability of rcpt
      obtain ⟨vs₁, hlk₁, hflow₁⟩ := ha
      obtain ⟨vs₂, hlk₂, hflow₂⟩ := ha2
      simp only [hlk₁, hlk₂]
      by_cases hr : readable obs rcpt
      · -- rcpt readable: entries pass filter; must show values equal
        have hallread : ∀ c ∈ vs₁.map (·.2), readable obs c := by
          intro c hc
          obtain ⟨vc, hvcmem, hvceq⟩ := List.mem_map.mp hc
          have hf := hflow₁ vc hvcmem
          -- vc.2 flows to rcpt, rcpt flows to obs ⇒ vc.2 flows to obs
          unfold readable at hr ⊢
          rw [← hvceq]
          intro p hp
          exact hf p (hr p hp)
        have hvaleq : vs₁.map (·.1) = vs₂.map (·.1) :=
          lookupAll_val_agree hstore args vs₁ vs₂ hlk₁ hlk₂ hallread
        have hout' : List.filter (fun e => @decide (readable obs e.2.2) (Classical.propDecidable _)) s₁.out
                   = List.filter (fun e => @decide (readable obs e.2.2) (Classical.propDecidable _)) s₂.out := hout
        simp only [visLog, List.filter_append, hvaleq, hout']
      · -- rcpt not readable: new entries filtered out of both visLogs
        have hout' : List.filter (fun e => @decide (readable obs e.2.2) (Classical.propDecidable _)) s₁.out
                   = List.filter (fun e => @decide (readable obs e.2.2) (Classical.propDecidable _)) s₂.out := hout
        have hdf : @decide (readable obs rcpt) (Classical.propDecidable _) = false :=
          decide_eq_false_iff_not.mpr hr
        simp only [visLog, List.filter_append, List.filter_cons, hdf, Bool.false_eq_true,
                   if_false, List.filter_nil, List.append_nil]
        exact hout'
    · have ha2 : ¬ Admits s₂.store args rcpt := fun h => ha ((admits_agree hstore args rcpt).mpr h)
      simp only [ha, ha2, if_false]
      cases lookupAll s₁.store args <;> cases lookupAll s₂.store args <;> exact hout


end Camelcore

namespace Camelcore

/-- **CaMeL noninterference (the theorem).** For any observer capability, running a
    plan on two observer-equivalent states yields observer-equivalent states: data
    the observer cannot read cannot influence the tool calls it observes — for any
    plan the (untrusted) Privileged LLM proposes. This is CaMeL's guarantee. -/
theorem cap_noninterference {obs : Cap} (prog : List Stmt) {s₁ s₂ : State}
    (h : CapLowEq obs s₁ s₂) : CapLowEq obs (run s₁ prog) (run s₂ prog) := by
  unfold run
  induction prog generalizing s₁ s₂ with
  | nil => exact h
  | cons st sts ih => exact ih (step_preserves_capLowEq st h)

end Camelcore

#print axioms Camelcore.cap_noninterference
