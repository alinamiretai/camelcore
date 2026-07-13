import Camelcore.Model
import Camelcore.Plan

/-!
# Camelcore.Noninterference (v2) — CaMeL's confidentiality guarantee, machine-checked

For any observer capability `obs`, any deterministic tool environment, and ANY
sound capability-only policy: two runs of a plan that agree on all
observer-readable data (and agree on all capabilities) produce identical
observer-visible tool-call outputs, identical halt status, and observer-
equivalent stores. Data the observer cannot read provably cannot influence what
it observes — for any plan the (untrusted) Privileged LLM proposes.

Compared to v1:
- capabilities carry sources as well as readers (both must agree);
- tool calls return labeled values into the store (`wrap_output` modeled);
- policy denial and undefined variables HALT, and halt-status is part of the
  low-equivalence (the guarantee is termination-sensitive w.r.t. denial);
- the theorem quantifies over every `SoundPolicy`, i.e. every policy that is
  (a) capability-only and (b) at least as strict as reader-flow. Both
  conditions are necessary: (a) fails for the implementation's value-inspecting
  `SecurityPolicy` protocol, (b) fails for e.g. the trivial always-allow policy.

Simplification exploited throughout: both runs execute the SAME plan, so
capabilities agree on the nose — `varCapEq` demands equality of capabilities,
not merely pointwise agreement of reader predicates. This eliminates v1's
`flows_congr` / `meetList_readers_eq` congruence plumbing.
-/

namespace Camelcore

/-- A capability is observer-readable if it flows to the observer. -/
def readable (obs : Cap) (c : Cap) : Prop := Cap.flows c obs

/-- Per-variable equivalence from the observer's view: the two lookups agree on
    the capability (always, on the nose), and on the value when that capability
    is observer-readable. -/
def varCapEq (obs : Cap) (r₁ r₂ : Option (Nat × Cap)) : Prop :=
  match r₁, r₂ with
  | some pc₁, some pc₂ => pc₁.2 = pc₂.2 ∧ (readable obs pc₁.2 → pc₁.1 = pc₂.1)
  | none, none => True
  | _, _ => False

/-- Stores are observer-low-equivalent: agree per-variable in the above sense. -/
def StoreCapEq (obs : Cap) (σ₁ σ₂ : Store) : Prop :=
  ∀ x, varCapEq obs (lookup σ₁ x) (lookup σ₂ x)

/-- The observer-visible projection of an output log: keep only the tool-call
    entries whose recipients the observer can read. -/
noncomputable def visLog (obs : Cap) (log : List (Nat × List Nat × Cap)) :
    List (Nat × List Nat × Cap) :=
  log.filter (fun e => @decide (readable obs e.2.2) (Classical.propDecidable _))

/-- States are observer-low-equivalent: equal halt status + equal visible
    output logs + equivalent stores. -/
def CapLowEq (obs : Cap) (s₁ s₂ : State) : Prop :=
  s₁.halted = s₂.halted ∧ visLog obs s₁.out = visLog obs s₂.out ∧
    StoreCapEq obs s₁.store s₂.store

end Camelcore

namespace Camelcore

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
      refine ⟨hx.1.symm, fun hr => ?_⟩
      have hr' : readable obs p₁.2 := by rw [hx.1]; exact hr
      exact (hx.2 hr').symm

/-- If all args are defined in σ₁ and the stores are observer-equivalent, the
    args are defined in σ₂ too, and their capabilities are EQUAL pointwise. -/
theorem lookupAll_cap_agree {obs : Cap} {σ₁ σ₂ : Store} (h : StoreCapEq obs σ₁ σ₂) :
    ∀ (args : List Var) (vs₁ : List (Nat × Cap)),
      lookupAll σ₁ args = some vs₁ →
      ∃ vs₂, lookupAll σ₂ args = some vs₂ ∧ vs₁.map (·.2) = vs₂.map (·.2) := by
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
    cases hx1 : lookup σ₁ x with
    | none => rw [hx1] at h1; simp at h1
    | some p₁ =>
      cases hxs1 : lookupAll σ₁ xs with
      | none => rw [hx1, hxs1] at h1; simp at h1
      | some ps₁ =>
        rw [hx1, hxs1] at h1
        simp only [Option.some.injEq] at h1
        subst h1
        have hvx := h x
        unfold varCapEq at hvx
        rw [hx1] at hvx
        cases hx2 : lookup σ₂ x with
        | none => rw [hx2] at hvx; exact hvx.elim
        | some p₂ =>
          rw [hx2] at hvx
          obtain ⟨ps₂, hps₂, hmapxs⟩ := ih ps₁ hxs1
          refine ⟨p₂ :: ps₂, ?_, ?_⟩
          · simp only [lookupAll, hx2, hps₂]
          · simp only [List.map_cons, hmapxs, hvx.1]

/-- Companion for the value half: if lookupAll succeeds on both observer-
    equivalent stores and all result caps are observer-readable, the looked-up
    VALUES agree. -/
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
            have hvx := h x
            unfold varCapEq at hvx
            rw [hx1, hx2] at hvx
            have hreadhd : readable obs p₁.2 := by
              apply hread; simp [List.map_cons]
            have hveq : p₁.1 = p₂.1 := hvx.2 hreadhd
            have htail : ps₁.map (·.1) = ps₂.map (·.1) := by
              apply ih ps₁ ps₂ hxs1 hxs2
              intro c hc; apply hread
              simp only [List.map_cons]
              exact List.mem_cons_of_mem _ hc
            simp only [List.map_cons, hveq, htail]

/-- **Gate agreement.** On observer-equivalent stores, ANY capability-only
    policy admits a tool call in one run iff it admits it in the other: the
    gate inspects only capabilities, which are equal. (In v1 this was a page of
    congruence reasoning; with on-the-nose capability agreement it is a
    rewrite — the proof itself exhibits WHY capability-only policies are the
    safe class.) -/
theorem admits_agree {obs : Cap} {σ₁ σ₂ : Store} (h : StoreCapEq obs σ₁ σ₂)
    (P : Policy) (tool : Nat) (args : List Var) (rcpt : Recipients) :
    Admits P σ₁ tool args rcpt ↔ Admits P σ₂ tool args rcpt := by
  unfold Admits
  constructor
  · rintro ⟨vs₁, hlk₁, hp⟩
    obtain ⟨vs₂, hlk₂, hmap⟩ := lookupAll_cap_agree h args vs₁ hlk₁
    exact ⟨vs₂, hlk₂, hmap ▸ hp⟩
  · rintro ⟨vs₂, hlk₂, hp⟩
    obtain ⟨vs₁, hlk₁, hmap⟩ := lookupAll_cap_agree (StoreCapEq.symm h) args vs₂ hlk₂
    exact ⟨vs₁, hlk₁, hmap ▸ hp⟩

end Camelcore

namespace Camelcore

/-- If the meet of a list of caps is observer-readable, then every cap in the
    list is observer-readable. This is why `compute` is safe: a readable result
    had only readable sources. (Readers-only reasoning; unchanged from v1 apart
    from `Cap.meet` now also carrying sources, which this proof never touches.) -/
theorem readable_meetList {obs : Cap} :
    ∀ (cs : List Cap), readable obs (Cap.meetList cs) → ∀ c ∈ cs, readable obs c := by
  intro cs
  induction cs with
  | nil => intro _ c hc; simp at hc
  | cons d ds ih =>
    intro hmeet c hc
    unfold Cap.meetList at hmeet
    unfold readable Cap.flows Cap.meet at hmeet
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

/-- Readability of a meet gives readability of the right component. Used for
    tool results: readable(toolResultCap t caps) ⇒ readable(meetList caps). -/
theorem readable_meet_right {obs a b : Cap} (h : readable obs (Cap.meet a b)) :
    readable obs b := by
  unfold readable Cap.flows at h ⊢
  unfold Cap.meet at h
  intro p hp
  exact (h p hp).2

end Camelcore

namespace Camelcore

open Classical

/-- **The paired-step lemma (the heart).** One statement, executed with the same
    tool oracle and the same sound capability-only policy on two observer-
    equivalent states, yields observer-equivalent states. The cases:
    - halted: both runs are stuck identically (halt status agreed).
    - `assign`: same literal + cap added to both; trivially preserved.
    - `compute`: the result cap is the meet of sources; if readable, all
      sources were readable (`readable_meetList`) so their values agreed, so
      the folded result agrees. Caps agree by rewriting. Undefined ⇒ both halt.
    - `toolCall`: both runs admit-or-deny identically (`admits_agree`, using
      only that the policy is capability-only). When both admit: the stored
      result agrees because a readable result cap forces readable argument
      caps, hence equal argument values, hence equal oracle outputs; the
      logged entry agrees because `enforces_flow` (policy soundness) makes an
      admitted call's arguments readable whenever the recipients are — this is
      where CaMeL's security becomes a theorem, and where BOTH conditions on
      the policy are consumed. When both deny: both halt. -/
theorem step_preserves_capLowEq {obs : Cap} (T : ToolEnv) (SP : SoundPolicy)
    (st : Stmt) {s₁ s₂ : State} (h : CapLowEq obs s₁ s₂) :
    CapLowEq obs (step T SP.P s₁ st) (step T SP.P s₂ st) := by
  obtain ⟨hhalt, hout, hstore⟩ := h
  have hout' : List.filter (fun e => @decide (readable obs e.2.2) (Classical.propDecidable _)) s₁.out
             = List.filter (fun e => @decide (readable obs e.2.2) (Classical.propDecidable _)) s₂.out := hout
  by_cases hh : s₁.halted = true
  · have hh2 : s₂.halted = true := by rw [← hhalt]; exact hh
    unfold step
    rw [if_pos hh, if_pos hh2]
    exact ⟨hhalt, hout, hstore⟩
  · have hh2 : ¬(s₂.halted = true) := by rw [← hhalt]; exact hh
    unfold step
    rw [if_neg hh, if_neg hh2]
    cases st with
    | assign x n c =>
      simp only [step1]
      refine ⟨hhalt, hout, ?_⟩
      intro y
      have hs := hstore y
      simp only [lookup, List.find?_cons] at hs ⊢
      cases hxy : (x == y) with
      | true =>
        unfold varCapEq
        exact ⟨rfl, fun _ => rfl⟩
      | false =>
        exact hs
    | compute dst srcs =>
      cases hla1 : lookupAll s₁.store srcs with
      | none =>
        cases hla2 : lookupAll s₂.store srcs with
        | none =>
          simp only [step1, hla1, hla2]
          exact ⟨rfl, hout, hstore⟩
        | some vs2 =>
          obtain ⟨vs1, hla1', _⟩ := lookupAll_cap_agree (StoreCapEq.symm hstore) srcs vs2 hla2
          rw [hla1] at hla1'
          exact absurd hla1' (by simp)
      | some vs1 =>
        obtain ⟨vs2, hla2, hmap⟩ := lookupAll_cap_agree hstore srcs vs1 hla1
        simp only [step1, hla1, hla2]
        refine ⟨hhalt, hout, ?_⟩
        intro y
        simp only [lookup, List.find?_cons]
        cases hdy : (dst == y) with
        | true =>
          unfold varCapEq
          refine ⟨by rw [hmap], fun hread => ?_⟩
          have hallread : ∀ c ∈ vs1.map (·.2), readable obs c := by
            apply readable_meetList
            simpa using hread
          have hvaleq : vs1.map (·.1) = vs2.map (·.1) :=
            lookupAll_val_agree hstore srcs vs1 vs2 hla1 hla2 hallread
          rw [hvaleq]
        | false =>
          exact hstore y
    | toolCall dst tool args rcpt =>
      cases hla1 : lookupAll s₁.store args with
      | none =>
        cases hla2 : lookupAll s₂.store args with
        | none =>
          simp only [step1, hla1, hla2]
          exact ⟨rfl, hout, hstore⟩
        | some vs2 =>
          obtain ⟨vs1, hla1', _⟩ := lookupAll_cap_agree (StoreCapEq.symm hstore) args vs2 hla2
          rw [hla1] at hla1'
          exact absurd hla1' (by simp)
      | some vs₁ =>
        obtain ⟨vs₂, hla2, hmap⟩ := lookupAll_cap_agree hstore args vs₁ hla1
        by_cases ha : Admits SP.P s₁.store tool args rcpt
        · have ha2 : Admits SP.P s₂.store tool args rcpt :=
            (admits_agree hstore SP.P tool args rcpt).mp ha
          simp only [step1, hla1, hla2, ha, ha2, if_true]
          -- Extract the flow guarantee from the admitted gate (policy soundness).
          obtain ⟨vs₁', hlk₁', hp⟩ := ha
          rw [hla1] at hlk₁'
          simp only [Option.some.injEq] at hlk₁'
          subst hlk₁'
          have hflow : ∀ c ∈ vs₁.map (·.2), Cap.flows c rcpt :=
            SP.enforces_flow tool (vs₁.map (·.2)) rcpt hp
          refine ⟨hhalt, ?_, ?_⟩
          · -- visLog agreement for the appended entry
            by_cases hr : readable obs rcpt
            · have hallread : ∀ c ∈ vs₁.map (·.2), readable obs c := by
                intro c hc
                have hf := hflow c hc
                unfold readable Cap.flows at hr ⊢
                unfold Cap.flows at hf
                intro p hp'
                exact hf p (hr p hp')
              have hvaleq : vs₁.map (·.1) = vs₂.map (·.1) :=
                lookupAll_val_agree hstore args vs₁ vs₂ hla1 hla2 hallread
              simp only [visLog, List.filter_append, hvaleq, hout']
            · have hdf : @decide (readable obs rcpt) (Classical.propDecidable _) = false :=
                decide_eq_false_iff_not.mpr hr
              simp only [visLog, List.filter_append, List.filter_cons, hdf,
                         Bool.false_eq_true, if_false, List.filter_nil, List.append_nil]
              exact hout'
          · -- store agreement, including the newly bound tool result
            intro y
            simp only [lookup, List.find?_cons]
            cases hdy : (dst == y) with
            | true =>
              unfold varCapEq
              refine ⟨by unfold toolResultCap; rw [hmap], fun hread => ?_⟩
              unfold toolResultCap at hread
              have hread' : readable obs (Cap.meetList (vs₁.map (·.2))) :=
                readable_meet_right hread
              have hallread : ∀ c ∈ vs₁.map (·.2), readable obs c :=
                readable_meetList (vs₁.map (·.2)) hread'
              have hvaleq : vs₁.map (·.1) = vs₂.map (·.1) :=
                lookupAll_val_agree hstore args vs₁ vs₂ hla1 hla2 hallread
              rw [hvaleq]
            | false =>
              exact hstore y
        · have ha2 : ¬ Admits SP.P s₂.store tool args rcpt :=
            fun h' => ha ((admits_agree hstore SP.P tool args rcpt).mpr h')
          simp only [step1, hla1, hla2, ha, ha2, if_false]
          exact ⟨rfl, hout, hstore⟩

end Camelcore

namespace Camelcore

/-- **CaMeL noninterference (the theorem).** For any observer capability, any
    deterministic tool environment, and ANY sound capability-only policy:
    running a plan on two observer-equivalent states yields observer-equivalent
    states — equal visible tool-call logs, equal halt status, equivalent
    stores. Data the observer cannot read cannot influence what it observes,
    for any plan the (untrusted) Privileged LLM proposes.

    The two conditions packaged in `SoundPolicy` are each necessary:
    (a) capability-only — the implementation's value-inspecting policies fall
        outside the theorem;
    (b) flow-enforcing — an over-permissive policy admits calls that disclose
        unreadable data to readable recipients. -/
theorem cap_noninterference {obs : Cap} (T : ToolEnv) (SP : SoundPolicy)
    (prog : List Stmt) {s₁ s₂ : State} (h : CapLowEq obs s₁ s₂) :
    CapLowEq obs (run T SP.P s₁ prog) (run T SP.P s₂ prog) := by
  unfold run
  induction prog generalizing s₁ s₂ with
  | nil => exact h
  | cons st sts ih => exact ih (step_preserves_capLowEq T SP st h)

/-- Specialization to the base policy of `security_policy.py`. -/
theorem cap_noninterference_base {obs : Cap} (T : ToolEnv) (prog : List Stmt)
    {s₁ s₂ : State} (h : CapLowEq obs s₁ s₂) :
    CapLowEq obs (run T basePolicy s₁ prog) (run T basePolicy s₂ prog) :=
  cap_noninterference T basePolicySound prog h

end Camelcore

#print axioms Camelcore.cap_noninterference
