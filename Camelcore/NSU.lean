import Camelcore.Model
import Camelcore.Plan
import Camelcore.Control
import Camelcore.Noninterference
import Camelcore.Leak

/-!
# Layer 4: the FIX — failstop no-sensitive-upgrade semantics, and
# termination-insensitive noninterference (TINI) for it.

`Leak.lean` proves that plain noninterference is FALSE for the faithful STRICT
semantics: an admitted tool call inside a secret branch fires in one run and
not the other. This file repairs the interpreter with the two classical
dynamic-IFC changes (Austin–Flanagan style) and proves the classical guarantee:

1. **pc-gated admission** (`AdmitsNSU`): a tool call is admitted only if the
   ambient pc ALSO flows to the recipients. A call inside a secret branch can
   then only target secret recipients, so its log entry is invisible.
2. **No-sensitive-upgrade write guard** (`WriteOK`): a write is allowed only if
   the overwritten binding is absent or at least as confidential as the pc.
   This blocks a secret branch from clobbering a public variable — the classic
   flow-sensitivity leak.
3. **Failstop**: any failure (undefined variable, denied call, blocked upgrade)
   HALTS the run — exactly as the real interpreter raises. The price is the
   classical one-bit termination channel; the guarantee is therefore
   TERMINATION-INSENSITIVE: runs that both complete produce identical visible
   logs. (`NSULowEq` builds the disjunction in.)
-/

namespace Camelcore

open Classical

/-- Failstop: a failed operation halts the run (the interpreter raises). -/
def failNSU (s : CState) : CState := { s with halted := true }

/-- The no-sensitive-upgrade write guard: writing `dst` is permitted iff `dst`
    is currently unbound, or its current capability is at least as confidential
    as the ambient pc (`pcCap pc` flows to it). At top level (`pc = []`,
    `pcCap = public`) every write is permitted; under a secret pc only fresh or
    already-secret variables may be written. -/
def WriteOK (σ : Store) (pc : List Cap) (dst : Var) : Prop :=
  match lookup σ dst with
  | none => True
  | some p => Cap.flows (pcCap pc) p.2

/-- The FIXED admission gate: the shipped check (policy on the argument
    capabilities) PLUS the repair — the ambient pc must flow to the recipients. -/
def AdmitsNSU (P : Policy) (σ : Store) (pc : List Cap)
    (tool : Nat) (args : List Var) (rcpt : Recipients) : Prop :=
  ∃ vs, lookupAll σ args = some vs ∧ P tool (vs.map (·.2)) rcpt ∧
        Cap.flows (pcCap pc) rcpt

mutual

/-- One step of the FIXED interpreter (STRICT mode): pc-gated admission,
    NSU write guard, failstop failures. -/
noncomputable def cstepNSU (T : ToolEnv) (P : Policy) (m : Mode)
    (s : CState) (st : CStmt) : CState :=
  if s.halted = true then s else
  match st with
  | .assign x n c =>
      if WriteOK s.store s.pc x then
        { s with store := (x, n, assignCap m s.pc c) :: s.store }
      else failNSU s
  | .compute dst srcs =>
      match lookupAll s.store srcs with
      | some vs =>
          if WriteOK s.store s.pc dst then
            { s with store :=
                (dst, (vs.map (·.1)).foldl (· + ·) 0,
                  assignCap m s.pc (Cap.meetList (vs.map (·.2)))) :: s.store }
          else failNSU s
      | none => failNSU s
  | .toolCall dst tool args rcpt =>
      match lookupAll s.store args with
      | some vs =>
          if AdmitsNSU P s.store s.pc tool args rcpt ∧ WriteOK s.store s.pc dst then
            { s with
                store := (dst, T tool (vs.map (·.1)),
                  Cap.meet (toolResultCap tool (vs.map (·.2))) (pcCap s.pc)) :: s.store
                out   := s.out ++ [(tool, vs.map (·.1), rcpt)] }
          else failNSU s
      | none => failNSU s
  | .ite cond thenB elseB =>
      match lookup s.store cond with
      | some (v, c) =>
          let s' := { s with pc := c :: s.pc }
          let s'' := if v ≠ 0
                     then cstepListNSU T P m s' thenB
                     else cstepListNSU T P m s' elseB
          { s'' with pc := s.pc }
      | none => failNSU s

noncomputable def cstepListNSU (T : ToolEnv) (P : Policy) (m : Mode)
    (s : CState) : List CStmt → CState
  | [] => s
  | st :: rest => cstepListNSU T P m (cstepNSU T P m s st) rest

end

/-- Run a plan under the fixed semantics. -/
noncomputable def crunNSU (T : ToolEnv) (P : Policy) (m : Mode)
    (s : CState) (prog : List CStmt) : CState :=
  cstepListNSU T P m s prog

/-! ## Basic structural lemmas -/

theorem failNSU_halted (s : CState) : (failNSU s).halted = true := rfl
theorem failNSU_out (s : CState) : (failNSU s).out = s.out := rfl
theorem failNSU_pc (s : CState) : (failNSU s).pc = s.pc := rfl
theorem failNSU_store (s : CState) : (failNSU s).store = s.store := rfl

/-- A halted state is a fixed point of the step function. -/
theorem cstepNSU_halted (T : ToolEnv) (P : Policy) (s : CState) (st : CStmt)
    (h : s.halted = true) : cstepNSU T P .strict s st = s := by
  unfold cstepNSU; rw [if_pos h]

/-- A halted state is a fixed point of the run function. -/
theorem cstepListNSU_halted (T : ToolEnv) (P : Policy) (s : CState)
    (prog : List CStmt) (h : s.halted = true) :
    cstepListNSU T P .strict s prog = s := by
  induction prog with
  | nil => simp only [cstepListNSU]
  | cons st rest ih =>
    simp only [cstepListNSU]
    rw [cstepNSU_halted T P s st h, ih]

/-! ## Readability helpers -/

theorem readable_of_flows {obs a b : Cap} (hf : Cap.flows a b) (hb : readable obs b) :
    readable obs a := by
  intro p hp; exact hf p (hb p hp)

theorem readable_meet_left {obs a b : Cap} (h : readable obs (Cap.meet a b)) :
    readable obs a := by
  intro p hp; exact (h p hp).1

theorem readable_meet_intro {obs a b : Cap} (ha : readable obs a)
    (hb : readable obs b) : readable obs (Cap.meet a b) := by
  intro p hp; exact ⟨ha p hp, hb p hp⟩

theorem readable_pcCap_nil {obs : Cap} : readable obs (pcCap ([] : List Cap)) := by
  intro p _; trivial

theorem nonreadable_pc_ne_nil {obs : Cap} {pc : List Cap}
    (h : ¬ readable obs (pcCap pc)) : pc ≠ [] := by
  intro he; rw [he] at h; exact h readable_pcCap_nil

/-- The heart of the gate repair: an ADMITTED call under a non-observer-readable
    pc has non-observer-readable recipients, so its log entry is filtered. -/
theorem nsu_gate_nonreadable_rcpt {obs : Cap} {P : Policy} {σ : Store}
    {pc : List Cap} {tool : Nat} {args : List Var} {rcpt : Recipients}
    (hnr : ¬ readable obs (pcCap pc))
    (ha : AdmitsNSU P σ pc tool args rcpt) : ¬ readable obs rcpt := by
  intro hr
  obtain ⟨_, _, _, hpf⟩ := ha
  exact hnr (readable_of_flows hpf hr)

/-- The heart of the write-guard repair: a write PERMITTED under a
    non-observer-readable pc targets a variable whose current binding (if any)
    is itself non-observer-readable. -/
theorem writeOK_secret {obs : Cap} {σ : Store} {pc : List Cap} {dst : Var}
    (hnr : ¬ readable obs (pcCap pc)) (hw : WriteOK σ pc dst) :
    ∀ p, lookup σ dst = some p → ¬ readable obs p.2 := by
  intro p hl hr
  unfold WriteOK at hw
  rw [hl] at hw
  exact hnr (readable_of_flows hw hr)

/-! ## The observer store relation -/

/-- Per-variable observer-equivalence: the observer only constrains bindings it
    can read. If either side's cap is readable, both caps must be equal and the
    values must agree; a binding present on one side only must be non-readable. -/
def varObsEq (obs : Cap) (r₁ r₂ : Option (Nat × Cap)) : Prop :=
  match r₁, r₂ with
  | some p₁, some p₂ =>
      (readable obs p₁.2 ∨ readable obs p₂.2) → (p₁.2 = p₂.2 ∧ p₁.1 = p₂.1)
  | none, none => True
  | some p₁, none => ¬ readable obs p₁.2
  | none, some p₂ => ¬ readable obs p₂.2

/-- Observer store-equivalence. -/
def StoreObsEq (obs : Cap) (σ₁ σ₂ : Store) : Prop :=
  ∀ x, varObsEq obs (lookup σ₁ x) (lookup σ₂ x)

theorem varObsEq.symm {obs : Cap} {r₁ r₂ : Option (Nat × Cap)}
    (h : varObsEq obs r₁ r₂) : varObsEq obs r₂ r₁ := by
  unfold varObsEq at *
  cases r₁ with
  | none => cases r₂ with
    | none => trivial
    | some p₂ => exact h
  | some p₁ => cases r₂ with
    | none => exact h
    | some p₂ =>
      intro hor
      have := h (hor.symm)
      exact ⟨this.1.symm, this.2.symm⟩

theorem StoreObsEq.symm {obs : Cap} {σ₁ σ₂ : Store} (h : StoreObsEq obs σ₁ σ₂) :
    StoreObsEq obs σ₂ σ₁ := fun x => (h x).symm

/-- `StoreCapEq` (on-the-nose caps) implies `StoreObsEq`. Used to enter the
    relation from the straight-line world. -/
theorem StoreCapEq.toObs {obs : Cap} {σ₁ σ₂ : Store} (h : StoreCapEq obs σ₁ σ₂) :
    StoreObsEq obs σ₁ σ₂ := by
  intro x
  have hx := h x
  unfold varCapEq at hx
  unfold varObsEq
  cases h1 : lookup σ₁ x with
  | none =>
    cases h2 : lookup σ₂ x with
    | none => trivial
    | some p => rw [h1, h2] at hx; exact hx.elim
  | some p1 =>
    cases h2 : lookup σ₂ x with
    | none => rw [h1, h2] at hx; exact hx.elim
    | some p2 =>
      rw [h1, h2] at hx
      intro hor
      refine ⟨hx.1, hx.2 ?_⟩
      rcases hor with hr | hr
      · exact hr
      · rw [hx.1]; exact hr

/-- Prepending EQUAL bindings preserves `StoreObsEq`. -/
theorem StoreObsEq.cons_eq {obs : Cap} {σ₁ σ₂ : Store} {dst : Var}
    {n₁ n₂ : Nat} {c₁ c₂ : Cap} (h : StoreObsEq obs σ₁ σ₂)
    (hc : c₁ = c₂) (hn : n₁ = n₂) :
    StoreObsEq obs ((dst, n₁, c₁) :: σ₁) ((dst, n₂, c₂) :: σ₂) := by
  intro x
  by_cases hx : dst = x
  · subst hx
    have hl1 : lookup ((dst, n₁, c₁) :: σ₁) dst = some (n₁, c₁) := by
      simp [lookup]
    have hl2 : lookup ((dst, n₂, c₂) :: σ₂) dst = some (n₂, c₂) := by
      simp [lookup]
    rw [hl1, hl2]
    unfold varObsEq
    intro _
    exact ⟨hc, hn⟩
  · have hbf : (dst == x) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact hx
    have hl1 : lookup ((dst, n₁, c₁) :: σ₁) x = lookup σ₁ x := by
      simp [lookup, hbf]
    have hl2 : lookup ((dst, n₂, c₂) :: σ₂) x = lookup σ₂ x := by
      simp [lookup, hbf]
    rw [hl1, hl2]
    exact h x

/-- Prepending NON-readable bindings (values and caps may differ) preserves
    `StoreObsEq`. -/
theorem StoreObsEq.cons_nonreadable {obs : Cap} {σ₁ σ₂ : Store} {dst : Var}
    {n₁ n₂ : Nat} {c₁ c₂ : Cap} (h : StoreObsEq obs σ₁ σ₂)
    (h1 : ¬ readable obs c₁) (h2 : ¬ readable obs c₂) :
    StoreObsEq obs ((dst, n₁, c₁) :: σ₁) ((dst, n₂, c₂) :: σ₂) := by
  intro x
  by_cases hx : dst = x
  · subst hx
    have hl1 : lookup ((dst, n₁, c₁) :: σ₁) dst = some (n₁, c₁) := by
      simp [lookup]
    have hl2 : lookup ((dst, n₂, c₂) :: σ₂) dst = some (n₂, c₂) := by
      simp [lookup]
    rw [hl1, hl2]
    unfold varObsEq
    intro hor
    rcases hor with hh | hh
    · exact absurd hh h1
    · exact absurd hh h2
  · have hbf : (dst == x) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact hx
    have hl1 : lookup ((dst, n₁, c₁) :: σ₁) x = lookup σ₁ x := by
      simp [lookup, hbf]
    have hl2 : lookup ((dst, n₂, c₂) :: σ₂) x = lookup σ₂ x := by
      simp [lookup, hbf]
    rw [hl1, hl2]
    exact h x

/-- Prepending a NON-readable binding on ONE side preserves `StoreObsEq`,
    provided the other side's binding for that variable (if any) is also
    non-readable. This is the frame condition the NSU write guard provides. -/
theorem StoreObsEq.cons_left_guarded {obs : Cap} {σ₁ σ₂ : Store} {dst : Var}
    {n₁ : Nat} {c₁ : Cap} (h : StoreObsEq obs σ₁ σ₂)
    (h1 : ¬ readable obs c₁)
    (h2 : ∀ p, lookup σ₂ dst = some p → ¬ readable obs p.2) :
    StoreObsEq obs ((dst, n₁, c₁) :: σ₁) σ₂ := by
  intro x
  by_cases hx : dst = x
  · subst hx
    have hl1 : lookup ((dst, n₁, c₁) :: σ₁) dst = some (n₁, c₁) := by
      simp [lookup]
    rw [hl1]
    cases hl2 : lookup σ₂ dst with
    | none => exact h1
    | some p2 =>
      unfold varObsEq
      intro hor
      rcases hor with hh | hh
      · exact absurd hh h1
      · exact absurd hh (h2 p2 hl2)
  · have hbf : (dst == x) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact hx
    have hl1 : lookup ((dst, n₁, c₁) :: σ₁) x = lookup σ₁ x := by
      simp [lookup, hbf]
    rw [hl1]
    exact h x

/-! ## lookupAll helpers over `StoreObsEq` -/

/-- If `lookupAll` succeeds on σ₁ and every looked-up cap is readable, it also
    succeeds on σ₂ with agreeing caps AND values. -/
theorem lookupAll_obs_agree {obs : Cap} {σ₁ σ₂ : Store} (h : StoreObsEq obs σ₁ σ₂) :
    ∀ (args : List Var) (vs₁ : List (Nat × Cap)),
      lookupAll σ₁ args = some vs₁ →
      (∀ c ∈ vs₁.map (·.2), readable obs c) →
      ∃ vs₂, lookupAll σ₂ args = some vs₂ ∧
             vs₁.map (·.2) = vs₂.map (·.2) ∧ vs₁.map (·.1) = vs₂.map (·.1) := by
  intro args
  induction args with
  | nil =>
    intro vs₁ h1 _
    simp only [lookupAll, Option.some.injEq] at h1
    subst h1; exact ⟨[], rfl, rfl, rfl⟩
  | cons x xs ih =>
    intro vs₁ h1 hread
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
        unfold varObsEq at hvx
        rw [hx1] at hvx
        have hrhd : readable obs p₁.2 := by apply hread; simp [List.map_cons]
        cases hx2 : lookup σ₂ x with
        | none => rw [hx2] at hvx; exact absurd hrhd hvx
        | some p₂ =>
          rw [hx2] at hvx
          obtain ⟨hce, hve⟩ := hvx (Or.inl hrhd)
          have hreadtl : ∀ c ∈ ps₁.map (·.2), readable obs c := by
            intro c hc; apply hread; simp only [List.map_cons]
            exact List.mem_cons_of_mem _ hc
          obtain ⟨ps₂, hps₂, hcmap, hvmap⟩ := ih ps₁ hxs1 hreadtl
          refine ⟨p₂ :: ps₂, ?_, ?_, ?_⟩
          · simp only [lookupAll, hx2, hps₂]
          · simp only [List.map_cons, hcmap, hce]
          · simp only [List.map_cons, hvmap, hve]

/-- Non-readability of the meet TRANSFERS between two successful lookups on
    observer-equivalent stores: if run 1's result taint is non-readable, so is
    run 2's. (A readable cap on either side forces the caps equal.) -/
theorem lookupAll_obs_nonreadable_transfer {obs : Cap} {σ₁ σ₂ : Store}
    (h : StoreObsEq obs σ₁ σ₂) :
    ∀ (args : List Var) (vs₁ vs₂ : List (Nat × Cap)),
      lookupAll σ₁ args = some vs₁ → lookupAll σ₂ args = some vs₂ →
      ¬ readable obs (Cap.meetList (vs₁.map (·.2))) →
      ¬ readable obs (Cap.meetList (vs₂.map (·.2))) := by
  intro args
  induction args with
  | nil =>
    intro vs₁ vs₂ h1 h2 hnr
    simp only [lookupAll, Option.some.injEq] at h1 h2
    subst h1; subst h2
    exact hnr
  | cons x xs ih =>
    intro vs₁ vs₂ h1 h2 hnr
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
            simp only [List.map_cons, Cap.meetList] at hnr ⊢
            intro hrd
            apply hnr
            have hrd2hd : readable obs p₂.2 := readable_meet_left hrd
            have hrd2tl : readable obs (Cap.meetList (ps₂.map (·.2))) :=
              readable_meet_right hrd
            -- head transfers back via varObsEq
            have hvx := h x
            unfold varObsEq at hvx
            rw [hx1, hx2] at hvx
            obtain ⟨hce, _⟩ := hvx (Or.inr hrd2hd)
            have hrd1hd : readable obs p₁.2 := by rw [hce]; exact hrd2hd
            -- tail transfers back via IH (contrapositive)
            have hrd1tl : readable obs (Cap.meetList (ps₁.map (·.2))) :=
              Classical.byContradiction
                (fun hntl => ih ps₁ ps₂ hxs1 hxs2 hntl hrd2tl)
            exact readable_meet_intro hrd1hd hrd1tl

/-! ## The TINI relation -/

/-- Program-counter agreement: pc-caps equal on the nose, or both
    non-observer-readable; and empty iff empty (branch depth in sync). -/
def pcRelN (obs : Cap) (pc₁ pc₂ : List Cap) : Prop :=
  (pcCap pc₁ = pcCap pc₂ ∨
    (¬ readable obs (pcCap pc₁) ∧ ¬ readable obs (pcCap pc₂))) ∧
  (pc₁ = [] ↔ pc₂ = [])

/-- **Termination-insensitive observer-equivalence.** Either run has failstopped
    (in which case nothing further is claimed — the classical one-bit
    termination channel), or both runs are live and agree on everything the
    observer can see. -/
def NSULowEq (obs : Cap) (s₁ s₂ : CState) : Prop :=
  s₁.halted = true ∨ s₂.halted = true ∨
  (s₁.halted = false ∧ s₂.halted = false ∧
   visLog obs s₁.out = visLog obs s₂.out ∧
   pcRelN obs s₁.pc s₂.pc ∧
   (readable obs (pcCap s₁.pc) → StoreObsEq obs s₁.store s₂.store))

/-- Soundness of the relation: for runs that BOTH complete, the halt statuses
    and observer-visible logs agree — genuine (termination-insensitive)
    noninterference. -/
theorem NSULowEq.observable {obs : Cap} {s₁ s₂ : CState}
    (h : NSULowEq obs s₁ s₂)
    (h1 : s₁.halted = false) (h2 : s₂.halted = false) :
    visLog obs s₁.out = visLog obs s₂.out := by
  rcases h with hh | hh | ⟨_, _, hv, _, _⟩
  · rw [h1] at hh; exact absurd hh (by simp)
  · rw [h2] at hh; exact absurd hh (by simp)
  · exact hv

end Camelcore

namespace Camelcore

open Classical

/-! ## Single-run lemmas under a secret pc -/

mutual

/-- Under a non-empty, non-observer-readable pc, one fixed step either
    failstops, or leaves halt/visible-log/pc unchanged. (An admitted tool call
    is possible, but its recipients are non-readable — `nsu_gate` — so the new
    entry is filtered out of the visible log.) -/
theorem cstepNSU_secret {obs : Cap} (T : ToolEnv) (P : Policy)
    (s : CState) (st : CStmt)
    (_hne : s.pc ≠ []) (hnr : ¬ readable obs (pcCap s.pc)) (hnh : s.halted = false) :
    (cstepNSU T P .strict s st).halted = true ∨
    ((cstepNSU T P .strict s st).halted = false ∧
     visLog obs (cstepNSU T P .strict s st).out = visLog obs s.out ∧
     (cstepNSU T P .strict s st).pc = s.pc) := by
  have hh : ¬ s.halted = true := by rw [hnh]; simp
  cases st with
  | assign x n c =>
    unfold cstepNSU
    rw [if_neg hh]
    simp only []
    by_cases hw : WriteOK s.store s.pc x
    · simp only [if_pos hw]
      right
      refine ⟨hnh, ?_, ?_⟩
      · first | rfl | trivial
      · first | rfl | trivial
    · simp only [if_neg hw]; left; rfl
  | compute dst srcs =>
    unfold cstepNSU
    rw [if_neg hh]
    cases hla : lookupAll s.store srcs with
    | none => simp only [hla]; left; rfl
    | some vs =>
      simp only [hla]
      by_cases hw : WriteOK s.store s.pc dst
      · rw [if_pos hw]; right; exact ⟨hnh, rfl, rfl⟩
      · rw [if_neg hw]; left; rfl
  | toolCall dst tool args rcpt =>
    unfold cstepNSU
    rw [if_neg hh]
    cases hla : lookupAll s.store args with
    | none => simp only [hla]; left; rfl
    | some vs =>
      simp only [hla]
      by_cases hadm : AdmitsNSU P s.store s.pc tool args rcpt ∧ WriteOK s.store s.pc dst
      · rw [if_pos hadm]
        right
        refine ⟨hnh, ?_, rfl⟩
        have hrc : ¬ readable obs rcpt := nsu_gate_nonreadable_rcpt hnr hadm.1
        have hdf : @decide (readable obs rcpt) (Classical.propDecidable _) = false :=
          decide_eq_false_iff_not.mpr hrc
        simp only [visLog, List.filter_append, List.filter_cons, hdf,
                   Bool.false_eq_true, if_false, List.filter_nil, List.append_nil]
      · rw [if_neg hadm]; left; rfl
  | ite cond thenB elseB =>
    unfold cstepNSU
    rw [if_neg hh]
    cases hlc : lookup s.store cond with
    | none => simp only [hlc]; left; rfl
    | some p =>
      obtain ⟨v, c⟩ := p
      simp only [hlc]
      have hne' : (c :: s.pc) ≠ [] := by simp
      have hnr' : ¬ readable obs (pcCap (c :: s.pc)) := by
        intro hrd
        have hexp : pcCap (c :: s.pc) = Cap.meet c (pcCap s.pc) := rfl
        rw [hexp] at hrd
        exact hnr (readable_meet_right hrd)
      by_cases hv : v ≠ 0
      · simp only [if_pos hv]
        have hrec := cstepListNSU_secret (obs := obs) T P
          { s with pc := c :: s.pc } thenB hne' hnr' hnh
        rcases hrec with hhl | ⟨hhl, hvl, _⟩
        · left; exact hhl
        · right; refine ⟨hhl, ?_, ?_⟩
          · first | exact hvl | trivial
          · first | rfl | trivial
      · simp only [if_neg hv]
        have hrec := cstepListNSU_secret (obs := obs) T P
          { s with pc := c :: s.pc } elseB hne' hnr' hnh
        rcases hrec with hhl | ⟨hhl, hvl, _⟩
        · left; exact hhl
        · right; refine ⟨hhl, ?_, ?_⟩
          · first | exact hvl | trivial
          · first | rfl | trivial
  termination_by sizeOf st

/-- List version of `cstepNSU_secret`. -/
theorem cstepListNSU_secret {obs : Cap} (T : ToolEnv) (P : Policy)
    (s : CState) (prog : List CStmt)
    (hne : s.pc ≠ []) (hnr : ¬ readable obs (pcCap s.pc)) (hnh : s.halted = false) :
    (cstepListNSU T P .strict s prog).halted = true ∨
    ((cstepListNSU T P .strict s prog).halted = false ∧
     visLog obs (cstepListNSU T P .strict s prog).out = visLog obs s.out ∧
     (cstepListNSU T P .strict s prog).pc = s.pc) := by
  match prog with
  | [] =>
    simp only [cstepListNSU]
    right; refine ⟨hnh, ?_, ?_⟩
    · first | rfl | trivial
    · first | rfl | trivial
  | st :: rest =>
    simp only [cstepListNSU]
    have hstep := cstepNSU_secret (obs := obs) T P s st hne hnr hnh
    rcases hstep with hhl | ⟨hhl, hvl, hpl⟩
    · left
      rw [cstepListNSU_halted T P _ rest hhl]
      exact hhl
    · have hne2 : (cstepNSU T P .strict s st).pc ≠ [] := by rw [hpl]; exact hne
      have hnr2 : ¬ readable obs (pcCap (cstepNSU T P .strict s st).pc) := by
        rw [hpl]; exact hnr
      have hrest := cstepListNSU_secret (obs := obs) T P
        (cstepNSU T P .strict s st) rest hne2 hnr2 hhl
      rcases hrest with hh2 | ⟨hh2, hv2, hp2⟩
      · left; exact hh2
      · right
        refine ⟨hh2, ?_, ?_⟩
        · rw [hv2, hvl]
        · rw [hp2, hpl]
  termination_by sizeOf prog

end

/-! ## The fixed semantics always restores the pc -/

theorem cstepNSU_pc (T : ToolEnv) (P : Policy) (s : CState) (st : CStmt) :
    (cstepNSU T P .strict s st).pc = s.pc := by
  by_cases hh : s.halted = true
  · unfold cstepNSU; rw [if_pos hh]
  · cases st with
    | assign x n c =>
      unfold cstepNSU; rw [if_neg hh]
      simp only []
      by_cases hw : WriteOK s.store s.pc x
      · simp only [if_pos hw]
      · simp only [if_neg hw]; exact failNSU_pc s
    | compute dst srcs =>
      unfold cstepNSU; rw [if_neg hh]
      cases hlk : lookupAll s.store srcs with
      | none => simp only [hlk]; exact failNSU_pc s
      | some vs =>
        simp only [hlk]
        by_cases hw : WriteOK s.store s.pc dst
        · rw [if_pos hw]
        · rw [if_neg hw]; exact failNSU_pc s
    | toolCall dst tool args rcpt =>
      unfold cstepNSU; rw [if_neg hh]
      cases hlk : lookupAll s.store args with
      | none => simp only [hlk]; exact failNSU_pc s
      | some vs =>
        simp only [hlk]
        by_cases hadm : AdmitsNSU P s.store s.pc tool args rcpt ∧ WriteOK s.store s.pc dst
        · rw [if_pos hadm]
        · rw [if_neg hadm]; exact failNSU_pc s
    | ite cond thenB elseB =>
      unfold cstepNSU; rw [if_neg hh]
      cases hlk : lookup s.store cond with
      | none => simp only [hlk]; exact failNSU_pc s
      | some p => obtain ⟨v, c⟩ := p; simp only [hlk]

theorem cstepListNSU_pc (T : ToolEnv) (P : Policy) (s : CState) (prog : List CStmt) :
    (cstepListNSU T P .strict s prog).pc = s.pc := by
  induction prog generalizing s with
  | nil => simp only [cstepListNSU]
  | cons st rest ih =>
    simp only [cstepListNSU]
    rw [ih (cstepNSU T P .strict s st), cstepNSU_pc T P s st]

/-! ## The store-frame lemma (TRUE thanks to the NSU write guard) -/

mutual

/-- One guarded step under a secret pc preserves `StoreObsEq` against a fixed
    external store σ (on the right): every permitted write targets a variable
    whose current binding is absent-or-non-readable — hence (by `varObsEq`) so
    is σ's — and stamps a non-readable capability. Failstops don't touch the
    store. -/
theorem cstepNSU_secret_store {obs : Cap} (T : ToolEnv) (P : Policy)
    (σ : Store) (s : CState) (st : CStmt)
    (_hne : s.pc ≠ []) (hnr : ¬ readable obs (pcCap s.pc))
    (h : StoreObsEq obs s.store σ) :
    StoreObsEq obs (cstepNSU T P .strict s st).store σ := by
  by_cases hh : s.halted = true
  · rw [cstepNSU_halted T P s st hh]; exact h
  · -- helper: σ's binding for a WriteOK-target is non-readable
    have hguard : ∀ dst, WriteOK s.store s.pc dst →
        ∀ p, lookup σ dst = some p → ¬ readable obs p.2 := by
      intro dst hw p hlp hrp
      have hvx := h dst
      unfold varObsEq at hvx
      cases hl1 : lookup s.store dst with
      | none => rw [hl1, hlp] at hvx; exact hvx hrp
      | some p1 =>
        rw [hl1, hlp] at hvx
        obtain ⟨hce, _⟩ := hvx (Or.inr hrp)
        have : readable obs p1.2 := by rw [hce]; exact hrp
        exact writeOK_secret hnr hw p1 hl1 this
    have hnrw : ∀ c : Cap, ¬ readable obs (Cap.meet c (pcCap s.pc)) := by
      intro c hrd; exact hnr (readable_meet_right hrd)
    cases st with
    | assign x n c =>
      unfold cstepNSU
      rw [if_neg hh]
      simp only []
      by_cases hw : WriteOK s.store s.pc x
      · simp only [if_pos hw]
        exact StoreObsEq.cons_left_guarded h (hnrw c) (hguard x hw)
      · simp only [if_neg hw]; exact h
    | compute dst srcs =>
      unfold cstepNSU
      rw [if_neg hh]
      cases hla : lookupAll s.store srcs with
      | none => simp only [hla]; exact h
      | some vs =>
        simp only [hla]
        by_cases hw : WriteOK s.store s.pc dst
        · rw [if_pos hw]
          refine StoreObsEq.cons_left_guarded h ?_ (hguard dst hw)
          show ¬ readable obs (assignCap .strict s.pc (Cap.meetList (vs.map (·.2))))
          unfold assignCap
          exact hnrw (Cap.meetList (vs.map (·.2)))
        · rw [if_neg hw]; exact h
    | toolCall dst tool args rcpt =>
      unfold cstepNSU
      rw [if_neg hh]
      cases hla : lookupAll s.store args with
      | none => simp only [hla]; exact h
      | some vs =>
        simp only [hla]
        by_cases hadm : AdmitsNSU P s.store s.pc tool args rcpt ∧ WriteOK s.store s.pc dst
        · rw [if_pos hadm]
          exact StoreObsEq.cons_left_guarded h
            (hnrw (toolResultCap tool (vs.map (·.2)))) (hguard dst hadm.2)
        · rw [if_neg hadm]; exact h
    | ite cond thenB elseB =>
      unfold cstepNSU
      rw [if_neg hh]
      cases hlc : lookup s.store cond with
      | none => simp only [hlc]; exact h
      | some p =>
        obtain ⟨v, c⟩ := p
        simp only [hlc]
        have hne' : (c :: s.pc) ≠ [] := by simp
        have hnr' : ¬ readable obs (pcCap (c :: s.pc)) := by
          intro hrd
          have hexp : pcCap (c :: s.pc) = Cap.meet c (pcCap s.pc) := rfl
          rw [hexp] at hrd
          exact hnr (readable_meet_right hrd)
        by_cases hv : v ≠ 0
        · simp only [if_pos hv]
          exact cstepListNSU_secret_store (obs := obs) T P σ
            { s with pc := c :: s.pc } thenB hne' hnr' h
        · simp only [if_neg hv]
          exact cstepListNSU_secret_store (obs := obs) T P σ
            { s with pc := c :: s.pc } elseB hne' hnr' h
  termination_by sizeOf st

/-- List version of the frame lemma. -/
theorem cstepListNSU_secret_store {obs : Cap} (T : ToolEnv) (P : Policy)
    (σ : Store) (s : CState) (prog : List CStmt)
    (hne : s.pc ≠ []) (hnr : ¬ readable obs (pcCap s.pc))
    (h : StoreObsEq obs s.store σ) :
    StoreObsEq obs (cstepListNSU T P .strict s prog).store σ := by
  match prog with
  | [] => simp only [cstepListNSU]; exact h
  | st :: rest =>
    simp only [cstepListNSU]
    have hstep := cstepNSU_secret_store (obs := obs) T P σ s st hne hnr h
    have hpc := cstepNSU_pc T P s st
    have hne2 : (cstepNSU T P .strict s st).pc ≠ [] := by rw [hpc]; exact hne
    have hnr2 : ¬ readable obs (pcCap (cstepNSU T P .strict s st).pc) := by
      rw [hpc]; exact hnr
    exact cstepListNSU_secret_store (obs := obs) T P σ
      (cstepNSU T P .strict s st) rest hne2 hnr2 hstep
  termination_by sizeOf prog

end

/-! ## The main paired-step lemma -/

mutual

/-- **TINI preservation, single statement.** The disjunctive relation makes
    every asymmetric situation (a lookup that fails in one run, an admission or
    write-guard decision that differs) TRIVIAL: the failing run halts, landing
    in a halt disjunct. Substantive work remains only where BOTH runs act. -/
theorem cstepNSU_preserves_NSULowEq {obs : Cap} (T : ToolEnv) (SP : SoundPolicy)
    (st : CStmt) {s₁ s₂ : CState}
    (h : NSULowEq obs s₁ s₂) :
    NSULowEq obs (cstepNSU T SP.P .strict s₁ st) (cstepNSU T SP.P .strict s₂ st) := by
  rcases h with hh1 | hh2 | ⟨hnf1, hnf2, hvis, hpc, hstore⟩
  · left; rw [cstepNSU_halted T SP.P s₁ st hh1]; exact hh1
  · right; left; rw [cstepNSU_halted T SP.P s₂ st hh2]; exact hh2
  · -- both live
    have hh : ¬ s₁.halted = true := by rw [hnf1]; simp
    have hh2 : ¬ s₂.halted = true := by rw [hnf2]; simp
    by_cases hprd : readable obs (pcCap s₁.pc)
    · -- READABLE pc: pcs equal, StoreObsEq available.
      have hpceq : pcCap s₁.pc = pcCap s₂.pc := by
        rcases hpc.1 with heq | ⟨hn1, _⟩
        · exact heq
        · exact absurd hprd hn1
      have hse : StoreObsEq obs s₁.store s₂.store := hstore hprd
      cases st with
      | assign x n c =>
        unfold cstepNSU
        rw [if_neg hh, if_neg hh2]
        simp only []
        by_cases hw1 : WriteOK s₁.store s₁.pc x
        · by_cases hw2 : WriteOK s₂.store s₂.pc x
          · simp only [if_pos hw1, if_pos hw2]
            right; right
            refine ⟨hnf1, hnf2, hvis, hpc, fun _ => ?_⟩
            have hce : assignCap .strict s₁.pc c = assignCap .strict s₂.pc c := by
              unfold assignCap; rw [hpceq]
            exact StoreObsEq.cons_eq hse hce rfl
          · simp only [if_pos hw1, if_neg hw2]; right; left; rfl
        · simp only [if_neg hw1]; left; rfl
      | compute dst srcs =>
        unfold cstepNSU
        rw [if_neg hh, if_neg hh2]
        cases hla1 : lookupAll s₁.store srcs with
        | none => simp only [hla1]; left; rfl
        | some vs1 =>
          cases hla2 : lookupAll s₂.store srcs with
          | none => simp only [hla1, hla2]; right; left; rfl
          | some vs2 =>
            simp only [hla1, hla2]
            by_cases hw1 : WriteOK s₁.store s₁.pc dst
            · by_cases hw2 : WriteOK s₂.store s₂.pc dst
              · rw [if_pos hw1, if_pos hw2]
                right; right
                refine ⟨hnf1, hnf2, hvis, hpc, fun _ => ?_⟩
                by_cases hrr : readable obs (Cap.meetList (vs1.map (·.2)))
                · -- readable result taint ⇒ all srcs readable ⇒ full agreement
                  have hallread : ∀ cc ∈ vs1.map (·.2), readable obs cc :=
                    fun cc hcc => readable_meetList (vs1.map (·.2)) hrr cc hcc
                  obtain ⟨vs2', hla2', hcmap, hvmap⟩ :=
                    lookupAll_obs_agree hse srcs vs1 hla1 hallread
                  have hvs : vs2' = vs2 := Option.some.inj (hla2'.symm.trans hla2)
                  rw [hvs] at hcmap hvmap
                  have hce : assignCap .strict s₁.pc (Cap.meetList (vs1.map (·.2)))
                           = assignCap .strict s₂.pc (Cap.meetList (vs2.map (·.2))) := by
                    unfold assignCap; rw [hpceq, hcmap]
                  have hve : (vs1.map (·.1)).foldl (· + ·) 0
                           = (vs2.map (·.1)).foldl (· + ·) 0 := by rw [hvmap]
                  exact StoreObsEq.cons_eq hse hce hve
                · -- non-readable taint transfers ⇒ both bindings non-readable
                  have hrr2 : ¬ readable obs (Cap.meetList (vs2.map (·.2))) :=
                    lookupAll_obs_nonreadable_transfer hse srcs vs1 vs2 hla1 hla2 hrr
                  have h1 : ¬ readable obs (assignCap .strict s₁.pc (Cap.meetList (vs1.map (·.2)))) := by
                    intro hrd
                    unfold assignCap at hrd
                    exact hrr (readable_meet_left hrd)
                  have h2 : ¬ readable obs (assignCap .strict s₂.pc (Cap.meetList (vs2.map (·.2)))) := by
                    intro hrd
                    unfold assignCap at hrd
                    exact hrr2 (readable_meet_left hrd)
                  exact StoreObsEq.cons_nonreadable hse h1 h2
              · rw [if_pos hw1, if_neg hw2]; right; left; rfl
            · rw [if_neg hw1]; left; rfl
      | toolCall dst tool args rcpt =>
        unfold cstepNSU
        rw [if_neg hh, if_neg hh2]
        cases hla1 : lookupAll s₁.store args with
        | none => simp only [hla1]; left; rfl
        | some vs1 =>
          cases hla2 : lookupAll s₂.store args with
          | none => simp only [hla1, hla2]; right; left; rfl
          | some vs2 =>
            simp only [hla1, hla2]
            by_cases hg1 : AdmitsNSU SP.P s₁.store s₁.pc tool args rcpt ∧ WriteOK s₁.store s₁.pc dst
            · by_cases hg2 : AdmitsNSU SP.P s₂.store s₂.pc tool args rcpt ∧ WriteOK s₂.store s₂.pc dst
              · rw [if_pos hg1, if_pos hg2]
                right; right
                -- extract policy facts for run 1
                have hpol : SP.P tool (vs1.map (·.2)) rcpt := by
                  obtain ⟨⟨vs, hlk, hp, _⟩, _⟩ := hg1
                  rw [hla1] at hlk
                  have hvv : vs = vs1 := (Option.some.inj hlk).symm
                  subst hvv; exact hp
                have hflow : ∀ c ∈ vs1.map (·.2), Cap.flows c rcpt :=
                  SP.enforces_flow tool (vs1.map (·.2)) rcpt hpol
                refine ⟨hnf1, hnf2, ?_, hpc, fun _ => ?_⟩
                · -- visible log
                  by_cases hr : readable obs rcpt
                  · have hallread : ∀ c ∈ vs1.map (·.2), readable obs c := fun c hc =>
                      readable_of_flows (hflow c hc) hr
                    obtain ⟨vs2', hla2', hcmap, hvmap⟩ :=
                      lookupAll_obs_agree hse args vs1 hla1 hallread
                    have hvs : vs2' = vs2 := Option.some.inj (hla2'.symm.trans hla2)
                    rw [hvs] at hvmap
                    have hvis' : List.filter
                        (fun e => @decide (readable obs e.2.2) (Classical.propDecidable _)) s₁.out
                      = List.filter
                        (fun e => @decide (readable obs e.2.2) (Classical.propDecidable _)) s₂.out := hvis
                    simp only [visLog, List.filter_append, hvmap]
                    rw [hvis']
                  · have hdf : @decide (readable obs rcpt) (Classical.propDecidable _) = false :=
                      decide_eq_false_iff_not.mpr hr
                    simp only [visLog, List.filter_append, List.filter_cons, hdf,
                               Bool.false_eq_true, if_false, List.filter_nil, List.append_nil]
                    exact hvis
                · -- store: binding readable ⇒ args readable ⇒ agree; else both non-readable
                  by_cases hrr : readable obs (Cap.meetList (vs1.map (·.2)))
                  · have hallread : ∀ cc ∈ vs1.map (·.2), readable obs cc :=
                      fun cc hcc => readable_meetList (vs1.map (·.2)) hrr cc hcc
                    obtain ⟨vs2', hla2', hcmap, hvmap⟩ :=
                      lookupAll_obs_agree hse args vs1 hla1 hallread
                    have hvs : vs2' = vs2 := Option.some.inj (hla2'.symm.trans hla2)
                    rw [hvs] at hcmap hvmap
                    have hce : Cap.meet (toolResultCap tool (vs1.map (·.2))) (pcCap s₁.pc)
                             = Cap.meet (toolResultCap tool (vs2.map (·.2))) (pcCap s₂.pc) := by
                      unfold toolResultCap; rw [hcmap, hpceq]
                    have hve : T tool (vs1.map (·.1)) = T tool (vs2.map (·.1)) := by rw [hvmap]
                    exact StoreObsEq.cons_eq hse hce hve
                  · have hrr2 : ¬ readable obs (Cap.meetList (vs2.map (·.2))) :=
                      lookupAll_obs_nonreadable_transfer hse args vs1 vs2 hla1 hla2 hrr
                    have h1 : ¬ readable obs (Cap.meet (toolResultCap tool (vs1.map (·.2))) (pcCap s₁.pc)) := by
                      intro hrd
                      have := readable_meet_left hrd
                      unfold toolResultCap at this
                      exact hrr (readable_meet_right this)
                    have h2 : ¬ readable obs (Cap.meet (toolResultCap tool (vs2.map (·.2))) (pcCap s₂.pc)) := by
                      intro hrd
                      have := readable_meet_left hrd
                      unfold toolResultCap at this
                      exact hrr2 (readable_meet_right this)
                    exact StoreObsEq.cons_nonreadable hse h1 h2
              · rw [if_pos hg1, if_neg hg2]; right; left; rfl
            · rw [if_neg hg1]; left; rfl
      | ite cond thenB elseB =>
        by_cases hlc1 : (lookup s₁.store cond).isSome
        · obtain ⟨⟨v1, c1⟩, hl1⟩ := Option.isSome_iff_exists.mp hlc1
          cases hl2 : lookup s₂.store cond with
          | none =>
            right; left
            unfold cstepNSU
            rw [if_neg hh2]
            simp only [hl2]
            rfl
          | some p2 =>
            obtain ⟨v2, c2⟩ := p2
            have hvx := hse cond
            unfold varObsEq at hvx
            rw [hl1, hl2] at hvx
            unfold cstepNSU
            rw [if_neg hh, if_neg hh2]
            simp only [hl1, hl2]
            by_cases hrc : readable obs c1
            · -- readable condition: caps and VALUES agree ⇒ same branch (two-way)
              obtain ⟨hcc0, hvv0⟩ := hvx (Or.inl hrc)
              have hcc : c1 = c2 := hcc0
              have hvv : v1 = v2 := hvv0
              subst hcc; subst hvv
              have hprd' : readable obs (pcCap (c1 :: s₁.pc)) := by
                have hexp : pcCap (c1 :: s₁.pc) = Cap.meet c1 (pcCap s₁.pc) := rfl
                rw [hexp]
                exact readable_meet_intro hrc hprd
              have hrec : NSULowEq obs
                  { s₁ with pc := c1 :: s₁.pc } { s₂ with pc := c1 :: s₂.pc } := by
                right; right
                refine ⟨hnf1, hnf2, hvis, ⟨?_, by simp⟩, fun _ => hse⟩
                left
                show pcCap (c1 :: s₁.pc) = pcCap (c1 :: s₂.pc)
                have e1 : pcCap (c1 :: s₁.pc) = Cap.meet c1 (pcCap s₁.pc) := rfl
                have e2 : pcCap (c1 :: s₂.pc) = Cap.meet c1 (pcCap s₂.pc) := rfl
                rw [e1, e2, hpceq]
              by_cases hv0 : v1 ≠ 0
              · simp only [if_pos hv0]
                have hrecres := cstepListNSU_preserves_NSULowEq T SP thenB hrec
                have hpp1 : (cstepListNSU T SP.P .strict { s₁ with pc := c1 :: s₁.pc } thenB).pc
                          = c1 :: s₁.pc := cstepListNSU_pc T SP.P _ thenB
                have hpp2 : (cstepListNSU T SP.P .strict { s₂ with pc := c1 :: s₂.pc } thenB).pc
                          = c1 :: s₂.pc := cstepListNSU_pc T SP.P _ thenB
                rcases hrecres with hb1 | hb2 | ⟨hb1, hb2, hbv, _, hbs⟩
                · left; exact hb1
                · right; left; exact hb2
                · right; right
                  exact ⟨hb1, hb2, hbv, hpc, fun _ => hbs (hpp1.symm ▸ hprd')⟩
              · simp only [if_neg hv0]
                have hrecres := cstepListNSU_preserves_NSULowEq T SP elseB hrec
                have hpp1 : (cstepListNSU T SP.P .strict { s₁ with pc := c1 :: s₁.pc } elseB).pc
                          = c1 :: s₁.pc := cstepListNSU_pc T SP.P _ elseB
                rcases hrecres with hb1 | hb2 | ⟨hb1, hb2, hbv, _, hbs⟩
                · left; exact hb1
                · right; left; exact hb2
                · right; right
                  exact ⟨hb1, hb2, hbv, hpc, fun _ => hbs (hpp1.symm ▸ hprd')⟩
            · -- non-readable condition: c2 also non-readable; branches DIVERGE,
              --   but each runs under a secret pc.
              have hrc2 : ¬ readable obs c2 := by
                intro hr2
                obtain ⟨hcc, _⟩ := hvx (Or.inr hr2)
                have hcc' : c1 = c2 := hcc
                rw [hcc'] at hrc; exact hrc hr2
              have hne1' : (c1 :: s₁.pc) ≠ [] := by simp
              have hne2' : (c2 :: s₂.pc) ≠ [] := by simp
              have hnr1' : ¬ readable obs (pcCap (c1 :: s₁.pc)) := by
                intro hrd
                have hexp : pcCap (c1 :: s₁.pc) = Cap.meet c1 (pcCap s₁.pc) := rfl
                rw [hexp] at hrd
                exact hrc (readable_meet_left hrd)
              have hnr2' : ¬ readable obs (pcCap (c2 :: s₂.pc)) := by
                intro hrd
                have hexp : pcCap (c2 :: s₂.pc) = Cap.meet c2 (pcCap s₂.pc) := rfl
                rw [hexp] at hrd
                exact hrc2 (readable_meet_left hrd)
              have hsec1 := cstepListNSU_secret (obs := obs) T SP.P
                { s₁ with pc := c1 :: s₁.pc } (if v1 ≠ 0 then thenB else elseB)
                hne1' hnr1' hnf1
              have hsec2 := cstepListNSU_secret (obs := obs) T SP.P
                { s₂ with pc := c2 :: s₂.pc } (if v2 ≠ 0 then thenB else elseB)
                hne2' hnr2' hnf2
              rw [show (if v1 ≠ 0 then cstepListNSU T SP.P .strict { s₁ with pc := c1 :: s₁.pc } thenB
                        else cstepListNSU T SP.P .strict { s₁ with pc := c1 :: s₁.pc } elseB)
                     = cstepListNSU T SP.P .strict { s₁ with pc := c1 :: s₁.pc }
                        (if v1 ≠ 0 then thenB else elseB) from by split <;> rfl,
                  show (if v2 ≠ 0 then cstepListNSU T SP.P .strict { s₂ with pc := c2 :: s₂.pc } thenB
                        else cstepListNSU T SP.P .strict { s₂ with pc := c2 :: s₂.pc } elseB)
                     = cstepListNSU T SP.P .strict { s₂ with pc := c2 :: s₂.pc }
                        (if v2 ≠ 0 then thenB else elseB) from by split <;> rfl]
              rcases hsec1 with hb1 | ⟨hb1, hv1', _⟩
              · left; exact hb1
              · rcases hsec2 with hb2 | ⟨hb2, hv2', _⟩
                · right; left; exact hb2
                · right; right
                  refine ⟨hb1, hb2, ?_, hpc, fun _ => ?_⟩
                  · rw [hv1', hv2']; exact hvis
                  · -- store: frame lemma on each divergent branch
                    have hst1 := cstepListNSU_secret_store (obs := obs) T SP.P
                      s₂.store { s₁ with pc := c1 :: s₁.pc }
                      (if v1 ≠ 0 then thenB else elseB) hne1' hnr1' hse
                    have hst2 := cstepListNSU_secret_store (obs := obs) T SP.P
                      (cstepListNSU T SP.P .strict { s₁ with pc := c1 :: s₁.pc }
                        (if v1 ≠ 0 then thenB else elseB)).store
                      { s₂ with pc := c2 :: s₂.pc }
                      (if v2 ≠ 0 then thenB else elseB) hne2' hnr2' hst1.symm
                    exact hst2.symm
        · left
          unfold cstepNSU
          rw [if_neg hh]
          cases hl1 : lookup s₁.store cond with
          | none => simp only [hl1]; rfl
          | some p => rw [hl1] at hlc1; simp at hlc1
    · -- NON-READABLE pc: whole statement runs secretly.
      have hne1 : s₁.pc ≠ [] := nonreadable_pc_ne_nil hprd
      have hnr2 : ¬ readable obs (pcCap s₂.pc) := by
        rcases hpc.1 with heq | ⟨_, hn2⟩
        · rw [← heq]; exact hprd
        · exact hn2
      have hne2 : s₂.pc ≠ [] := nonreadable_pc_ne_nil hnr2
      have hs1 := cstepNSU_secret (obs := obs) T SP.P s₁ st hne1 hprd hnf1
      have hs2 := cstepNSU_secret (obs := obs) T SP.P s₂ st hne2 hnr2 hnf2
      rcases hs1 with hh1' | ⟨hh1', hv1', hp1'⟩
      · left; exact hh1'
      · rcases hs2 with hh2' | ⟨hh2', hv2', hp2'⟩
        · right; left; exact hh2'
        · right; right
          refine ⟨hh1', hh2', ?_, ?_, ?_⟩
          · rw [hv1', hv2']; exact hvis
          · rw [hp1', hp2']  -- pcRelN after pc restoration
            exact hpc
          · rw [hp1']
            intro hc; exact absurd hc hprd
  termination_by sizeOf st

/-- **TINI preservation, statement list.** -/
theorem cstepListNSU_preserves_NSULowEq {obs : Cap} (T : ToolEnv) (SP : SoundPolicy)
    (prog : List CStmt) {s₁ s₂ : CState}
    (h : NSULowEq obs s₁ s₂) :
    NSULowEq obs (cstepListNSU T SP.P .strict s₁ prog) (cstepListNSU T SP.P .strict s₂ prog) := by
  match prog with
  | [] => simp only [cstepListNSU]; exact h
  | st :: rest =>
    simp only [cstepListNSU]
    have hstep := cstepNSU_preserves_NSULowEq T SP st h
    exact cstepListNSU_preserves_NSULowEq T SP rest hstep
  termination_by sizeOf prog

end

/-- **Unconditional termination-insensitive noninterference for the FIXED
    semantics.** For ANY plan, running two `NSULowEq`-related states preserves
    the relation; by `NSULowEq.observable`, two runs that both complete produce
    IDENTICAL observer-visible tool-call logs. The repair is the classical
    dynamic-IFC pair — the pc-gated admission check and the no-sensitive-upgrade
    write guard, with failstop failures — exactly the discipline of
    Austin–Flanagan applied to CaMeL's interpreter. -/
theorem nsu_noninterference {obs : Cap} (T : ToolEnv) (SP : SoundPolicy)
    (prog : List CStmt) {s₁ s₂ : CState}
    (h : NSULowEq obs s₁ s₂) :
    NSULowEq obs (crunNSU T SP.P .strict s₁ prog) (crunNSU T SP.P .strict s₂ prog) := by
  unfold crunNSU
  exact cstepListNSU_preserves_NSULowEq T SP prog h

end Camelcore

-- Axiom audit: the fix's noninterference must rest on the standard classical
-- axioms only (no sorryAx).
#print axioms Camelcore.nsu_noninterference
#print axioms Camelcore.NSULowEq.observable
#print axioms Camelcore.cstepListNSU_secret_store
