/-!
# Camelcore.Model — the core CaMeL calculus for noninterference (v2)

A machine-checked core of CaMeL (Debenedetti et al., "Defeating Prompt Injections
by Design"), refined against the released implementation
(google-research/camel-prompt-injection). We formalize the SECURITY-RELEVANT core:

- Capabilities are two-sided, matching `capabilities/capabilities.py`:
  * `readers`  — who may read the value; combined by INTERSECTION (meet), with
    `Public` as the top element (`readers.py`: `Public() & x = x`).
  * `sources`  — provenance; combined by UNION (join), matching
    `utils.py:get_all_sources`.
- `Cap.meet` is the taint-propagation composition: readers-meet + sources-join.
  It is the DENOTATION of the implementation's lazy dependency-graph traversal
  (`get_all_readers` / `get_all_sources` over `_dependencies`).
- `Cap.trusted` mirrors `utils.py:is_trusted` (all sources in the trusted set).
- `flows` is readers-only, as in the implementation's `can_readers_read_value`.

Fidelity notes (documented simplifications):
- `Tool.inner_sources` is dropped: a tool source is just a tool identifier.
- `Capabilities.other_metadata` (an untyped dict) is out of scope.
- Values are `Nat` payloads; the proof tracks capabilities and value-equality.
-/

namespace Camelcore

/-- Principals: readers of data. Kept abstract. -/
abbrev Principal := Nat

/-- Provenance labels, mirroring `sources.py`: the `SourceEnum` cases plus tool
    sources (simplified to a tool identifier; `inner_sources` dropped). -/
inductive Source where
  | user
  | camel
  | assistant
  | trustedTool
  | tool (name : Nat)

/-- A capability, mirroring `Capabilities(sources_set, readers_set)`:
    `readers p` = principal p may read the value (with "everyone" playing the
    role of `Public`); `sources s` = provenance label s is among the value's
    sources. Both are predicates so the core theorem holds for arbitrary
    (even infinite) label spaces; decidable checkers are layered on separately. -/
structure Cap where
  readers : Principal → Prop
  sources : Source → Prop

/-- Public readers, no sources: the identity for `meet`. -/
def Cap.public : Cap := { readers := fun _ => True, sources := fun _ => False }

/-- `Capabilities.default()`: user-sourced, publicly readable. -/
def Cap.user : Cap := { readers := fun _ => True, sources := fun s => s = .user }

/-- `Capabilities.camel()`: CaMeL-sourced, publicly readable. -/
def Cap.camel : Cap := { readers := fun _ => True, sources := fun s => s = .camel }

/-- The capability stamped on a tool's output by `value.py:wrap_output`:
    sources = {Tool(name)}, readers = Public. The output additionally depends on
    the arguments; see `toolResultCap` in Plan.lean. -/
def Cap.toolSource (name : Nat) : Cap :=
  { readers := fun _ => True, sources := fun s => s = .tool name }

/-- Taint-propagation composition: readers are INTERSECTED (only principals
    allowed by both — `get_all_readers` uses `&`), sources are UNIONED
    (`get_all_sources` uses `|`). This is the denotation of following the
    implementation's dependency edges. -/
def Cap.meet (a b : Cap) : Cap :=
  { readers := fun p => a.readers p ∧ b.readers p
    sources := fun s => a.sources s ∨ b.sources s }

/-- Meet over a list of capabilities (taint of an n-ary operation).
    Empty list = public with no sources. -/
def Cap.meetList : List Cap → Cap
  | []      => Cap.public
  | c :: cs => Cap.meet c (Cap.meetList cs)

/-- `flows a b`: a value with capability `a` may flow into a context requiring
    capability `b` iff a's readers ⊇ b's readers. Readers-only, matching
    `can_readers_read_value`. -/
def Cap.flows (a b : Cap) : Prop := ∀ p, b.readers p → a.readers p

/-- The trusted source set, mirroring `utils.py:_TRUSTED_SET`. A bare tool
    source is untrusted (the `inner_sources ⊆ trusted` refinement is dropped
    with `inner_sources` itself). -/
def trustedSource : Source → Prop
  | .user        => True
  | .camel       => True
  | .assistant   => True
  | .trustedTool => True
  | .tool _      => False

/-- `is_trusted`: every source of the value is trusted. -/
def Cap.trusted (c : Cap) : Prop := ∀ s, c.sources s → trustedSource s

/-- Trust distributes over the taint composition (sources are unioned). -/
theorem Cap.trusted_meet {a b : Cap} :
    (Cap.meet a b).trusted ↔ (a.trusted ∧ b.trusted) := by
  unfold Cap.trusted Cap.meet
  constructor
  · intro h
    exact ⟨fun s hs => h s (Or.inl hs), fun s hs => h s (Or.inr hs)⟩
  · rintro ⟨ha, hb⟩ s hs
    cases hs with
    | inl h' => exact ha s h'
    | inr h' => exact hb s h'

/-- Variables in the plan's store. -/
abbrev Var := String

/-- A store maps variables to (value, capability). -/
abbrev Store := List (Var × Nat × Cap)

def lookup (σ : Store) (x : Var) : Option (Nat × Cap) :=
  (σ.find? (·.1 == x)).map (·.2)

end Camelcore
