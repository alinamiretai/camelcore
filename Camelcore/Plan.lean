import Camelcore.Model

/-!
# Camelcore.Plan (v2) — operations, capability-only policies, execution

Refinements against the released implementation:

- **Tool calls return values** that re-enter the store, stamped with
  `toolResultCap`: sources = {Tool t} ∪ (sources of the args), readers = meet of
  the args' readers. This is exactly `value.py:wrap_output`, which labels the
  output `Capabilities({Tool(name)}, Public())` with dependencies
  `(fn, args, kwargs)` — the meet with the argument capabilities is the
  denotation of those dependency edges.
- **Tools are a deterministic oracle** `ToolEnv : Nat → List Nat → Nat`, shared
  by both runs. ASSUMPTION (documented): a tool's output depends only on its
  arguments. Real tools touch the world; noninterference is relative to this.
- **Policies are capability-only**: `Policy = Nat → List Cap → Recipients → Prop`
  receives the tool name and the ARGUMENT CAPABILITIES, never the values. This
  is a definitional encoding of the condition under which CaMeL's guarantee
  holds: the implementation's `SecurityPolicy` protocol receives raw
  `CaMeLValue`s and CAN inspect values — such policies fall outside this type,
  and outside the theorem (deliberately: that is a finding, not an oversight).
- **`SoundPolicy`** additionally requires the policy to enforce reader-flow to
  the recipients (`enforces_flow`). Without it, a permissive policy could admit
  a call that discloses non-`rcpt`-readable data to `rcpt`, and the
  noninterference theorem would be false. `basePolicy`
  (= `security_policy.py:base_security_policy`, generalized from `Public` to
  `rcpt`) is the canonical instance.
- **Denial halts.** The implementation RAISES `SecurityPolicyDeniedError`
  (interpreter.py:2063) rather than skipping the call; likewise an undefined
  variable raises. `State.halted` models abnormal termination, and the
  noninterference relation requires the halt-status to agree — making the
  guarantee termination-SENSITIVE with respect to policy denial.
-/

namespace Camelcore

abbrev Recipients := Cap

/-- Deterministic tool oracle: tool name × argument values → output value. -/
abbrev ToolEnv := Nat → List Nat → Nat

/-- A capability-only security policy: may inspect the tool name, the argument
    CAPABILITIES, and the recipients — never argument values. -/
abbrev Policy := Nat → List Cap → Recipients → Prop

/-- The base policy: every argument's capability flows to the recipients. -/
def basePolicy : Policy := fun _tool caps rcpt => ∀ c ∈ caps, Cap.flows c rcpt

/-- A policy together with a proof that it enforces reader-flow: admitting a
    call implies every argument may be disclosed to the recipients. This is the
    exact side condition under which noninterference holds for ANY policy. -/
structure SoundPolicy where
  P : Policy
  enforces_flow : ∀ tool caps rcpt, P tool caps rcpt → ∀ c ∈ caps, Cap.flows c rcpt

/-- The base policy is sound (its content IS the flow condition). -/
def basePolicySound : SoundPolicy := ⟨basePolicy, fun _ _ _ h => h⟩

inductive Stmt where
  | assign   (x : Var) (n : Nat) (c : Cap)
  | compute  (dst : Var) (srcs : List Var)
  | toolCall (dst : Var) (tool : Nat) (args : List Var) (rcpt : Recipients)

structure State where
  store  : Store
  out    : List (Nat × List Nat × Cap)
  halted : Bool

def lookupAll (σ : Store) : List Var → Option (List (Nat × Cap))
  | [] => some []
  | x :: xs =>
    match lookup σ x, lookupAll σ xs with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- The gate as a PROPOSITION: the arguments are all defined and the policy
    admits the call given their capabilities. Parameterizing over the policy
    makes the noninterference theorem quantify over ALL capability-only
    policies. -/
def Admits (P : Policy) (σ : Store) (tool : Nat) (args : List Var)
    (rcpt : Recipients) : Prop :=
  ∃ vs, lookupAll σ args = some vs ∧ P tool (vs.map (·.2)) rcpt

/-- Capability of a tool's return value (`value.py:wrap_output` + dependency
    edges to the arguments): tool source joined onto the meet of the argument
    capabilities. -/
def toolResultCap (tool : Nat) (argCaps : List Cap) : Cap :=
  Cap.meet (Cap.toolSource tool) (Cap.meetList argCaps)

end Camelcore

namespace Camelcore

open Classical

/-- One statement on a non-halted state.
    - `assign`: bind x to (n, c) — a literal with its label.
    - `compute`: bind dst to a value whose capability is the MEET of the srcs'
      caps (dependency-graph taint). Undefined src ⇒ halt (NameError raises).
    - `toolCall`: if the gate admits, bind dst to the oracle's output stamped
      with `toolResultCap` and log (tool, values, rcpt) to the observable
      output; if the gate denies, HALT (`SecurityPolicyDeniedError` raises).
      The `if` is on a Prop, made total by classical decidability — caps and
      policies stay arbitrary (strongest theorem). -/
noncomputable def step1 (T : ToolEnv) (P : Policy) (s : State) (st : Stmt) : State :=
  match st with
  | .assign x n c => { s with store := (x, n, c) :: s.store }
  | .compute dst srcs =>
      match lookupAll s.store srcs with
      | some vs =>
          { s with store :=
              (dst, (vs.map (·.1)).foldl (· + ·) 0, Cap.meetList (vs.map (·.2))) :: s.store }
      | none => { s with halted := true }
  | .toolCall dst tool args rcpt =>
      match lookupAll s.store args with
      | some vs =>
          if Admits P s.store tool args rcpt then
            { s with
                store := (dst, T tool (vs.map (·.1)), toolResultCap tool (vs.map (·.2))) :: s.store
                out   := s.out ++ [(tool, vs.map (·.1), rcpt)] }
          else { s with halted := true }
      | none => { s with halted := true }

/-- Apply one statement: a halted state is stuck (an exception aborted the plan). -/
noncomputable def step (T : ToolEnv) (P : Policy) (s : State) (st : Stmt) : State :=
  if s.halted = true then s else step1 T P s st

/-- Run a plan: fold step over the statements. -/
noncomputable def run (T : ToolEnv) (P : Policy) (s : State) (prog : List Stmt) : State :=
  prog.foldl (step T P) s

end Camelcore
