/-!
# Camelcore.Model — the core CaMeL calculus for noninterference

A machine-checked core of CaMeL (Debenedetti et al., "Defeating Prompt Injections
by Design"). We formalize the SECURITY-RELEVANT core, not Python: values carry
capabilities (allowed-reader sets), operations propagate taint conservatively
(intersection of readers), and tool calls are gated by a policy that checks the
recipients against the arguments' capabilities.

The confidentiality theorem (Noninterference.lean) proves: two runs of a plan whose
data differs only in fields no permitted tool can read produce identical tool-call
outputs. This is CaMeL's guarantee, machine-checked.

Design (signed off):
- Capability = set of allowed readers (as a predicate Principal → Prop).
- flows := superset (⊇): a value may flow where its readers include all required.
- operation taint := intersection of input readers (the conservative meet).
- tool-call admitted iff every argument's readers ⊇ the recipients.
-/

namespace Camelcore

/-- Principals: readers of data (users, or the special Public case handled by the
    reader-set containing everyone). Kept abstract. -/
abbrev Principal := Nat

/-- A capability is the set of principals allowed to read a value, represented as
    a predicate. `readers p` means principal p may read the value. -/
structure Cap where
  readers : Principal → Prop

/-- Public data: everyone may read it (the least restrictive capability). -/
def Cap.public : Cap := { readers := fun _ => True }

/-- The intersection of two capabilities: only principals allowed by BOTH.
    This is the taint-propagation meet for binary operations. -/
def Cap.meet (a b : Cap) : Cap := { readers := fun p => a.readers p ∧ b.readers p }

/-- Meet over a list of capabilities: a principal may read the result iff it may
    read every input. (Taint of an n-ary operation.) Empty list = public. -/
def Cap.meetList : List Cap → Cap
  | []      => Cap.public
  | c :: cs => Cap.meet c (Cap.meetList cs)

/-- `flows a b`: a value with capability `a` may flow into a context requiring
    capability `b`, iff every reader required by b is already allowed by a
    (a.readers ⊇ b.readers). More-permissive flows into more-restrictive. -/
def Cap.flows (a b : Cap) : Prop := ∀ p, b.readers p → a.readers p

/-- Variables in the plan's store. -/
abbrev Var := String

/-- A store maps variables to (value, capability). Values are Nat payloads; the
    proof tracks capabilities and value-equality, not arithmetic. -/
abbrev Store := List (Var × Nat × Cap)

def lookup (σ : Store) (x : Var) : Option (Nat × Cap) :=
  (σ.find? (·.1 == x)).map (·.2)

end Camelcore
