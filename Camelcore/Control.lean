import Camelcore.Model
import Camelcore.Plan

/-!
# Camelcore.Control — control flow, pc-taint, and the no-sensitive-upgrade finding

This layer adds branching (`CStmt.ite`) with a program-counter (pc) taint stack,
modeled faithfully against `interpreter.py`:

- `_eval_if` (line 1687) pushes the branch TEST value onto the ambient
  `dependencies` list while executing the TAKEN branch, then pops it
  (line 1701 `dependencies.remove(test)`). We model this with a `pc : List Cap`
  stack in `CState`.
- In STRICT mode, `_assign_name` (line 648) stamps the ambient dependencies
  (which include the pc) onto the assigned value. So an assignment inside a
  branch is tainted by the branch condition — but ONLY on the taken branch.
- `_eval_call` (line 2050) passes the ambient `dependencies` to
  `check_policy`, and `security_policy.py` denies any state-changing call
  depending on a non-public value. So a tool call inside a branch is pc-GATED,
  and — crucially — this happens in ALL eval modes, not only STRICT. We model
  the gate as consulting the pc alongside the argument capabilities.

The asymmetry between these two (assignment taint is STRICT-only; tool gating is
mode-independent) is exactly what makes the no-sensitive-upgrade leak subtle,
and it is why the leak is about the PRESENCE/ABSENCE of a visible event rather
than about an unprotected send.

## Roadmap within this file
1. Types + faithful STRICT semantics (this layer).
2. The leak witness: a plan + two observer-equivalent states whose visible
   logs differ — a machine-checked proof that plain NI is FALSE.  [next layer]
3. `NoSensitiveUpgrade`: the side condition on plans under which NI holds
   (the safe-usage boundary for the current interpreter).           [next layer]
4. `stepNSU`: the fixed semantics (halt on public-var upgrade under non-public
   pc) with unconditional NI — the proposed remedy.                  [next layer]
-/

namespace Camelcore

/-- Statements with branching. `ite cond thenB elseB` mirrors `ast.If`; the
    condition is a variable (its VALUE decides the branch, its CAP enters the
    pc). We reuse the flat `Stmt` operations by embedding them. -/
inductive CStmt where
  | assign   (x : Var) (n : Nat) (c : Cap)
  | compute  (dst : Var) (srcs : List Var)
  | toolCall (dst : Var) (tool : Nat) (args : List Var) (rcpt : Recipients)
  | ite      (cond : Var) (thenB elseB : List CStmt)

/-- Evaluation mode, mirroring `interpreter.py:MetadataEvalMode`. In STRICT,
    assignments absorb the pc; in NORMAL they do not (implicit flows are not
    propagated into stored values — itself a finding, layer 5). Tool-call
    gating consults the pc in BOTH modes. -/
inductive Mode where
  | strict
  | normal

/-- Execution state with a program-counter taint stack. -/
structure CState where
  store  : Store
  out    : List (Nat × List Nat × Cap)
  halted : Bool
  pc     : List Cap

/-- The ambient capability contributed by the pc stack: the meet of all
    enclosing branch conditions. Empty pc = public (no control-flow taint). -/
def pcCap (pc : List Cap) : Cap := Cap.meetList pc

/-- The gate with pc: arguments AND the pc must satisfy the policy against the
    recipients. We fold the pc capability in as an extra "argument capability",
    matching the implementation passing ambient dependencies to `check_policy`.
    This is mode-INDEPENDENT. -/
def CAdmits (P : Policy) (σ : Store) (pc : List Cap) (tool : Nat)
    (args : List Var) (rcpt : Recipients) : Prop :=
  ∃ vs, lookupAll σ args = some vs ∧ P tool (pcCap pc :: vs.map (·.2)) rcpt

/-- In STRICT mode, an assignment absorbs the pc into the stored capability;
    in NORMAL mode it does not. This is the ONE place the modes differ for
    stored values. -/
def assignCap (m : Mode) (pc : List Cap) (c : Cap) : Cap :=
  match m with
  | .strict => Cap.meet c (pcCap pc)
  | .normal => c

end Camelcore

namespace Camelcore

open Classical

-- `cstep` / `cstepList` are mutually recursive because branch bodies are
-- `List CStmt`. `ite` pushes the condition's cap, runs the taken branch, and
-- pops — exactly `_eval_if`. A halted state is stuck.
mutual

/-- One control statement, faithful to `interpreter.py`. -/
noncomputable def cstep (T : ToolEnv) (P : Policy) (m : Mode)
    (s : CState) (st : CStmt) : CState :=
  if s.halted = true then s else
  match st with
  | .assign x n c =>
      { s with store := (x, n, assignCap m s.pc c) :: s.store }
  | .compute dst srcs =>
      match lookupAll s.store srcs with
      | some vs =>
          { s with store :=
              (dst, (vs.map (·.1)).foldl (· + ·) 0,
                assignCap m s.pc (Cap.meetList (vs.map (·.2)))) :: s.store }
      | none => { s with halted := true }
  | .toolCall dst tool args rcpt =>
      match lookupAll s.store args with
      | some vs =>
          if CAdmits P s.store s.pc tool args rcpt then
            { s with
                store := (dst, T tool (vs.map (·.1)),
                  Cap.meet (toolResultCap tool (vs.map (·.2))) (pcCap s.pc)) :: s.store
                out   := s.out ++ [(tool, vs.map (·.1), rcpt)] }
          else { s with halted := true }
      | none => { s with halted := true }
  | .ite cond thenB elseB =>
      match lookup s.store cond with
      | some (v, c) =>
          -- push the condition's cap; take the branch determined by the value
          let s' := { s with pc := c :: s.pc }
          let s'' := if v ≠ 0
                     then cstepList T P m s' thenB
                     else cstepList T P m s' elseB
          -- pop the pc (restore the enclosing stack)
          { s'' with pc := s.pc }
      | none => { s with halted := true }

noncomputable def cstepList (T : ToolEnv) (P : Policy) (m : Mode)
    (s : CState) : List CStmt → CState
  | [] => s
  | st :: rest => cstepList T P m (cstep T P m s st) rest

end

/-- Run a control-flow plan. -/
noncomputable def crun (T : ToolEnv) (P : Policy) (m : Mode)
    (s : CState) (prog : List CStmt) : CState :=
  cstepList T P m s prog

end Camelcore
