import Camelcore.Model
import Camelcore.Plan
import Camelcore.Control
import Camelcore.Noninterference

/-!
# Camelcore.Leak — the no-sensitive-upgrade leak, machine-checked

This file proves that plain noninterference is **FALSE** for the faithful
STRICT-mode control-flow semantics of `Control.lean`. It is not a limitation of
our model — it is the real behavior of `interpreter.py`, formalized:

- STRICT-mode assignment taints only the value assigned on the TAKEN branch
  (`_assign_name` + ambient pc). The other branch leaves the variable's label
  untouched (`test_control_flow.py::if_false_no_else`).
- A subsequent tool call is pc-gated and DENIED (→ halt) when its argument is
  tainted, but ADMITTED (→ a visible log entry) when it is not.

So whether a visible tool call happens depends on which branch was taken, i.e.
on the secret condition — even though the secret's VALUE never flows into any
admitted call. An observer of the tool-call channel learns the secret.

## The witness

    x    := 0                       -- public
    ite secret then x := 1 else y := 0   -- STRICT: taken branch taints x
    send(x) to a public recipient

Two states agree on all observer-readable data (they differ only in `secret`'s
value, under a capability the observer cannot read), yet produce different
visible logs: one halts on a denied send, the other emits the send. Hence
`CapLowEq` in, `¬ CapLowEq` out — noninterference fails.

The theorem `plain_NI_is_false` states this as a refutation of the natural
control-flow analogue of `cap_noninterference`.
-/

namespace Camelcore

/-- The observer is principal 0. -/
def obsPrincipal : Principal := 0

/-- The observer capability: reads exactly what principal 0 may read. -/
def obsCap : Cap := { readers := fun p => p = obsPrincipal, sources := fun _ => False }

/-- A secret capability the observer CANNOT read: everyone EXCEPT principal 0.
    (So `readable obsCap secretCap` is false — the secret does not flow to the
    observer.) -/
def secretCap : Cap := { readers := fun p => p ≠ obsPrincipal, sources := fun _ => False }

/-- A public capability the observer CAN read. -/
def pubCap : Cap := { readers := fun _ => True, sources := fun _ => False }

/-- Low-equivalence lifted to control states: same halt, same visible log, and
    observer-equivalent stores. (The pc stacks start empty and are internal;
    they are restored to the caller's stack after each `ite`, so they play no
    role in the observable relation.) -/
def CCapLowEq (obs : Cap) (s₁ s₂ : CState) : Prop :=
  s₁.halted = s₂.halted ∧ visLog obs s₁.out = visLog obs s₂.out ∧
    StoreCapEq obs s₁.store s₂.store

end Camelcore

namespace Camelcore

/-- `pubCap` is observer-readable. -/
theorem readable_pub : readable obsCap pubCap := by
  unfold readable Cap.flows pubCap obsCap
  intro p hp
  trivial

/-- `secretCap` is NOT observer-readable: the observer (principal 0) is excluded
    from its readers, but the recipient/obs requires principal 0 to be a reader. -/
theorem not_readable_secret : ¬ readable obsCap secretCap := by
  unfold readable Cap.flows secretCap obsCap
  intro h
  have := h obsPrincipal rfl
  exact this rfl

end Camelcore

namespace Camelcore

/-- The witness plan. `sendTool` is an arbitrary tool id; `pubCap` is the
    recipient (a public sink the observer can read). The `else` branch assigns a
    fresh variable `y`, leaving `x` untouched — this is the asymmetry that
    creates the leak. -/
def sendTool : Nat := 42

def witnessPlan : List CStmt :=
  [ .assign "x" 0 pubCap
  , .ite "secret"
      [ .assign "x" 1 pubCap ]      -- taken when secret ≠ 0: STRICT taints x with pc(secret)
      [ .assign "y" 0 pubCap ]      -- taken when secret = 0: x stays public
  , .toolCall "r" sendTool ["x"] pubCap ]

/-- Initial store with `secret` set to a given value under `secretCap`. -/
def initStore (secretVal : Nat) : Store := [("secret", secretVal, secretCap)]

/-- Initial control state for a given secret value. -/
def initState (secretVal : Nat) : CState :=
  { store := initStore secretVal, out := [], halted := false, pc := [] }

/-- The two runs start observer-low-equivalent: they agree on `secret`'s
    capability (both `secretCap`) and — since `secretCap` is not observer-
    readable — need not agree on its value; every other variable is absent. -/
theorem inits_lowEq : CCapLowEq obsCap (initState 1) (initState 0) := by
  refine ⟨rfl, rfl, ?_⟩
  intro x
  unfold initState initStore
  simp only [lookup, List.find?_cons, List.find?_nil]
  by_cases hx : ("secret" == x) = true
  · simp only [hx]
    unfold varCapEq
    refine ⟨rfl, fun hread => ?_⟩
    exact absurd hread not_readable_secret
  · simp only [hx]
    unfold varCapEq
    trivial

end Camelcore

namespace Camelcore

open Classical

/-! ### Reducing the two runs

We evaluate `crun … witnessPlan (initState k)` for k = 1 and k = 0. The plan has
three top-level statements; we reduce them in order. The only non-definitional
step is the `toolCall`, whose gate `CAdmits` is a classically-decided `Prop`; we
supply the deciding proof explicitly.
-/

/-- After `x := 0`, the store has `x ↦ (0, pubCap)` on top (STRICT with empty pc:
    `assignCap .strict [] pubCap = pubCap ⊓ public = pubCap`-equivalent). -/
theorem step1_store (k : Nat) :
    (cstep (fun _ _ => 0) basePolicy .strict (initState k) (.assign "x" 0 pubCap)).store
      = ("x", 0, assignCap .strict [] pubCap) :: initStore k := by
  unfold cstep
  simp only [initState, if_neg (by decide : ¬ (false = true))]

end Camelcore

/-!
--- CHECKPOINT BOUNDARY ---
The reduction lemmas below (`run1_visLog`, `run2_visLog`) are the computational
heart. We reduce each run one `cstep` at a time; the only non-definitional move
is the `toolCall` gate, discharged with an explicit `CAdmits` / `¬ CAdmits`
proof via `if_pos` / `if_neg`.
-/

namespace Camelcore

open Classical

/- Helpers: the base policy admits the send in run 2 (x is public, pc is public)
   and denies it in run 1 (x is tainted with `secretCap`, which does not flow to
   the public recipient). These are the two facts that make the visible logs
   differ. -/

/-- In run 2 (secret = 0), after the `else` branch `x ↦ (0, pubCap)` and the pc
    is empty, so every argument cap and the pc-cap flow to `pubCap`: admitted. -/
theorem admits_run2 (store2 : Store)
    (hx : lookup store2 "x" = some (0, pubCap)) :
    CAdmits basePolicy store2 [] sendTool ["x"] pubCap := by
  refine ⟨[(0, pubCap)], ?_, ?_⟩
  · simp only [lookupAll, hx]
  · intro c hc
    simp only [pcCap, Cap.meetList, List.map_cons, List.map_nil, List.mem_cons,
               List.not_mem_nil, or_false] at hc
    rcases hc with h | h
    · -- c = pcCap [] = Cap.public; flows to pubCap
      subst h
      unfold Cap.flows Cap.public pubCap
      intro p hp; trivial
    · -- c = pubCap; flows to pubCap
      subst h
      unfold Cap.flows pubCap
      intro p hp; exact hp

end Camelcore

namespace Camelcore

open Classical

/-- `cstepList` distributes over list append: running `xs ++ ys` is running `xs`
    then running `ys` from the resulting state. (Standard fold-append; lets us
    reduce a plan prefix independently of its tail.) -/
theorem cstepList_append (T : ToolEnv) (P : Policy) (m : Mode) (s : CState) :
    ∀ (xs ys : List CStmt),
      cstepList T P m s (xs ++ ys)
        = cstepList T P m (cstepList T P m s xs) ys := by
  intro xs
  induction xs generalizing s with
  | nil => intro ys; rfl
  | cons a as ih =>
    intro ys
    simp only [List.cons_append, cstepList]
    exact ih (cstep T P m s a) ys

/-- The concrete state after the first two statements of run 2 (`x := 0` then the
    `ite` taking the else-branch because secret = 0). Everything here is
    computable (no gate), so it reduces by simp with the string decisions. -/
theorem run2_prefix :
    cstepList (fun _ _ => 0) basePolicy .strict (initState 0)
        [ .assign "x" 0 pubCap
        , .ite "secret" [ .assign "x" 1 pubCap ] [ .assign "y" 0 pubCap ] ]
      = { store := [("y", 0, assignCap .strict [secretCap] pubCap),
                    ("x", 0, assignCap .strict [] pubCap),
                    ("secret", 0, secretCap)],
          out := [], halted := false, pc := [] } := by
  simp only [cstepList, cstep, initState, initStore, lookup,
             List.find?_cons, beq_self_eq_true, Option.map_some,
             if_neg (by decide : ¬ (false = true)),
             show ("x" == "secret") = false by decide,
             (by decide : ¬ ((0 : Nat) ≠ 0)), if_false]

/-- The base policy admits the send on the concrete run-2 prefix state: the sole
    argument `x` has cap `assignCap .strict [] pubCap = pubCap ⊓ public`, and the
    pc is empty (`pcCap [] = public`); both flow to the public recipient. -/
theorem admits_run2_concrete :
    CAdmits basePolicy
      [("y", 0, assignCap .strict [secretCap] pubCap),
       ("x", 0, assignCap .strict [] pubCap),
       ("secret", 0, secretCap)] [] sendTool ["x"] pubCap := by
  refine ⟨[(0, assignCap .strict [] pubCap)], ?_, ?_⟩
  · simp only [lookupAll, lookup, List.find?_cons, Option.map_some,
               show ("y" == "x") = false by decide,
               show ("x" == "x") = true by decide]
  · intro c hc
    simp only [pcCap, Cap.meetList, List.map_cons, List.map_nil, List.mem_cons,
               List.not_mem_nil, or_false] at hc
    rcases hc with h | h
    · subst h; unfold Cap.flows Cap.public pubCap; intro p hp; trivial
    · subst h
      -- c = assignCap .strict [] pubCap = pubCap ⊓ public; flows to pubCap
      unfold assignCap pcCap Cap.meetList Cap.flows Cap.meet pubCap Cap.public
      intro p hp; exact ⟨hp, trivial⟩

/-- Reduce run 2 (secret = 0) to its visible log: after `run2_prefix`, `x` is
    public, so `send(x)` is admitted (`admits_run2_concrete`) and appended; the
    recipient `pubCap` is observer-readable, so it survives `visLog`. -/
theorem run2_visLog :
    visLog obsCap (crun (fun _ _ => 0) basePolicy .strict (initState 0) witnessPlan).out
      = [(sendTool, [0], pubCap)] := by
  unfold crun witnessPlan
  rw [show ([ .assign "x" 0 pubCap
           , .ite "secret" [ .assign "x" 1 pubCap ] [ .assign "y" 0 pubCap ]
           , .toolCall "r" sendTool ["x"] pubCap ] : List CStmt)
        = [ .assign "x" 0 pubCap
          , .ite "secret" [ .assign "x" 1 pubCap ] [ .assign "y" 0 pubCap ] ]
          ++ [ .toolCall "r" sendTool ["x"] pubCap ] from rfl]
  rw [cstepList_append, run2_prefix]
  -- One toolCall step on the concrete prefix state; the args lookup and the gate.
  simp only [cstepList, cstep, if_neg (by decide : ¬ (false = true)),
             lookupAll, lookup, List.find?_cons, Option.map_some,
             show ("y" == "x") = false by decide,
             show ("x" == "x") = true by decide,
             if_pos admits_run2_concrete, List.map_cons, List.map_nil,
             List.nil_append]
  -- Now evaluate visLog on the single appended entry (recipient pubCap, readable).
  simp only [visLog, List.filter_cons, List.filter_nil,
             decide_eq_true_eq]
  rw [if_pos]
  exact readable_pub

end Camelcore



namespace Camelcore

open Classical

/-- The concrete state after the first two statements of run 1 (`x := 0` then the
    `ite` taking the THEN branch because secret = 1). `x` is now tainted with the
    pc = [secretCap]. -/
theorem run1_prefix :
    cstepList (fun _ _ => 0) basePolicy .strict (initState 1)
        [ .assign "x" 0 pubCap
        , .ite "secret" [ .assign "x" 1 pubCap ] [ .assign "y" 0 pubCap ] ]
      = { store := [("x", 1, assignCap .strict [secretCap] pubCap),
                    ("x", 0, assignCap .strict [] pubCap),
                    ("secret", 1, secretCap)],
          out := [], halted := false, pc := [] } := by
  simp only [cstepList, cstep, initState, initStore, lookup,
             List.find?_cons, beq_self_eq_true, Option.map_some,
             if_neg (by decide : ¬ (false = true)),
             show ("x" == "secret") = false by decide,
             if_pos (show (1 : Nat) ≠ 0 by decide)]

/-- The base policy DENIES the send on the run-1 prefix: the argument `x` has cap
    `pubCap ⊓ secretCap`, whose readers exclude the observer, so it does not flow
    to the public recipient `pubCap`. -/
theorem denies_run1_concrete :
    ¬ CAdmits basePolicy
        [("x", 1, assignCap .strict [secretCap] pubCap),
         ("x", 0, assignCap .strict [] pubCap),
         ("secret", 1, secretCap)] [] sendTool ["x"] pubCap := by
  rintro ⟨vs, hvs, hp⟩
  simp only [lookupAll, lookup, List.find?_cons, Option.map_some,
             show ("x" == "x") = true by decide] at hvs
  -- hvs : some [(1, …)] = some vs — strip the `some`.
  rw [Option.some.injEq] at hvs
  subst hvs
  have hc : (assignCap .strict [secretCap] pubCap) ∈
              (pcCap [] :: List.map (·.2) [(1, assignCap .strict [secretCap] pubCap)]) := by
    simp only [List.map_cons, List.map_nil, List.mem_cons]
    right
    simp only [List.not_mem_nil, or_false]
  have hflow := hp _ hc
  rw [Cap.flows] at hflow
  have hr := hflow obsPrincipal (by simp [pubCap])
  -- `hr` says the observer may read a secretCap-tainted value; but secretCap
  -- excludes the observer. `simp` computes the meet's readers at obsPrincipal
  -- to `… ∧ (0 ≠ 0) ∧ …`, i.e. False.
  simp [assignCap, pcCap, Cap.meetList, Cap.meet, secretCap, pubCap,
        Cap.public, obsPrincipal] at hr

/-- Reduce run 1 (secret = 1) to its visible log: the send is denied, the run
    halts before appending anything, so the visible log is EMPTY. -/
theorem run1_visLog :
    visLog obsCap (crun (fun _ _ => 0) basePolicy .strict (initState 1) witnessPlan).out
      = [] := by
  unfold crun witnessPlan
  rw [show ([ .assign "x" 0 pubCap
           , .ite "secret" [ .assign "x" 1 pubCap ] [ .assign "y" 0 pubCap ]
           , .toolCall "r" sendTool ["x"] pubCap ] : List CStmt)
        = [ .assign "x" 0 pubCap
          , .ite "secret" [ .assign "x" 1 pubCap ] [ .assign "y" 0 pubCap ] ]
          ++ [ .toolCall "r" sendTool ["x"] pubCap ] from rfl]
  rw [cstepList_append, run1_prefix]
  simp only [cstepList, cstep, if_neg (by decide : ¬ (false = true)),
             lookupAll, lookup, List.find?_cons, Option.map_some,
             show ("x" == "x") = true by decide,
             if_neg denies_run1_concrete]
  simp only [visLog, List.filter_nil]

end Camelcore

namespace Camelcore

open Classical

/-- **The no-sensitive-upgrade leak, machine-checked.** Plain noninterference is
    FALSE for the faithful STRICT-mode control-flow semantics: the two runs start
    observer-low-equivalent (`inits_lowEq`) but produce different visible logs —
    run 1 (secret = 1) halts on a denied send (empty log), run 2 (secret = 0)
    emits the send (`[(sendTool, [0], pubCap)]`). An observer of the tool-call
    channel therefore distinguishes two low-equivalent inputs: the secret leaks
    through control flow. This is not a modeling artifact — it is the behavior of
    `interpreter.py`, formalized. -/
theorem plain_NI_is_false :
    ¬ (∀ (T : ToolEnv) (SP : SoundPolicy) (prog : List CStmt) (s₁ s₂ : CState),
        CCapLowEq obsCap s₁ s₂ →
        CCapLowEq obsCap (crun T SP.P .strict s₁ prog) (crun T SP.P .strict s₂ prog)) := by
  intro hNI
  have h := hNI (fun _ _ => 0) basePolicySound witnessPlan
              (initState 1) (initState 0) inits_lowEq
  obtain ⟨_, hvis, _⟩ := h
  -- `basePolicySound.P` is definitionally `basePolicy`; make it syntactic.
  dsimp only [basePolicySound] at hvis
  rw [run1_visLog, run2_visLog] at hvis
  exact absurd hvis (by simp)

end Camelcore

#print axioms Camelcore.plain_NI_is_false
