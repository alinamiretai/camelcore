# Camelcore: a machine-checked noninterference study of CaMeL

A [Lean 4](https://leanprover.github.io/) formalization of the security core of
CaMeL (Debenedetti et al., *Defeating Prompt Injections by Design*,
[arXiv:2503.18813](https://arxiv.org/abs/2503.18813)). It models CaMeL's
capability system and interpreter, proves what the design guarantees,
exhibits a machine-checked counterexample showing what it does not, and
proves a repaired interpreter that restores the missing guarantee for every plan.

Everything here is checked by the Lean kernel. The three headline results depend
only on the standard classical axioms `[propext, Classical.choice, Quot.sound]` —
there are no `sorry`s anywhere in the development (verified via
`#print axioms`, see below).

---

## The three results

| # | Theorem | File | Informal statement |
|---|---------|------|--------------------|
| 1 | `cap_noninterference` | `Noninterference.lean` | The two-sided capability semantics is noninterferent: low-equivalent inputs stay low-equivalent under any policy that enforces reader-flow. |
| 2 | `plain_NI_is_false` | `Leak.lean` | **The leak.** Plain noninterference is *false* for the faithful STRICT-mode control-flow interpreter: a tool call inside a secret branch fires in one run and is denied in the other, so the secret leaks through the visible tool-call log. |
| 3 | `nsu_noninterference` | `NSU.lean` | **The fix.** A repaired interpreter — pc-gated admission + a no-sensitive-upgrade write guard + failstop failures — satisfies *termination-insensitive* noninterference for **every** plan (no fragment restriction). |

Result 2 is the centerpiece: it is a proof of a *non-theorem*, i.e. a
formalized counterexample. It shows the leak is not a modeling artifact but the
behavior of `interpreter.py` under a shipped, capability-only policy.

Result 3 is the remedy the CaMeL papers' future-work sections asked for: the
classical dynamic information-flow-control discipline (Austin–Flanagan
no-sensitive-upgrade), instantiated on CaMeL's interpreter and mechanized.

---

## Module map

Layered bottom-up; each file imports only those above it.

| File | Contents |
|------|----------|
| `Model.lean` | Two-sided capabilities `Cap` (reader/source predicates), `Cap.meet`/`meetList`/`flows`, the `Store`, and `lookup`. |
| `Plan.lean` | The plan language, `lookupAll`, `toolResultCap`, `ToolEnv`, `Policy`, and `SoundPolicy` (a policy plus its reader-flow guarantee). |
| `Checker.lean` | The admit-check correctness lemma. |
| `Noninterference.lean` | Straight-line capability semantics and **Result 1**, plus the reusable observer machinery (`readable`, `varCapEq`, `StoreCapEq`, `readable_meetList`, …). |
| `Control.lean` | pc-tainting control-flow interpreter faithful to `interpreter.py`: `CStmt`, `CState`, `pcCap`, `cstep`/`cstepList`/`crun`, and `visLog` (the recipient-filtered visible log). |
| `Leak.lean` | The witness plan, the low-equivalence relation `CCapLowEq`, and **Result 2** (`plain_NI_is_false`). |
| `SafeFragment.lean` | Taint analysis and frame lemmas (`tainted`, `taintStep`, `cstep_frame`). Retained as infrastructure; the Layer-3 fragment-restricted proof was superseded by Layer 4. |
| `NSU.lean` | The fixed interpreter and **Result 3**. Defines `AdmitsNSU`, `WriteOK`, `failNSU`, `cstepNSU`, the TINI relation `NSULowEq`, and the full preservation proof. |

---

## The fix, precisely (`NSU.lean`)

The repaired step function `cstepNSU` differs from `cstep` in exactly three
places, each closing a distinct channel that the proof attempt surfaced:

1. **pc-gated admission — `AdmitsNSU`.** A tool call is admitted only if, in
   addition to the shipped policy check on the argument capabilities, the ambient
   program-counter capability flows to the recipients (`Cap.flows (pcCap pc)
   rcpt`). A call inside a secret branch can then only target secret recipients,
   so its log entry is filtered from the observer's view. *This is the channel
   `plain_NI_is_false` exploits.*

2. **No-sensitive-upgrade write guard — `WriteOK`.** A write to `dst` is
   permitted only if `dst` is unbound or its current capability is at least as
   confidential as the pc. This blocks a secret branch from clobbering a public
   variable — the classic flow-sensitivity leak. *Discovered because the
   preservation proof fails without it: a secret branch overwriting a
   public-readable variable is observable.*

3. **Failstop failures — `failNSU`.** Any failure (undefined variable, denied
   call, blocked upgrade) halts the run, exactly as `interpreter.py` raises. The
   disclosed price is the classical one-bit termination channel; the guarantee is
   therefore *termination-insensitive*: two runs that **both complete** produce
   identical visible logs. *Discovered because silent-skip failure handling is
   unsound — a variable defined in one run but absent in the other (via a
   divergent branch or a failed lookup) is itself observable.*

The relation `NSULowEq` builds the termination-insensitivity in as a
disjunction: `halted₁ ∨ halted₂ ∨ (both live ∧ full agreement)`. Every
asymmetric situation drops into a halt disjunct with no proof obligation, which
is what makes the fixed semantics provable where the original is not.
`NSULowEq.observable` is the soundness bridge: for runs that both complete, the
relation implies equal visible logs.

Points 2 and 3 are findings in their own right — they are properties the
mechanization *forced*, not choices made up front, and they are exactly the kind
of subtlety a machine-checked proof exists to catch.

---

## Building & verifying

Requires Lean 4 (toolchain pinned in `lean-toolchain`) and Mathlib.

```bash
lake build                      # builds the whole development
lake build Camelcore.NSU        # builds Layer 4 and prints the axiom audit
```

A successful build prints, with **no `sorryAx`**:

```
'Camelcore.cap_noninterference'       depends on axioms: [propext, Classical.choice, Quot.sound]
'Camelcore.plain_NI_is_false'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Camelcore.nsu_noninterference'       depends on axioms: [propext, Classical.choice, Quot.sound]
'Camelcore.NSULowEq.observable'       depends on axioms: [propext, Classical.choice, Quot.sound]
```

To re-audit any result directly:

```lean
#print axioms Camelcore.nsu_noninterference
```

---

## Assumptions & scope

- **Tool determinism.** Tools are modeled as pure functions `ToolEnv = Nat →
  List Nat → Nat`; the results concern information flow, not tool side effects.
- **Policy soundness.** `SoundPolicy` bundles a policy with a proof that
  admitting a call implies each argument capability may flow to the recipients —
  the exact side condition under which noninterference holds for *any* policy.
- **Values are naturals; the store is an association list.** The capability
  reasoning is independent of the value domain.
- **Observer model.** An observer is a capability `obs`; it sees a tool-call log
  entry iff the recipients are readable to it (`visLog`). Result 3 additionally
  assumes the observer is non-degenerate (reads at least one principal), which is
  the only setting in which noninterference is a non-vacuous requirement.

The formalization targets the *security core* — the capability calculus and the
control-flow interpreter — not the full Python surface (quarantined-LLM parsing,
the value graph, error message construction). Two source-level findings outside
the core are noted for the authors rather than modeled: an f-string in the
denial path that interpolates raw private values into an exception, and the
error/termination channel that motivates the failstop design above.

---

## Layout

```
Camelcore.lean            -- umbrella import
Camelcore/
  Model.lean  Plan.lean  Checker.lean
  Noninterference.lean    -- Result 1
  Control.lean  SafeFragment.lean
  Leak.lean               -- Result 2  (the leak)
  NSU.lean                -- Result 3  (the fix)
```
