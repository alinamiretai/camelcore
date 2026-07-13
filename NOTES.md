# Camelcore v2 — refinement against google-research/camel-prompt-injection

**Status: written without a Lean toolchain available (sandboxed authoring
environment). The definitions are careful; the proofs mirror idioms from the
v1 files that are known to compile on your setup, but they have NOT been
typechecked. Build first; see "Compile-risk list" for the spots most likely to
need a one-line fix.**

## What changed from v1

| v1 | v2 | Why (implementation source) |
|---|---|---|
| `Cap = readers` | `Cap = readers × sources` | `capabilities.py`: `Capabilities(sources_set, readers_set)` |
| — | `Cap.meet` also unions sources | `utils.py:get_all_sources` (union) vs `get_all_readers` (intersection) |
| — | `Cap.trusted`, `trustedSource` | `utils.py:is_trusted`, `_TRUSTED_SET` |
| `toolCall` only logs | `toolCall dst …` binds a result: value from a deterministic oracle `ToolEnv`, cap = `toolResultCap` = toolSource ⊓ meet(argCaps) | `value.py:wrap_output`: `Capabilities({Tool(name)}, Public())` + dependency edges `(fn, args, kwargs)` |
| fixed gate `Admits` | gate parameterized by `Policy = tool → List Cap → Recipients → Prop`; NI proved for every `SoundPolicy` | `security_policy.py`: `SecurityPolicyEngine.check_policy`; the theorem now states the exact class of safe policies |
| deny ⇒ no-op | deny ⇒ `halted := true`; undefined var ⇒ halt; `CapLowEq` includes halt status | `interpreter.py:2063` **raises** `SecurityPolicyDeniedError`; NameError likewise raises |
| `varCapEq` = pointwise reader agreement | `varCapEq` = capability **equality** | both runs execute the same plan, so labels agree on the nose; deletes `flows_congr` and `meetList_readers_eq` |

`Capabilities.default()` = `Cap.user`, `Capabilities.camel()` = `Cap.camel`
(from `capabilities.py`). `other_metadata` (untyped dict) is out of scope.
`Tool.inner_sources` is dropped (tool source = identifier only).

## Model ↔ implementation mapping

- `Cap.meetList` over a `compute`'s sources = the denotation of the lazy
  dependency-graph traversal (`get_all_readers`/`get_all_sources` over
  `_dependencies`). **Open item (bridge lemma):** formalize the graph
  representation `(metadata, dependencies)` and prove the traversal equals the
  eager meet. Watch the cycle-detection semantics (`visited_objects` by
  Python `id()`): at a back-edge `get_all_readers` returns the node's local
  readers, so on cyclic heaps the traversal is NOT obviously
  order-independent — pin this down or restrict the bridge lemma to DAGs.
- `Admits P σ tool args rcpt` = `check_policy` restricted to capability-only
  policies. The real engine ALSO receives the ambient pc-dependency list
  (`interpreter.py:2050-2054` passes `dependencies`) — see roadmap item 2.
- `ToolEnv` determinism = ASSUMPTION: a tool's output depends only on its
  arguments. Real tools touch the world; the theorem is relative to this
  (standard for NI results; state it in the paper/email).

## Findings the formalization pins down

1. **Policy soundness is load-bearing, twice.** NI requires policies to be
   (a) capability-only — the implementation's `SecurityPolicy` protocol
   receives raw `CaMeLValue`s and can inspect values, which falls outside the
   theorem; and (b) flow-enforcing (`enforces_flow`) — otherwise an admitted
   call discloses non-readable arg values to a readable recipient and the
   `visLog` case of `step_preserves_capLowEq` fails. The proof consumes each
   condition at exactly one spot; that's the cleanest possible statement of
   "which policies preserve CaMeL's guarantee."
2. **No-sensitive-upgrade gap (roadmap, not yet formalized).** STRICT mode
   taints only the TAKEN branch (`_assign_name` + ambient deps;
   `if False: a = 1` with no else leaves the namespace untouched —
   `test_control_flow.py::if_false_no_else`). Classic dynamic-IFC leak:
   `x = public; if secret: x = …; send(x)` — denial (which raises) in one run,
   successful visible send in the other ⇒ the observer learns `secret`.
   Plan: add `Stmt.ite` with taken-branch pc-taint, formalize the
   counterexample as a non-theorem, then prove NI under a side condition
   (no partially-assigning branches on non-public tests, or NSU semantics).
3. **Denial reason leaks raw private values.** `check_policy` interpolates
   `d.raw` of non-public dependencies into the `Denied` reason, raised as a
   plain exception OUTSIDE the capability-carrying `CaMeLException` path
   (contrast `interpreter.py:2111`, which stamps tool errors with
   capabilities). Wherever that message surfaces (error feedback to the
   P-LLM), private data enters the privileged context untracked.
4. **`query_ai_assistant` in STRICT mode appends its args to the ambient
   dependency list with no matching removal** (`interpreter.py:2067-2068`),
   tainting everything downstream. Possibly intentional (post-QLLM code is
   contaminated), possibly a bug; model it faithfully when adding QLLM calls
   and flag it.

## Compile-risk list (check these first if the build fails)

1. `step_preserves_capLowEq`, halted case: `rw [if_pos hh, if_pos hh2]` /
   `rw [if_neg hh, if_neg hh2]` on `if s.halted = true`. If `rw` balks,
   `simp only [step, hh, hh2, if_true]` (resp. `Bool.false_eq_true, if_false`
   with `hh1 : s₁.halted = false`) is the fallback.
2. `simp only [step1, hla1, hla2, ha, ha2, if_true]` (and the `if_false`
   twin): mirrors v1's `simp only [ha, ha2, if_true]`, which compiled, but the
   match-reduction now goes through `step1`'s equations. Fallback: `unfold
   step1` first, then `simp only [hla1, hla2, ha, ha2, if_true]`.
3. `varCapEq` mismatch cases use `hx.elim` / `absurd … (by simp)`: the match
   is now on bare `Option` constructors (no pair patterns), so reduction
   should be definitional; if not, `simp [varCapEq] at hx` closes it.
4. `unfold readable Cap.flows at hr ⊢` followed by `unfold Cap.flows at hf`
   in the visLog branch: `unfold` fails if the constant doesn't occur at a
   location; if so, split into separate `unfold … at hr`, `… at hf`, `… ⊢`.
5. `List.mem_map_of_mem hvc` (Checker) — arity/implicitness of `f` varies
   across toolchain versions; v1 used the one-argument form successfully.
6. `simp [List.map_cons]` for head-membership goals (`lookupAll_val_agree`) —
   v1 idiom, kept verbatim.
7. `hmap ▸ hp` in `admits_agree`: if the motive fails to infer, replace with
   `by rw [← hmap] at hp ⊢ <;> exact hp` or `hmap ▸ hp` → `by rw [hmap] at hp; exact hp`
   (direction: `hmap : vs₁.map (·.2) = vs₂.map (·.2)`).

## Roadmap (in order)

1. Build + fix; re-run `#print axioms` (expect `Classical.choice`,
   `propext`, `Quot.sound` only).
2. **Control flow**: `Stmt.ite (cond : Var) (then else : List Stmt)` with a
   pc-stack in `State`; taken-branch tainting per STRICT mode; ambient pc
   passed to the gate (both modes, per `interpreter.py`). Formalize the NSU
   counterexample (finding 2) and the side-conditioned NI theorem.
3. **Bridge lemma**: graph-labeled values ⇔ eager meet.
4. **Decidable instantiation**: finite readers (`Finset ⊕ Public`) `FlowsDec`
   instance + an executable end-to-end example (`#eval` an injection being
   blocked) to open the extraction path.
5. NORMAL-mode counterexample (no implicit-flow tainting of stored values).
