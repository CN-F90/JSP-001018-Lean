# Verification record — JSP-001018

All evidence below is reproducible from this repository. The authoritative,
externally checkable record is the CI run linked in the pull request; build logs
for each run are attached to the corresponding GitHub Actions run.

---

## 1. Environment

| item | value |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.34.0` (pinned in `lean-toolchain`) |
| mathlib | `v4.34.0`, pinned to commit `5ed2965256430c3649e86755f9576b54eca72435` |
| Project | `name = "JSP001018"`, library `JSP001018` |
| Build targets | `JSP001018`, `JSP001018.Axioms` (both in `defaultTargets`) |

The mathlib revision is pinned to the exact v4.34.0 release commit (not a
floating branch), so the build is bit-reproducible and the referenced proof can
never silently change.

---

## 2. Build

```bash
lake update
lake exe cache get            # optional, usually unnecessary
lake build JSP001018 JSP001018.Axioms
```

Result: `Build completed successfully` — all six modules compile:

```
JSP001018.Util
JSP001018.Arith
JSP001018.Family
JSP001018.Sequence
JSP001018          ← main theorem `erdos_1213`
JSP001018.Axioms   ← axiom audit
```

---

## 3. Axiom audit

`JSP001018/Axioms.lean` is a build target, so the audit is executed on **every**
build and its output is part of the CI log. The command

```bash
lake env lean JSP001018/Axioms.lean
```

prints:

```
'JSP001018.erdos_1213' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP001018.erdos_1213_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'ListUtil.bounded_nodup_length_le' depends on axioms: [propext, Quot.sound]
'JSP001018.length_famList' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP001018.nodup_famList' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP001018.famList_mem_spec' depends on axioms: [propext, Quot.sound]
'JSP001018.length_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP001018.isum_cap_le' depends on axioms: [propext, Quot.sound]
'JSP001018.weight_bound' depends on axioms: [propext, Quot.sound]
```

**Interpretation.** Every declaration depends only on `propext`, `Classical.choice`
and `Quot.sound` — Lean's standard foundations, which are shipped with the kernel
and are unavoidable for classical reasoning. In particular:

* **no user-introduced `axiom`** appears anywhere in the dependency set;
* `Classical.choice` is introduced solely by the `classical` block in
  `JSP001018.lean` (used for the contrapositive/pigeonhole extraction) and would
  be avoided only by a constructive rewriting of that step;
* `propext` and `Quot.sound` are the ordinary logical/quotient axioms.

The audit covers the main theorem, the non-vacuity witness, and seven supporting
declarations, i.e. the whole proof spine rather than only the top-level name.

---

## 4. Absence of placeholders

```bash
grep -rnE 'sorry|admit' --include='*.lean' JSP001018.lean JSP001018/
grep -rnE '^[[:space:]]*(axiom|unsafe)\b' --include='*.lean' JSP001018.lean JSP001018/
```

Both commands produce **no output**. This is additionally enforced by CI
(`.github/workflows/build.yml`, step *"Reject forbidden placeholders"*), which
fails the build if any of `sorry`, `admit`, `axiom` or `unsafe` is introduced.

Consequently the proof contains:

* no `sorry`
* no `admit`
* no new/unproved `axiom`
* no `unsafe` escape hatch

---

## 5. Statement scope

See [`STATEMENT.md`](STATEMENT.md) for the complete item-by-item correspondence.
In summary, the formalized statement is the **full original problem**:

| criterion | status |
|---|---|
| Full original statement (existence of `f(a,K)`) | ✔ proved for all `a ≥ 1`, all `K ≥ 1` |
| Not a special case | ✔ no restriction on `a`, `K`, gaps or length |
| No weakened quantifiers | ✔ `∀` over sequences/lengths preserved; `∃` in `f` realised by an explicit witness |
| No extra unproved hypotheses | ✔ only `0 < a`, `0 < K` — the same as the original |
| No `scoped`/partial component presented as complete | ✔ single theorem covering the whole problem |
| Non-vacuity | ✔ `erdos_1213_nonvacuous` gives a concrete input |

---

## 6. Cross-checks performed

1. **Clean rebuild.** The proof was rebuilt from an empty `.lake` directory
   (no incremental state) and completed successfully.
2. **Independent arithmetic cross-check.** The combinatorial core was
   independently re-checked numerically outside Lean: `blockList` produces no
   duplicates, `|Γ| = J·2^(2J−1)` holds, and the inequalities `m + p ≤ 2^(2J)`,
   `m·p ≤ 2^(2J)`, `J > 8K` hold for the parameter ranges used.
3. **Non-vacuity.** A concrete satisfying input is exhibited and proved.

---

## 7. Known limitations (stated honestly)

* The explicit witness `f(a,K) = a + K·2^{2J}` with `J = 16K + 2 + 2a` is
  **not optimal**, and no optimality or sharpness statement is made or proved.
  The original problem asks only for existence of some `f`.
* The result depends on classical logic (`Classical.choice`); a fully
  constructive version is not provided.
* The formalization is of the **affirmative answer to the problem**, not of
  Hegyvári's particular paper or of his specific bound.
