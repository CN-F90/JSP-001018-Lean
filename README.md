# JSP-001018 — Erdős problem #1213

**A complete, kernel-verified Lean 4 formalization of the affirmative answer to
Erdős problem #1213 (Justin Sun Prize entry JSP-001018).**

- Top-level theorem: **`JSP001018.erdos_1213`**
- Main source file: **`JSP001018.lean`**
- Toolchain: **Lean `v4.34.0`** + **mathlib `v4.34.0`** (pinned to commit `5ed2965256430c3649e86755f9576b54eca72435`)
- No `sorry`, no `admit`, no `unsafe`, no user-introduced `axiom`
- Axiom audit: `[propext, Classical.choice, Quot.sound]` — Lean's standard foundations only
- CI: see the badge above / `.github/workflows/build.yml`

---

## 1. The original problem

Erdős problem #1213, as stated at <https://www.erdosproblems.com/1213>:

> Let $a,K\geq 1$. Does there exist $f(a,K)$ such that if
> $$a=a_1<\cdots<a_s$$
> is a sequence of integers with $a_s > f(a,K)$ and with bounded gaps
> $a_{i+1}-a_i\leq K$ then there are two distinct intervals $I$ and $J$ such that
> $$\sum_{i\in I}a_i=\sum_{j\in J}a_j\;?$$

Upstream status: **proved in the affirmative**. The problem page records that

> [He86] has proved the answer is yes, and gives an explicit bound of the shape
> $f(a,K) \ll a e^{O(K)}$. Hegyvári believes that the exponential dependence on
> $K$ here is not best possible.

The corresponding Justin Sun Prize entry is **JSP-001018**, catalogued in
`TheJustinSunPrize/awards` → `problems/catalog-1001-1022.md`, which lists it as
*Current status: Solved*, *Lean proof: No*.

---

## 2. What is formalized

The formalization proves the **full original statement** — the existence of a
threshold $f(a,K)$ — by exhibiting one explicitly. The witness produced is

$$f(a,K) = a + K\cdot X^2,\qquad X = 2^{J},\qquad J = 16K + 2 + 2a .$$

```lean
theorem erdos_1213 (a K : Nat) (ha : 0 < a) (hK : 0 < K) :
    ∃ F : Nat, ∀ (s : Nat) (u : Nat → Nat),
      0 < s →
      u 0 = a →
      (∀ i, i + 1 < s → u i < u (i + 1)) →
      (∀ i, i + 1 < s → u (i + 1) - u i ≤ K) →
      F < u (s - 1) →
      ∃ p n p' n' : Nat,
        0 < n ∧ 0 < n' ∧
        p + n ≤ s ∧ p' + n' ≤ s ∧
        (p ≠ p' ∨ n ≠ n') ∧
        isum u p n = isum u p' n'
```

**Index convention.** A sequence $a_1<\cdots<a_s$ is encoded as `u : Nat → Nat`
with $a_i = $ `u (i-1)`, so `u 0 = a` is $a_1=a$ and `u (s-1)` is $a_s$. An
interval is a non-empty consecutive block $\{p,\dots,p+n-1\}$ with `p + n ≤ s`,
and `isum u p n` is its sum.

### Scope

The formalization resolves the **whole** problem, not a special case:

| | |
|---|---|
| Quantifiers | Universal in the sequence `u`, the length `s` and the last term; existential in `F` |
| Cases | All `a ≥ 1` and all `K ≥ 1` |
| Conclusion | Two **distinct** non-empty intervals with **exactly equal** sums |
| Extra hypotheses | None — no additional unproved assumptions are introduced |
| Weakening | None — not a special case, not a bounded/conditional variant |

A detailed statement-by-statement correspondence, including the (harmless)
`Nat`-vs-`Int` domain choice, is in **[`STATEMENT.md`](STATEMENT.md)**.

> **On the explicit bound.** The witness `f(a,K) = a + K·2^{2J}`,
> `J = 16K + 2 + 2a`, is *explicit and elementary* but deliberately **not
> claimed to be optimal**; the formalization makes no sharpness assertion. The
> original problem only asks for existence of some `f`.

### Non-vacuity

`JSP001018.erdos_1213_nonvacuous` exhibits a concrete input satisfying every
hypothesis (`a = K = 1`, `u i = i + 1`, length `f(1,1) + 2`), so the theorem is
not vacuously true.

### Proof outline

1. **Term bound.** `a_{i+1} ≤ a_i + K` and `a₁ = a` give `a_i ≤ a + K·(i−1)`.
2. **Length.** `aₛ > a + K·X²` combined with (1) forces `s ≥ X² = 2^(2J)`.
3. **The dyadic family Γ.** For `k < J`, let
   `Γ_k = { (m, p) : m ∈ [2^k, 2^(k+1)), p < 2^(2J−(k+1)) }` and `Γ = ⋃_{k<J} Γ_k`.
   With `A = 2^(k+1)`, `B = 2^(2J−(k+1))` one has `A·B = 2^(2J) = X²` exactly, so
   for every member `(m,p)`: `m·p ≤ X²`, `m + p ≤ A + B ≤ A·B = X² ≤ s` (the
   interval fits inside the sequence), and its sum is at most
   `m·a + K·m·(p+m) ≤ X² + K·(X² + X²) ≤ 4K·X² =: T`.
4. **Counting.** `|Γ_k| = 2^k · 2^(2J−(k+1)) = 2^(2J−1)`, hence `|Γ| = J·2^(2J−1)`.
   Since `J = 16K + 2 + 2a > 8K`, we get `T = 4K·2^(2J) = 8K·2^(2J−1) < J·2^(2J−1) = |Γ|`.
5. **Pigeonhole.** All `|Γ|` sums lie in `[1, T]` and `|Γ| > T`, so two distinct
   members of `Γ` — i.e. two distinct intervals — share the same sum. ∎

Everything is elementary: no analysis, no probability, no logarithms, no floors.

---

## 3. Repository layout

| file | content |
|---|---|
| `JSP001018.lean` | **the main theorem `erdos_1213`** + non-vacuity theorem |
| `JSP001018/Util.lean` | finite-block machinery on `List` + the pigeonhole principle |
| `JSP001018/Arith.lean` | powers of two, dyadic product identities, `weight_bound`, `combine_bound`, parameters `expJ` / `bigX` / `bigT` |
| `JSP001018/Family.lean` | the dyadic family: `blockList`, `famList`, `Nodup`, cardinality `J·2^(2J−1)`, per-member size specification |
| `JSP001018/Sequence.lean` | `isum`, `term_bound`, `length_lower`, `isum_cap_le`, `isum_pos` |
| `JSP001018/Axioms.lean` | `#print axioms` audit |
| `STATEMENT.md` | statement-by-statement correspondence with the original problem |
| `VERIFICATION.md` | build evidence and verification record |
| `.github/workflows/build.yml` | reproducible remote build (CI) |
| `lakefile.toml`, `lean-toolchain` | pinned toolchain and mathlib commit |

Total: 871 lines of Lean across 6 files.

---

## 4. How to reproduce

### Prerequisites

[`elan`](https://github.com/leanprover/elan) (the Lean toolchain manager). The
toolchain `leanprover/lean4:v4.34.0` is read from `lean-toolchain` and installed
automatically.

### Build

```bash
git clone https://github.com/CN-F90/JSP-001018-Lean.git
cd JSP-001018-Lean
lake update                       # fetches mathlib v4.34.0 at the pinned commit
lake exe cache get                # optional: precompiled mathlib oleans
lake build JSP001018 JSP001018.Axioms
```

A successful build ends with the `JSP001018` and `JSP001018.Axioms` targets
(`Build completed successfully`). To confirm there is no `sorry`:

```bash
grep -rnE 'sorry|admit|^[[:space:]]*(axiom|unsafe)\b' JSP001018.lean JSP001018/
# (no output expected)
```

### Axiom audit

```bash
lake env lean JSP001018/Axioms.lean
```

Expected output (Lean's standard foundations only — no user-added axiom):

```
'JSP001018.erdos_1213' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Classical.choice` is introduced solely by the `classical` block / pigeonhole
extraction in the main proof; `propext` and `Quot.sound` are the usual
foundational axioms. The audit is re-run on every CI build and its output is
part of the build log.

### Continuous integration

`.github/workflows/build.yml` performs the full sequence on a clean runner:
install `elan` → `lake update` → `lake exe cache get` → `lake build` →
`#print axioms` → placeholder scan (`sorry`/`admit`/`axiom`/`unsafe`) → olean
existence check. Any failure fails the build.

---

## 5. Verification evidence

| item | result |
|---|---|
| Clean `lake build` | success, all 6 modules built |
| Lean / mathlib | `v4.34.0` / `v4.34.0` (`5ed2965256430c3649e86755f9576b54eca72435`) |
| `sorry` / `admit` | none (CI-enforced by grep) |
| New `axiom` / `unsafe` | none (CI-enforced by grep) |
| `#print axioms JSP001018.erdos_1213` | `[propext, Classical.choice, Quot.sound]` |
| Statement scope | full original problem (see `STATEMENT.md`) |
| Non-vacuity | `erdos_1213_nonvacuous` provides a concrete witness input |

Details, including the raw log excerpts, are collected in
**[`VERIFICATION.md`](VERIFICATION.md)**.

---

## 6. Attribution and scope of the claim

**Mathematical result.** The mathematical theorem is due to
**N. Hegyvári**, *On consecutive sums in sequences*, Acta Mathematica
Hungarica (1986), 193–200 [He86] — as recorded on the Erdős Problems page for
#1213. The mathematics of this problem is **not** original to this repository.

**This repository claims only the Lean formalization contribution.** It provides
a complete, machine-checked Lean 4 proof of the original statement together with
its reproducible build environment. It makes **no** claim of mathematical
discovery, priority, or first formalization.

**Formalization.** Prepared by the repository owner
([@CN-F90](https://github.com/CN-F90)) with AI-assisted development.

### References

- [He86] N. Hegyvári, *On consecutive sums in sequences*, Acta Math. Hungar.
  (1986), 193–200.
- Erdős Problems #1213 — T. F. Bloom, <https://www.erdosproblems.com/1213>.
- Justin Sun Prize problem bank — `TheJustinSunPrize/awards`,
  `problems/catalog-1001-1022.md` (entry JSP-001018).
