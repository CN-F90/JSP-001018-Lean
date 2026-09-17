# Statement correspondence — JSP-001018 / Erdős problem #1213

This document records, item by item, how the Lean statement
`JSP001018.erdos_1213` corresponds to the original problem. It is intended to
let a reviewer check the **full theorem scope** without reading the proof.

---

## 1. Original statement (verbatim)

From the Erdős Problems database, problem #1213
(<https://www.erdosproblems.com/1213>); the Justin Sun Prize bank lists the same
problem as **JSP-001018**:

> PROVED. This has been solved in the affirmative. Let $a,K\geq 1$. Does there
> exist $f(a,K)$ such that if
> $$a=a_1<\cdots<a_s$$
> is a sequence of integers with $a_s> f(a,K)$ and with bounded gaps
> $a_{i+1}-a_i\leq K$ then there are two distinct intervals $I$ and $J$ such that
> $$\sum_{i\in I}a_i=\sum_{j\in J}a_j\;?$$

---

## 2. Lean statement (verbatim)

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

with

```lean
def expJ  (a K : Nat) : Nat := 16 * K + 2 + 2 * a
def bigX  (a K : Nat) : Nat := 2 ^ expJ a K
def bigT  (a K : Nat) : Nat := 4 * K * (bigX a K) ^ 2

def isum (u : Nat → Nat) (p : Nat) : Nat → Nat
  | 0          => 0
  | Nat.succ n => isum u p n + u (p + n)
```

The theorem is proved with the explicit witness `F := a + K * X ^ 2`, i.e.
`f(a,K) = a + K·X²` with `X = 2^J`, `J = 16K + 2 + 2a`.

---

## 3. Field-by-field correspondence

| # | Original | Lean | notes |
|---|---|---|---|
| 1 | `a ≥ 1` | `(ha : 0 < a)` with `a : Nat` | exact |
| 2 | `K ≥ 1` | `(hK : 0 < K)` with `K : Nat` | exact |
| 3 | "there exists `f(a,K)`" | `∃ F : Nat` | `F` is produced from `a` and `K`, i.e. a genuine **explicit** witness, not a hypothesis |
| 4 | `a = a₁ < ⋯ < a_s` | `0 < s`, `u 0 = a`, `∀ i, i+1 < s → u i < u (i+1)` | `a_i = u (i−1)`; `u 0 = a` is `a₁ = a`; strict increase is `a_i < a_{i+1}` for all `i ≤ s−2` |
| 5 | bounded gaps `a_{i+1} − a_i ≤ K` | `∀ i, i+1 < s → u (i+1) − u i ≤ K` | exactly the `s−1` gaps `a₂−a₁, …, a_s−a_{s−1}` |
| 6 | `a_s > f(a,K)` | `F < u (s − 1)` | `u (s−1)` is `a_s` because `0 < s` |
| 7 | "two distinct intervals `I`, `J`" | `∃ p n p' n', 0 < n ∧ 0 < n' ∧ (p ≠ p' ∨ n ≠ n')` | see §4 |
| 8 | intervals lie in the sequence | `p + n ≤ s ∧ p' + n' ≤ s` | see §4 |
| 9 | `∑_{i∈I} a_i = ∑_{j∈J} a_j` | `isum u p n = isum u p' n'` | see §4 |
| 10 | — | `0 < n ∧ 0 < n'` (non-empty) | see §5 |
| 11 | additional assumptions | none | no extra hypothesis, no `sorry`, no new `axiom` |

---

## 4. Intervals, indices and distinctness

An interval is a **non-empty consecutive block of indices**
`{p, …, p+n−1}` with `n ≥ 1` and `p + n ≤ s`; its sum is
`isum u p n = u p + u (p+1) + ⋯ + u (p+n−1)`. This is the reading of
"intervals `I`, `J`" that makes the problem non-trivial (see §5).

Two intervals are the *same* interval precisely when they have the same start
`p` and the same length `n` (both being consecutive blocks of `ℕ`). Hence

```
(p ≠ p' ∨ n ≠ n')   ⇔   the intervals {p,…,p+n−1} and {p',…,p'+n'−1} are distinct
```

is an exact rendering of "two **distinct** intervals".

The formalization does **not** require `I` and `J` to be disjoint, and does not
require them to be ordered — matching the original statement, which allows the
two intervals to overlap.

---

## 5. Domain: `ℕ` versus `ℤ` (no loss of generality)

The original speaks of a "sequence of **integers**"; the formalization uses
`u : Nat → Nat`. This is not a weakening — the two statements are equivalent.

* **(ℤ ⟹ ℕ)** Immediate: every `ℕ`-valued sequence is an integer sequence.
* **(ℕ ⟹ ℤ)** Let `b₁ < ⋯ < b_s` be any integer sequence with
  `b₁ = a ≥ 1` and gaps `≤ K`. Since the sequence is strictly increasing from
  `b₁ = a ≥ 1`, every term satisfies `b_i ≥ 1`, so every `b_i` is a positive
  integer. Taking `u i := (b_{i+1}).toNat : Nat` gives a `ℕ`-valued sequence
  `u` with `u 0 = a`, the same strict increase, the same gaps and the same last
  term. The `ℕ`-version then yields a collision, which is a collision for `b`.

Hence the same `f` works in both settings, and a proof for `ℕ` proves the
original `ℤ` statement in full.

**Why non-emptiness is required.** If empty intervals were admitted, taking
`I = J = ∅` would give `0 = 0` and the conclusion would hold trivially for every
sequence, making the problem vacuous. The formalization therefore states
`0 < n ∧ 0 < n'` explicitly; this is the intended meaning of "interval with a
sum" and is what makes the theorem substantive.

**The case `s = 1`.** With `s = 1` the last term is `a₁ = a`, and the hypothesis
`F < u (s−1)` reads `F < a`, which is impossible for the witness
`F = a + K·X² ≥ a`. So `s = 1` is vacuous, exactly as in the informal reading
where `a_s > f(a,K)` cannot hold for a one-term sequence.

---

## 6. What is *not* claimed

* **No optimality.** The witness `f(a,K) = a + K·2^{2J}`, `J = 16K + 2 + 2a`, is
  explicit and elementary, but the formalization makes no claim that it is
  sharp or asymptotically best possible. Hegyvári's own remark that the
  exponential dependence on `K` "is not best possible" is **not** addressed
  here. The original problem asks only for the existence of some `f`.
* **No priority claim.** The mathematics is due to Hegyvári (1986). See
  `README.md` §6.
* **No `special case` substitution.** The theorem is not restricted to
  particular `a`, `K`, particular gap patterns, or particular sequence lengths.

---

## 7. Non-vacuity witness

To rule out a vacuously true theorem, the repository also proves

```lean
theorem erdos_1213_nonvacuous :
    ∃ s : Nat, ∃ p n p' n' : Nat,
      0 < n ∧ 0 < n' ∧
      p + n ≤ s ∧ p' + n' ≤ s ∧
      (p ≠ p' ∨ n ≠ n') ∧
      isum (fun i => i + 1) p n = isum (fun i => i + 1) p' n'
```

which instantiates the main theorem at `a = K = 1` with the arithmetic
progression `u i = i + 1` (gaps exactly `1`) and length `s = f(1,1) + 2`. This
shows that the hypotheses of `erdos_1213` are satisfiable and that the conclusion
is realised by a concrete, verifiable input.
