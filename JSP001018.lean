import JSP001018.Util
import JSP001018.Arith
import JSP001018.Family
import JSP001018.Sequence

/-!
# JSP-001018 — Erdős problem #1213

**Official problem statement** (`erdosproblems.com/#1213`; mirrored in
`papers/erdosproblem-db/all/1213.html`, and listed in the Justin Sun Prize
repository `TheJustinSunPrize/awards` as JSP-001018):

> Let `a, K ≥ 1`.  Does there exist `f(a,K)` such that, if
>
>     a = a₁ < a₂ < … < aₛ
>
> is a sequence of integers with `aₛ > f(a,K)` and with bounded gaps
> `a_{i+1} − a_i ≤ K`, then there are two **distinct** intervals `I` and `J`
> with `Σ_{i∈I} a_i = Σ_{j∈J} a_j` ?

Status upstream: `proved` (Hegyvári 1986), `formal_status = unformalized`,
`formalized = no` — i.e. solved mathematically but with **no Lean proof**.

We prove the affirmative answer with the completely explicit bound

    f(a,K) = a + K·X² ,     X = 2^J ,   J = 16K + 2 + 2a .

**Proof.**  Assume `aₛ > a + K·X²`.  From the gap bound, `a_i ≤ a + K·(i−1)`,
hence `s ≥ X²`.  Consider the family `Γ` of all pairs `(m, p)` (interval
*length* `m`, interval *start* `p`) with

    k < J,    m ∈ [2^k, 2^(k+1)),    p < 2^(2J−(k+1)) .

There are `J·2^(2J−1)` such pairs.  For each of them `m ≤ 2^(k+1)`,
`p ≤ 2^(2J−(k+1))` and the product of those two bounds is exactly `2^(2J) = X²`,
so `m + p ≤ X² ≤ s` (the interval fits) and

    Σ ≤ m·a + K·m·(p+m) ≤ X² + K·(X² + X²) ≤ 4·K·X² =: T .

Since `J > 8K` we have `|Γ| = J·2^(2J−1) > 8K·2^(2J−1) = 4K·2^(2J) = T`, so by the
pigeonhole principle two distinct members of `Γ` have the same sum.  Distinct
members of `Γ` are distinct pairs, hence distinct intervals.  ∎

Index convention: the sequence is `u : Nat → Nat` with `a_i = u (i−1)`, so
`a₁ = u 0` and `aₛ = u (s−1)`; an interval is `{p,…,p+n−1}` with `n ≥ 1`,
`p + n ≤ s`.  The witness is *not* weakened: the statement is an existential
over `f`, and we exhibit one.

No `sorry`, no `admit`, no new axioms.
-/

namespace JSP001018

open List

/-- Main theorem: Erdős problem #1213 (Justin Sun Prize, JSP-001018), affirmed. -/
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
        isum u p n = isum u p' n' := by
  classical
  let J := expJ a K
  let X := bigX a K
  let T := bigT a K
  refine ⟨a + K * X ^ 2, ?_⟩
  intro s u hs hu0 hinc hgap hbig
  have hJpos : 0 < J := by
    dsimp [J]
    exact expJ_pos a K
  have hXsq : X ^ 2 = 2 ^ (2 * J) := by
    dsimp [X, bigX]
    exact sq_two_pow J
  have hs_ge : 2 ^ (2 * J) ≤ s := by
    have hxl := length_lower (a := a) (K := K) (s := s) (X := X) (u := u)
      hK hs hu0 hinc hgap hbig
    omega
  let G := famList J
  have hGnodup : G.Nodup := by
    dsimp [G]
    exact nodup_famList J
  have hGlen : G.length = J * 2 ^ (2 * J - 1) := by
    dsimp [G]
    exact length_famList J
  have hTlt : T < G.length := by
    rw [hGlen]
    have hstep : 2 ^ (2 * J - 1) * 2 = 2 ^ (2 * J) := block_step J hJpos
    have hgt : 8 * K < J := by
      dsimp [J]
      exact expJ_gt_8K a K
    have hA : 0 < 2 ^ (2 * J - 1) := two_pow_pos _
    have hm : 8 * K * 2 ^ (2 * J - 1) < J * 2 ^ (2 * J - 1) :=
      Nat.mul_lt_mul_of_pos_right hgt hA
    calc
      T = 4 * K * X ^ 2 := by rfl
      _ = 4 * K * 2 ^ (2 * J) := by rw [hXsq]
      _ = 4 * K * (2 ^ (2 * J - 1) * 2) := by rw [hstep]
      _ = 4 * K * (2 * 2 ^ (2 * J - 1)) := by
            congr 1
            rw [Nat.mul_comm]
      _ = 8 * K * 2 ^ (2 * J - 1) := four_mul_two_fold K (2 ^ (2 * J - 1))
      _ < J * 2 ^ (2 * J - 1) := hm
  have hbounds : ∀ x ∈ G, 0 < isum u x.2 x.1 ∧ isum u x.2 x.1 ≤ T := by
    intro x hx
    rcases x with ⟨n, p⟩
    have hspec := famList_mem_spec hJpos (by simpa [G] using hx)
    have hpns : p + n ≤ s := by omega
    constructor
    · have hlast_lt : p + (n - 1) < s := by omega
      have hge := seq_ge_zero (s := s) (u := u) hinc (p + (n - 1)) hlast_lt
      have hupos : 0 < u (p + (n - 1)) := by omega
      exact isum_pos hspec.1 hupos
    · have hper : ∀ i, i < n → u (p + i) ≤ a + K * (p + n) := by
        intro i hi
        have hidx : p + i < s := by omega
        have ht := term_bound (a := a) (K := K) (s := s) (u := u)
          hu0 hinc hgap (p + i) hidx
        have hmono : a + K * (p + i) ≤ a + K * (p + n) := by
          have := Nat.mul_le_mul_left K (by omega : p + i ≤ p + n)
          omega
        omega
      have hle := isum_cap_le (u := u) (p := p) (n := n) (C := a + K * (p + n)) hper
      have hexp : n * (a + K * (p + n)) = n * a + K * (n * (p + n)) := by
        rw [Nat.mul_add]
        congr 1
        rw [← Nat.mul_assoc, Nat.mul_comm n K, Nat.mul_assoc]
      have hnX : n ≤ X := by
        dsimp [X, bigX]
        exact hspec.2.1
      have haX : a ≤ X := a_le_bigX (a := a) (K := K)
      have hXX : X ^ 2 = 2 ^ (2 * J) := hXsq
      have hnp : n * p ≤ 2 ^ (2 * J) := hspec.2.2.1
      have hwb := weight_bound (n := n) (p := p) (a := a) (K := K)
        (X := X) (P := 2 ^ (2 * J)) hnX haX hnp hXX
      have hcb := combine_bound K (2 ^ (2 * J)) hK
      calc
        isum u p n ≤ n * (a + K * (p + n)) := hle
        _ = n * a + K * (n * (p + n)) := hexp
        _ ≤ 2 ^ (2 * J) + K * (2 ^ (2 * J) + 2 ^ (2 * J)) := hwb
        _ ≤ 4 * K * 2 ^ (2 * J) := hcb
        _ = T := by
              rw [← hXsq]
              rfl
  have hnotinj : ¬ (∀ x ∈ G, ∀ y ∈ G, isum u x.2 x.1 = isum u y.2 y.1 → x = y) := by
    intro hinj
    let img := G.map fun x => isum u x.2 x.1 - 1
    have hnd : img.Nodup := ListUtil.nodup_map_of_inj (by simpa [img] using hGnodup) (by
      intro x hx y hy heq
      apply hinj x hx y hy
      have hx1 := (hbounds x hx).1
      have hy1 := (hbounds y hy).1
      omega)
    have hbd : ∀ v ∈ img, v < T := by
      intro v hv
      rcases (List.mem_map.mp hv) with ⟨x, hx, hvx⟩
      have hx1 := (hbounds x hx).1
      have hx2 := (hbounds x hx).2
      omega
    have hle := ListUtil.bounded_nodup_length_le T img hnd hbd
    have hlen_img : img.length = G.length := by
      dsimp [img]
      simp
    omega
  have hcollision :
      ∃ x, x ∈ G ∧ ∃ y, y ∈ G ∧ isum u x.2 x.1 = isum u y.2 y.1 ∧ x ≠ y := by
    apply Classical.byContradiction
    intro hnone
    apply hnotinj
    intro x hx y hy hsum
    apply Classical.byContradiction
    intro hxy
    apply hnone
    exact ⟨x, hx, y, hy, hsum, hxy⟩
  rcases hcollision with ⟨x, hxG, y, hyG, hsums, hxyne⟩
  rcases x with ⟨n, p⟩
  rcases y with ⟨n', p'⟩
  have hxspec := famList_mem_spec hJpos (by simpa [G] using hxG)
  have hyspec := famList_mem_spec hJpos (by simpa [G] using hyG)
  refine ⟨p, n, p', n', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hxspec.1
  · exact hyspec.1
  · omega
  · omega
  · by_cases hp : p = p'
    · right
      intro hn
      exact hxyne (by simp [hp, hn])
    · left
      exact hp
  · exact hsums

/--
Non-vacuity: the hypotheses of `erdos_1213` are satisfiable, so the theorem really
produces a collision.  Take `a = K = 1` and the arithmetic progression `u i = i+1`
(gaps exactly 1), of length `s = f(1,1) + 2`, so `u (s-1) = s = f(1,1)+2 > f(1,1)`.
-/
theorem erdos_1213_nonvacuous :
    ∃ s : Nat, ∃ p n p' n' : Nat,
      0 < n ∧ 0 < n' ∧
      p + n ≤ s ∧ p' + n' ≤ s ∧
      (p ≠ p' ∨ n ≠ n') ∧
      isum (fun i => i + 1) p n = isum (fun i => i + 1) p' n' := by
  rcases erdos_1213 1 1 (by omega) (by omega) with ⟨F, hF⟩
  let s := F + 2
  refine ⟨s, ?_⟩
  apply hF s (fun i => i + 1)
  · dsimp [s]
    omega
  · simp
  · intro i hi
    omega
  · intro i hi
    omega
  · dsimp [s]
    omega

end JSP001018
