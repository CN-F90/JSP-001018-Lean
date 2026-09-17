import Std
import JSP001018.Arith
import JSP001018.Util

/-!
# JSP-001018 (= Erdős problem #1213) — module `Family`

The pigeonhole family: all pairs `(m, p)` where `m` is the interval **length** and
`p` its **start**, stratified into dyadic blocks

    block k :  m ∈ [2^k, 2^(k+1)) ,  p < 2^(2J-(k+1)) ,   k = 0,…,J-1 .

Crucially each block satisfies `m ≤ 2^(k+1)`, `p ≤ 2^(2J-(k+1))` and the product of those
two bounds is exactly `2^(2J) = X²`, so *every* member of the family has both
`m + p ≤ X²` (so the interval fits inside the sequence) and `m·p ≤ X²`
(so its sum is small).  Each block has exactly `2^(2J-1)` elements and there are `J`
blocks, giving `|Γ| = J·2^(2J-1)`.

No `sorry`, no `admit`, no new axioms.
-/

namespace JSP001018

/-- number of admissible start positions in dyadic block `k`. -/
def blockStarts (J k : Nat) : Nat := 2 ^ (2 * J - (k + 1))

/-- the block of the family belonging to dyadic level `k`. -/
def blockList (J k : Nat) : List (Nat × Nat) :=
  (List.range (2 ^ k)).flatMap fun j =>
    (List.range (blockStarts J k)).map fun p => (2 ^ k + j, p)

/-- the full family of candidate intervals. -/
def famList (J : Nat) : List (Nat × Nat) :=
  (List.range J).flatMap fun k => blockList J k

-- ------------------------------------------------------------------- structure

/-- Membership in a block pins the length into `[2^k, 2^(k+1))` and bounds the start. -/
theorem mem_blockList_bounds {J k len st : Nat}
    (h : (len, st) ∈ blockList J k) :
    2 ^ k ≤ len ∧ len < 2 ^ (k + 1) ∧ st < blockStarts J k := by
  unfold blockList at h
  rw [List.mem_flatMap] at h
  rcases h with ⟨j, hj, hx⟩
  rw [List.mem_map] at hx
  rcases hx with ⟨p, hp, hpx⟩
  have hjlt : j < 2 ^ k := List.mem_range.mp hj
  have hplt : p < blockStarts J k := List.mem_range.mp hp
  have hlen : len = 2 ^ k + j := (congrArg Prod.fst hpx).symm
  have hst : st = p := (congrArg Prod.snd hpx).symm
  subst len
  subst st
  exact ⟨by omega, dyadic_upper hjlt, hplt⟩

theorem nodup_blockList (J k : Nat) : (blockList J k).Nodup := by
  unfold blockList
  apply ListUtil.nodup_flatMap_of_disjoint
  · exact List.nodup_range
  · intro j hj
    apply ListUtil.nodup_map_of_inj
    · exact List.nodup_range
    · intro p hp p' hp' heq
      exact congrArg Prod.snd heq
  · intro j hj j' hj' hne x hx
    intro hx'
    rcases (List.mem_map.mp hx) with ⟨p, hp, hpx⟩
    rcases (List.mem_map.mp hx') with ⟨p', hp', hpx'⟩
    have hfst : 2 ^ k + j = 2 ^ k + j' := by
      calc
        2 ^ k + j = Prod.fst (2 ^ k + j, p) := rfl
        _ = Prod.fst x := congrArg Prod.fst hpx
        _ = Prod.fst (2 ^ k + j', p') := (congrArg Prod.fst hpx').symm
        _ = 2 ^ k + j' := rfl
    omega

theorem nodup_famList (J : Nat) : (famList J).Nodup := by
  unfold famList
  apply ListUtil.nodup_flatMap_of_disjoint
  · exact List.nodup_range
  · intro k hk
    exact nodup_blockList J k
  · intro k hk k' hk' hne x hx
    intro hx'
    rcases x with ⟨len, st⟩
    have hb := mem_blockList_bounds hx
    have hb' := mem_blockList_bounds hx'
    have hklt : k < J := List.mem_range.mp hk
    have hklt' : k' < J := List.mem_range.mp hk'
    by_cases hle : k ≤ k'
    · have hlt : k < k' := by omega
      have hs : k + 1 ≤ k' := by omega
      have hpow : 2 ^ (k + 1) ≤ 2 ^ k' := two_pow_mono hs
      omega
    · have hlt : k' < k := by omega
      have hs : k' + 1 ≤ k := by omega
      have hpow : 2 ^ (k' + 1) ≤ 2 ^ k := two_pow_mono hs
      omega

-- ---------------------------------------------------------------------- counting

/-- `2^k · 2^(2J-(k+1)) = 2^(2J-1)` for `k < J`. -/
theorem block_card (J k : Nat) (hk : k < J) :
    2 ^ k * 2 ^ (2 * J - (k + 1)) = 2 ^ (2 * J - 1) := by
  rw [← Nat.pow_add]
  congr 1
  omega

theorem length_blockList (J k : Nat) (hk : k < J) :
    (blockList J k).length = 2 ^ (2 * J - 1) := by
  unfold blockList blockStarts
  have hconst :
      ((List.range (2 ^ k)).flatMap fun j =>
        (List.range (2 ^ (2 * J - (k + 1)))).map fun p => (2 ^ k + j, p)).length
        = (List.range (2 ^ k)).length * 2 ^ (2 * J - (k + 1)) := by
    apply ListUtil.length_flatMap_of_const_len
    · exact List.nodup_range
    · intro j hj
      simp
  rw [hconst, List.length_range, block_card J k hk]

theorem length_famList (J : Nat) : (famList J).length = J * 2 ^ (2 * J - 1) := by
  unfold famList
  have h := ListUtil.length_flatMap_of_const_len (2 ^ (2 * J - 1))
      (l := List.range J) (f := fun k => blockList J k) List.nodup_range
      (by
        intro k hk
        exact length_blockList J k (List.mem_range.mp hk))
  simpa [List.length_range] using h

-- ------------------------------------------------------- per-member size estimates

/-- Every member of the family is legal and small, given `s ≥ X²`. -/
theorem famList_mem_spec {J len st : Nat} (hJ : 0 < J)
    (h : (len, st) ∈ famList J) :
    0 < len ∧ len ≤ 2 ^ J ∧
    len * st ≤ 2 ^ (2 * J) ∧ len + st ≤ 2 ^ (2 * J) := by
  unfold famList at h
  rw [List.mem_flatMap] at h
  rcases h with ⟨k, hk, hx⟩
  have hklt : k < J := List.mem_range.mp hk
  have hb := mem_blockList_bounds hx
  have hlen_upto : len ≤ 2 ^ (k + 1) := Nat.le_of_lt hb.2.1
  have hA : 2 ≤ 2 ^ (k + 1) := by
    have := two_pow_mono (i := 1) (j := k + 1) (by omega)
    omega
  have hexpB : 1 ≤ 2 * J - (k + 1) := by omega
  have hB : 2 ≤ blockStarts J k := by
    dsimp [blockStarts]
    have := two_pow_mono (i := 1) (j := 2 * J - (k + 1)) hexpB
    omega
  have hprod : 2 ^ (k + 1) * blockStarts J k = 2 ^ (2 * J) := by
    dsimp [blockStarts]
    exact block_prod J k hklt
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hb.1
    omega
  · have hpow : 2 ^ (k + 1) ≤ 2 ^ J := two_pow_mono (by omega : k + 1 ≤ J)
    omega
  · exact mul_le_of_le_factors hlen_upto (Nat.le_of_lt hb.2.2) hprod
  · exact add_le_of_le_factors hlen_upto (Nat.le_of_lt hb.2.2) hA hB hprod

end JSP001018
