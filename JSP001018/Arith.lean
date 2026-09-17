import Std

/-!
# JSP-001018 (= Erdős problem #1213) — module `Arith`

Explicit elementary arithmetic used by the main proof: powers of two,
product bounds, and the parameters `J`, `X`, `T`.

No `sorry`, no `admit`, no new axioms.
-/

namespace JSP001018

-- ------------------------------------------------------------------ powers of two

theorem two_pow_pos (n : Nat) : 0 < 2 ^ n := Nat.two_pow_pos n

theorem two_pow_mono {i j : Nat} (h : i ≤ j) : 2 ^ i ≤ 2 ^ j :=
  Nat.pow_le_pow_right (by omega : 2 > 0) h

theorem two_pow_succ' (n : Nat) : 2 ^ Nat.succ n = 2 ^ n + 2 ^ n := by
  rw [Nat.pow_succ, Nat.mul_two]

theorem two_pow_succ_eq (n : Nat) : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
  simpa [Nat.succ_eq_add_one] using two_pow_succ' n

/-- If `j < 2^k` then `2^k + j < 2^(k+1)` (the dyadic block really lies below `2^(k+1)`). -/
theorem dyadic_upper {k j : Nat} (hj : j < 2 ^ k) : 2 ^ k + j < 2 ^ (k + 1) := by
  rw [two_pow_succ_eq k]
  omega

/-- Product of the two dyadic blocks: `2^(k+1) * 2^(2J-(k+1)) = 2^(2J)`. -/
theorem block_prod (J k : Nat) (hk : k < J) :
    2 ^ (k + 1) * 2 ^ (2 * J - (k + 1)) = 2 ^ (2 * J) := by
  have hle : k + 1 ≤ 2 * J := by omega
  have h := Nat.pow_sub_mul_pow (a := 2) (m := k + 1) (n := 2 * J) hle
  calc
    2 ^ (k + 1) * 2 ^ (2 * J - (k + 1))
        = 2 ^ (2 * J - (k + 1)) * 2 ^ (k + 1) := Nat.mul_comm _ _
    _ = 2 ^ (2 * J) := h

/-- One step down from `2^(2J)`: `2^(2J-1) * 2 = 2^(2J)`. -/
theorem block_step (J : Nat) (hJ : 0 < J) :
    2 ^ (2 * J - 1) * 2 = 2 ^ (2 * J) := by
  have hle : 2 * J - 1 ≤ 2 * J := by omega
  have h := Nat.pow_sub_mul_pow (a := 2) (m := 2 * J - 1) (n := 2 * J) hle
  have hsub : 2 * J - (2 * J - 1) = 1 := by omega
  calc
    2 ^ (2 * J - 1) * 2
        = 2 * 2 ^ (2 * J - 1) := Nat.mul_comm _ _
    _ = 2 ^ (2 * J - (2 * J - 1)) * 2 ^ (2 * J - 1) := by rw [hsub, Nat.pow_one]
    _ = 2 ^ (2 * J) := h

/-- `(2^J)^2 = 2^(2J)`. -/
theorem sq_two_pow (J : Nat) : (2 ^ J) ^ 2 = 2 ^ (2 * J) := by
  rw [← Nat.pow_mul]
  congr 1
  omega

-- --------------------------------------------------------------- small inequalities

/-- For naturals at least 2, `A + B ≤ A * B`. -/
theorem add_le_mul_of_two_le (A B : Nat) (hA : 2 ≤ A) (hB : 2 ≤ B) : A + B ≤ A * B := by
  by_cases hAB : A ≤ B
  · have h1 : 2 * B ≤ A * B := Nat.mul_le_mul_right B hA
    omega
  · have hBA : B ≤ A := by omega
    have h1 : 2 * A ≤ B * A := Nat.mul_le_mul_right A hB
    rw [Nat.mul_comm B A] at h1
    omega

/-- Transfer additive bounds through two factors whose product is `P`. -/
theorem add_le_of_le_factors {len st A B P : Nat}
    (hlen : len ≤ A) (hst : st ≤ B) (hA : 2 ≤ A) (hB : 2 ≤ B) (hprod : A * B = P) :
    len + st ≤ P := by
  have h1 : len + st ≤ A + B := Nat.add_le_add hlen hst
  have h2 : A + B ≤ A * B := add_le_mul_of_two_le A B hA hB
  omega

/-- Transfer multiplicative bounds through two factors whose product is `P`. -/
theorem mul_le_of_le_factors {len st A B P : Nat}
    (hlen : len ≤ A) (hst : st ≤ B) (hprod : A * B = P) :
    len * st ≤ P := by
  calc
    len * st ≤ A * B := Nat.mul_le_mul hlen hst
    _ = P := hprod

-- ---------------------------------------------------------------------- parameters

/-- `J = 16K + 2 + 2a`. -/
def expJ (a K : Nat) : Nat := 16 * K + 2 + 2 * a

/-- `X = 2^J`. -/
def bigX (a K : Nat) : Nat := 2 ^ expJ a K

/-- `T = 4·K·X²`. -/
def bigT (a K : Nat) : Nat := 4 * K * (bigX a K) ^ 2

theorem expJ_pos (a K : Nat) : 0 < expJ a K := by
  dsimp [expJ]
  omega

theorem expJ_gt_8K (a K : Nat) : 8 * K < expJ a K := by
  dsimp [expJ]
  omega

theorem two_le_bigX (a K : Nat) : 2 ≤ bigX a K := by
  dsimp [bigX, expJ]
  have hj : 1 ≤ 16 * K + 2 + 2 * a := by omega
  have h := two_pow_mono (i := 1) (j := 16 * K + 2 + 2 * a) hj
  simpa using h

theorem bigX_pos (a K : Nat) : 0 < bigX a K := by
  have := two_le_bigX a K
  omega

/-- `X^2 = X·X` (core `simp` does not unfold the square). -/
theorem sq_eq_mul (X : Nat) : X ^ 2 = X * X := by
  change X ^ (Nat.succ (Nat.succ Nat.zero)) = X * X
  simp [Nat.pow_succ, Nat.pow_zero]

/--
Bounds a block-sum `n·a + K·(n·(p+n))` using only `n ≤ X`, `a ≤ X`, `n·p ≤ P` and `X² = P`.
-/
theorem weight_bound {n p a K X P : Nat}
    (hnX : n ≤ X) (haX : a ≤ X) (hnp : n * p ≤ P) (hXX : X ^ 2 = P) :
    n * a + K * (n * (p + n)) ≤ P + K * (P + P) := by
  have hXXm : X * X = P := by simpa [sq_eq_mul X] using hXX
  have hna : n * a ≤ P := by
    calc
      n * a ≤ X * X := Nat.mul_le_mul hnX haX
      _ = P := hXXm
  have hnn : n * n ≤ P := by
    calc
      n * n ≤ X * X := Nat.mul_le_mul hnX hnX
      _ = P := hXXm
  have hnpn : n * (p + n) ≤ P + P := by
    rw [Nat.mul_add]
    omega
  have hKm : K * (n * (p + n)) ≤ K * (P + P) := Nat.mul_le_mul_left K hnpn
  omega

/-- `P + K·(P+P) ≤ 4·K·P` whenever `K ≥ 1`. -/
theorem combine_bound (K P : Nat) (hK : 0 < K) : P + K * (P + P) ≤ 4 * K * P := by
  have hKP : P ≤ K * P := by
    calc
      P = 1 * P := by simp
      _ ≤ K * P := Nat.mul_le_mul_right P (by omega)
  rw [Nat.mul_assoc]
  have hsplit : K * (P + P) = K * P + K * P := by rw [Nat.mul_add]
  omega

/-- `4·K·(2·A) = 8·K·A`. -/
theorem four_mul_two_fold (K A : Nat) : 4 * K * (2 * A) = 8 * K * A := by
  rw [← Nat.mul_assoc]
  congr 1
  omega

/-- `a ≤ X` — follows from `n < 2^n` and `a ≤ J`. -/
theorem a_le_bigX (a K : Nat) : a ≤ bigX a K := by
  dsimp [bigX]
  have hJ : a ≤ expJ a K := by dsimp [expJ]; omega
  have hpow : 2 ^ a ≤ 2 ^ (expJ a K) := two_pow_mono hJ
  have hlt : a < 2 ^ a := Nat.lt_two_pow_self (n := a)
  omega

end JSP001018
