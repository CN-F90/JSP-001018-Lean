import Std
import JSP001018.Arith
import JSP001018.Util
import JSP001018.Family

/-!
# JSP-001018 (= Erdős problem #1213) — module `Sequence`

Elementary facts about the input sequence `a = a₁ < a₂ < ... < aₛ` with gaps
`a_{i+1} - a_i ≤ K`, written zero-based as `u : Nat → Nat` with `u 0 = a`.

* `term_bound`   : `u i ≤ a + K·i`
* `length_lower` : `u (s-1) > a + K·X²` forces `s ≥ X²`
* `isum_le`      : size of an interval sum

No `sorry`, no `admit`, no new axioms.
-/

namespace JSP001018

/-- Sum of the block `u p + u (p+1) + ... + u (p+n-1)` (empty block = 0). -/
def isum (u : Nat → Nat) (p : Nat) : Nat → Nat
  | 0 => 0
  | Nat.succ n => isum u p n + u (p + n)

-- ------------------------------------------------------------------ input sequence

/-- A gap bound together with strict increase gives `u (i+1) ≤ u i + K`. -/
theorem step_from_gap {u : Nat → Nat} {i K : Nat}
    (hlt : u i < u (i + 1)) (hgap : u (i + 1) - u i ≤ K) :
    u (i + 1) ≤ u i + K := by
  have hle : u i ≤ u (i + 1) := Nat.le_of_lt hlt
  have hcancel : u (i + 1) - u i + u i = u (i + 1) := Nat.sub_add_cancel hle
  omega

/-- Lemma 1: `u i ≤ a + K·i` for every `i < s`. -/
theorem term_bound {a K s : Nat} {u : Nat → Nat}
    (hu0 : u 0 = a)
    (hinc : ∀ i, i + 1 < s → u i < u (i + 1))
    (hgap : ∀ i, i + 1 < s → u (i + 1) - u i ≤ K) :
    ∀ i, i < s → u i ≤ a + K * i := by
  intro i hi
  induction i with
  | zero => simp [hu0]
  | succ i ih =>
      have hi' : i < s := by omega
      have hih := ih hi'
      have hstep : u (i + 1) ≤ u i + K := step_from_gap (hinc i (by omega)) (hgap i (by omega))
      calc
        u (i + 1) ≤ u i + K := hstep
        _ ≤ (a + K * i) + K := by omega
        _ = a + K * (i + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
            omega

/-- The sequence is non-decreasing, so every term dominates `u 0`. -/
theorem seq_ge_zero {s : Nat} {u : Nat → Nat}
    (hinc : ∀ i, i + 1 < s → u i < u (i + 1)) :
    ∀ i, i < s → u 0 ≤ u i := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
      have hi' : i < s := by omega
      have hstep : u i ≤ u (i + 1) := Nat.le_of_lt (hinc i (by omega))
      calc
        u 0 ≤ u i := ih hi'
        _ ≤ u (i + 1) := hstep

/-- Lemma 2: a large last term forces the sequence to be long enough. -/
theorem length_lower {a K s X : Nat} {u : Nat → Nat}
    (hK : 0 < K) (hs : 0 < s)
    (hu0 : u 0 = a)
    (hinc : ∀ i, i + 1 < s → u i < u (i + 1))
    (hgap : ∀ i, i + 1 < s → u (i + 1) - u i ≤ K)
    (hbig : a + K * X ^ 2 < u (s - 1)) :
    X ^ 2 ≤ s := by
  have hs1 : s - 1 < s := by omega
  have hb := term_bound (a := a) (K := K) (s := s) (u := u) hu0 hinc hgap (s - 1) hs1
  have hmul_lt : K * X ^ 2 < K * (s - 1) := by omega
  have hxlt : X ^ 2 < s - 1 := (Nat.mul_lt_mul_left hK).mp hmul_lt
  omega

-- ------------------------------------------------------------------ interval sums

/-- A block sum is bounded by `length × (a common bound for all its terms)`. -/
theorem isum_cap_le {u : Nat → Nat} {p n C : Nat}
    (hu : ∀ i, i < n → u (p + i) ≤ C) :
    isum u p n ≤ n * C := by
  induction n with
  | zero => simp [isum]
  | succ n ih =>
      have ih' := ih (by intro i hi; exact hu i (by omega))
      have hlast : u (p + n) ≤ C := hu n (by omega)
      change isum u p n + u (p + n) ≤ Nat.succ n * C
      rw [Nat.succ_mul]
      omega

/-- A non-empty block whose terms are all positive has positive sum. -/
theorem isum_pos {u : Nat → Nat} {p n : Nat} (hn : 0 < n) (hu : 0 < u (p + (n - 1))) :
    0 < isum u p n := by
  cases n with
  | zero => omega
  | succ n' =>
      have : 0 < u (p + n') := by simpa using hu
      change 0 < isum u p n' + u (p + n')
      omega

end JSP001018
