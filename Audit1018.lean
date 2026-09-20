/-
  Independent audit bridge — Justin Sun Prize JSP-001018 (Erdős problem #1213)
  ============================================================================

  Original problem (Erdős Problems database #1213; prize bank JSP-001018):

      "Let a, K ≥ 1.  Does there exist f(a,K) such that if
           a = a_1 < … < a_s
       is a sequence of integers with a_s > f(a,K) and with bounded gaps
       a_{i+1} − a_i ≤ K, then there are two distinct intervals I and J such
       that  Σ_{i∈I} a_i  =  Σ_{j∈J} a_j ?"

  Purpose of this file
  --------------------
  It performs the official `lean-verify` self-check step: "write a minimal
  target statement and `example : IntendedStatement := ...` in a separate audit
  file, connecting it to the submitted theorem."  Renaming a definition is NOT
  an independent check, so the restatement below differs structurally from the
  submitted one in both of its two ingredients.

  (A) INDEPENDENT RESTATEMENT.  `JSP001018.lean` states the conclusion with

        * a CUSTOM RECURSIVE block sum `isum u p n`, and
        * "distinct intervals" rendered as a disjunction on the endpoints,
          `(p ≠ p' ∨ n ≠ n')`.

      Here the conclusion is restated the way the problem text itself phrases it:

        * an interval is an explicit INDEX SET `Finset.Ico p (p + n)`, and the
          block sum is the ordinary `Finset` sum `∑ i ∈ I, u i` (no custom
          recursion anywhere in this file);
        * "distinct" is set inequality `I ≠ J` between the two index sets.

  (B) BRIDGE.  Two substantive lemmas connect the two renderings, and neither
      is a rename:

        * `isum_eq_sum_range` proves the submitted recursive block sum equals
          the standard `Finset.range` sum, by induction on the block length;
        * `Ico_inj` proves an index set `Finset.Ico p (p + n)` determines the
          pair `(p, n)` (via least element and cardinality), so set-inequality
          is exactly the submitted endpoint disjunction.

      `submitted_yields_intended` then transports a proof of the submitted
      statement to the restated one, and `submitted_theorem_yields_intended`
      applies that transport to the published proof term
      `JSP001018.erdos_1213`, whose type is checked against
      `SubmittedStatement` by `submitted_theorem_has_submitted_type`.

  No `sorry`, no `admit`, no custom axiom.
-/

import Mathlib
import JSP001018

set_option maxHeartbeats 0

namespace Audit1018

open JSP001018
open scoped BigOperators

--------------------------------------------------------------------------------
-- (A) Independent restatement of the target
--------------------------------------------------------------------------------

/-- An interval of indices, as an explicit finite set. -/
def Block (p n : ℕ) : Finset ℕ := Finset.Ico p (p + n)

/-- The INTENDED statement, read straight off the official problem text:
    intervals are index sets, sums are `Finset` sums, and "distinct" is set
    inequality. -/
def IntendedStatement : Prop :=
  ∀ a K : ℕ, 0 < a → 0 < K →
    ∃ F : ℕ, ∀ (s : ℕ) (u : ℕ → ℕ),
      0 < s →
      u 0 = a →
      (∀ i, i + 1 < s → u i < u (i + 1)) →
      (∀ i, i + 1 < s → u (i + 1) - u i ≤ K) →
      F < u (s - 1) →
      ∃ I J : Finset ℕ,
        I ≠ J ∧
        (∃ p n : ℕ, 0 < n ∧ p + n ≤ s ∧ I = Block p n) ∧
        (∃ p n : ℕ, 0 < n ∧ p + n ≤ s ∧ J = Block p n) ∧
        (∑ i ∈ I, u i) = ∑ i ∈ J, u i

/-- The statement actually submitted in `JSP001018.lean`, quoted here so that
    the bridge can be applied to it. -/
def SubmittedStatement : Prop :=
  ∀ a K : ℕ, 0 < a → 0 < K →
    ∃ F : ℕ, ∀ (s : ℕ) (u : ℕ → ℕ),
      0 < s →
      u 0 = a →
      (∀ i, i + 1 < s → u i < u (i + 1)) →
      (∀ i, i + 1 < s → u (i + 1) - u i ≤ K) →
      F < u (s - 1) →
      ∃ p n p' n' : ℕ,
        0 < n ∧ 0 < n' ∧
        p + n ≤ s ∧ p' + n' ≤ s ∧
        (p ≠ p' ∨ n ≠ n') ∧
        isum u p n = isum u p' n'

--------------------------------------------------------------------------------
-- (B) Bridge lemmas
--------------------------------------------------------------------------------

/-- The submitted recursive block sum is the ordinary sum over a range.
    Proved by induction on the block length; the step uses `sum_range_succ`. -/
theorem isum_eq_sum_range (u : ℕ → ℕ) (p n : ℕ) :
    isum u p n = ∑ i ∈ Finset.range n, u (p + i) := by
  induction n with
  | zero => simp [isum]
  | succ n ih =>
      simp [isum, ih, Finset.sum_range_succ]

/-- The block sum over the index set `Block p n` is the range sum. -/
theorem sum_block_eq_sum_range (u : ℕ → ℕ) (p n : ℕ) :
    (∑ i ∈ (Block p n), u i) = ∑ i ∈ Finset.range n, u (p + i) := by
  simpa [Block, Nat.add_sub_cancel_left] using
    (Finset.sum_Ico_eq_sum_range (fun i => u i) p (p + n))

/-- An index set `Block p n` with `n > 0` determines `(p, n)`: the least
    element is `p` and the cardinality is `n`. -/
theorem Ico_inj {p n p' n' : ℕ} (hn : 0 < n) (hn' : 0 < n')
    (h : Block p n = Block p' n') : p = p' ∧ n = n' := by
  have hpL : p ∈ Block p n := by
    simp [Block, Finset.mem_Ico, hn]
  have hpR : p ∈ Block p' n' := by simpa [h] using hpL
  have hpL' : p' ∈ Block p' n' := by
    simp [Block, Finset.mem_Ico, hn']
  have hpR' : p' ∈ Block p n := by simpa [h] using hpL'
  have h1 : p' ≤ p := (Finset.mem_Ico.mp hpR).1
  have h2 : p ≤ p' := (Finset.mem_Ico.mp hpR').1
  have hp : p = p' := le_antisymm h2 h1
  subst p'
  have hcard := congrArg Finset.card h
  have hn_eq : n = n' := by
    simpa [Block] using hcard
  exact ⟨rfl, hn_eq⟩

/-- Transport: a proof of the submitted statement proves the restated one. -/
theorem submitted_yields_intended (h : SubmittedStatement) : IntendedStatement := by
  intro a K ha hK
  rcases h a K ha hK with ⟨F, hF⟩
  refine ⟨F, ?_⟩
  intro s u hs hu0 hinc hgap hbig
  rcases hF s u hs hu0 hinc hgap hbig with
    ⟨p, n, p', n', hn, hn', hpn, hpn', hdist, hsum⟩
  let I : Finset ℕ := Block p n
  let J : Finset ℕ := Block p' n'
  refine ⟨I, J, ?_, ?_, ?_, ?_⟩
  · intro hIJ
    rcases Ico_inj hn hn' hIJ with ⟨hp, hn_eq⟩
    rcases hdist with hpne | hnne
    · exact hpne hp
    · exact hnne hn_eq
  · exact ⟨p, n, hn, hpn, rfl⟩
  · exact ⟨p', n', hn', hpn', rfl⟩
  · dsimp [I, J]
    calc
      (∑ i ∈ (Block p n), u i) = ∑ i ∈ Finset.range n, u (p + i) :=
          sum_block_eq_sum_range u p n
      _ = isum u p n := (isum_eq_sum_range u p n).symm
      _ = isum u p' n' := hsum
      _ = ∑ i ∈ Finset.range n', u (p' + i) := isum_eq_sum_range u p' n'
      _ = (∑ i ∈ (Block p' n'), u i) := (sum_block_eq_sum_range u p' n').symm

/-- The published proof term really has the submitted statement as its type. -/
theorem submitted_theorem_has_submitted_type : SubmittedStatement :=
  JSP001018.erdos_1213

/-- Bridge applied to the submitted theorem. -/
theorem submitted_theorem_yields_intended : IntendedStatement :=
  submitted_yields_intended JSP001018.erdos_1213

-- The `example : IntendedStatement := ...` form required by `lean-verify` §2.
example : IntendedStatement := submitted_theorem_yields_intended

--------------------------------------------------------------------------------
-- Axiom audit
--------------------------------------------------------------------------------

#print axioms Audit1018.isum_eq_sum_range
#print axioms Audit1018.sum_block_eq_sum_range
#print axioms Audit1018.Ico_inj
#print axioms Audit1018.submitted_yields_intended
#print axioms Audit1018.submitted_theorem_has_submitted_type
#print axioms Audit1018.submitted_theorem_yields_intended

end Audit1018
