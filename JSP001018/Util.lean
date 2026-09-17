import Std

/-!
# JSP-001018 (= Erdős problem #1213) — module `ListUtil`

Core Lean 4.23 ships `Init` + `Std` but **no `Finset` / `Multiset` / `Fintype`**,
so we build the small amount of finite-set machinery we need directly on `List`.

No `sorry`, no `admit`, no new axioms.
-/

set_option linter.unusedSimpArgs false

namespace ListUtil

open List

-- ---------------------------------------------------------------- map / sum

theorem sum_map_const {α : Type} (l : List α) (c : Nat) :
    (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp [List.map_cons, List.sum_cons, ih, Nat.succ_mul]
      omega

theorem sum_append (l₁ l₂ : List Nat) :
    (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  induction l₁ with
  | nil => simp
  | cons x xs ih => simp [List.sum_cons, ih, Nat.add_assoc]

theorem nodup_map_of_inj {α β : Type} {f : α → β} {l : List α}
    (nd : l.Nodup) (h : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) :
    (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [List.nodup_cons] at nd ⊢
      constructor
      · intro hmem
        apply nd.1
        rcases (List.mem_map.mp hmem) with ⟨y, hyxs, hyx⟩
        have hxy : y = x := h y (by simp [hyxs]) x (by simp) hyx
        simpa [hxy] using hyxs
      · exact ih nd.2 (by
          intro a ha b hb heq
          exact h a (by simp [ha]) b (by simp [hb]) heq)

theorem nodup_filter {α : Type} (p : α → Bool) {l : List α} (nd : l.Nodup) :
    (l.filter p).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons] at nd
      by_cases hx : p x = true
      · rw [List.filter_cons_of_pos hx, List.nodup_cons]
        constructor
        · intro hmem
          exact nd.1 ((List.mem_filter.mp hmem).1)
        · exact ih nd.2
      · rw [List.filter_cons_of_neg hx]
        exact ih nd.2

theorem length_filter_partition {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter fun x => !p x).length = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp [List.filter]
      by_cases hx : p x = true
      · simp [hx, ih]
        omega
      · have hnx : (!p x) = true := by
          cases hp : p x <;> simp_all
        simp [hx, hnx, ih]
        omega

-- ------------------------------------------------------------------- flatMap

theorem nodup_flatMap_of_disjoint {α β : Type} {f : α → List β} {l : List α}
    (nd : l.Nodup)
    (hfi : ∀ a ∈ l, (f a).Nodup)
    (hdj : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ x ∈ f a, x ∉ f b) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.flatMap_cons, List.nodup_append]
      rw [List.nodup_cons] at nd
      have hfi_xs : ∀ a ∈ xs, (f a).Nodup := by
        intro a ha
        exact hfi a (by simp [ha])
      have hdj_xs : ∀ a ∈ xs, ∀ b ∈ xs, a ≠ b → ∀ y ∈ f a, y ∉ f b := by
        intro a ha b hb hne y hy hz
        exact (hdj a (by simp [ha]) b (by simp [hb]) hne y hy) hz
      refine ⟨hfi x (by simp), ih nd.2 hfi_xs hdj_xs, ?_⟩
      intro u hu v hv huv
      subst huv
      rcases (List.mem_flatMap.mp hv) with ⟨a, ha, hua⟩
      have hax : a ≠ x := by
        intro hax'
        subst a
        exact nd.1 ha
      exact (hdj a (by simp [ha]) x (by simp) hax u hua) hu

theorem length_flatMap_of_const_len {α β : Type} {f : α → List β} {l : List α} (n : Nat)
    (hl : l.Nodup)
    (h : ∀ a ∈ l, (f a).length = n) :
    (l.flatMap f).length = l.length * n := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hl
      have h_fin_x : (f x).length = n := h x (by simp)
      have hfi_xs : ∀ a ∈ xs, (f a).length = n := by
        intro a ha
        exact h a (by simp [ha])
      calc
        (List.flatMap f (x :: xs)).length
            = (f x).length + (List.flatMap f xs).length := by
                rw [List.flatMap_cons, List.length_append]
        _ = n + xs.length * n := by rw [h_fin_x, ih hl.2 hfi_xs]
        _ = (Nat.succ xs.length) * n := by rw [Nat.succ_mul]; omega
        _ = (x :: xs).length * n := by simp

-- ------------------------------------------------------- pigeonhole principle

/-- A `Nodup` list of naturals all equal to the same `T` has length at most 1. -/
theorem nodup_all_eq_len_le_one (l : List Nat) (T : Nat)
    (nd : l.Nodup) (h : ∀ x ∈ l, x = T) : l.length ≤ 1 := by
  cases l with
  | nil => simp
  | cons y ys =>
      cases ys with
      | nil => simp
      | cons z zs =>
          exfalso
          rw [List.nodup_cons] at nd
          have hyT : y = T := h y (by simp)
          have hzT : z = T := h z (by simp)
          have hyz : y = z := by omega
          exact nd.1 (by simp [hyz])

/-- A `Nodup` list of naturals all `< T` has length at most `T`. -/
theorem bounded_nodup_length_le : ∀ (T : Nat) (l : List Nat),
    l.Nodup → (∀ x ∈ l, x < T) → l.length ≤ T
  | 0, l, nd, hb => by
      cases l with
      | nil => simp
      | cons x xs =>
          have : x < 0 := hb x (by simp)
          omega
  | T + 1, l, nd, hb => by
      let p : Nat → Bool := fun x => decide (x = T)
      let lo := l.filter fun x => !p x
      let hi := l.filter p
      have hpart0 := ListUtil.length_filter_partition p l
      have hpart : lo.length + hi.length = l.length := by
        dsimp [lo, hi]
        omega
      have hnd_lo : lo.Nodup := ListUtil.nodup_filter _ (by simpa [lo] using nd)
      have hb_lo : ∀ x ∈ lo, x < T := by
        intro x hx
        have hxl : x ∈ l := (List.mem_filter.mp hx).1
        have hne : x ≠ T := by
          have hb2 := (List.mem_filter.mp hx).2
          simp [p] at hb2
          exact hb2
        have hlt : x < T + 1 := hb x hxl
        omega
      have hle_lo : lo.length ≤ T := ListUtil.bounded_nodup_length_le T lo hnd_lo hb_lo
      have hle_hi : hi.length ≤ 1 := by
        have all_eq : ∀ x ∈ hi, x = T := by
          intro x hx
          exact of_decide_eq_true (by simpa [hi, p] using (List.mem_filter.mp hx).2)
        exact ListUtil.nodup_all_eq_len_le_one hi T
          (ListUtil.nodup_filter p (by simpa [hi] using nd)) all_eq
      omega

end ListUtil
