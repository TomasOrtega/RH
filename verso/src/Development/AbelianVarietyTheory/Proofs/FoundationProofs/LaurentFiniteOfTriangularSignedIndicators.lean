import Mathlib

namespace GlobalTheory.LaurentFinite

open AddMonoidAlgebra

def cut (j n : ℤ) : ℤ := if j ≤ |n| then Int.sign n else 0

/- English proof (translation)
Unfold `cut`. Use `split_ifs`. Break down `lt_trichotomy n 0 with h | h | h` into its components or cases. Simplify using `[Int.sign_eq_neg_one_of_neg h]`. Simplify using `[h]`.

Simplify using `[Int.sign_eq_one_of_pos h]`. Simplify using the standard rewrite rules.
-/
theorem abs_cut_le (j n : ℤ) : |cut j n| ≤ 1 := by
  unfold cut
  split_ifs
  · rcases lt_trichotomy n 0 with h | h | h
    · simp [Int.sign_eq_neg_one_of_neg h]
    · simp [h]
    · simp [Int.sign_eq_one_of_pos h]
  · simp

/- English proof (translation)
Establish `hk' : k = -1 ∨ k = 0 ∨ k = 1`. Rewrite `hk` using `[abs_le]`. Use linear arithmetic over natural numbers and integers. Unfold `cut at *`. Use `split_ifs at * with h`.

Break down `lt_trichotomy n 0 with h0 | h0 | h0` into its components or cases. Rewrite `*` using `[Int.sign_eq_neg_one_of_neg h0]`. Rewrite `h`, `hn` using `[abs_of_neg h0]`. Break down `hk' with rfl | rfl | rfl` into its components or cases. Conclude with `absurd rfl hne`.

Evaluate the numerical expressions. Use the polynomial consequences of the given equalities and inequalities. Evaluate the numerical expressions. Use the polynomial consequences of the given equalities and inequalities. Substitute `h0` using the available equality.

Simplify using `at h`. Use linear arithmetic over natural numbers and integers. Rewrite `*` using `[Int.sign_eq_one_of_pos h0]`. Rewrite `h`, `hn` using `[abs_of_pos h0]`. Break down `hk' with rfl | rfl | rfl` into its components or cases.

Evaluate the numerical expressions. Use the polynomial consequences of the given equalities and inequalities. Evaluate the numerical expressions. Use the polynomial consequences of the given equalities and inequalities. Conclude with `absurd rfl hne`.

Establish `h2 : |n| ≤ j - 2` using `by omega`. Rewrite `h2` using `[abs_le]`. Break down `hk' with rfl | rfl | rfl` into its components or cases. Evaluate the numerical expressions. Use polynomial arithmetic with `[h2.1, h2.2]`.

Conclude with `absurd rfl hne`. Evaluate the numerical expressions. Use polynomial arithmetic with `[h2.1, h2.2]`.
-/
theorem pointwise_lt (j n k : ℤ) (hj : 2 ≤ j) (hn : |n| ≠ j - 1) (hk : |k| ≤ 1)
    (hne : k ≠ cut j n) :
    (2 * j - 2) * (|cut j n| - |k|) < n ^ 2 - (n - cut j n + k) ^ 2 := by
  have hk' : k = -1 ∨ k = 0 ∨ k = 1 := by
    rw [abs_le] at hk; omega
  unfold cut at *
  split_ifs at * with h
  · rcases lt_trichotomy n 0 with h0 | h0 | h0
    · rw [Int.sign_eq_neg_one_of_neg h0] at *
      rw [abs_of_neg h0] at h hn
      rcases hk' with rfl | rfl | rfl
      · exact absurd rfl hne
      · norm_num; nlinarith
      · norm_num; nlinarith
    · subst h0; simp at h; omega
    · rw [Int.sign_eq_one_of_pos h0] at *
      rw [abs_of_pos h0] at h hn
      rcases hk' with rfl | rfl | rfl
      · norm_num; nlinarith
      · norm_num; nlinarith
      · exact absurd rfl hne
  · have h2 : |n| ≤ j - 2 := by omega
    rw [abs_le] at h2
    rcases hk' with rfl | rfl | rfl
    · norm_num; nlinarith [h2.1, h2.2]
    · exact absurd rfl hne
    · norm_num; nlinarith [h2.1, h2.2]

/- English proof (translation)
Take `⟨i0, hi0⟩` from `Function.ne_iff.mp hne`. Establish `h1 : ∑ i, (2 * j - 2) * (|cut j (ν i)| - |κ i|) < ∑ i, (ν i ^ 2 - (ν i - cut j (ν i) + κ i) ^ 2)`. Apply `Finset.sum_lt_sum` to reduce the goal to its premises. Introduce `i _`. Distinguish the cases in `h : κ i = cut j (ν i)`.

Rewrite using `[h]`. Simplify using the standard rewrite rules. Conclude with `(pointwise_lt j _ _ hj (hν i) (hκ i) h).le`. Conclude with `⟨i0, Finset.mem_univ _, pointwise_lt j _ _ hj (hν i0) (hκ i0) hi0⟩`. Rewrite `h1` using `[← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib]`.

Establish `: 0 ≤ (2 * j - 2) * (∑ i, |cut j (ν i)| - ∑ i, |κ i|)` using `mul_nonneg (by omega) (by omega)`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_sq_lt {m : ℕ} (j : ℤ) (ν κ : Fin m → ℤ) (hj : 2 ≤ j) (hν : ∀ i, |ν i| ≠ j - 1)
    (hκ : ∀ i, |κ i| ≤ 1) (hs : ∑ i, |κ i| ≤ ∑ i, |cut j (ν i)|)
    (hne : κ ≠ fun i => cut j (ν i)) :
    ∑ i, (ν i - cut j (ν i) + κ i) ^ 2 < ∑ i, ν i ^ 2 := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hne
  have h1 : ∑ i, (2 * j - 2) * (|cut j (ν i)| - |κ i|)
      < ∑ i, (ν i ^ 2 - (ν i - cut j (ν i) + κ i) ^ 2) := by
    apply Finset.sum_lt_sum
    · intro i _
      by_cases h : κ i = cut j (ν i)
      · rw [h]; simp
      · exact (pointwise_lt j _ _ hj (hν i) (hκ i) h).le
    · exact ⟨i0, Finset.mem_univ _, pointwise_lt j _ _ hj (hν i0) (hκ i0) hi0⟩
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at h1
  have : 0 ≤ (2 * j - 2) * (∑ i, |cut j (ν i)| - ∑ i, |κ i|) :=
    mul_nonneg (by omega) (by omega)
  omega

/- English proof (translation)
Establish `hcard : ((Finset.univ.erase i0).image fun i => |ν i|).card < (Finset.Icc (1 : ℤ) m).card`. Use `lt_of_le_of_lt Finset.card_image_le ?_` and prove the remaining obligations. Use `i0.pos` as an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Take `⟨t, ht, ht'⟩` from `Finset.exists_mem_notMem_of_card_lt_card hcard`. Rewrite `ht` using `[Finset.mem_Icc]`. Use `⟨t + 1, by omega, by omega, fun i hi => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h0 : i = i0`. Substitute `h0` using the available equality.

Use linear arithmetic over natural numbers and integers. Conclude with `ht' (Finset.mem_image.mpr ⟨i, by simp [h0], by omega⟩)`.
-/
theorem exists_gap {m : ℕ} (ν : Fin m → ℤ) (i0 : Fin m) (h : (m : ℤ) < |ν i0|) :
    ∃ j : ℤ, 2 ≤ j ∧ j ≤ |ν i0| ∧ ∀ i, |ν i| ≠ j - 1 := by
  have hcard : ((Finset.univ.erase i0).image fun i => |ν i|).card < (Finset.Icc (1 : ℤ) m).card := by
    refine lt_of_le_of_lt Finset.card_image_le ?_
    have := i0.pos
    simp
    omega
  obtain ⟨t, ht, ht'⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_Icc] at ht
  refine ⟨t + 1, by omega, by omega, fun i hi => ?_⟩
  by_cases h0 : i = i0
  · subst h0; omega
  · exact ht' (Finset.mem_image.mpr ⟨i, by simp [h0], by omega⟩)

/- English proof (translation)
Use `set S : Finset (AddMonoidAlgebra ℂ (Fin m → ℤ)) := (Fintype.piFinset fun _ : Fin m => Finset.Icc (-(m : ℤ)) m).image fun ν => single ν 1 with hS`. Use `set N : Submodule B (AddMonoidAlgebra ℂ (Fin m → ℤ)) := Submodule.span B (S : Set _) with hN`. Establish `hsm : ∀ (ν : Fin m → ℤ) (c : ℂ), single ν 1 ∈ N → single ν c ∈ N`. Introduce `ν c h`. Use `N.smul_of_tower_mem c h` as an intermediate fact.

Rewrite `this` using `[smul_single', mul_one]`. Then use the resulting hypothesis. Establish `key : ∀ (n : ℕ) (ν : Fin m → ℤ), ∑ i, ν i ^ 2 < n → single ν (1 : ℂ) ∈ N`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`.

Introduce `ν h`. Establish `: 0 ≤ ∑ i, ν i ^ 2` using `Finset.sum_nonneg fun i _ => sq_nonneg _`. Simplify using `at h`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih`.

Introduce `ν h`. Distinguish the cases in `hb : ∀ i, |ν i| ≤ m`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨ν, ?_, rfl⟩)` and prove the remaining obligations. Rewrite using `[Fintype.mem_piFinset]`.

Introduce `i`. Conclude with `Finset.mem_Icc.mpr (abs_le.mp (hb i))`. Use `push Not at hb`. Take `⟨i0, hi0⟩` from `hb`. Take `⟨j, hj, hj0, hν⟩` from `exists_gap ν i0 hi0`.

Use `set ε : Fin m → ℤ := fun i => cut j (ν i) with hε`. Take `⟨s, hsB, hs0, hs⟩` from `hB ε fun i => abs_cut_le _ _`. Establish `step : ∀ κ : Fin m → ℤ, (∀ i, |κ i| ≤ 1) → ∑ i, |κ i| ≤ ∑ i, |ε i| → κ ≠ ε → single (κ + (ν - ε)) (1 : ℂ) ∈ N`. Introduce `κ h1 h2 h3`. Apply `ih` to reduce the goal to its premises.

Use `sum_sq_lt j ν κ hj hν h1 h2 h3` as an intermediate fact. Establish `e : ∑ i, (κ + (ν - ε)) i ^ 2 = ∑ i, (ν i - cut j (ν i) + κ i) ^ 2` using `Finset.sum_congr rfl fun i _ => by simp [hε, add_comm]`. Move the coercions through the operations in `at h`. Use linear arithmetic over natural numbers and integers. Establish `h0 : single (ν - ε) (1 : ℂ) ∈ N`.

Use `step 0 (by simp) (by simpa using Finset.sum_nonneg fun i _ => abs_nonneg (ε i)) (by` as an intermediate fact. Introduce `h0`. Establish `h1 : ε i0 = 0` using `by rw [← h0]; rfl`. Simplify using `only [hε, cut, hj0, if_true, Int.sign_eq_zero_iff_zero] at h1`. Rewrite `hj0` using `[h1]`.

Simplify using `at hj0`. Use the proof step `omega)`. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis. Establish `h1 : s * single (ν - ε) (1 : ℂ) ∈ N` using `N.smul_mem ⟨s, hsB⟩ h0`. Establish `h2 : s * single (ν - ε) (1 : ℂ) = ∑ κ ∈ s.coeff.support, single (κ + (ν - ε)) (s.coeff κ)` using `by conv_lhs => rw [← sum_coeff_single s, Finsupp.sum, Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun κ _ => by rw [single_mul_single, mul_one]`. Rewrite `h1` using `[h2, ← Finset.add_sum_erase _ _ (Finsupp.mem_support_iff.mpr hs0)]`. Establish `h3 : ∑ κ ∈ s.coeff.support.erase ε, single (κ + (ν - ε)) (s.coeff κ) ∈ N`. Use `N.sum_mem fun κ hκ => hsm _ _ ?_` and prove the remaining obligations. Rewrite `hκ` using `[Finset.mem_erase, Finsupp.mem_support_iff]`.

Conclude with `step κ (hs κ hκ.2).1 (hs κ hκ.2).2 hκ.1`. Establish `h4` using `N.smul_of_tower_mem (s.coeff ε)⁻¹ ((N.add_mem_iff_left h3).mp h1)`. Rewrite `h4` using `[smul_single', inv_mul_cancel₀ hs0, add_sub_cancel]`. Then use the resulting hypothesis. Use `Module.Finite.of_fg_top ⟨S, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`.

Introduce `x _`. Express the relevant statement in the definitionally equal form `x ∈ N`. Proceed by induction on `x using induction_linear with`. Consider the case `zero => exact N.zero_mem`. Consider the case `add x y hx hy => exact N.add_mem (hx trivial) (hy trivial)`.

Consider the case `single ν c`. Use `hsm _ _ (key ((∑ i, ν i ^ 2).toNat + 1) ν ?_)` and prove the remaining obligations. Use `push_cast`. Use linear arithmetic over natural numbers and integers.
-/
theorem finite_of_triangular (m : ℕ) (B : Subalgebra ℂ (AddMonoidAlgebra ℂ (Fin m → ℤ)))
    (hB : ∀ ε : Fin m → ℤ, (∀ i, |ε i| ≤ 1) → ∃ s ∈ B, s.coeff ε ≠ 0 ∧
      ∀ κ, s.coeff κ ≠ 0 → (∀ i, |κ i| ≤ 1) ∧ ∑ i, |κ i| ≤ ∑ i, |ε i|) :
    Module.Finite B (AddMonoidAlgebra ℂ (Fin m → ℤ)) := by
  classical
  set S : Finset (AddMonoidAlgebra ℂ (Fin m → ℤ)) :=
    (Fintype.piFinset fun _ : Fin m => Finset.Icc (-(m : ℤ)) m).image fun ν => single ν 1 with hS
  set N : Submodule B (AddMonoidAlgebra ℂ (Fin m → ℤ)) := Submodule.span B (S : Set _) with hN
  have hsm : ∀ (ν : Fin m → ℤ) (c : ℂ), single ν 1 ∈ N → single ν c ∈ N := by
    intro ν c h
    have := N.smul_of_tower_mem c h
    rwa [smul_single', mul_one] at this
  have key : ∀ (n : ℕ) (ν : Fin m → ℤ), ∑ i, ν i ^ 2 < n → single ν (1 : ℂ) ∈ N := by
    intro n
    induction n with
    | zero =>
      intro ν h
      have : 0 ≤ ∑ i, ν i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      simp at h
      omega
    | succ n ih =>
      intro ν h
      by_cases hb : ∀ i, |ν i| ≤ m
      · apply Submodule.subset_span
        refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨ν, ?_, rfl⟩)
        rw [Fintype.mem_piFinset]
        intro i
        exact Finset.mem_Icc.mpr (abs_le.mp (hb i))
      · push Not at hb
        obtain ⟨i0, hi0⟩ := hb
        obtain ⟨j, hj, hj0, hν⟩ := exists_gap ν i0 hi0
        set ε : Fin m → ℤ := fun i => cut j (ν i) with hε
        obtain ⟨s, hsB, hs0, hs⟩ := hB ε fun i => abs_cut_le _ _
        have step : ∀ κ : Fin m → ℤ, (∀ i, |κ i| ≤ 1) → ∑ i, |κ i| ≤ ∑ i, |ε i| → κ ≠ ε →
            single (κ + (ν - ε)) (1 : ℂ) ∈ N := by
          intro κ h1 h2 h3
          apply ih
          have := sum_sq_lt j ν κ hj hν h1 h2 h3
          have e : ∑ i, (κ + (ν - ε)) i ^ 2 = ∑ i, (ν i - cut j (ν i) + κ i) ^ 2 :=
            Finset.sum_congr rfl fun i _ => by simp [hε, add_comm]
          push_cast at h
          omega
        have h0 : single (ν - ε) (1 : ℂ) ∈ N := by
          have := step 0 (by simp) (by simpa using Finset.sum_nonneg fun i _ => abs_nonneg (ε i)) (by
            intro h0
            have h1 : ε i0 = 0 := by rw [← h0]; rfl
            simp only [hε, cut, hj0, if_true, Int.sign_eq_zero_iff_zero] at h1
            rw [h1] at hj0
            simp at hj0
            omega)
          rwa [zero_add] at this
        have h1 : s * single (ν - ε) (1 : ℂ) ∈ N := N.smul_mem ⟨s, hsB⟩ h0
        have h2 : s * single (ν - ε) (1 : ℂ)
            = ∑ κ ∈ s.coeff.support, single (κ + (ν - ε)) (s.coeff κ) := by
          conv_lhs => rw [← sum_coeff_single s, Finsupp.sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun κ _ => by rw [single_mul_single, mul_one]
        rw [h2, ← Finset.add_sum_erase _ _ (Finsupp.mem_support_iff.mpr hs0)] at h1
        have h3 : ∑ κ ∈ s.coeff.support.erase ε, single (κ + (ν - ε)) (s.coeff κ) ∈ N := by
          refine N.sum_mem fun κ hκ => hsm _ _ ?_
          rw [Finset.mem_erase, Finsupp.mem_support_iff] at hκ
          exact step κ (hs κ hκ.2).1 (hs κ hκ.2).2 hκ.1
        have h4 := N.smul_of_tower_mem (s.coeff ε)⁻¹ ((N.add_mem_iff_left h3).mp h1)
        rwa [smul_single', inv_mul_cancel₀ hs0, add_sub_cancel] at h4
  refine Module.Finite.of_fg_top ⟨S, ?_⟩
  rw [eq_top_iff]
  intro x _
  change x ∈ N
  induction x using induction_linear with
  | zero => exact N.zero_mem
  | add x y hx hy => exact N.add_mem (hx trivial) (hy trivial)
  | single ν c =>
    refine hsm _ _ (key ((∑ i, ν i ^ 2).toNat + 1) ν ?_)
    push_cast
    omega

end GlobalTheory.LaurentFinite
