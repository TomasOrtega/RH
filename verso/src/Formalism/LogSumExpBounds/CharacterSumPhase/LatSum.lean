import Formalism.LogSumExpBounds.StatementZ

namespace Formalism.NuclearRankWeightBounds.P

open Finset

noncomputable def psi (n : ℤ) : ℝ := (4 / (|(n : ℝ)| + 1)) ^ (5 / 4 : ℝ)

/- English proof (translation)
Unfold `psi`. Check the signs of the components of the expression.
-/
lemma psi_nonneg (n : ℤ) : 0 ≤ psi n := by
  unfold psi; positivity

/- English proof (translation)
Establish `hnat : Summable (fun n : ℕ => (4 / ((n : ℝ) + 1)) ^ (5 / 4 : ℝ))`. Establish `h1 : Summable (fun n : ℕ => (((n : ℝ)) ^ (5 / 4 : ℝ))⁻¹)` using `Real.summable_nat_rpow_inv.mpr (by norm_num)`. Establish `h2 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ))⁻¹)` using `(summable_nat_add_iff 1).mpr h1`. Establish `h3` using `h2.mul_left ((4 : ℝ) ^ (5 / 4 : ℝ))`. Use `h3.congr (fun n => ?_)` and prove the remaining obligations.

Establish `hn : (0 : ℝ) ≤ (n : ℝ) + 1` using `by positivity`. Rewrite using `[Real.div_rpow (by norm_num) hn]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[summable_int_iff_summable_nat_and_neg]`.

Prove the components needed by the constructor for the conclusion. Use `hnat.congr (fun n => ?_)` and prove the remaining obligations. Simplify using `[psi]`. Use `hnat.congr (fun n => ?_)` and prove the remaining obligations. Simplify using `[psi]`.
-/
lemma summable_psi : Summable psi := by
  have hnat : Summable (fun n : ℕ => (4 / ((n : ℝ) + 1)) ^ (5 / 4 : ℝ)) := by
    have h1 : Summable (fun n : ℕ => (((n : ℝ)) ^ (5 / 4 : ℝ))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    have h2 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ))⁻¹) :=
      (summable_nat_add_iff 1).mpr h1
    have h3 := h2.mul_left ((4 : ℝ) ^ (5 / 4 : ℝ))
    refine h3.congr (fun n => ?_)
    have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [Real.div_rpow (by norm_num) hn]
    push_cast
    ring
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · refine hnat.congr (fun n => ?_)
    simp [psi]
  · refine hnat.congr (fun n => ?_)
    simp [psi]

/- English proof (translation)
The claim follows from `summable_psi.sum_le_tsum T (fun n _ => psi_nonneg n)`.
-/
lemma psi_sum_le (T : Finset ℤ) : ∑ n ∈ T, psi n ≤ ∑' n, psi n :=
  summable_psi.sum_le_tsum T (fun n _ => psi_nonneg n)

/- English proof (translation)
The claim follows from `tsum_nonneg psi_nonneg`.
-/
lemma tsum_psi_nonneg : 0 ≤ ∑' n, psi n := tsum_nonneg psi_nonneg

/- English proof (translation)
Establish `hK' : (3 : ℝ) ≤ K` using `by exact_mod_cast hK`. Break down `le_or_gt t 1 with h | h` into its components or cases. Rewrite using `[min_eq_right h, min_eq_right (pow_le_one₀ ht.le h)]`. Rewrite using `[← Real.rpow_add ht, ← Real.rpow_add ht, ← Real.rpow_natCast]`. Apply `le_of_eq` to reduce the goal to its premises.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[min_eq_left h.le, Real.one_rpow, mul_one, mul_one]`. Use `(min_le_left _ _).trans ?_` and prove the remaining obligations. Conclude with `Real.one_le_rpow h.le (by linarith)`.
-/
lemma min_pow_le (t : ℝ) (ht : 0 < t) (K : ℕ) (hK : 3 ≤ K) :
    min 1 (t ^ K) ≤ t ^ ((K : ℝ) - 5 / 2) * ((min 1 t) ^ (5 / 4 : ℝ) * (min 1 t) ^ (5 / 4 : ℝ)) := by
  have hK' : (3 : ℝ) ≤ K := by exact_mod_cast hK
  rcases le_or_gt t 1 with h | h
  · rw [min_eq_right h, min_eq_right (pow_le_one₀ ht.le h)]
    rw [← Real.rpow_add ht, ← Real.rpow_add ht, ← Real.rpow_natCast]
    apply le_of_eq
    congr 1
    ring
  · rw [min_eq_left h.le, Real.one_rpow, mul_one, mul_one]
    refine (min_le_left _ _).trans ?_
    exact Real.one_le_rpow h.le (by linarith)

/- English proof (translation)
Unfold `psi`. Use `set a : ℤ := ⌊2 * r / x⌋ with ha`. Establish `key : min 1 (x / y) ≤ 4 / (|(a : ℝ)| + 1)`. Break down `le_or_gt |(a : ℝ)| 2 with h | h` into its components or cases. Use `(min_le_left _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[le_div_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `(min_le_right _ _).trans ?_` and prove the remaining obligations. Establish `h1 : (a : ℝ) ≤ 2 * r / x` using `Int.floor_le _`. Establish `h2 : 2 * r / x < a + 1` using `Int.lt_floor_add_one _`.

Establish `h3 : |(a : ℝ)| - 1 ≤ |2 * r / x|`. Break down `le_or_gt 0 (a : ℝ) with h0 | h0` into its components or cases. Rewrite using `[abs_of_nonneg h0]`. Establish `: (a : ℝ) ≤ |2 * r / x|` using `h1.trans (le_abs_self _)`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[abs_of_neg h0]`. Establish `ha1 : (a : ℝ) + 1 ≤ 0`. Establish `: a < 0` using `by exact_mod_cast h0`. Establish `: a + 1 ≤ 0` using `by omega`. Conclude with `this` after adjusting the coercions.

Establish `: -(2 * r / x) ≤ |2 * r / x|` using `neg_le_abs _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : |2 * r / x| = 2 * |r| / x`. Rewrite using `[abs_div, abs_mul, abs_of_pos hx]`. Evaluate the numerical expressions.

Rewrite `h3` using `[h4]`. Establish `h3' : (3 : ℝ) ≤ |(a : ℝ)|`. Rewrite `h`, the goal using `[← Int.cast_abs]`. Establish `h6 : (2 : ℤ) < |a|` using `by exact_mod_cast h`. Establish `h7 : (3 : ℤ) ≤ |a|` using `by omega`.

Conclude with `h7` after adjusting the coercions. Establish `h5 : (|(a : ℝ)| + 1) / 2 ≤ 2 * y / x`. Establish `: 2 * |r| / x ≤ 2 * y / x`. Apply `div_le_div_of_nonneg_right _ hx.le` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[div_le_div_iff₀ hy (by positivity)]`. Rewrite `h5` using `[le_div_iff₀ hx]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h0 : 0 ≤ min 1 (x / y)` using `le_min zero_le_one (by positivity)`.

Conclude with `Real.rpow_le_rpow h0 key (by norm_num)`.
-/
lemma min_le_psi (x y r : ℝ) (hx : 0 < x) (hy : 0 < y) (hr : |r| ≤ y) :
    (min 1 (x / y)) ^ (5 / 4 : ℝ) ≤ psi ⌊2 * r / x⌋ := by
  unfold psi
  set a : ℤ := ⌊2 * r / x⌋ with ha
  have key : min 1 (x / y) ≤ 4 / (|(a : ℝ)| + 1) := by
    rcases le_or_gt |(a : ℝ)| 2 with h | h
    · refine (min_le_left _ _).trans ?_
      rw [le_div_iff₀ (by positivity)]
      linarith
    · refine (min_le_right _ _).trans ?_
      have h1 : (a : ℝ) ≤ 2 * r / x := Int.floor_le _
      have h2 : 2 * r / x < a + 1 := Int.lt_floor_add_one _
      have h3 : |(a : ℝ)| - 1 ≤ |2 * r / x| := by
        rcases le_or_gt 0 (a : ℝ) with h0 | h0
        · rw [abs_of_nonneg h0]
          have : (a : ℝ) ≤ |2 * r / x| := h1.trans (le_abs_self _)
          linarith
        · rw [abs_of_neg h0]
          have ha1 : (a : ℝ) + 1 ≤ 0 := by
            have : a < 0 := by exact_mod_cast h0
            have : a + 1 ≤ 0 := by omega
            exact_mod_cast this
          have : -(2 * r / x) ≤ |2 * r / x| := neg_le_abs _
          linarith
      have h4 : |2 * r / x| = 2 * |r| / x := by
        rw [abs_div, abs_mul, abs_of_pos hx]; norm_num
      rw [h4] at h3
      have h3' : (3 : ℝ) ≤ |(a : ℝ)| := by
        rw [← Int.cast_abs] at h ⊢
        have h6 : (2 : ℤ) < |a| := by exact_mod_cast h
        have h7 : (3 : ℤ) ≤ |a| := by omega
        exact_mod_cast h7
      have h5 : (|(a : ℝ)| + 1) / 2 ≤ 2 * y / x := by
        have : 2 * |r| / x ≤ 2 * y / x := by
          apply div_le_div_of_nonneg_right _ hx.le; linarith
        linarith
      rw [div_le_div_iff₀ hy (by positivity)]
      rw [le_div_iff₀ hx] at h5
      nlinarith
  have h0 : 0 ≤ min 1 (x / y) := le_min zero_le_one (by positivity)
  exact Real.rpow_le_rpow h0 key (by norm_num)

/- English proof (translation)
Use `set T : Finset ℤ := (P.biUnion fun p => univ.image fun v => (p v).1) ∪ (P.biUnion fun p => univ.image fun v => (p v).2) with hT`. Establish `hsub : P ⊆ Fintype.piFinset (fun _ : Fin f => T ×ˢ T)`. Introduce `p hp`. Rewrite using `[Fintype.mem_piFinset]`. Introduce `v`.

Rewrite using `[mem_product]`. Prove the components needed by the constructor for the conclusion. Apply `mem_union_left` to reduce the goal to its premises. Conclude with `mem_biUnion.mpr ⟨p, hp, mem_image.mpr ⟨v, mem_univ _, rfl⟩⟩`. Apply `mem_union_right` to reduce the goal to its premises.

Conclude with `mem_biUnion.mpr ⟨p, hp, mem_image.mpr ⟨v, mem_univ _, rfl⟩⟩`. Combine the equalities or inequalities in the displayed calculation. Apply `sum_le_sum_of_subset_of_nonneg hsub` to reduce the goal to its premises. Introduce `p _ _`. Conclude with `prod_nonneg (fun v _ => mul_nonneg (psi_nonneg _) (psi_nonneg _))`.

Use `_ = ∏ _v : Fin f, ∑ q ∈ T ×ˢ T, psi q.1 * psi q.2 := by`. Rewrite using `[prod_univ_sum]`. Use `_ = ∏ _v : Fin f, ((∑ n ∈ T, psi n) * (∑ n ∈ T, psi n)) := by`. Rewrite using `[sum_mul_sum, sum_product]`. Use `_ ≤ ∏ _v : Fin f, ((∑' n, psi n) ^ 2) := by`.

Apply `prod_le_prod` to reduce the goal to its premises. Introduce `v _`. Conclude with `mul_nonneg (sum_nonneg fun n _ => psi_nonneg n) (sum_nonneg fun n _ => psi_nonneg n)`. Introduce `v _`. Rewrite using `[sq]`.

Conclude with `mul_le_mul (psi_sum_le T) (psi_sum_le T) (sum_nonneg fun n _ => psi_nonneg n) tsum_psi_nonneg`. Use `_ = ((∑' n, psi n) ^ 2) ^ f := by`. Rewrite using `[prod_const, card_univ, Fintype.card_fin]`.
-/
lemma cell_sum_le (f : ℕ) (P : Finset (Fin f → ℤ × ℤ)) :
    ∑ p ∈ P, ∏ v, (psi (p v).1 * psi (p v).2) ≤ ((∑' n, psi n) ^ 2) ^ f := by
  classical
  set T : Finset ℤ := (P.biUnion fun p => univ.image fun v => (p v).1) ∪
    (P.biUnion fun p => univ.image fun v => (p v).2) with hT
  have hsub : P ⊆ Fintype.piFinset (fun _ : Fin f => T ×ˢ T) := by
    intro p hp
    rw [Fintype.mem_piFinset]
    intro v
    rw [mem_product]
    constructor
    · apply mem_union_left
      exact mem_biUnion.mpr ⟨p, hp, mem_image.mpr ⟨v, mem_univ _, rfl⟩⟩
    · apply mem_union_right
      exact mem_biUnion.mpr ⟨p, hp, mem_image.mpr ⟨v, mem_univ _, rfl⟩⟩
  calc ∑ p ∈ P, ∏ v, (psi (p v).1 * psi (p v).2)
      ≤ ∑ p ∈ Fintype.piFinset (fun _ : Fin f => T ×ˢ T), ∏ v, (psi (p v).1 * psi (p v).2) := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro p _ _
        exact prod_nonneg (fun v _ => mul_nonneg (psi_nonneg _) (psi_nonneg _))
    _ = ∏ _v : Fin f, ∑ q ∈ T ×ˢ T, psi q.1 * psi q.2 := by
        rw [prod_univ_sum]
    _ = ∏ _v : Fin f, ((∑ n ∈ T, psi n) * (∑ n ∈ T, psi n)) := by
        rw [sum_mul_sum, sum_product]
    _ ≤ ∏ _v : Fin f, ((∑' n, psi n) ^ 2) := by
        apply prod_le_prod
        · intro v _
          exact mul_nonneg (sum_nonneg fun n _ => psi_nonneg n) (sum_nonneg fun n _ => psi_nonneg n)
        · intro v _
          rw [sq]
          exact mul_le_mul (psi_sum_le T) (psi_sum_le T) (sum_nonneg fun n _ => psi_nonneg n)
            tsum_psi_nonneg
    _ = ((∑' n, psi n) ^ 2) ^ f := by
        rw [prod_const, card_univ, Fintype.card_fin]

/- English proof (translation)
Use `⟨((∑' n, psi n) + 1) ^ 2, by have := tsum_psi_nonneg; positivity, ?_⟩` and prove the remaining obligations. Introduce `f La x K S hLa hx hxprod hK hS`. Use `set D := ∑' n, psi n with hD`. Establish `hD0 : 0 ≤ D` using `tsum_psi_nonneg`. Set `c : (Fin f → ℂ) → (Fin f → ℤ × ℤ)` to `fun o v => (⌊2 * (o v).re / x v⌋, ⌊2 * (o v).im / x v⌋)`.

Establish `hne : ∀ o ∈ S, ∀ v, o v ≠ 0`. Introduce `o ho v h0`. Establish `h1` using `hLa o (hS o ho).1 (hS o ho).2`. Rewrite `h1` using `[prod_eq_zero (mem_univ v) (by simp [h0])]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hinj : Set.InjOn c S`. Introduce `o ho o' ho' hc`. Assume the negation of the conclusion as `hoo`. Establish `hmem : o - o' ∈ La` using `La.sub_mem (hS o ho).1 (hS o' ho').1`. Establish `h1` using `hLa (o - o') hmem (sub_ne_zero.mpr hoo)`.

Establish `h2 : ∏ v, ‖(o - o') v‖ ≤ ∏ v, x v`. Apply `prod_le_prod (fun v _ => norm_nonneg _)` to reduce the goal to its premises. Introduce `v _`. Establish `hcv` using `congrFun hc v`. Simplify using `only [c, Prod.mk.injEq] at hcv`.

Establish `hre` using `Int.abs_sub_lt_one_of_floor_eq_floor hcv.1`. Establish `him` using `Int.abs_sub_lt_one_of_floor_eq_floor hcv.2`. Establish `hxv` using `hx v`. Establish `e1 : 2 * (o v).re / x v - 2 * (o' v).re / x v = 2 * ((o v).re - (o' v).re) / x v`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2 : 2 * (o v).im / x v - 2 * (o' v).im / x v = 2 * ((o v).im - (o' v).im) / x v`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hre` using `[e1, abs_div, abs_mul, abs_of_pos hxv, div_lt_one hxv]`. Rewrite `him` using `[e2, abs_div, abs_mul, abs_of_pos hxv, div_lt_one hxv]`. Establish `h3` using `Complex.norm_le_abs_re_add_abs_im ((o - o') v)`.

Simplify using `only [Pi.sub_apply, Complex.sub_re, Complex.sub_im] at h3 ⊢`. Evaluate the numerical expressions using `at hre him`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpt : ∀ o ∈ S, ∏ v, min 1 ((x v / ‖o v‖) ^ K) ≤ (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * ∏ v, (psi (c o v).1 * psi (c o v).2)`.

Introduce `o ho`. Establish `hno : ∀ v, 0 < ‖o v‖` using `fun v => norm_pos_iff.mpr (hne o ho v)`. Establish `ht : ∀ v, 0 < x v / ‖o v‖` using `fun v => div_pos (hx v) (hno v)`. Combine the equalities or inequalities in the displayed calculation. Apply `prod_le_prod` to reduce the goal to its premises.

Introduce `v _`. Conclude with `le_min zero_le_one (pow_nonneg (ht v).le _)`. Introduce `v _`. Conclude with `min_pow_le _ (ht v) K hK`. Use `_ = (∏ v, (x v / ‖o v‖) ^ ((K : ℝ) - 5 / 2)) * ∏ v, ((min 1 (x v / ‖o v‖)) ^ (5 / 4 : ℝ) * (min 1 (x v / ‖o v‖)) ^ (5 / 4 : ℝ)) := by`.

Rewrite using `[prod_mul_distrib]`. Use `_ ≤ (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * ∏ v, (psi (c o v).1 * psi (c o v).2) := by`. Establish `hK' : (3 : ℝ) ≤ K` using `by exact_mod_cast hK`. Apply `mul_le_mul` to reduce the goal to its premises. Rewrite using `[Real.finsetProd_rpow _ _ (fun v _ => (ht v).le)]`.

Apply `Real.rpow_le_rpow (prod_nonneg fun v _ => (ht v).le) _ (by linarith)` to reduce the goal to its premises. Rewrite using `[prod_div_distrib]`. Conclude with `div_le_self (prod_nonneg fun v _ => (hx v).le) (hLa o (hS o ho).1 (hS o ho).2)`. Apply `prod_le_prod` to reduce the goal to its premises. Introduce `v _`.

Establish `h0 : 0 ≤ min 1 (x v / ‖o v‖)` using `le_min zero_le_one (ht v).le`. Check the signs of the components of the expression. Introduce `v _`. Establish `h0 : 0 ≤ min 1 (x v / ‖o v‖)` using `le_min zero_le_one (ht v).le`. Apply `mul_le_mul` to reduce the goal to its premises.

Conclude with `min_le_psi _ _ _ (hx v) (hno v) (Complex.abs_re_le_norm _)`. Conclude with `min_le_psi _ _ _ (hx v) (hno v) (Complex.abs_im_le_norm _)`. Check the signs of the components of the expression. Conclude with `psi_nonneg _`. Conclude with `prod_nonneg fun v _ => mul_nonneg (Real.rpow_nonneg (le_min zero_le_one (ht v).le) _) (Real.rpow_nonneg (le_min zero_le_one (ht v).le) _)`.

Conclude with `Real.rpow_nonneg (prod_nonneg fun v _ => (hx v).le) _`. Establish `hX0 : 0 ≤ (∏ v, x v) ^ ((K : ℝ) - 5 / 2)` using `Real.rpow_nonneg (prod_nonneg fun v _ => (hx v).le) _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_sum, sum_image (fun a ha b hb h => hinj ha hb h)]`. Use `_ ≤ (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * (D ^ 2) ^ f := mul_le_mul_of_nonneg_left (cell_sum_le f _) hX0`.

Use `_ ≤ (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * ((D + 1) ^ 2) ^ f := by`. Apply `mul_le_mul_of_nonneg_left _ hX0` to reduce the goal to its premises. Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Use `_ = ((D + 1) ^ 2) ^ f * (∏ v, x v) ^ ((K : ℝ) - 5 / 2) := mul_comm _ _`.
-/
theorem lattice_sum_holds : Formalism.NuclearRankWeightBounds.Z.LatSum := by
  classical
  refine ⟨((∑' n, psi n) + 1) ^ 2, by have := tsum_psi_nonneg; positivity, ?_⟩
  intro f La x K S hLa hx hxprod hK hS
  set D := ∑' n, psi n with hD
  have hD0 : 0 ≤ D := tsum_psi_nonneg

  let c : (Fin f → ℂ) → (Fin f → ℤ × ℤ) := fun o v =>
    (⌊2 * (o v).re / x v⌋, ⌊2 * (o v).im / x v⌋)
  have hne : ∀ o ∈ S, ∀ v, o v ≠ 0 := by
    intro o ho v h0
    have h1 := hLa o (hS o ho).1 (hS o ho).2
    rw [prod_eq_zero (mem_univ v) (by simp [h0])] at h1
    linarith

  have hinj : Set.InjOn c S := by
    intro o ho o' ho' hc
    by_contra hoo
    have hmem : o - o' ∈ La := La.sub_mem (hS o ho).1 (hS o' ho').1
    have h1 := hLa (o - o') hmem (sub_ne_zero.mpr hoo)
    have h2 : ∏ v, ‖(o - o') v‖ ≤ ∏ v, x v := by
      apply prod_le_prod (fun v _ => norm_nonneg _)
      intro v _
      have hcv := congrFun hc v
      simp only [c, Prod.mk.injEq] at hcv
      have hre := Int.abs_sub_lt_one_of_floor_eq_floor hcv.1
      have him := Int.abs_sub_lt_one_of_floor_eq_floor hcv.2
      have hxv := hx v
      have e1 : 2 * (o v).re / x v - 2 * (o' v).re / x v = 2 * ((o v).re - (o' v).re) / x v := by
        ring
      have e2 : 2 * (o v).im / x v - 2 * (o' v).im / x v = 2 * ((o v).im - (o' v).im) / x v := by
        ring
      rw [e1, abs_div, abs_mul, abs_of_pos hxv, div_lt_one hxv] at hre
      rw [e2, abs_div, abs_mul, abs_of_pos hxv, div_lt_one hxv] at him
      have h3 := Complex.norm_le_abs_re_add_abs_im ((o - o') v)
      simp only [Pi.sub_apply, Complex.sub_re, Complex.sub_im] at h3 ⊢
      norm_num at hre him
      linarith
    linarith

  have hpt : ∀ o ∈ S, ∏ v, min 1 ((x v / ‖o v‖) ^ K)
      ≤ (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * ∏ v, (psi (c o v).1 * psi (c o v).2) := by
    intro o ho
    have hno : ∀ v, 0 < ‖o v‖ := fun v => norm_pos_iff.mpr (hne o ho v)
    have ht : ∀ v, 0 < x v / ‖o v‖ := fun v => div_pos (hx v) (hno v)
    calc ∏ v, min 1 ((x v / ‖o v‖) ^ K)
        ≤ ∏ v, ((x v / ‖o v‖) ^ ((K : ℝ) - 5 / 2) *
            ((min 1 (x v / ‖o v‖)) ^ (5 / 4 : ℝ) * (min 1 (x v / ‖o v‖)) ^ (5 / 4 : ℝ))) := by
          apply prod_le_prod
          · intro v _
            exact le_min zero_le_one (pow_nonneg (ht v).le _)
          · intro v _
            exact min_pow_le _ (ht v) K hK
      _ = (∏ v, (x v / ‖o v‖) ^ ((K : ℝ) - 5 / 2)) *
            ∏ v, ((min 1 (x v / ‖o v‖)) ^ (5 / 4 : ℝ) * (min 1 (x v / ‖o v‖)) ^ (5 / 4 : ℝ)) := by
          rw [prod_mul_distrib]
      _ ≤ (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * ∏ v, (psi (c o v).1 * psi (c o v).2) := by
          have hK' : (3 : ℝ) ≤ K := by exact_mod_cast hK
          apply mul_le_mul
          · rw [Real.finsetProd_rpow _ _ (fun v _ => (ht v).le)]
            apply Real.rpow_le_rpow (prod_nonneg fun v _ => (ht v).le) _ (by linarith)
            rw [prod_div_distrib]
            exact div_le_self (prod_nonneg fun v _ => (hx v).le) (hLa o (hS o ho).1 (hS o ho).2)
          · apply prod_le_prod
            · intro v _
              have h0 : 0 ≤ min 1 (x v / ‖o v‖) := le_min zero_le_one (ht v).le
              positivity
            · intro v _
              have h0 : 0 ≤ min 1 (x v / ‖o v‖) := le_min zero_le_one (ht v).le
              apply mul_le_mul
              · exact min_le_psi _ _ _ (hx v) (hno v) (Complex.abs_re_le_norm _)
              · exact min_le_psi _ _ _ (hx v) (hno v) (Complex.abs_im_le_norm _)
              · positivity
              · exact psi_nonneg _
          · exact prod_nonneg fun v _ =>
              mul_nonneg (Real.rpow_nonneg (le_min zero_le_one (ht v).le) _)
                (Real.rpow_nonneg (le_min zero_le_one (ht v).le) _)
          · exact Real.rpow_nonneg (prod_nonneg fun v _ => (hx v).le) _
  have hX0 : 0 ≤ (∏ v, x v) ^ ((K : ℝ) - 5 / 2) :=
    Real.rpow_nonneg (prod_nonneg fun v _ => (hx v).le) _
  calc ∑ o ∈ S, ∏ v, min 1 ((x v / ‖o v‖) ^ K)
      ≤ ∑ o ∈ S, (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * ∏ v, (psi (c o v).1 * psi (c o v).2) :=
        sum_le_sum hpt
    _ = (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * ∑ p ∈ S.image c, ∏ v, (psi (p v).1 * psi (p v).2) := by
        rw [← mul_sum, sum_image (fun a ha b hb h => hinj ha hb h)]
    _ ≤ (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * (D ^ 2) ^ f :=
        mul_le_mul_of_nonneg_left (cell_sum_le f _) hX0
    _ ≤ (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * ((D + 1) ^ 2) ^ f := by
        apply mul_le_mul_of_nonneg_left _ hX0
        apply pow_le_pow_left₀ (by positivity)
        nlinarith
    _ = ((D + 1) ^ 2) ^ f * (∏ v, x v) ^ ((K : ℝ) - 5 / 2) := mul_comm _ _

end Formalism.NuclearRankWeightBounds.P
