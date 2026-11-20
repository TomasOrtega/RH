import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsShiftedLtClassMin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBimultiplicativeOfSecondQuotConst
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.ValLat

/- English proof (translation)
Rewrite using `[← h.tsum_eq]`. Conclude with `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr hf`.
-/
theorem norm_le_of_hasSum {I C : Type} [NormedAddCommGroup C] [IsUltrametricDist C] {f : I → C} {a : C}
    (h : HasSum f a) {r : ℝ} (hr : 0 ≤ r) (hf : ∀ x, ‖f x‖ ≤ r) : ‖a‖ ≤ r := by
  rw [← h.tsum_eq]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr hf

/- English proof (translation)
Break down `(norm_nonneg (f b)).eq_or_lt with h0 | h0` into its components or cases. Rewrite using `[← h0]`. Conclude with `norm_nonneg _`. Choose the witnesses or unpack the hypotheses as in `⟨r, hr0, hrb, hr⟩ : ∃ r, 0 ≤ r ∧ r < ‖f b‖ ∧ ∀ x, x ≠ b → ‖f x‖ ≤ r := by`. Establish `ht` using `(tendsto_zero_iff_norm_tendsto_zero.1 h.summable.tendsto_cofinite_zero).eventually (gt_mem_nhds (half_pos h0))`.

Establish `hfin : {x | x ≠ b ∧ ‖f b‖ / 2 ≤ ‖f x‖}.Finite` using `(Filter.eventually_cofinite.1 ht).subset fun x hx => not_lt.2 hx.2`. Break down `Set.eq_empty_or_nonempty {x | x ≠ b ∧ ‖f b‖ / 2 ≤ ‖f x‖} with he | he` into its components or cases. Use `⟨‖f b‖ / 2, by positivity, half_lt_self h0, fun x hx => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Conclude with `(Set.eq_empty_iff_forall_notMem.1 he x) ⟨hx, (not_le.1 hc).le⟩`.

Take `⟨y, hy, hm⟩` from `Set.exists_max_image _ (fun x => ‖f x‖) hfin he`. Use `⟨‖f y‖, norm_nonneg _, hf y hy.1, fun x hx => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hc : ‖f b‖ / 2 ≤ ‖f x‖`. Conclude with `hm x ⟨hx, hc⟩`. Conclude with `(not_le.1 hc).le.trans hy.2`.

Establish `h1` using `norm_le_of_hasSum (h.update b 0) hr0 fun x => by`. Break down `eq_or_ne x b with rfl | hx` into its components or cases. Simplify using `using hr0`. Rewrite using `[Function.update_of_ne hx]`. Conclude with `hr x hx`.

Assume the negation of the conclusion as `hc`. Establish `h2` using `IsUltrametricDist.norm_add_le_max a (-(0 - f b + a))`. Rewrite `h2` using `[norm_neg, show a + -(0 - f b + a) = f b by abel]`. Conclude with `h2.not_gt (max_lt (not_le.1 hc) (h1.trans_lt hrb))`.
-/
theorem le_norm_of_hasSum {I C : Type} [NormedAddCommGroup C] [IsUltrametricDist C] {f : I → C} {a : C}
    (h : HasSum f a) {b : I} (hf : ∀ x, x ≠ b → ‖f x‖ < ‖f b‖) : ‖f b‖ ≤ ‖a‖ := by
  rcases (norm_nonneg (f b)).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  obtain ⟨r, hr0, hrb, hr⟩ : ∃ r, 0 ≤ r ∧ r < ‖f b‖ ∧ ∀ x, x ≠ b → ‖f x‖ ≤ r := by
    have ht := (tendsto_zero_iff_norm_tendsto_zero.1 h.summable.tendsto_cofinite_zero).eventually
      (gt_mem_nhds (half_pos h0))
    have hfin : {x | x ≠ b ∧ ‖f b‖ / 2 ≤ ‖f x‖}.Finite :=
      (Filter.eventually_cofinite.1 ht).subset fun x hx => not_lt.2 hx.2
    rcases Set.eq_empty_or_nonempty {x | x ≠ b ∧ ‖f b‖ / 2 ≤ ‖f x‖} with he | he
    · refine ⟨‖f b‖ / 2, by positivity, half_lt_self h0, fun x hx => ?_⟩
      by_contra hc
      exact (Set.eq_empty_iff_forall_notMem.1 he x) ⟨hx, (not_le.1 hc).le⟩
    · obtain ⟨y, hy, hm⟩ := Set.exists_max_image _ (fun x => ‖f x‖) hfin he
      refine ⟨‖f y‖, norm_nonneg _, hf y hy.1, fun x hx => ?_⟩
      by_cases hc : ‖f b‖ / 2 ≤ ‖f x‖
      · exact hm x ⟨hx, hc⟩
      · exact (not_le.1 hc).le.trans hy.2
  have h1 := norm_le_of_hasSum (h.update b 0) hr0 fun x => by
    rcases eq_or_ne x b with rfl | hx
    · simpa using hr0
    · rw [Function.update_of_ne hx]; exact hr x hx
  by_contra hc
  have h2 := IsUltrametricDist.norm_add_le_max a (-(0 - f b + a))
  rw [norm_neg, show a + -(0 - f b + a) = f b by abel] at h2
  exact h2.not_gt (max_lt (not_le.1 hc) (h1.trans_lt hrb))

/- English proof (translation)
Introduce `X _ _ _ q g N J cls p _ w ν hq hg hN _ ⟨t, κ, hκ, hsum, hcls, hsz⟩ ⟨i₀, hi₀, hmax⟩`. Establish `hQ` using `GlobalTheory.posDef_realExt_of_tendsto q hq`. Establish `hN0 : (0 : ℝ) < N` using `lt_trans (by positivity) hN`. Take `⟨m, hm⟩` from `ClassMin.exists_global_min (ClassMin.realExtension_eq_realExt q ▸ hQ) ν one_pos`. Simplify using `only [div_one] at hm`.

Set `ν' : X →+ ℝ` to `ν + (QuadraticMap.polarBilin q m).toAddMonoidHom`. Establish `hν' : ∀ x, ν' x = ν x + QuadraticMap.polar q m x` using `fun x => rfl`. Distinguish the cases in `h0 : ν' = 0`. Use `⟨-m, fun α => ?_⟩` and prove the remaining obligations. Use `hν' α` as an intermediate fact.

Rewrite `this` using `[h0]`. Rewrite using `[QuadraticMap.polar_neg_left]`. Simplify using `only [AddMonoidHom.zero_apply] at this`. Combine the linear equalities and inequalities to obtain the conclusion. It suffices to derive a contradiction.

Take `⟨α, -, h1, h2⟩` from `ClassMin.exists_shifted_lt_of_le (N := (N : ℤ)) hg hQ (by exact_mod_cast hN) h0 fun y => by`. Use `hm (m + y)` as an intermediate fact. Rewrite `this` using `[map_add ν]`. Rewrite using `[hν', QuadraticMap.polar]`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `only [natCast_zsmul, Int.cast_natCast] at h1 h2`. Establish `hshift : ∀ x, q (x + N • m) / N + ν (x + N • m) = q x / N + ν' x + N * (q m + ν m)` using `fun x => by`. Establish `e` using `ClassMin.map_add_zsmul q x m (N : ℤ)`. Rewrite `e` using `[natCast_zsmul]`. Rewrite using `[e, hν', map_add, map_nsmul, nsmul_eq_mul, QuadraticMap.polar_comm q m x]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨i, hi⟩` from `(hsz (α + N • m)).2`. Take `⟨u, hu⟩` from `hcls (α + N • m) i (by`.

Rewrite using `[← norm_pos_iff, hi]`. Use the proof step `positivity)`. Establish `hA : ‖t (α + N • m) i‖ ≤ ‖w i‖` using `le_norm_of_hasSum (f := fun x => t x i) (hsum i) fun x hx => by`. Distinguish the cases in `hz : t x i = 0`. Rewrite using `[hz, norm_zero, hi]`.

Check the signs of the components of the expression. Take `⟨v, hv⟩` from `hcls x i hz`. Establish `e : x = α + N • (v - u) + N • m`. Rewrite using `[hv, add_right_comm, hu, smul_sub]`. Normalize the expressions using the abelian group laws.

Establish `h3` using `h1 (v - u) fun h => hx (by rw [e, h, smul_zero, add_zero])`. Use `((hsz x).1 i).trans_lt ?_` and prove the remaining obligations. Rewrite using `[hi]`. Use `mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 ?_) hκ` and prove the remaining obligations. Establish `e1` using `hshift (α + N • (v - u))`.

Rewrite `e1` using `[← e]`. Establish `e2` using `hshift α`. Rewrite using `[sub_div, sub_div]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB : ‖w i₀‖ ≤ κ * Real.exp (-(N * (q m + ν m)))` using `norm_le_of_hasSum (hsum i₀) (by positivity) fun x => by`.

Distinguish the cases in `hz : t x i₀ = 0`. Rewrite using `[hz, norm_zero]`. Check the signs of the components of the expression. Take `⟨v, hv⟩` from `hcls x i₀ hz`. Use `((hsz x).1 i₀).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hκ.le)` and prove the remaining obligations.

Establish `e` using `ClassMin.shifted_zsmul (Q := q) (N := (N : ℤ)) (by exact_mod_cast hN0.ne') ν v`. Simplify using `only [natCast_zsmul, Int.cast_natCast] at e`. Rewrite using `[hv, hi₀, zero_add, map_zero, sub_zero, e]`. Conclude with `neg_le_neg (mul_le_mul_of_nonneg_left (hm v) hN0.le)`. Establish `hC` using `(hA.trans (hmax i)).trans hB`.

Rewrite `hC` using `[hi]`. Establish `hD` using `Real.exp_le_exp.1 (le_of_mul_le_mul_left hC hκ)`. Establish `h3` using `h2 (m - u)`. Establish `e : α + N • (m - u) = cls i`. Rewrite using `[smul_sub, ← add_sub_assoc, hu]`.

Normalize the expressions using the abelian group laws. Rewrite `h3` using `[e]`. Establish `e2` using `hshift α`. Rewrite `hD` using `[sub_div]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem main : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (q : QuadraticMap ℤ X ℝ) (g N : ℕ) (J : Type) (cls : J → X) (p : ℕ) [Fact p.Prime] (w : J → PadicAlgCl p) (ν : X →+ ℝ), Filter.Tendsto q Filter.cofinite Filter.atTop → Module.finrank ℤ X ≤ g → 1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < N → (∀ i, Short q N (cls i)) → Ser q N cls w ν → (∃ i₀, cls i₀ = 0 ∧ ∀ i, ‖w i‖ ≤ ‖w i₀‖) → ∃ m, ∀ α, ν α = QuadraticMap.polar q m α := by
  intro X _ _ _ q g N J cls p _ w ν hq hg hN _ ⟨t, κ, hκ, hsum, hcls, hsz⟩ ⟨i₀, hi₀, hmax⟩
  have hQ := GlobalTheory.posDef_realExt_of_tendsto q hq
  have hN0 : (0 : ℝ) < N := lt_trans (by positivity) hN
  obtain ⟨m, hm⟩ := ClassMin.exists_global_min (ClassMin.realExtension_eq_realExt q ▸ hQ) ν one_pos
  simp only [div_one] at hm
  let ν' : X →+ ℝ := ν + (QuadraticMap.polarBilin q m).toAddMonoidHom
  have hν' : ∀ x, ν' x = ν x + QuadraticMap.polar q m x := fun x => rfl
  by_cases h0 : ν' = 0
  · refine ⟨-m, fun α => ?_⟩
    have := hν' α
    rw [h0] at this
    rw [QuadraticMap.polar_neg_left]
    simp only [AddMonoidHom.zero_apply] at this
    linarith
  exfalso
  obtain ⟨α, -, h1, h2⟩ := ClassMin.exists_shifted_lt_of_le (N := (N : ℤ)) hg hQ (by exact_mod_cast hN) h0
    fun y => by
      have := hm (m + y)
      rw [map_add ν] at this
      rw [hν', QuadraticMap.polar]
      linarith
  simp only [natCast_zsmul, Int.cast_natCast] at h1 h2
  have hshift : ∀ x, q (x + N • m) / N + ν (x + N • m) = q x / N + ν' x + N * (q m + ν m) := fun x => by
    have e := ClassMin.map_add_zsmul q x m (N : ℤ)
    rw [natCast_zsmul] at e
    rw [e, hν', map_add, map_nsmul, nsmul_eq_mul, QuadraticMap.polar_comm q m x]
    push_cast
    field_simp
    ring
  obtain ⟨i, hi⟩ := (hsz (α + N • m)).2
  obtain ⟨u, hu⟩ := hcls (α + N • m) i (by
    rw [← norm_pos_iff, hi]; positivity)
  have hA : ‖t (α + N • m) i‖ ≤ ‖w i‖ := le_norm_of_hasSum (f := fun x => t x i) (hsum i) fun x hx => by
    by_cases hz : t x i = 0
    · rw [hz, norm_zero, hi]; positivity
    obtain ⟨v, hv⟩ := hcls x i hz
    have e : x = α + N • (v - u) + N • m := by
      rw [hv, add_right_comm, hu, smul_sub]; abel
    have h3 := h1 (v - u) fun h => hx (by rw [e, h, smul_zero, add_zero])
    refine ((hsz x).1 i).trans_lt ?_
    rw [hi]
    refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 ?_) hκ
    have e1 := hshift (α + N • (v - u))
    rw [← e] at e1
    have e2 := hshift α
    rw [sub_div, sub_div]
    linarith
  have hB : ‖w i₀‖ ≤ κ * Real.exp (-(N * (q m + ν m))) := norm_le_of_hasSum (hsum i₀) (by positivity) fun x => by
    by_cases hz : t x i₀ = 0
    · rw [hz, norm_zero]; positivity
    obtain ⟨v, hv⟩ := hcls x i₀ hz
    refine ((hsz x).1 i₀).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hκ.le)
    have e := ClassMin.shifted_zsmul (Q := q) (N := (N : ℤ)) (by exact_mod_cast hN0.ne') ν v
    simp only [natCast_zsmul, Int.cast_natCast] at e
    rw [hv, hi₀, zero_add, map_zero, sub_zero, e]
    exact neg_le_neg (mul_le_mul_of_nonneg_left (hm v) hN0.le)
  have hC := (hA.trans (hmax i)).trans hB
  rw [hi] at hC
  have hD := Real.exp_le_exp.1 (le_of_mul_le_mul_left hC hκ)
  have h3 := h2 (m - u)
  have e : α + N • (m - u) = cls i := by
    rw [smul_sub, ← add_sub_assoc, hu]; abel
  rw [e] at h3
  have e2 := hshift α
  rw [sub_div] at hD
  linarith

end GlobalTheory.ZH.ValLat
