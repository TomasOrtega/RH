import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TchOfIntegral
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormEqOfNormSubLt

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation

open Polynomial Finset

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Use `monic_X_pow_add (lt_of_le_of_lt (degree_sum_le _ _) ((Finset.sup_lt_iff (WithBot.bot_lt_coe d)).2 ?_))` and prove the remaining obligations. Introduce `i hi`. Conclude with `(degree_C_mul_X_pow_le i (a i)).trans_lt (WithBot.coe_lt_coe.2 (mem_range.1 hi))`.
-/
theorem monic_X_pow_add_sum {R : Type*} [CommRing R] [Nontrivial R] (d : ℕ) (a : ℕ → R) :
    (X ^ d + ∑ i ∈ range d, C (a i) * X ^ i).Monic := by
  refine monic_X_pow_add
    (lt_of_le_of_lt (degree_sum_le _ _) ((Finset.sup_lt_iff (WithBot.bot_lt_coe d)).2 ?_))
  intro i hi
  exact (degree_C_mul_X_pow_le i (a i)).trans_lt (WithBot.coe_lt_coe.2 (mem_range.1 hi))

/- English proof (translation)
Use `set x : ℤ_[l] := ⟨a, ha⟩ with hxdef`. Take `⟨n, hn⟩` from `PadicInt.denseRange_natCast.exists_dist_lt x one_pos`. Establish `hxa : (x : ℚ_[l]) = a` using `rfl`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite `hn` using `[dist_eq_norm, PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast, hxa]`.

Conclude with `hn`.
-/
theorem exists_nat_near (a : ℚ_[l]) (ha : ‖a‖ ≤ 1) : ∃ n : ℕ, ‖a - n‖ < 1 := by
  set x : ℤ_[l] := ⟨a, ha⟩ with hxdef
  obtain ⟨n, hn⟩ := PadicInt.denseRange_natCast.exists_dist_lt x one_pos
  have hxa : (x : ℚ_[l]) = a := rfl
  refine ⟨n, ?_⟩
  rw [dist_eq_norm, PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast, hxa] at hn
  exact hn

/- English proof (translation)
Use `set P := minpoly ℚ_[l] y with hPdef`. Establish `hint : IsIntegral ℚ_[l] y` using `(Algebra.IsAlgebraic.isAlgebraic y).isIntegral`. Establish `hmon : P.Monic` using `minpoly.monic hint`. Establish `hcoef : ∀ i, ‖P.coeff i‖ ≤ 1`. Establish `h1 : spectralValue P ≤ 1`.

Establish `: spectralNorm ℚ_[l] (PadicAlgCl l) y = ‖y‖` using `PadicAlgCl.spectralNorm_eq l y`. Rewrite `this` using `[spectralNorm]`. Rewrite using `[hPdef, this]`. Conclude with `hy`. Conclude with `(spectralValue_le_one_iff hmon).1 h1`.

Use `choose c hc using fun i => exists_nat_near l (P.coeff i) (hcoef i)`. Use `⟨P.natDegree, c, ?_⟩` and prove the remaining obligations. Use `set z : ℂ_[l] := (y : ℂ_[l]) with hz`. Establish `hP0 : aeval z P = 0`. Rewrite using `[hz, PadicComplex.coe_eq, aeval_algebraMap_apply, minpoly.aeval, map_zero]`.

Establish `hPsum : aeval z P = z ^ P.natDegree + ∑ i ∈ range P.natDegree, algebraMap ℚ_[l] ℂ_[l] (P.coeff i) * z ^ i` using `by conv_lhs => rw [hmon.as_sum]`. Simplify using `[map_add, map_sum, aeval_X, aeval_C]`. Establish `he : (X ^ P.natDegree + ∑ i ∈ range P.natDegree, C ((c i : ℕ) : ℂ_[l]) * X ^ i).eval z = ∑ i ∈ range P.natDegree, algebraMap ℚ_[l] ℂ_[l] ((c i : ℚ_[l]) - P.coeff i) * z ^ i`. Establish `: (X ^ P.natDegree + ∑ i ∈ range P.natDegree, C ((c i : ℕ) : ℂ_[l]) * X ^ i).eval z = (X ^ P.natDegree + ∑ i ∈ range P.natDegree, C ((c i : ℕ) : ℂ_[l]) * X ^ i).eval z - aeval z P` using `by rw [hP0, sub_zero]`. Rewrite using `[this, hPsum]`.

Simplify using `only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_natCast, map_sub, map_natCast, sub_mul, sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Establish `hz1 : ‖z‖ ≤ 1` using `by rw [hz, PadicComplex.norm_extends]; exact hy`. Rewrite using `[he]`. Take `⟨i, hi, hle⟩` from `IsUltrametricDist.exists_norm_finsetSum_le (range P.natDegree) (fun i => algebraMap ℚ_[l] ℂ_[l] ((c i : ℚ_[l]) - P.coeff i) * z ^ i)`.

Use `lt_of_le_of_lt hle ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_algebraMap', norm_pow, norm_sub_rev]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz1)) (hc i)`.
-/
theorem exists_nat_poly_near (y : PadicAlgCl l) (hy : ‖y‖ ≤ 1) :
    ∃ d : ℕ, ∃ c : ℕ → ℕ, ‖((X ^ d + ∑ i ∈ range d, C ((c i : ℕ) : ℂ_[l]) * X ^ i).eval
      (y : ℂ_[l]))‖ < 1 := by
  set P := minpoly ℚ_[l] y with hPdef
  have hint : IsIntegral ℚ_[l] y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have hmon : P.Monic := minpoly.monic hint
  have hcoef : ∀ i, ‖P.coeff i‖ ≤ 1 := by
    have h1 : spectralValue P ≤ 1 := by
      have : spectralNorm ℚ_[l] (PadicAlgCl l) y = ‖y‖ := PadicAlgCl.spectralNorm_eq l y
      rw [spectralNorm] at this
      rw [hPdef, this]; exact hy
    exact (spectralValue_le_one_iff hmon).1 h1
  choose c hc using fun i => exists_nat_near l (P.coeff i) (hcoef i)
  refine ⟨P.natDegree, c, ?_⟩
  set z : ℂ_[l] := (y : ℂ_[l]) with hz
  have hP0 : aeval z P = 0 := by
    rw [hz, PadicComplex.coe_eq, aeval_algebraMap_apply, minpoly.aeval, map_zero]
  have hPsum : aeval z P = z ^ P.natDegree +
      ∑ i ∈ range P.natDegree, algebraMap ℚ_[l] ℂ_[l] (P.coeff i) * z ^ i := by
    conv_lhs => rw [hmon.as_sum]
    simp [map_add, map_sum, aeval_X, aeval_C]
  have he : (X ^ P.natDegree + ∑ i ∈ range P.natDegree, C ((c i : ℕ) : ℂ_[l]) * X ^ i).eval z =
      ∑ i ∈ range P.natDegree, algebraMap ℚ_[l] ℂ_[l] ((c i : ℚ_[l]) - P.coeff i) * z ^ i := by
    have : (X ^ P.natDegree + ∑ i ∈ range P.natDegree, C ((c i : ℕ) : ℂ_[l]) * X ^ i).eval z =
        (X ^ P.natDegree + ∑ i ∈ range P.natDegree, C ((c i : ℕ) : ℂ_[l]) * X ^ i).eval z -
          aeval z P := by rw [hP0, sub_zero]
    rw [this, hPsum]
    simp only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_natCast, map_sub,
      map_natCast, sub_mul, sum_sub_distrib]
    ring
  have hz1 : ‖z‖ ≤ 1 := by rw [hz, PadicComplex.norm_extends]; exact hy
  rw [he]
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le (range P.natDegree)
    (fun i => algebraMap ℚ_[l] ℂ_[l] ((c i : ℚ_[l]) - P.coeff i) * z ^ i)
  refine lt_of_le_of_lt hle ?_
  rw [norm_mul, norm_algebraMap', norm_pow, norm_sub_rev]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz1))
    (hc i)

end ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve Polynomial
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Take `⟨y, hy⟩` from `UniformSpace.Completion.denseRange_coe.exists_dist_lt x one_pos`. Rewrite `hy` using `[dist_eq_norm]`. Establish `hy1 : ‖y‖ ≤ 1`. Rewrite using `[← PadicComplex.norm_extends]`. Combine the equalities or inequalities in the displayed calculation.

Use `IsUltrametricDist.norm_add_le_max x (-(x - (y : ℂ_[l])))` as an intermediate fact. Rewrite `this` using `[← sub_eq_add_neg, norm_neg]`. Then use the resulting hypothesis. Use `_ ≤ 1 := max_le hx hy.le`. Take `⟨d, c, hQ⟩` from `ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.exists_nat_poly_near l y hy1`. Use `set Q' : (Rmu l)[X] := X ^ d + ∑ i ∈ Finset.range d, C ((c i : ℕ) : Rmu l) * X ^ i with hQ'`.

Establish `hmon : Q'.Monic` using `ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.monic_X_pow_add_sum d (fun i => ((c i : ℕ) : Rmu l))`. Establish `hmap : Q'.map (algebraMap (Rmu l) ℂ_[l]) = X ^ d + ∑ i ∈ Finset.range d, C ((c i : ℕ) : ℂ_[l]) * X ^ i`. Rewrite using `[hQ', Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_natCast]`. Take `⟨α, hroot, hα⟩` from `ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.exists_root_near l (X ^ d + ∑ i ∈ Finset.range d, C ((c i : ℕ) : ℂ_[l]) * X ^ i) (by rw [← hmap]; exact hmon.map _) (y : ℂ_[l]) hQ`. Establish `hint : IsIntegral (Rmu l) α` using `⟨Q', hmon, by rw [eval₂_eq_eval_map, hmap]; exact hroot⟩`. Take `⟨ξ, hξ, hξα⟩` from `tch_of_integral l α hint`. Use `⟨ξ, hξ, ?_⟩` and prove the remaining obligations.

Establish `e : x - ξ = (x - y) + ((y - α) + (α - ξ))` using `by ring`. Rewrite using `[e]`. Use `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hy ?_)` and prove the remaining obligations. Conclude with `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hα hξα)`.
-/
theorem res_full (x : ℂ_[l]) (hx : ‖x‖ ≤ 1) : ∃ ξ ∈ Tch l, ‖x - ξ‖ < 1 := by
  obtain ⟨y, hy⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt x one_pos
  rw [dist_eq_norm] at hy
  have hy1 : ‖y‖ ≤ 1 := by
    rw [← PadicComplex.norm_extends]
    calc ‖(y : ℂ_[l])‖ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
      _ ≤ max ‖x‖ ‖x - y‖ := by
        have := IsUltrametricDist.norm_add_le_max x (-(x - (y : ℂ_[l])))
        rwa [← sub_eq_add_neg, norm_neg] at this
      _ ≤ 1 := max_le hx hy.le
  obtain ⟨d, c, hQ⟩ := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.exists_nat_poly_near l y hy1
  set Q' : (Rmu l)[X] := X ^ d + ∑ i ∈ Finset.range d, C ((c i : ℕ) : Rmu l) * X ^ i with hQ'
  have hmon : Q'.Monic := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.monic_X_pow_add_sum d (fun i => ((c i : ℕ) : Rmu l))
  have hmap : Q'.map (algebraMap (Rmu l) ℂ_[l]) =
      X ^ d + ∑ i ∈ Finset.range d, C ((c i : ℕ) : ℂ_[l]) * X ^ i := by
    rw [hQ', Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_natCast]
  obtain ⟨α, hroot, hα⟩ := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.exists_root_near l
    (X ^ d + ∑ i ∈ Finset.range d, C ((c i : ℕ) : ℂ_[l]) * X ^ i)
    (by rw [← hmap]; exact hmon.map _) (y : ℂ_[l]) hQ
  have hint : IsIntegral (Rmu l) α := ⟨Q', hmon, by rw [eval₂_eq_eval_map, hmap]; exact hroot⟩
  obtain ⟨ξ, hξ, hξα⟩ := tch_of_integral l α hint
  refine ⟨ξ, hξ, ?_⟩
  have e : x - ξ = (x - y) + ((y - α) + (α - ξ)) := by ring
  rw [e]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hy ?_)
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hα hξα)

end ReciprocityTheory.ChartRestriction.L1
