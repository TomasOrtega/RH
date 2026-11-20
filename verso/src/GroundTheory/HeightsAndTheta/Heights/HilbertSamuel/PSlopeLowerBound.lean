import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibre
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsRank
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDegreePositive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

namespace SlopeLowerBound

/- English proof (translation)
Establish `hcast : (D : ℝ) - 1 = ((D - 1 : ℕ) : ℝ)` using `by rw [Nat.cast_sub hD, Nat.cast_one]`. Establish `h1 : (fun n : ℕ => ((n : ℝ) + 1) ^ ((D : ℝ) - 1)) = fun n : ℕ => ((n : ℝ) + 1) ^ (D - 1)`. Use function extensionality and compare the values at `n`. Rewrite using `[hcast, Real.rpow_natCast]`. Rewrite using `[h1]`.

Establish `hO : (fun n : ℕ => ((n : ℝ) + 1) ^ (D - 1)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (D - 1)`. Use `IsBigO.of_bound (2 ^ (D - 1)) ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop 1] with n hn`. Establish `hn' : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Rewrite using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), ← mul_pow]`.

Conclude with `pow_le_pow_left₀ (by positivity) (by linarith) _`. Conclude with `hO.trans_isLittleO ((isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (show D - 1 < D by omega)).comp_tendsto tendsto_natCast_atTop_atTop)`.
-/
theorem succ_rpow_isLittleO (D : ℕ) (hD : 1 ≤ D) :
    (fun n : ℕ => ((n : ℝ) + 1) ^ ((D : ℝ) - 1)) =o[atTop] fun n : ℕ => (n : ℝ) ^ D := by
  have hcast : (D : ℝ) - 1 = ((D - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hD, Nat.cast_one]
  have h1 : (fun n : ℕ => ((n : ℝ) + 1) ^ ((D : ℝ) - 1)) = fun n : ℕ => ((n : ℝ) + 1) ^ (D - 1) := by
    funext n; rw [hcast, Real.rpow_natCast]
  rw [h1]
  have hO : (fun n : ℕ => ((n : ℝ) + 1) ^ (D - 1)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (D - 1) := by
    refine IsBigO.of_bound (2 ^ (D - 1)) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
      ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  exact hO.trans_isLittleO ((isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (show D - 1 < D by omega)).comp_tendsto
    tendsto_natCast_atTop_atTop)

/- English proof (translation)
Introduce `D Ω _ _ κ _ I d hI ε hε`. Take `⟨hqP, hqd⟩` from `hGen Ω κ d.x D d.arith`. Take `⟨C, hC⟩` from `hRank κ ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ))) D hqP hqd`. Establish `hδ0` using `hPos ℚ κ ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ))) D hqP hqd`. Establish `hg : genDeg (ι` using `GlobalTheory κ) (coordIdeal ℤ d.x) D 1 = GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ : Fin D => fun _ => (1 : ℤ)) := by`.

Unfold `genDeg`. Use `rfl` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules. Establish `hδ : (0 : ℝ) < (genDeg (ι` using `GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) := by rw [hg]; exact_mod_cast hδ0`. Establish `hrank : ∀ n : ℕ, |(Module.finrank ℤ (sec ℤ d.x n) : ℝ) - (genDeg (ι` using `GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) * (n : ℝ) ^ D / D.factorial| ≤ C * ((n : ℝ) + 1) ^ ((D : ℝ) - 1) := by`.

Introduce `n`. Establish `e : (GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι` using `GlobalTheory κ) ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ => (n : ℤ)) : ℝ) = (Module.finrank ℤ (sec ℤ d.x n) : ℝ) := by exact_mod_cast hRk Ω κ d.x n`. Rewrite using `[← e, hg]`. Conclude with `hC n`. Use `set δ : ℝ := (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) with hδdef`.

Use `set T : ℝ := top I d.x d.m D with hTdef`. Use `set r : ℕ → ℝ := fun n => (Module.finrank ℤ (sec ℤ d.x n) : ℝ) with hrdef`. Establish `hfD : (0 : ℝ) < D.factorial` using `by exact_mod_cast Nat.factorial_pos D`. Establish `hfac : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial`. Rewrite using `[Nat.factorial_succ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `set c : ℝ := T / (((D : ℝ) + 1) * δ) with hcdef`. Establish `hR : (fun n : ℕ => r n - δ * (n : ℝ) ^ D / D.factorial) =o[atTop] fun n : ℕ => (n : ℝ) ^ D`. Use `IsBigO.trans_isLittleO ?_ (succ_rpow_isLittleO D d.one_le)` and prove the remaining obligations.

Use `IsBigO.of_bound C (Eventually.of_forall fun n => ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]`. Conclude with `hrank n`. Establish `hH : (fun n : ℕ => resChi d n - T * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =o[atTop] pw D` using `(hHSM D Ω κ I d hI).1`. Establish `hE : (fun n : ℕ => resChi d n - c * n * r n) =o[atTop] pw D`.

Establish `h2 : (fun n : ℕ => (c * (n : ℝ)) * (r n - δ * (n : ℝ) ^ D / D.factorial)) =o[atTop] pw D`. Use `(((isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).const_mul_left c).mul_isLittleO hR).congr (fun _ => rfl) ?_` and prove the remaining obligations. Introduce `n`. Simplify using `only [pw]`. Expand and normalize the polynomial expressions, which then agree.

Use `(hH.sub h2).congr (fun n => ?_) (fun _ => rfl)` and prove the remaining obligations. Rewrite using `[hcdef, hfac]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hlow : ∀ᶠ n : ℕ in atTop, δ / (2 * D.factorial) * (n : ℝ) ^ D ≤ r n` using `by filter_upwards [hR.def (show 0 < δ / (2 * D.factorial) by positivity)] with n hn`.

Rewrite `hn` using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ D)]`. Establish `h1` using `neg_abs_le (r n - δ * (n : ℝ) ^ D / D.factorial)`. Establish `e : δ * (n : ℝ) ^ D / D.factorial = 2 * (δ / (2 * D.factorial) * (n : ℝ) ^ D)`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.

Use `filter_upwards [hlow, hE.def (show 0 < ε * (δ / (2 * D.factorial)) by positivity), eventually_ge_atTop 1] with n hn hEn hn1`. Establish `hn1' : (1 : ℝ) ≤ n` using `by exact_mod_cast hn1`. Establish `hrpos : 0 < r n` using `lt_of_lt_of_le (by positivity) hn`. Rewrite `hEn` using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ pw D n)]`. Establish `hslope : T * n / (((D : ℝ) + 1) * δ) = c * n` using `by rw [hcdef]; ring`.

Use `show T * n / (((D : ℝ) + 1) * δ) - ε * n ≤ resChi d n / r n`. Rewrite using `[hslope, le_div_iff₀ hrpos]`. Establish `h1 : ε * n * (δ / (2 * D.factorial) * (n : ℝ) ^ D) ≤ ε * n * r n` using `mul_le_mul_of_nonneg_left hn (by positivity)`. Establish `h2` using `neg_abs_le (resChi d n - c * n * r n)`. Establish `h4 : ε * (δ / (2 * D.factorial)) * pw D n = ε * n * (δ / (2 * D.factorial) * (n : ℝ) ^ D)`.

Simplify using `only [pw]`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem proof (hHSM : TheoremHSM.Statement) (hRank : RankOfSections.Statement)
    (hGen : GenericFibre.Statement) (hRk : SectionsRank.Statement) (hPos : DegreePositive.Statement) :
    SlopeLowerBound.Statement := by
  intro D Ω _ _ κ _ I d hI ε hε
  obtain ⟨hqP, hqd⟩ := hGen Ω κ d.x D d.arith
  obtain ⟨C, hC⟩ := hRank κ ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ))) D hqP hqd
  have hδ0 := hPos ℚ κ ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ))) D hqP hqd
  have hg : genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 =
      GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ)))
        (fun _ : Fin D => fun _ => (1 : ℤ)) := by
    unfold genDeg
    convert rfl
    simp
  have hδ : (0 : ℝ) < (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) := by rw [hg]; exact_mod_cast hδ0
  have hrank : ∀ n : ℕ, |(Module.finrank ℤ (sec ℤ d.x n) : ℝ) -
      (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) * (n : ℝ) ^ D / D.factorial| ≤
        C * ((n : ℝ) + 1) ^ ((D : ℝ) - 1) := by
    intro n
    have e : (GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory κ)
        ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ => (n : ℤ)) : ℝ) =
        (Module.finrank ℤ (sec ℤ d.x n) : ℝ) := by exact_mod_cast hRk Ω κ d.x n
    rw [← e, hg]
    exact hC n
  set δ : ℝ := (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) with hδdef
  set T : ℝ := top I d.x d.m D with hTdef
  set r : ℕ → ℝ := fun n => (Module.finrank ℤ (sec ℤ d.x n) : ℝ) with hrdef
  have hfD : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  have hfac : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  set c : ℝ := T / (((D : ℝ) + 1) * δ) with hcdef

  have hR : (fun n : ℕ => r n - δ * (n : ℝ) ^ D / D.factorial) =o[atTop] fun n : ℕ => (n : ℝ) ^ D := by
    refine IsBigO.trans_isLittleO ?_ (succ_rpow_isLittleO D d.one_le)
    refine IsBigO.of_bound C (Eventually.of_forall fun n => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact hrank n

  have hH : (fun n : ℕ => resChi d n - T * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =o[atTop] pw D :=
    (hHSM D Ω κ I d hI).1

  have hE : (fun n : ℕ => resChi d n - c * n * r n) =o[atTop] pw D := by
    have h2 : (fun n : ℕ => (c * (n : ℝ)) * (r n - δ * (n : ℝ) ^ D / D.factorial)) =o[atTop] pw D := by
      refine (((isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).const_mul_left c).mul_isLittleO hR).congr
        (fun _ => rfl) ?_
      intro n; simp only [pw]; ring
    refine (hH.sub h2).congr (fun n => ?_) (fun _ => rfl)
    rw [hcdef, hfac]
    field_simp
    ring

  have hlow : ∀ᶠ n : ℕ in atTop, δ / (2 * D.factorial) * (n : ℝ) ^ D ≤ r n := by
    filter_upwards [hR.def (show 0 < δ / (2 * D.factorial) by positivity)] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ D)] at hn
    have h1 := neg_abs_le (r n - δ * (n : ℝ) ^ D / D.factorial)
    have e : δ * (n : ℝ) ^ D / D.factorial = 2 * (δ / (2 * D.factorial) * (n : ℝ) ^ D) := by
      field_simp
    linarith
  filter_upwards [hlow, hE.def (show 0 < ε * (δ / (2 * D.factorial)) by positivity), eventually_ge_atTop 1]
    with n hn hEn hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hrpos : 0 < r n := lt_of_lt_of_le (by positivity) hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ pw D n)] at hEn
  have hslope : T * n / (((D : ℝ) + 1) * δ) = c * n := by rw [hcdef]; ring
  show T * n / (((D : ℝ) + 1) * δ) - ε * n ≤ resChi d n / r n
  rw [hslope, le_div_iff₀ hrpos]
  have h1 : ε * n * (δ / (2 * D.factorial) * (n : ℝ) ^ D) ≤ ε * n * r n :=
    mul_le_mul_of_nonneg_left hn (by positivity)
  have h2 := neg_abs_le (resChi d n - c * n * r n)
  have h4 : ε * (δ / (2 * D.factorial)) * pw D n = ε * n * (δ / (2 * D.factorial) * (n : ℝ) ^ D) := by
    simp only [pw]; ring
  linarith

end SlopeLowerBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
