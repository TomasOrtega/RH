import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarIntAdd
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

namespace VarIntAdd

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

A detailed English derivation is pending.
-/
theorem ringKrullDim_eq_of_injective_finite {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hinj : Function.Injective f) (hfin : f.Finite) : ringKrullDim S = ringKrullDim R := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hfin.to_isIntegral⟩
  apply le_antisymm
  · have hg : StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
      intro q₁ q₂ hq
      have hlt : q₁.asIdeal < q₂.asIdeal := hq
      obtain ⟨hle, x, hx2, hx1⟩ := SetLike.lt_iff_le_and_exists.mp hlt
      show q₁.asIdeal.comap (algebraMap R S) < q₂.asIdeal.comap (algebraMap R S)
      exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hx2, hx1⟩
        (Algebra.IsIntegral.isIntegral x)
    exact Order.krullDim_le_of_strictMono _ hg
  · refine iSup_le fun l => ?_
    have hker : (⊥ : Ideal S).comap (algebraMap R S) ≤ (RelSeries.head l).asIdeal := by
      intro r hr
      have : f r = 0 := hr
      rw [show r = 0 from hinj (by rw [this, map_zero])]
      exact Ideal.zero_mem _
    obtain ⟨P, -, hP, hPo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral _ ⊥ hker
    have : P.LiesOver (RelSeries.head l).asIdeal := ⟨hPo.symm⟩
    obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    exact le_iSup_of_le L (by rw [hlen])

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem ringKrullDim_of_isFiniteProjection {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin k) (Fin n) ℂ} (hA : IsFiniteProjection J A) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = k := by
  rw [ringKrullDim_eq_of_injective_finite (projHom J A).toRingHom hA.injective hA.finite,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem chartDens_add {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin k) (Fin n) ℂ}
    (hfin : ∀ y, (fibre J A y).Finite) (f g : (Fin n → ℂ) → ℝ) (φ : Fin k → (Fin n → ℂ) → ℝ) :
    chartDens J A (f + g) φ = chartDens J A f φ + chartDens J A g φ := by
  funext y
  simp only [chartDens, sheetSum, Pi.add_apply]
  rw [← finsum_mem_add_distrib (hfin y)]
  refine finsum_mem_congr rfl fun x _ => ?_
  split_ifs <;> ring

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem abs_chartDens_le {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin k) (Fin n) ℂ}
    (hfin : ∀ y, (fibre J A y).Finite) (w : (Fin n → ℂ) → ℝ) (φ : Fin k → (Fin n → ℂ) → ℝ)
    (y : Fin k → ℂ) : |chartDens J A w φ y| ≤ chartAbsDens J A w φ y := by
  simp only [chartDens, chartAbsDens, sheetSum]
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
  split_ifs <;> simp

end VarIntAdd

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem VarIntAdd.proof (hCM : ChartMassCompact.Statement) : VarIntAdd.Statement := by
  intro n k J f g φ hJ hfc hfs hgc hgs hφ
  unfold varInt
  split_ifs with h
  · set A := h.choose
    have hA : IsFiniteProjection J A := h.choose_spec
    have hd := VarIntAdd.ringKrullDim_of_isFiniteProjection hA
    have hfin : ∀ y, (fibre J A y).Finite := fun y => (FibreBound.proof n k J A hJ hd hA y).2.1
    have hint : ∀ w : (Fin n → ℂ) → ℝ, Continuous w → HasCompactSupport w →
        Integrable (chartDens J A w φ) := by
      intro w hwc hws
      have hm := SheetSumMeasurable.proof n k J A w φ hJ hd hA hwc.measurable hφ
      refine (hCM n k J A w φ hJ hd hA hwc.continuousOn hφ (Or.inl hws)).mono'
        hm.1.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs]
      exact VarIntAdd.abs_chartDens_le hfin w φ y
    unfold chartInt
    rw [VarIntAdd.chartDens_add hfin, integral_add' (hint f hfc hfs) (hint g hgc hgs)]
  · simp

end

end GroundTheory.Heights₂.Heights
