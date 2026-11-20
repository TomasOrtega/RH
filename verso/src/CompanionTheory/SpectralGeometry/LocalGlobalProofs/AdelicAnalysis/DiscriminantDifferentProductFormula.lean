import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix nonZeroDivisors

namespace GlobalTheory.CompanionTheory.SW.SelfDual

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem differentExp_finite (F : Type) [Field F] [NumberField F] :
    {v : HeightOneSpectrum (𝓞 F) | GroundTheory.Global.differentExp v ≠ 0}.Finite := by
  unfold GroundTheory.Global.differentExp
  exact Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors _)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem differentIdeal_int_ne_zero (F : Type) [Field F] [NumberField F] :
    differentIdeal ℤ (𝓞 F) ≠ 0 := by
  intro h
  have h1 := absNorm_differentIdeal F (𝓞 F)
  rw [h, map_zero] at h1
  exact discr_ne_zero F (Int.natAbs_eq_zero.1 h1.symm)

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
private theorem differentExp_eq_count_differentIdeal (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    GroundTheory.Global.differentExp v =
      ((Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 F))).factors : ℤ) := by
  unfold GroundTheory.Global.differentExp
  exact FractionalIdeal.count_coe F v (differentIdeal_int_ne_zero F)

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
private theorem prod_absNorm_pow_count_differentIdeal_eq_natAbs_discr (F : Type) [Field F] [NumberField F] :
    ∏ v ∈ (differentExp_finite F).toFinset, Ideal.absNorm v.asIdeal ^
      ((Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 F))).factors) =
      (discr F).natAbs := by
  have hprod := Ideal.finprod_heightOneSpectrum_factorization (differentIdeal_int_ne_zero F)
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := (differentExp_finite F).toFinset) ?_] at hprod
  · have hN := congrArg Ideal.absNorm hprod
    rw [map_prod, absNorm_differentIdeal F (𝓞 F)] at hN
    rw [← hN]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [HeightOneSpectrum.maxPowDividing, map_pow]
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq, differentExp_eq_count_differentIdeal]
    intro h0
    apply hv
    have h0' : (Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 F))).factors = 0 := by
      exact_mod_cast h0
    rw [HeightOneSpectrum.maxPowDividing, h0', pow_zero]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem sqrt_discr_mul_finprod_different (F : Type) [Field F] [NumberField F] :
    (∀ᶠ v in Filter.cofinite, (Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ≥0) ^ (((-GroundTheory.Global.differentExp v : ℤ) : ℝ) / 2) = 1) ∧ Real.toNNReal (Real.sqrt |(discr F : ℝ)|) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (((-GroundTheory.Global.differentExp v : ℤ) : ℝ) / 2) = 1 := by
  refine ⟨?_, ?_⟩
  · filter_upwards [FractionalIdeal.finite_factors (K := F)
      ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)] with v hv
    have hv' : GroundTheory.Global.differentExp v = 0 := hv
    rw [hv']
    simp
  · rw [finprod_eq_prod_of_mulSupport_subset _ (s := (differentExp_finite F).toFinset) ?_]
    · have hterm : ∀ v : HeightOneSpectrum (𝓞 F),
          (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (((-GroundTheory.Global.differentExp v : ℤ) : ℝ) / 2) =
            ((Ideal.absNorm v.asIdeal : ℝ≥0) ^
              ((Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 F))).factors)) ^
                (-(1 / 2 : ℝ)) := by
        intro v
        rw [differentExp_eq_count_differentIdeal, ← NNReal.rpow_natCast, ← NNReal.rpow_mul]
        congr 1
        push_cast
        ring
      rw [Finset.prod_congr rfl (fun v _ => hterm v), NNReal.finsetProd_rpow]
      have h := congrArg (fun n : ℕ => (n : ℝ≥0)) (prod_absNorm_pow_count_differentIdeal_eq_natAbs_discr F)
      simp only [Nat.cast_prod, Nat.cast_pow] at h
      rw [h]
      have ha0 : ((discr F).natAbs : ℝ≥0) ≠ 0 := by
        exact_mod_cast Int.natAbs_ne_zero.2 (discr_ne_zero F)
      have ha : (((discr F).natAbs : ℝ≥0) : ℝ) = |(discr F : ℝ)| := by
        rw [NNReal.coe_natCast, Nat.cast_natAbs, Int.cast_abs]
      rw [← ha, ← Real.coe_sqrt, Real.toNNReal_coe, NNReal.sqrt_eq_rpow, ← NNReal.rpow_add ha0]
      norm_num
    · intro v hv
      rw [Function.mem_mulSupport] at hv
      rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      intro h0
      exact hv (by rw [h0]; simp)

end GlobalTheory.CompanionTheory.SW.SelfDual
