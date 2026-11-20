import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyMulLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyOfSigmaOnlyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinConstantTermPartDifferentiableOnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaTotallyRealAtMostSimplePoleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinZeroFrequencyPartIsSmoothHolomorpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinNonconstantFourierSumSmoothHolomoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoContinuationEqLatticeSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinWeightTwoQExpansionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnHilbertEisensteinWeightTwoSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoConstantTermEqPartialZetaNegOneStatement

noncomputable section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

/- English proof (translation)
Introduce `hFE F _ _ _ hf 𝔞 𝔟`. Establish `hD0 : (differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) ∈ (Ideal (𝓞 F))⁰` using `mem_nonZeroDivisors_of_ne_zero (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))`. Set `D : (Ideal (𝓞 F))⁰` to `⟨_, hD0⟩`. Take `⟨Zb, Zb', hZb, hZb', hFEb⟩` from `hFE F (ClassGroup.mk F 𝔟)⁻¹ (ClassGroup.mk0 D * ClassGroup.mk F 𝔟) D rfl (by rw [mul_comm, mul_inv_cancel_right])`. Take `⟨R, hR, hZR⟩` from `GlobalTheory.T.partialZeta_totallyReal_at_most_simple_pole F _ _ Zb Zb' hZb hZb' hFEb`.

Take `⟨Za, Za', hZa, hZa', hFEa⟩` from `hFE F (ClassGroup.mk0 D * ClassGroup.mk F 𝔞) (ClassGroup.mk F 𝔞)⁻¹ D rfl (mul_inv_cancel_right _ _)`. Establish `hgood : IsGood (gFun Zb 𝔞 𝔟)` using `GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_add F _ _ (GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_add F _ _ (GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_of_sigma_only F _ (GlobalTheory.T.heckeEisensteinConstantTermPart_differentiableOn F 𝔞)) (GlobalTheory.T.heckeEise …`. Establish `hdF : 0 < dF F` using `abs_pos.2 (by exact_mod_cast discr_ne_zero F)`. Establish `hcK : (cK F 2 : ℂ) ≠ 0`. Establish `: 0 < cK F 2` using `by unfold cK; positivity`.

Conclude with `this.ne'` after adjusting the coercions. Establish `hω : (omegaFactor 𝔞 : ℂ) ≠ 0`. Establish `hn : 0 < nrm 𝔞`. Unfold `nrm`. Establish `h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0`.

Rewrite using `[Ne, FractionalIdeal.absNorm_eq_zero_iff]`. Conclude with `𝔞.ne_zero`. Establish `h3` using `lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) h2.symm`. Conclude with `h3` after adjusting the coercions. Establish `: 0 < omegaFactor 𝔞` using `by unfold omegaFactor; positivity`.

Conclude with `this.ne'` after adjusting the coercions. Establish `hG0 : ∀ z, gFun Zb 𝔞 𝔟 0 z = aPart 𝔞 0 + kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z`. Introduce `z`. Simplify using `[gFun, bZero]`. Establish `hB : ∀ z ∈ upperHalf F, kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z = (∑' c, qClass 𝔞 𝔟 2 z c) * (omegaFactor 𝔞 : ℂ) ^ 2 / (cK F 2 : ℂ)`.

Introduce `z hz`. Rewrite using `[← (GlobalTheory.T.heckeEisenstein_weight_two_qExpansion F 𝔞 𝔟 z hz).2]`. Clear the denominators using the available nonvanishing facts. Use `⟨gFun Zb 𝔞 𝔟, ⟨fun σ hσ z hz => GlobalTheory.T.heckeWeightTwoContinuation_eq_latticeSeries F 𝔞 𝔟 Zb hZb σ hσ z hz, hgood.1, hgood.2⟩, ?_, ?_⟩` and prove the remaining obligations. Use `DifferentiableOn.congr (f := fun z => aPart 𝔞 0 + (∑' c, qClass 𝔞 𝔟 2 z c) * ((omegaFactor 𝔞 : ℂ) ^ 2 / (cK F 2 : ℂ))) ?_ fun z hz => by rw [hG0, hB z hz, mul_div_assoc]` and prove the remaining obligations.

Apply `DifferentiableOn.const_add` to reduce the goal to its premises. Apply `DifferentiableOn.mul_const` to reduce the goal to its premises. Conclude with `GlobalTheory.T.differentiableOn_hilbertEisensteinWeightTwoSeries F 𝔞 𝔟`. Use `⟨Za', hZa', fun z hz => ⟨(GlobalTheory.T.heckeEisenstein_weight_two_qExpansion F 𝔞 𝔟 z hz).1, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hG0, mul_add, add_div, GlobalTheory.T.heckeWeightTwo_constantTerm_eq_partialZeta_neg_one F 𝔞 _ D Za Za' rfl (mul_inv_cancel_right _ _) hZa hZa' hFEa, (GlobalTheory.T.heckeEisenstein_weight_two_qExpansion F 𝔞 𝔟 z hz).2]`.
-/
theorem GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe : GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo := by
  intro hFE F _ _ _ hf 𝔞 𝔟
  have hD0 : (differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) ∈ (Ideal (𝓞 F))⁰ :=
    mem_nonZeroDivisors_of_ne_zero (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  let D : (Ideal (𝓞 F))⁰ := ⟨_, hD0⟩
  obtain ⟨Zb, Zb', hZb, hZb', hFEb⟩ := hFE F (ClassGroup.mk F 𝔟)⁻¹ (ClassGroup.mk0 D * ClassGroup.mk F 𝔟) D rfl
    (by rw [mul_comm, mul_inv_cancel_right])
  obtain ⟨R, hR, hZR⟩ := GlobalTheory.T.partialZeta_totallyReal_at_most_simple_pole F _ _ Zb Zb' hZb hZb' hFEb
  obtain ⟨Za, Za', hZa, hZa', hFEa⟩ := hFE F (ClassGroup.mk0 D * ClassGroup.mk F 𝔞) (ClassGroup.mk F 𝔞)⁻¹ D rfl
    (mul_inv_cancel_right _ _)
  have hgood : IsGood (gFun Zb 𝔞 𝔟) :=
    GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_add F _ _ (GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_add F _ _ (GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_of_sigma_only F _ (GlobalTheory.T.heckeEisensteinConstantTermPart_differentiableOn F 𝔞)) (GlobalTheory.T.heckeEisensteinZeroFrequencyPart_isSmoothHolomorphic F hf 𝔞 𝔟 Zb R hR hZR))
      (GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_mul_left F _ _ ((kFac_differentiable.mul_const _).differentiableOn) (GlobalTheory.T.heckeEisensteinNonconstantFourierSum_smoothHolomorphic F 𝔞 𝔟))
  have hdF : 0 < dF F := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  have hcK : (cK F 2 : ℂ) ≠ 0 := by
    have : 0 < cK F 2 := by unfold cK; positivity
    exact_mod_cast this.ne'
  have hω : (omegaFactor 𝔞 : ℂ) ≠ 0 := by
    have hn : 0 < nrm 𝔞 := by
      unfold nrm
      have h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
        rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
      have h3 := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) h2.symm
      exact_mod_cast h3
    have : 0 < omegaFactor 𝔞 := by unfold omegaFactor; positivity
    exact_mod_cast this.ne'
  have hG0 : ∀ z, gFun Zb 𝔞 𝔟 0 z = aPart 𝔞 0 + kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z := by
    intro z; simp [gFun, bZero]
  have hB : ∀ z ∈ upperHalf F, kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z =
      (∑' c, qClass 𝔞 𝔟 2 z c) * (omegaFactor 𝔞 : ℂ) ^ 2 / (cK F 2 : ℂ) := by
    intro z hz
    rw [← (GlobalTheory.T.heckeEisenstein_weight_two_qExpansion F 𝔞 𝔟 z hz).2]
    field_simp
  refine ⟨gFun Zb 𝔞 𝔟, ⟨fun σ hσ z hz => GlobalTheory.T.heckeWeightTwoContinuation_eq_latticeSeries F 𝔞 𝔟 Zb hZb σ hσ z hz, hgood.1, hgood.2⟩, ?_, ?_⟩
  · refine DifferentiableOn.congr (f := fun z => aPart 𝔞 0 + (∑' c, qClass 𝔞 𝔟 2 z c) * ((omegaFactor 𝔞 : ℂ) ^ 2 / (cK F 2 : ℂ)))
      ?_ fun z hz => by rw [hG0, hB z hz, mul_div_assoc]
    apply DifferentiableOn.const_add
    apply DifferentiableOn.mul_const
    exact GlobalTheory.T.differentiableOn_hilbertEisensteinWeightTwoSeries F 𝔞 𝔟
  · refine ⟨Za', hZa', fun z hz => ⟨(GlobalTheory.T.heckeEisenstein_weight_two_qExpansion F 𝔞 𝔟 z hz).1, ?_⟩⟩
    rw [hG0, mul_add, add_div, GlobalTheory.T.heckeWeightTwo_constantTerm_eq_partialZeta_neg_one F 𝔞 _ D Za Za' rfl (mul_inv_cancel_right _ _) hZa hZa' hFEa,
      (GlobalTheory.T.heckeEisenstein_weight_two_qExpansion F 𝔞 𝔟 z hz).2]
