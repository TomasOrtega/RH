import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpLiftL2DiscreteQuotientOnCompactStatement

open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.AutomorphicL2KernelIntegral

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[aestronglyMeasurable_quotMeasure_iff_lift, (leftInv_orbitSum h).lift_descend]`. Establish `hm : ∀ γ : Γ, AEMeasurable (fun x => h (γ * x)) μ` using `fun γ => hh.1.aemeasurable.comp_quasiMeasurePreserving (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving`. Conclude with `(AEMeasurable.tsum hm).aestronglyMeasurable`. Establish `h1` using `lintegral_eq_lintegral_tsum (Γ := Γ) hh.1.enorm`.

Use `lt_of_le_of_lt ?_ (h1.symm.trans_lt hh.2)` and prove the remaining obligations. Conclude with `lintegral_mono fun q => enorm_tsum_le_tsum_enorm`.
-/
theorem integrable_descend_orbitSum {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {μ : Measure G} [μ.IsMulLeftInvariant] {h : G → ℂ} (hh : Integrable h μ) :
    Integrable (descend Γ (orbitSum Γ h)) (quotMeasure Γ μ) := by
  refine ⟨?_, ?_⟩
  · rw [aestronglyMeasurable_quotMeasure_iff_lift, (leftInv_orbitSum h).lift_descend]
    have hm : ∀ γ : Γ, AEMeasurable (fun x => h (γ * x)) μ := fun γ =>
      hh.1.aemeasurable.comp_quasiMeasurePreserving (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving
    exact (AEMeasurable.tsum hm).aestronglyMeasurable
  · have h1 := lintegral_eq_lintegral_tsum (Γ := Γ) hh.1.enorm
    refine lt_of_le_of_lt ?_ (h1.symm.trans_lt hh.2)
    exact lintegral_mono fun q => enorm_tsum_le_tsum_enorm

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ Γ _ μ _ _ f hf hc F x`. Establish `hf' : Continuous fun y => f (x⁻¹ * y)` using `hf.comp (continuous_const_mul _)`. Establish `hc' : HasCompactSupport fun y => f (x⁻¹ * y)` using `hc.comp_homeomorph (Homeomorph.mulLeft x⁻¹)`. Establish `hloc : LocallyIntegrable (lift Γ F) μ` using `(locallyIntegrable_iff).2 fun C hC => (GlobalTheory.T.memLp_lift_L2DiscreteQuotient_on_compact G Γ μ F C hC).2`. Establish `hi : Integrable (fun y => f (x⁻¹ * y) * lift Γ F y) μ` using `hloc.integrable_smul_left_of_hasCompactSupport hf' hc'`.

Establish `key : descend Γ (orbitSum Γ fun y => f (x⁻¹ * y) * lift Γ F y) = fun q => kernelQ Γ f (mk Γ x) q * F q`. Use function extensionality and compare the values at `q`. Proceed by induction on `q using Quotient.inductionOn with`. Consider the case `h y`. Use `((leftInv_orbitSum _).descend_mk y).trans ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = kernelQ Γ f (mk Γ x) (mk Γ y) * F (mk Γ y)`. Rewrite using `[kernelQ_mk, kernel_eq_orbitSum, orbitSum, orbitSum, ← tsum_mul_right]`. Conclude with `tsum_congr fun γ => congrArg (fun z => _ * F z) (mk_mul γ y)`. Use `⟨key ▸ integrable_descend_orbitSum hi, ?_⟩` and prove the remaining obligations. Rewrite using `[convR_eq, integral_eq_integral_orbitSum (Γ := Γ) hi, key]`.
-/
theorem convR_eq_integral_kernelQ : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    ∀ f : G → ℂ, Continuous f → HasCompactSupport f → ∀ (F : L2 Γ μ) (x : G),
      Integrable (fun q => kernelQ Γ f (mk Γ x) q * F q) (quotMeasure Γ μ) ∧
        convR μ f (lift Γ F) x = ∫ q, kernelQ Γ f (mk Γ x) q * F q ∂quotMeasure Γ μ := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ f hf hc F x
  have hf' : Continuous fun y => f (x⁻¹ * y) := hf.comp (continuous_const_mul _)
  have hc' : HasCompactSupport fun y => f (x⁻¹ * y) := hc.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
  have hloc : LocallyIntegrable (lift Γ F) μ :=
    (locallyIntegrable_iff).2 fun C hC => (GlobalTheory.T.memLp_lift_L2DiscreteQuotient_on_compact G Γ μ F C hC).2
  have hi : Integrable (fun y => f (x⁻¹ * y) * lift Γ F y) μ :=
    hloc.integrable_smul_left_of_hasCompactSupport hf' hc'
  have key : descend Γ (orbitSum Γ fun y => f (x⁻¹ * y) * lift Γ F y) =
      fun q => kernelQ Γ f (mk Γ x) q * F q := by
    funext q
    induction q using Quotient.inductionOn with
    | h y =>
      refine ((leftInv_orbitSum _).descend_mk y).trans ?_
      change _ = kernelQ Γ f (mk Γ x) (mk Γ y) * F (mk Γ y)
      rw [kernelQ_mk, kernel_eq_orbitSum, orbitSum, orbitSum, ← tsum_mul_right]
      exact tsum_congr fun γ => congrArg (fun z => _ * F z) (mk_mul γ y)
  refine ⟨key ▸ integrable_descend_orbitSum hi, ?_⟩
  rw [convR_eq, integral_eq_integral_orbitSum (Γ := Γ) hi, key]

end GlobalTheory.AutomorphicL2KernelIntegral
