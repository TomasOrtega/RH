import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpLiftL2DiscreteQuotientOnCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed
open scoped Pointwise

namespace GlobalTheory.RopRep

/- English proof (translation)
Introduce `D V μ _ _ f hf F`. Take `⟨hfc, hfs⟩` from `GlobalTheory.Orb.continuous_of_mem_ccAd hf`. Establish `hloc : LocallyIntegrable (lift (GQ V) F) μ` using `(locallyIntegrable_iff).2 fun C hC => (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F C hC).2`. Establish `hint : ∀ x, Integrable (fun y => f (x⁻¹ * y) * lift (GQ V) F y) μ` using `fun x => hloc.integrable_smul_left_of_hasCompactSupport (hfc.comp (continuous_const_mul _)) (hfs.comp_homeomorph (Homeomorph.mulLeft x⁻¹))`. Establish `hconv : (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) = convR μ f (lift (GQ V) F)`.

Use function extensionality and compare the values at `fun x => (convR_eq f _ x).symm`. Use `⟨hint, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `continuous_iff_continuousAt.2 fun x₀ => ?_` and prove the remaining obligations. Take `⟨K, hK, hKx⟩` from `exists_compact_mem_nhds x₀`. Take `⟨M, hM⟩` from `hfc.bounded_above_of_compact_support hfs`.

Establish `hC : IsCompact (K * tsupport f)` using `hK.mul hfs`. Establish `hCi : IntegrableOn (lift (GQ V) F) (K * tsupport f) μ` using `(GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F _ hC).2`. Use `continuousAt_of_dominated (bound := (K * tsupport f).indicator fun y => M * ‖lift (GQ V) F y‖) (.of_forall fun x => (hint x).1) ?_ ?_ (.of_forall fun y => ?_)` and prove the remaining obligations. Use `filter_upwards [hKx] with x hx`. Use `.of_forall fun y => ?_` and prove the remaining obligations.

Distinguish the cases in `hy : f (x⁻¹ * y) = 0`. Rewrite using `[hy, zero_mul, norm_zero]`. Conclude with `Set.indicator_nonneg (fun _ _ => mul_nonneg ((norm_nonneg _).trans (hM 1)) (norm_nonneg _)) _`. Establish `hmem : y ∈ K * tsupport f` using `⟨x, hx, x⁻¹ * y, subset_tsupport f hy, by simp⟩`. Rewrite using `[Set.indicator_of_mem hmem, norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)`. Conclude with `(integrable_indicator_iff hC.isClosed.measurableSet).2 (hCi.norm.const_mul M)`. Conclude with `((hfc.comp (continuous_inv.mul continuous_const)).mul continuous_const).continuousAt`. Rewrite using `[hconv]`. Conclude with `(leftInv_lift _).convR f`.

Rewrite using `[hconv]`. Conclude with `(GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR _ (GQ V) μ f (hfc.integrable_of_hasCompactSupport hfs) F).2`.
-/
theorem rop_rep : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ f ∈ CcGA V, ∀ F : DividedPowerChartLift V μ, (∀ x, Integrable (fun y => f (x⁻¹ * y) * lift (GQ V) F y) μ) ∧ Continuous (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) ∧ LeftInv (GQ V) (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) ∧ lift (GQ V) (RopG V μ f F) =ᵐ[μ] fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ := by
  intro D V μ _ _ f hf F
  obtain ⟨hfc, hfs⟩ := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  have hloc : LocallyIntegrable (lift (GQ V) F) μ :=
    (locallyIntegrable_iff).2 fun C hC => (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F C hC).2
  have hint : ∀ x, Integrable (fun y => f (x⁻¹ * y) * lift (GQ V) F y) μ := fun x =>
    hloc.integrable_smul_left_of_hasCompactSupport (hfc.comp (continuous_const_mul _))
      (hfs.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  have hconv : (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) = convR μ f (lift (GQ V) F) :=
    funext fun x => (convR_eq f _ x).symm
  refine ⟨hint, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun x₀ => ?_
    obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x₀
    obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support hfs
    have hC : IsCompact (K * tsupport f) := hK.mul hfs
    have hCi : IntegrableOn (lift (GQ V) F) (K * tsupport f) μ :=
      (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F _ hC).2
    refine continuousAt_of_dominated
      (bound := (K * tsupport f).indicator fun y => M * ‖lift (GQ V) F y‖)
      (.of_forall fun x => (hint x).1) ?_ ?_ (.of_forall fun y => ?_)
    · filter_upwards [hKx] with x hx
      refine .of_forall fun y => ?_
      by_cases hy : f (x⁻¹ * y) = 0
      · rw [hy, zero_mul, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => mul_nonneg ((norm_nonneg _).trans (hM 1)) (norm_nonneg _)) _
      · have hmem : y ∈ K * tsupport f :=
          ⟨x, hx, x⁻¹ * y, subset_tsupport f hy, by simp⟩
        rw [Set.indicator_of_mem hmem, norm_mul]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    · exact (integrable_indicator_iff hC.isClosed.measurableSet).2 (hCi.norm.const_mul M)
    · exact ((hfc.comp (continuous_inv.mul continuous_const)).mul continuous_const).continuousAt
  · rw [hconv]
    exact (leftInv_lift _).convR f
  · rw [hconv]
    exact (GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR _ (GQ V) μ f
      (hfc.integrable_of_hasCompactSupport hfs) F).2

end GlobalTheory.RopRep
