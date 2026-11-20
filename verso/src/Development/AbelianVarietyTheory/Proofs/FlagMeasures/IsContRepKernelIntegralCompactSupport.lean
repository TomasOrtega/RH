import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightConvolutionOperatorAeEqIntegralAdelic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnfoldKernel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicKernelConvergencePropertiesStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.KernelContRep

/- English proof (translation)
Establish `: IsFiniteMeasure (ν.restrict C)` using `⟨by simpa using hC.measure_lt_top⟩`. Establish `hi : Integrable y ν` using `IntegrableOn.integrable_of_ae_notMem_eq_zero (s := C) ((hy.restrict C).integrable one_le_two) h0`. Establish `hc : ∀ x, Continuous fun z => K x z` using `fun x => hK.comp (Continuous.prodMk_right x)`. Use `continuous_iff_continuousAt.2 fun x₀ => ?_` and prove the remaining obligations. Take `⟨U, hU, hx⟩` from `exists_compact_mem_nhds x₀`.

Take `⟨M, hM⟩` from `(hU.prod hC).exists_bound_of_continuousOn hK.continuousOn`. Use `continuousAt_of_dominated (bound := fun z => M * ‖y z‖) ?_ ?_ (hi.norm.const_mul M) ?_` and prove the remaining obligations. Conclude with `Filter.Eventually.of_forall fun x => (hc x).aestronglyMeasurable.mul hi.1`. Use `filter_upwards [hx] with x hxU filter_upwards [h0] with z hz`. Distinguish the cases in `hzC : z ∈ C`.

Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hM (x, z) ⟨hxU, hzC⟩) (norm_nonneg _)`. Simplify using `[hz hzC]`. Conclude with `Filter.Eventually.of_forall fun z => ((hK.comp (Continuous.prodMk_left z)).mul continuous_const).continuousAt`.
-/
theorem continuous_integral_kernel {X Z : Type} [TopologicalSpace X] [LocallyCompactSpace X]
    [FirstCountableTopology X] [TopologicalSpace Z] [T2Space Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasureOnCompacts ν] (K : X → Z → ℂ)
    (hK : Continuous fun p : X × Z => K p.1 p.2) (y : Z → ℂ) (hy : MemLp y 2 ν) (C : Set Z)
    (hC : IsCompact C) (h0 : ∀ᵐ z ∂ν, z ∉ C → y z = 0) :
    Continuous fun x => ∫ z, K x z * y z ∂ν := by
  have : IsFiniteMeasure (ν.restrict C) := ⟨by simpa using hC.measure_lt_top⟩
  have hi : Integrable y ν :=
    IntegrableOn.integrable_of_ae_notMem_eq_zero (s := C) ((hy.restrict C).integrable one_le_two) h0
  have hc : ∀ x, Continuous fun z => K x z := fun x => hK.comp (Continuous.prodMk_right x)
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨U, hU, hx⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := (hU.prod hC).exists_bound_of_continuousOn hK.continuousOn
  refine continuousAt_of_dominated (bound := fun z => M * ‖y z‖) ?_ ?_ (hi.norm.const_mul M) ?_
  · exact Filter.Eventually.of_forall fun x => (hc x).aestronglyMeasurable.mul hi.1
  · filter_upwards [hx] with x hxU
    filter_upwards [h0] with z hz
    by_cases hzC : z ∈ C
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM (x, z) ⟨hxU, hzC⟩) (norm_nonneg _)
    · simp [hz hzC]
  · exact Filter.Eventually.of_forall fun z =>
      ((hK.comp (Continuous.prodMk_left z)).mul continuous_const).continuousAt

/- English proof (translation)
Establish `h2 : ∀ᵐ z ∂(B.I.muA B.μf), ∀ γ ∈ B.I.GFset, γ ≠ 1 → γ * z ∉ (fun y => γ * y) '' B.fund ∩ B.fund`. Use `(ae_ball_iff (GlobalTheory.RatDiscrete.countable_GFset B.I)).2 fun γ hγ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : γ = 1`. Conclude with `Filter.Eventually.of_forall fun z h => absurd h1 h`. Use `filter_upwards [(GlobalTheory.AdelicUnfold.measurePreserving_left B.I B.μf γ).quasiMeasurePreserving.ae (measure_eq_zero_iff_ae_notMem.1 (B.fund_spec.2.2 γ hγ h1))] with z hz _`.

Conclude with `hz`. Use `filter_upwards [ae_restrict_of_ae h2, ae_restrict_mem B.fund_spec.1] with z hz hzf`. Establish `h` using `B.fund_spec.2.1 z`. Establish `e : B.I.rep B.fund z = h.choose * z`. Unfold `AutInst.rep`.

Conclude with `dif_pos h`. Establish `e1 : h.choose = 1`. Assume the negation of the conclusion as `hne`. Conclude with `hz _ h.choose_spec.1 hne ⟨⟨z, hzf, rfl⟩, h.choose_spec.2⟩`. Use `show (y : B.I.GA → ℂ) (B.I.rep B.fund z) = _`.

Rewrite using `[e, e1, one_mul]`.
-/
theorem ext_ae_eq_on_fund (B : RowsAut) (y : B.I.L2 B.μf B.fund) :
    B.I.ext y =ᵐ[(B.I.muA B.μf).restrict B.fund] (y : B.I.GA → ℂ) := by
  have h2 : ∀ᵐ z ∂(B.I.muA B.μf), ∀ γ ∈ B.I.GFset, γ ≠ 1 →
      γ * z ∉ (fun y => γ * y) '' B.fund ∩ B.fund := by
    refine (ae_ball_iff (GlobalTheory.RatDiscrete.countable_GFset B.I)).2 fun γ hγ => ?_
    by_cases h1 : γ = 1
    · exact Filter.Eventually.of_forall fun z h => absurd h1 h
    · filter_upwards [(GlobalTheory.AdelicUnfold.measurePreserving_left B.I B.μf γ).quasiMeasurePreserving.ae
        (measure_eq_zero_iff_ae_notMem.1 (B.fund_spec.2.2 γ hγ h1))] with z hz _
      exact hz
  filter_upwards [ae_restrict_of_ae h2, ae_restrict_mem B.fund_spec.1] with z hz hzf
  have h := B.fund_spec.2.1 z
  have e : B.I.rep B.fund z = h.choose * z := by
    unfold AutInst.rep; exact dif_pos h
  have e1 : h.choose = 1 := by
    by_contra hne
    exact hz _ h.choose_spec.1 hne ⟨⟨z, hzf, rfl⟩, h.choose_spec.2⟩
  show (y : B.I.GA → ℂ) (B.I.rep B.fund z) = _
  rw [e, e1, one_mul]

/- English proof (translation)
Introduce `B d h hd hn hl hb T hT y C hC h0`. Take `⟨-, hK, hinv, -⟩` from `hA B d h hd hn hl hb`. Take `⟨hT2, hL, hS, -⟩` from `GlobalTheory.CongTop.adelic_topology B.I`. Establish `: BorelSpace B.I.GA` using `inferInstance`. Establish `: IsFiniteMeasureOnCompacts (B.I.muA B.μf)`.

Unfold `AutInst.muA`. Use `infer_instance`. Use `⟨?_, fun γ hγ x => ?_, ?_⟩` and prove the remaining obligations. Conclude with `continuous_integral_kernel _ (kern B.I (phe B d)) hK _ (Lp.memLp y) C hC h0`. Simplify using `only [(hinv γ hγ _ _).1]`.

Take `⟨h1, h2⟩` from `GlobalTheory.ConvKernel.rconv_eq_integral B _ T hT y`. Establish `h3` using `((GlobalTheory.RightRegFund.rightReg_unitary_continuous B).2.2.2.2 y).1`. Use `filter_upwards [h1, h2] with x hx1 hx2`. Rewrite using `[hx2, (GlobalTheory.AdelicUnfold.integral_unfold_kernel B _ _ x h3 hx1).2]`. Use `integral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [ext_ae_eq_on_fund B y] with z hz`. Rewrite using `[hz]`.
-/
theorem isContRep_of_kernel (hA : KernelA) : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (C : Set B.I.GA), IsCompact C → (∀ᵐ z ∂((B.I.muA B.μf).restrict B.fund), z ∉ C → (y : B.I.GA → ℂ) z = 0) → IsContRep B (T y) (fun x => ∫ z in B.fund, kern B.I (phe B d) x z * (y : B.I.GA → ℂ) z ∂(B.I.muA B.μf)) := by
  intro B d h hd hn hl hb T hT y C hC h0
  obtain ⟨-, hK, hinv, -⟩ := hA B d h hd hn hl hb
  obtain ⟨hT2, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  have : BorelSpace B.I.GA := inferInstance
  have : IsFiniteMeasureOnCompacts (B.I.muA B.μf) := by
    unfold AutInst.muA; infer_instance
  refine ⟨?_, fun γ hγ x => ?_, ?_⟩
  · exact continuous_integral_kernel _ (kern B.I (phe B d)) hK _ (Lp.memLp y) C hC h0
  · simp only [(hinv γ hγ _ _).1]
  · obtain ⟨h1, h2⟩ := GlobalTheory.ConvKernel.rconv_eq_integral B _ T hT y
    have h3 := ((GlobalTheory.RightRegFund.rightReg_unitary_continuous B).2.2.2.2 y).1
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx2, (GlobalTheory.AdelicUnfold.integral_unfold_kernel B _ _ x h3 hx1).2]
    refine integral_congr_ae ?_
    filter_upwards [ext_ae_eq_on_fund B y] with z hz
    rw [hz]

/- English proof (translation)
The claim follows from `isContRep_of_kernel GlobalTheory.T.automorphicKernel_convergence_properties`.
-/
theorem isContRep_integral_kernel : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (C : Set B.I.GA), IsCompact C → (∀ᵐ z ∂((B.I.muA B.μf).restrict B.fund), z ∉ C → (y : B.I.GA → ℂ) z = 0) → IsContRep B (T y) (fun x => ∫ z in B.fund, kern B.I (phe B d) x z * (y : B.I.GA → ℂ) z ∂(B.I.muA B.μf)) :=
  isContRep_of_kernel GlobalTheory.T.automorphicKernel_convergence_properties

end GlobalTheory.KernelContRep
