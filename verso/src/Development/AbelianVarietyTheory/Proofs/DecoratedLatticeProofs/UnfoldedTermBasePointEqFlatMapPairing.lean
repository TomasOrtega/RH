import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergIntegralFourierBesselBasePointEqPairinStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselThetaCharIntegrandLawsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalOrbitPointEqBesselBasePointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaIntegrandLocallyUniformMajorantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNormStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.FlatBase

variable {D : D7}

/- English proof (translation)
Establish `: IsTopologicalRing (AE D)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)`. Establish `ht : Continuous (Algebra.trace (AF D.host.F) (AE D))` using `IsModuleTopology.continuous_of_linearMap _`. Establish `hc : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hu : Continuous fun u : UX D ρ => upSum (u.1.1 : Mx D ρ ρ)`. Unfold `upSum`.

Use `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `(continuous_apply j).comp ((continuous_apply i).comp hc)`. Conclude with `continuous_const`. Conclude with `hψ.comp (ht.comp hu)`.
-/
theorem continuous_psiUni {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) (ρ : ℕ) :
    Continuous fun u : UX D ρ => psiUni ψ u.1 := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ) := Units.continuous_val.comp continuous_subtype_val
  have hu : Continuous fun u : UX D ρ => upSum (u.1.1 : Mx D ρ ρ) := by
    unfold upSum
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    split_ifs
    · exact (continuous_apply j).comp ((continuous_apply i).comp hc)
    · exact continuous_const
  exact hψ.comp (ht.comp hu)

/- English proof (translation)
Take `⟨t, htm, hMt, hσ⟩` from `hM.aefinStronglyMeasurable.exists_set_sigmaFinite`. Establish `h0 : ∀ᵐ u ∂ν, u ∈ tᶜ → M u = 0` using `(ae_restrict_iff' htm.compl).1 hMt`. Establish `hz : ∀ᵐ u ∂ν, u ∉ t → ∀ v, K u v = 0` using `h0.mono fun u hu hut v => by`. Establish `h` using `hb u v`. Rewrite `h` using `[hu hut, zero_mul]`.

Conclude with `norm_le_zero_iff.1 h`. Establish `e1 : ∫ u, ∫ v, K u v ∂μ ∂ν = ∫ u in t, ∫ v, K u v ∂μ ∂ν` using `(setIntegral_eq_integral_of_ae_compl_eq_zero (hz.mono fun u hu hut => by simp [hu hut])).symm`. Establish `e2 : (fun v => ∫ u, K u v ∂ν) = fun v => ∫ u in t, K u v ∂ν` using `funext fun v => (setIntegral_eq_integral_of_ae_compl_eq_zero (hz.mono fun u hu hut => hu hut v)).symm`. Rewrite using `[e1, e2]`. Use `haveI := hσ`.

Use `integral_integral_swap ?_` and prove the remaining obligations. Use `Integrable.mono' ((hM.restrict (s := t)).mul_prod (integrable_const C)) hK.aestronglyMeasurable ?_` and prove the remaining obligations. Conclude with `Filter.Eventually.of_forall fun p => hb p.1 p.2`.
-/
theorem integral_swap_of_majorant {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) (μ : Measure β) [IsFiniteMeasure μ] (K : α → β → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : α → ℝ) (hM : Integrable M ν) (C : ℝ)
    (hb : ∀ u v, ‖K u v‖ ≤ M u * C) :
    ∫ u, ∫ v, K u v ∂μ ∂ν = ∫ v, ∫ u, K u v ∂ν ∂μ := by
  obtain ⟨t, htm, hMt, hσ⟩ := hM.aefinStronglyMeasurable.exists_set_sigmaFinite
  have h0 : ∀ᵐ u ∂ν, u ∈ tᶜ → M u = 0 := (ae_restrict_iff' htm.compl).1 hMt
  have hz : ∀ᵐ u ∂ν, u ∉ t → ∀ v, K u v = 0 := h0.mono fun u hu hut v => by
    have h := hb u v
    rw [hu hut, zero_mul] at h
    exact norm_le_zero_iff.1 h
  have e1 : ∫ u, ∫ v, K u v ∂μ ∂ν = ∫ u in t, ∫ v, K u v ∂μ ∂ν :=
    (setIntegral_eq_integral_of_ae_compl_eq_zero (hz.mono fun u hu hut => by simp [hu hut])).symm
  have e2 : (fun v => ∫ u, K u v ∂ν) = fun v => ∫ u in t, K u v ∂ν := funext fun v =>
    (setIntegral_eq_integral_of_ae_compl_eq_zero (hz.mono fun u hu hut => hu hut v)).symm
  rw [e1, e2]
  haveI := hσ
  refine integral_integral_swap ?_
  refine Integrable.mono' ((hM.restrict (s := t)).mul_prod (integrable_const C)) hK.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun p => hb p.1 p.2

end GlobalTheory.FlatBase

namespace GlobalTheory.Unf.FB

open GlobalTheory.FlatBase

/- English proof (translation)
Introduce `D ψ σ J B s vb vL y Ψ hy hΨ`. Establish `hstd : IsStdChar D ψ (-1)` using `s.weil.std`. Establish `hchar` using `hstd.1`. Take `⟨-, ⟨My, hMy, -⟩, -, -, -, hlaw⟩` from `GlobalTheory.T.fourierBesselThetaCharIntegrand_laws D ψ hstd σ J B y hy`. Establish `hnorm : ∀ u : UX D (σ + 1), ‖psiUni ψ u.1‖ = 1` using `fun u => hchar.2.1 _`.

Establish `hfl : ∀ u : UX D (σ + 1), (∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (th J ψ B y) (x0 B) Ψ u b ∂vb.μ) = star (psiUni ψ u.1) * ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (x0 B ⬝ u.1.1) 0 ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ`. Introduce `u`. Establish `hf : Quasi ψ J.W₀ B.V (J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (x0 B ⬝ u.1.1))`. Establish `h` using `(GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hstd).1 J.W J.W₀ B.V (σ + 1) J.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ (x0 B ⬝ u.1.1)`. Conclude with `⟨h.quasi, h.cont⟩`.

Establish `hh` using `(GlobalTheory.T.heisenbergIntegral_fourierBesselBasePoint_eq_pairing D ψ hstd σ J.W₀ B vb s.vT vL _ y hf hy).1`. Combine the equalities or inequalities in the displayed calculation. Use `integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)` and prove the remaining obligations. Simplify using `only [flFun]`. Rewrite using `[hlaw b u.1 u.2]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by`. Rewrite using `[integral_const_mul]`. Conclude with `congrArg (star (psiUni ψ u.1) * ·) hh`. Establish `hLeft : fl ψ J.d B.V s.vS vb s.vU (th J ψ B y) (x0 B) Ψ = ∫ u, star (psiUni ψ u.1) * ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (x0 B ⬝ u.1.1) 0 ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ ∂s.vU.ν`.

Unfold `fl`. Conclude with `integral_congr_ae (Filter.Eventually.of_forall hfl)`. Take `⟨x, hxo, hx⟩` from `GlobalTheory.T.exists_mem_orb_rat_eq_x0 D σ B`. Take `⟨M, hMi, hMb⟩` from `GlobalTheory.T.flatThetaIntegrand_locallyUniform_majorant D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil s.vU x hxo.1 Ψ hΨ {1} isCompact_singleton`. Establish `hom1 : s.om 1 Ψ = Ψ` using `by rw [map_one]; rfl`.

Establish `hbound : ∀ (u : UX D (σ + 1)) (v : WO J.W₀ B.L), ‖flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v)‖ ≤ M u * My`. Introduce `u v`. Establish `h` using `hMb 1 (Set.mem_singleton 1) 0 ((B.o.resT J.W₀).symm (0, v)) u`. Rewrite `h` using `[hx, hom1]`. Rewrite using `[norm_mul, norm_star]`.

Conclude with `mul_le_mul h (hMy v) (norm_nonneg _) ((norm_nonneg _).trans h)`. Establish `: IsTopologicalRing (AE D)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)`. Establish `: BorelSpace (UX D (σ + 1))` using `⟨rfl⟩`. Establish `: BorelSpace (WO J.W₀ B.L)` using `⟨rfl⟩`. Establish `: SecondCountableTopology (WO J.W₀ B.L)` using `(lattice_Mx D B.L.rank J.W₀.rank).2.2.1`.

Establish `hE : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L => evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (x0 B ⬝ p.1.1.1) 0 ((B.o.resT J.W₀).symm (0, p.2))`. Establish `hmc` using `(GlobalTheory.T.weilMixedCoordinates_continuous_bounded_supNorm D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil Ψ hΨ).2`. Establish `hc : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L => (p.1.1.1 : Mx D (σ + 1) (σ + 1))` using `(Units.continuous_val.comp continuous_subtype_val).comp continuous_fst`. Establish `hin : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L => ((1 : GA D J.W × GA D B.V), x0 B ⬝ p.1.1.1, (0 : Mx D J.W₀.rank σ), (B.o.resT J.W₀).symm (0, p.2))` using `continuous_const.prodMk ((continuous_const.matrix_mul hc).prodMk (continuous_const.prodMk ((B.o.continuous_resT_symm J.W₀).comp (continuous_const.prodMk continuous_snd))))`. Establish `h` using `hmc.comp hin`.

Simplify `h` using `only [Function.comp_def, hom1]`. Establish `hK : Continuous (Function.uncurry fun (u : UX D (σ + 1)) (v : WO J.W₀ B.L) => flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v))` using `((continuous_star.comp ((continuous_psiUni hchar.1 (σ + 1)).comp continuous_fst)).mul hE).mul (continuous_star.comp (hy.2.comp continuous_snd))`. Use `haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) := isFiniteMeasure_restrict.2 (by rw [vL.covol.2.2]; simp)`. Establish `hswap` using `integral_swap_of_majorant s.vU.ν (vL.μ.restrict vL.𝓕) (fun u v => flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v)) hK.stronglyMeasurable M hMi My hbound`. Establish `h1 : fl ψ J.d B.V s.vS vb s.vU (th J ψ B y) (x0 B) Ψ = tFlat s vL y Ψ`.

Rewrite using `[hLeft]`. Combine the equalities or inequalities in the displayed calculation. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← integral_const_mul]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Simplify using `only [flatFun]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∫ v in vL.𝓕, ∫ u, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v) ∂s.vU.ν ∂vL.μ := hswap`. Use `_ = ∫ v in vL.𝓕, (∫ u, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u ∂s.vU.ν) * star (y v) ∂vL.μ := integral_congr_ae (Filter.Eventually.of_forall fun v => integral_mul_const _ _)`.

Use `_ = tFlat s vL y Ψ := rfl`. Use `⟨h1, fun Mb hMb' => ?_⟩` and prove the remaining obligations. Rewrite using `[← h1]`. Unfold `fl`. Combine the equalities or inequalities in the displayed calculation.

Use `lintegral_mono fun u => lintegral_mono fun b => ?_` and prove the remaining obligations. Simplify using `only [flFun]`. Rewrite using `[enorm_mul]`. Use `gcongr`. Rewrite using `[hlaw b u.1 u.2, ← ofReal_norm_eq_enorm, norm_mul, norm_star, norm_star, hnorm u, one_mul]`.

Conclude with `ENNReal.ofReal_le_ofReal (hMb' _)`. Use `_ = _ := (lintegral_congr fun u => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)`.
-/
theorem fl_base_eq_tFlat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vb : VolM D (σ + 1) J.W₀.rank) (vL : VolM D B.L.rank J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ), Quasi ψ J.W₀ B.L y → IsThetaFunO ψ J.W B.V Ψ → fl ψ J.d B.V s.vS vb s.vU (th J ψ B y) (x0 B) Ψ = tFlat s vL y Ψ ∧ ∀ M : ℝ, (∀ w, ‖y w‖ ≤ M) → ‖tFlat s vL y Ψ‖ₑ ≤ ENNReal.ofReal M * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (x0 B ⬝ u.1.1) (x0 B ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν := by
  intro D ψ σ J B s vb vL y Ψ hy hΨ
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  have hchar := hstd.1
  obtain ⟨-, ⟨My, hMy, -⟩, -, -, -, hlaw⟩ := GlobalTheory.T.fourierBesselThetaCharIntegrand_laws D ψ hstd σ J B y hy
  have hnorm : ∀ u : UX D (σ + 1), ‖psiUni ψ u.1‖ = 1 := fun u => hchar.2.1 _

  have hfl : ∀ u : UX D (σ + 1), (∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (th J ψ B y) (x0 B) Ψ u b ∂vb.μ) =
      star (psiUni ψ u.1) * ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (x0 B ⬝ u.1.1) 0
        ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ := by
    intro u
    have hf : Quasi ψ J.W₀ B.V (J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (x0 B ⬝ u.1.1)) := by
      have h := (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hstd).1 J.W J.W₀ B.V (σ + 1) J.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ (x0 B ⬝ u.1.1)
      exact ⟨h.quasi, h.cont⟩
    have hh := (GlobalTheory.T.heisenbergIntegral_fourierBesselBasePoint_eq_pairing D ψ hstd σ J.W₀ B vb s.vT vL _ y hf hy).1
    calc (∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (th J ψ B y) (x0 B) Ψ u b ∂vb.μ)
        = ∫ b in vb.𝓕, star (psiUni ψ u.1) * (J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (x0 B ⬝ u.1.1) (x0 B ⬝ b) *
            star (y (zl B ⬝ b))) ∂vb.μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
          simp only [flFun]
          rw [hlaw b u.1 u.2]
          ring
      _ = _ := by
          rw [integral_const_mul]
          exact congrArg (star (psiUni ψ u.1) * ·) hh
  have hLeft : fl ψ J.d B.V s.vS vb s.vU (th J ψ B y) (x0 B) Ψ = ∫ u, star (psiUni ψ u.1) *
      ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (x0 B ⬝ u.1.1) 0
        ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ ∂s.vU.ν := by
    unfold fl
    exact integral_congr_ae (Filter.Eventually.of_forall hfl)

  obtain ⟨x, hxo, hx⟩ := GlobalTheory.T.exists_mem_orb_rat_eq_x0 D σ B
  obtain ⟨M, hMi, hMb⟩ := GlobalTheory.T.flatThetaIntegrand_locallyUniform_majorant D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil s.vU x
    hxo.1 Ψ hΨ {1} isCompact_singleton
  have hom1 : s.om 1 Ψ = Ψ := by rw [map_one]; rfl
  have hbound : ∀ (u : UX D (σ + 1)) (v : WO J.W₀ B.L),
      ‖flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v)‖ ≤
        M u * My := by
    intro u v
    have h := hMb 1 (Set.mem_singleton 1) 0 ((B.o.resT J.W₀).symm (0, v)) u
    rw [hx, hom1] at h
    rw [norm_mul, norm_star]
    exact mul_le_mul h (hMy v) (norm_nonneg _) ((norm_nonneg _).trans h)
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : BorelSpace (UX D (σ + 1)) := ⟨rfl⟩
  have : BorelSpace (WO J.W₀ B.L) := ⟨rfl⟩
  have : SecondCountableTopology (WO J.W₀ B.L) := (lattice_Mx D B.L.rank J.W₀.rank).2.2.1
  have hE : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L =>
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (x0 B ⬝ p.1.1.1) 0 ((B.o.resT J.W₀).symm (0, p.2)) := by
    have hmc := (GlobalTheory.T.weilMixedCoordinates_continuous_bounded_supNorm D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil Ψ hΨ).2
    have hc : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L => (p.1.1.1 : Mx D (σ + 1) (σ + 1)) :=
      (Units.continuous_val.comp continuous_subtype_val).comp continuous_fst
    have hin : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L =>
        ((1 : GA D J.W × GA D B.V), x0 B ⬝ p.1.1.1, (0 : Mx D J.W₀.rank σ), (B.o.resT J.W₀).symm (0, p.2)) :=
      continuous_const.prodMk ((continuous_const.matrix_mul hc).prodMk (continuous_const.prodMk
        ((B.o.continuous_resT_symm J.W₀).comp (continuous_const.prodMk continuous_snd))))
    have h := hmc.comp hin
    simpa only [Function.comp_def, hom1] using h
  have hK : Continuous (Function.uncurry fun (u : UX D (σ + 1)) (v : WO J.W₀ B.L) =>
      flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v)) :=
    ((continuous_star.comp ((continuous_psiUni hchar.1 (σ + 1)).comp continuous_fst)).mul hE).mul
      (continuous_star.comp (hy.2.comp continuous_snd))
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) := isFiniteMeasure_restrict.2 (by rw [vL.covol.2.2]; simp)
  have hswap := integral_swap_of_majorant s.vU.ν (vL.μ.restrict vL.𝓕) (fun u v =>
      flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v))
    hK.stronglyMeasurable M hMi My hbound
  have h1 : fl ψ J.d B.V s.vS vb s.vU (th J ψ B y) (x0 B) Ψ = tFlat s vL y Ψ := by
    rw [hLeft]
    calc (∫ u, star (psiUni ψ u.1) * ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (x0 B ⬝ u.1.1) 0
            ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ ∂s.vU.ν)
        = ∫ u, ∫ v in vL.𝓕, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u *
            star (y v) ∂vL.μ ∂s.vU.ν := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          dsimp only
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
          simp only [flatFun]
          ring
      _ = ∫ v in vL.𝓕, ∫ u, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u *
            star (y v) ∂s.vU.ν ∂vL.μ := hswap
      _ = ∫ v in vL.𝓕, (∫ u, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u
            ∂s.vU.ν) * star (y v) ∂vL.μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun v => integral_mul_const _ _)
      _ = tFlat s vL y Ψ := rfl
  refine ⟨h1, fun Mb hMb' => ?_⟩
  rw [← h1]
  unfold fl
  calc ‖∫ u, ∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (th J ψ B y) (x0 B) Ψ u b ∂vb.μ ∂s.vU.ν‖ₑ
      ≤ ∫⁻ u, ‖∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (th J ψ B y) (x0 B) Ψ u b ∂vb.μ‖ₑ ∂s.vU.ν :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ u, ∫⁻ b in vb.𝓕, ‖flFun ψ J.d B.V s.vS (th J ψ B y) (x0 B) Ψ u b‖ₑ ∂vb.μ ∂s.vU.ν :=
        lintegral_mono fun u => enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ u, ∫⁻ b in vb.𝓕, ENNReal.ofReal Mb *
          ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (x0 B ⬝ u.1.1) (x0 B ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν := by
        refine lintegral_mono fun u => lintegral_mono fun b => ?_
        simp only [flFun]
        rw [enorm_mul]
        gcongr
        rw [hlaw b u.1 u.2, ← ofReal_norm_eq_enorm, norm_mul, norm_star, norm_star, hnorm u, one_mul]
        exact ENNReal.ofReal_le_ofReal (hMb' _)
    _ = _ := (lintegral_congr fun u => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)

end GlobalTheory.Unf.FB

end
