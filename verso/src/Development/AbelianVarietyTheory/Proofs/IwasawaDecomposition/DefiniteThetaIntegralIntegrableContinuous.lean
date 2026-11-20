import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteUnitaryCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKOContinuousAndRatInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLiftCont

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun g₀ => ?_` and prove the remaining obligations. Take `⟨N, hN, hN₀⟩` from `exists_compact_mem_nhds g₀`. Take `⟨M, hM⟩` from `(hN.prod hC).exists_bound_of_continuousOn hK.continuousOn`. Establish `hconst : IntegrableOn (fun _ : H => (M : ℂ)) 𝓕 μ` using `GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ continuous_const (fun _ _ _ => rfl)`. Establish `hconst' : Integrable (fun _ : H => M) (μ.restrict 𝓕)`.

Simplify using `using hconst.re`. Use `continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ hconst' ?_` and prove the remaining obligations. Use `Filter.Eventually.of_forall fun g => ?_` and prove the remaining obligations. Conclude with `(hK.comp (Continuous.prodMk_right g)).aestronglyMeasurable`. Use `filter_upwards [hN₀] with g hg`.

Use `Filter.Eventually.of_forall fun h => ?_` and prove the remaining obligations. Take `⟨γ, hγ, c, hc, rfl⟩` from `hcov h`. Rewrite using `[hinv γ hγ]`. Conclude with `hM (g, c) ⟨hg, hc⟩`. Use `Filter.Eventually.of_forall fun h => ?_` and prove the remaining obligations.

Conclude with `(hK.comp (Continuous.prodMk_left h)).continuousAt`.
-/
theorem continuous_integral_of_cocompact {G H : Type*} [TopologicalSpace G] [LocallyCompactSpace G]
    [FirstCountableTopology G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [Countable Γ] (μ : Measure H)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (𝓕 C : Set H)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : H, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (K : G → H → ℂ)
    (hK : Continuous fun p : G × H => K p.1 p.2)
    (hinv : ∀ γ ∈ Γ, ∀ g h, K g (γ * h) = K g h) :
    Continuous fun g => ∫ h in 𝓕, K g h ∂μ := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  obtain ⟨N, hN, hN₀⟩ := exists_compact_mem_nhds g₀
  obtain ⟨M, hM⟩ := (hN.prod hC).exists_bound_of_continuousOn hK.continuousOn
  have hconst : IntegrableOn (fun _ : H => (M : ℂ)) 𝓕 μ :=
    GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ continuous_const
      (fun _ _ _ => rfl)
  have hconst' : Integrable (fun _ : H => M) (μ.restrict 𝓕) := by
    simpa using hconst.re
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ hconst' ?_
  · refine Filter.Eventually.of_forall fun g => ?_
    exact (hK.comp (Continuous.prodMk_right g)).aestronglyMeasurable
  · filter_upwards [hN₀] with g hg
    refine Filter.Eventually.of_forall fun h => ?_
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    rw [hinv γ hγ]
    exact hM (g, c) ⟨hg, hc⟩
  · refine Filter.Eventually.of_forall fun h => ?_
    exact (hK.comp (Continuous.prodMk_left h)).continuousAt

/- English proof (translation)
Introduce `D ψ V W χS χT ω ν 𝓕 s F hω hpos hν h𝓕 hs hF hFinv`. Take `⟨C, hC, hcov⟩` from `GlobalTheory.definite_unitary_cocompact W hpos`. Take `⟨hcont, hinv⟩` from `GlobalTheory.thetaKO_continuous_and_rat_invariant ψ V W χS χT ω hω s hs`. Establish `hK : Continuous fun p : GA D V × GA D W => thetaKO ω p.1 p.2 s * F p.2` using `hcont.mul (hF.comp continuous_snd)`. Establish `hKinv : ∀ γ ∈ GQ W, ∀ g h, thetaKO ω g (γ * h) s * F (γ * h) = thetaKO ω g h s * F h`.

Introduce `γ hγ g h`. Use `hinv 1 (one_mem _) γ hγ g h` as an intermediate fact. Rewrite `this` using `[one_mul]`. Rewrite using `[this, hFinv γ hγ]`. Use `⟨fun g => ?_, ?_⟩` and prove the remaining obligations.

Conclude with `GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain W ν 𝓕 C hν h𝓕 hC hcov _ (hK.comp (Continuous.prodMk_right g)) (fun γ hγ h => hKinv γ hγ g h)`. Take `⟨-, -, -, _, _, -, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W`. Take `⟨_, _, -, -, -, -, -⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V`. Conclude with `continuous_integral_of_cocompact (GQ W) ν 𝓕 C h𝓕 hC hcov (fun g h => thetaKO ω g h s * F h) hK hKinv`.
-/
theorem theta_integral_integrable_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (s : WO V W → ℂ) (F : GA D W → ℂ), IsWeilDatumO ψ V W χS χT ω → (∀ τ, (gramAt D W τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → IsThetaFunO ψ V W s → Continuous F → (∀ γ ∈ GQ W, ∀ h, F (γ * h) = F h) → (∀ g, IntegrableOn (fun h => thetaKO ω g h s * F h) 𝓕 ν) ∧ Continuous (Lift.liftInt ν 𝓕 (thetaKO ω) s F) := by
  intro D ψ V W χS χT ω ν 𝓕 s F hω hpos hν h𝓕 hs hF hFinv
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact W hpos
  obtain ⟨hcont, hinv⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ V W χS χT ω hω s hs
  have hK : Continuous fun p : GA D V × GA D W => thetaKO ω p.1 p.2 s * F p.2 :=
    hcont.mul (hF.comp continuous_snd)
  have hKinv : ∀ γ ∈ GQ W, ∀ g h, thetaKO ω g (γ * h) s * F (γ * h) = thetaKO ω g h s * F h := by
    intro γ hγ g h
    have := hinv 1 (one_mem _) γ hγ g h
    rw [one_mul] at this
    rw [this, hFinv γ hγ]
  refine ⟨fun g => ?_, ?_⟩
  · exact GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain W ν 𝓕 C hν h𝓕 hC hcov _
      (hK.comp (Continuous.prodMk_right g)) (fun γ hγ h => hKinv γ hγ g h)
  · obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
    obtain ⟨_, _, -, -, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
    exact continuous_integral_of_cocompact (GQ W) ν 𝓕 C h𝓕 hC hcov
      (fun g h => thetaKO ω g h s * F h) hK hKinv

end GlobalTheory.DefLiftCont
