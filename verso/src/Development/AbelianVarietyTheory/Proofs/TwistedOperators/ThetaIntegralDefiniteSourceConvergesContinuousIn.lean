import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaIntegralIntegrableContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.DefSourceInt

/- English proof (translation)
Introduce `D ψ ε S W χS χW ω μ 𝓕 f hω hpos hμ h𝓕 hf`. Take `⟨C, hC, hcov⟩` from `GlobalTheory.definite_unitary_cocompact S hpos`. Take `⟨hcont, hinv⟩` from `GlobalTheory.thetaKO_continuous_and_rat_invariant ψ (sgn ε S) W χS χW (WRep.toSgn ε ω) hω f hf`. Establish `hK : ∀ g h, thetaKO ω g h f = thetaKO (WRep.toSgn ε ω) ((ofSgn ε S).symm g) h f` using `fun _ _ => rfl`. Establish `hKc : Continuous fun p : GA D S × GA D W => thetaKO ω p.1 p.2 f` using `(hcont.comp (((continuous_ofSgn_symm ε S).comp continuous_fst).prodMk continuous_snd)).congr fun p => (hK p.1 p.2).symm`.

Establish `hI : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ W, ∀ g h, thetaKO ω (γ * g) (γ' * h) f = thetaKO ω g h f`. Introduce `γ hγ γ' hγ' g h`. Rewrite using `[hK, hK, map_mul]`. Conclude with `hinv _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ ε hγ) γ' hγ' _ _`. Establish `hIS : ∀ γ ∈ GQ S, ∀ g h, thetaKO ω (γ * g) h f = thetaKO ω g h f` using `fun γ hγ g h => by`.

Use `hI γ hγ 1 (one_mem _) g h` as an intermediate fact. Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis. Establish `hIW : ∀ γ ∈ GQ W, ∀ g h, thetaKO ω g (γ * h) f = thetaKO ω g h f` using `fun γ hγ g h => by`. Use `hI 1 (one_mem _) γ hγ g h` as an intermediate fact. Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis.

Take `⟨_, _, _, _, _, _, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S`. Take `⟨_, _, _, _, _, _, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W`. Use `⟨fun h => ?_, ?_, fun γ hγ h => ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain S μ 𝓕 C hμ h𝓕 hC hcov _ (hKc.comp (Continuous.prodMk_left h)) (fun γ hγ g => hIS γ hγ g h)`. Conclude with `GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (GQ S) μ 𝓕 C h𝓕 hC hcov (fun h g => thetaKO ω g h f) (hKc.comp continuous_swap) (fun γ hγ h g => hIS γ hγ g h)`.

Establish `e : (fun g => thetaKO ω g (γ * h) f) = fun g => thetaKO ω g h f` using `funext fun g => hIW γ hγ g h`. Conclude with `congrArg (fun F : GA D S → ℂ => ∫ g in 𝓕, F g ∂μ) e`.
-/
theorem theta_integral_source_definite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S W : HSp D) (χS χW : (AE D)ˣ →* Circle) (ω : WRep S W) (μ : Measure (GA D S)) (𝓕 : Set (GA D S)) (f : WO S W → ℂ), IsWeil ψ ε S W χS χW ω → (∀ τ, (gramAt D S τ).PosDef) → μ.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 μ → IsThetaFunO ψ (sgn ε S) W f → (∀ h, IntegrableOn (fun g => thetaKO ω g h f) 𝓕 μ) ∧ (Continuous fun h => ∫ g in 𝓕, thetaKO ω g h f ∂μ) ∧ ∀ γ ∈ GQ W, ∀ h, ∫ g in 𝓕, thetaKO ω g (γ * h) f ∂μ = ∫ g in 𝓕, thetaKO ω g h f ∂μ := by
  intro D ψ ε S W χS χW ω μ 𝓕 f hω hpos hμ h𝓕 hf
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hpos
  obtain ⟨hcont, hinv⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ (sgn ε S) W χS χW (WRep.toSgn ε ω) hω f hf
  have hK : ∀ g h, thetaKO ω g h f = thetaKO (WRep.toSgn ε ω) ((ofSgn ε S).symm g) h f := fun _ _ => rfl
  have hKc : Continuous fun p : GA D S × GA D W => thetaKO ω p.1 p.2 f :=
    (hcont.comp (((continuous_ofSgn_symm ε S).comp continuous_fst).prodMk continuous_snd)).congr fun p => (hK p.1 p.2).symm
  have hI : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ W, ∀ g h, thetaKO ω (γ * g) (γ' * h) f = thetaKO ω g h f := by
    intro γ hγ γ' hγ' g h
    rw [hK, hK, map_mul]
    exact hinv _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ ε hγ) γ' hγ' _ _
  have hIS : ∀ γ ∈ GQ S, ∀ g h, thetaKO ω (γ * g) h f = thetaKO ω g h f := fun γ hγ g h => by
    have := hI γ hγ 1 (one_mem _) g h
    rwa [one_mul] at this
  have hIW : ∀ γ ∈ GQ W, ∀ g h, thetaKO ω g (γ * h) f = thetaKO ω g h f := fun γ hγ g h => by
    have := hI 1 (one_mem _) γ hγ g h
    rwa [one_mul] at this
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  refine ⟨fun h => ?_, ?_, fun γ hγ h => ?_⟩
  · exact GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain S μ 𝓕 C hμ h𝓕 hC hcov _
      (hKc.comp (Continuous.prodMk_left h)) (fun γ hγ g => hIS γ hγ g h)
  · exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (GQ S) μ 𝓕 C h𝓕 hC hcov
      (fun h g => thetaKO ω g h f) (hKc.comp continuous_swap) (fun γ hγ h g => hIS γ hγ g h)
  · have e : (fun g => thetaKO ω g (γ * h) f) = fun g => thetaKO ω g h f := funext fun g => hIW γ hγ g h
    exact congrArg (fun F : GA D S → ℂ => ∫ g in 𝓕, F g ∂μ) e

end GlobalTheory.DefSourceInt
