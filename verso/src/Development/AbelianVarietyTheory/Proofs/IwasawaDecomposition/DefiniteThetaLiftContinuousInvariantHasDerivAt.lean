import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaIntegralIntegrableContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLiftDer

/- English proof (translation)
Take `⟨N, hN, hN₀⟩` from `exists_compact_mem_nhds t₀`. Take `⟨M, hM⟩` from `(hN.prod hC).exists_bound_of_continuousOn hK'.continuousOn`. Establish `hconst : IntegrableOn (fun _ : H => (M : ℂ)) 𝓕 μ` using `GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ continuous_const (fun _ _ _ => rfl)`. Establish `hconst' : Integrable (fun _ : H => M) (μ.restrict 𝓕)`. Simplify using `using hconst.re`.

Use `(hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => M) hN₀ (Filter.Eventually.of_forall fun t => (hK t).aestronglyMeasurable) (GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ (hK t₀) (fun γ hγ h => hinv γ hγ t₀ h)) (hK'.comp (Conti …` and prove the remaining obligations. Use `Filter.Eventually.of_forall fun h t ht => ?_` and prove the remaining obligations. Take `⟨γ, hγ, c, hc, rfl⟩` from `hcov h`. Rewrite using `[hinv' γ hγ]`. Conclude with `hM (t, c) ⟨ht, hc⟩`.
-/
theorem hasDerivAt_integral_of_cocompact {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [Countable Γ] (μ : Measure H)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (𝓕 C : Set H)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : H, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (K K' : ℝ → H → ℂ)
    (hK : ∀ t, Continuous (K t)) (hK' : Continuous fun p : ℝ × H => K' p.1 p.2)
    (hinv : ∀ γ ∈ Γ, ∀ t h, K t (γ * h) = K t h) (hinv' : ∀ γ ∈ Γ, ∀ t h, K' t (γ * h) = K' t h)
    (hd : ∀ t h, HasDerivAt (fun s => K s h) (K' t h) t) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ h in 𝓕, K t h ∂μ) (∫ h in 𝓕, K' t₀ h ∂μ) t₀ := by
  obtain ⟨N, hN, hN₀⟩ := exists_compact_mem_nhds t₀
  obtain ⟨M, hM⟩ := (hN.prod hC).exists_bound_of_continuousOn hK'.continuousOn
  have hconst : IntegrableOn (fun _ : H => (M : ℂ)) 𝓕 μ :=
    GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ continuous_const
      (fun _ _ _ => rfl)
  have hconst' : Integrable (fun _ : H => M) (μ.restrict 𝓕) := by
    simpa using hconst.re
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => M) hN₀
    (Filter.Eventually.of_forall fun t => (hK t).aestronglyMeasurable)
    (GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ (hK t₀) (fun γ hγ h => hinv γ hγ t₀ h))
    (hK'.comp (Continuous.prodMk_right t₀)).aestronglyMeasurable ?_ hconst'
    (Filter.Eventually.of_forall fun h t _ => hd t h)).2
  refine Filter.Eventually.of_forall fun h t ht => ?_
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
  rw [hinv' γ hγ]
  exact hM (t, c) ⟨ht, hc⟩

/- English proof (translation)
Use `⟨?_, fun γ hγ g h => ?_, fun γ hγ g h => ?_⟩` and prove the remaining obligations. Set `b` to `Module.finBasis ℂ X`. Establish `e : (fun p : GA D T × GA D S => thetaKO om p.2 p.1 (L (F p.2))) = fun p => ∑ k, b.coord k (F p.2) * om (p.2, p.1) (L (b k)) 0`. Use function extensionality and compare the values at `p`. Use `conv_lhs => rw [← b.sum_repr (F p.2)]`.

Simplify using `only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]`. Rewrite using `[e]`. Use `continuous_finsetSum _ fun k _ => Continuous.mul ?_ ?_` and prove the remaining obligations. Conclude with `((b.coord k).continuous_of_finiteDimensional.comp hF).comp continuous_snd`. Conclude with `(hom.om_cont _ (hL (b k)) 0).comp continuous_swap`.

Use `(GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om hom _ (hL (F h))).2 γ hγ 1 (one_mem _) h g` as an intermediate fact. Rewrite `this` using `[one_mul]`. Rewrite using `[hinv γ hγ, this]`. Use `(GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om hom _ (hL (F h))).2 1 (one_mem _) γ hγ h g` as an intermediate fact. Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis.
-/
theorem kernel_continuous_invariant {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hom : IsWeilDatumO ψ S T χS χT om) {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    (L : X →ₗ[ℂ] (WO S T → ℂ)) (hL : ∀ x, IsThetaFunO ψ S T (L x)) {F : GA D S → X} (hF : Continuous F)
    (hinv : ∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) :
    (Continuous fun p : GA D T × GA D S => thetaKO om p.2 p.1 (L (F p.2))) ∧
      (∀ γ ∈ GQ S, ∀ g h, thetaKO om (γ * h) g (L (F (γ * h))) = thetaKO om h g (L (F h))) ∧
      ∀ γ ∈ GQ T, ∀ g h, thetaKO om h (γ * g) (L (F h)) = thetaKO om h g (L (F h)) := by
  refine ⟨?_, fun γ hγ g h => ?_, fun γ hγ g h => ?_⟩
  · let b := Module.finBasis ℂ X
    have e : (fun p : GA D T × GA D S => thetaKO om p.2 p.1 (L (F p.2))) =
        fun p => ∑ k, b.coord k (F p.2) * om (p.2, p.1) (L (b k)) 0 := by
      funext p
      conv_lhs => rw [← b.sum_repr (F p.2)]
      simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
    rw [e]
    refine continuous_finsetSum _ fun k _ => Continuous.mul ?_ ?_
    · exact ((b.coord k).continuous_of_finiteDimensional.comp hF).comp continuous_snd
    · exact (hom.om_cont _ (hL (b k)) 0).comp continuous_swap
  · have := (GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om hom _ (hL (F h))).2 γ hγ 1 (one_mem _) h g
    rw [one_mul] at this
    rw [hinv γ hγ, this]
  · have := (GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om hom _ (hL (F h))).2 1 (one_mem _) γ hγ h g
    rwa [one_mul] at this

/- English proof (translation)
Introduce `D ψ S T χS χT om hom θ hθ hpos X _ _ _ L hL F hF hinv ν 𝓕 hν h𝓕`. Take `⟨C, hC, hcov⟩` from `GlobalTheory.definite_unitary_cocompact S hpos`. Take `⟨-, -, -, _, _, -, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S`. Take `⟨_, _, _, _, _, _, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T`. Take `⟨hc, hiS, hiT⟩` from `kernel_continuous_invariant hom L hL hF hinv`.

Use `⟨⟨?_, fun γ hγ g => ?_⟩, fun τ Y hY => ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (GQ S) ν 𝓕 C h𝓕 hC hcov (fun g h => thetaKO om h g (L (F h))) hc hiS`. Simplify using `only [GlobalTheory.DefLift.lift, hiT γ hγ]`. Take `⟨Gn, hGn⟩` from `GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ Y hY`. Establish `hL' : ∀ x, IsThetaFunO ψ S T ((Gn ∘ₗ L) x)` using `fun x => (hGn _ (hL x)).1`.

Establish `hd : ∀ x h g, HasDerivAt (fun t : ℝ => thetaKO om h (g * oneP θ T τ Y t) (L x)) (thetaKO om h g ((Gn ∘ₗ L) x)) 0`. Introduce `x h g`. Use `(hGn _ (hL x)).2.2.2 (h, g) 0` as an intermediate fact. Simplify using `only [Prod.mk_mul_mk, mul_one] at this`. Conclude with `this`.

Use `⟨Gn ∘ₗ L, hL', hd, fun g => ?_⟩` and prove the remaining obligations. Take `⟨hc', hiS', -⟩` from `kernel_continuous_invariant hom (Gn ∘ₗ L) hL' hF hinv`. Establish `hp : Continuous fun t : ℝ => g * oneP θ T τ Y t` using `continuous_const.mul (GlobalTheory.Mem.Lift.continuous_oneP hθ hY)`. Establish `key` using `hasDerivAt_integral_of_cocompact (GQ S) ν 𝓕 C h𝓕 hC hcov (fun t h => thetaKO om h (g * oneP θ T τ Y t) (L (F h))) (fun t h => thetaKO om h (g * oneP θ T τ Y t) ((Gn ∘ₗ L) (F h))) (fun t => hc.comp (Continuous.prodMk_right (g * oneP θ T τ Y t))) (hc'.comp (hp.prodMap continuous_id …`. Simplify using `only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at key`.

Conclude with `key`.
-/
theorem lift_continuous_invariant_hasDerivAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → (∀ τ, (gramAt D S τ).PosDef) → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → (Continuous (lift om ν 𝓕 fun h => L (F h)) ∧ ∀ γ ∈ GQ T, ∀ g, lift om ν 𝓕 (fun h => L (F h)) (γ * g) = lift om ν 𝓕 (fun h => L (F h)) g) ∧ ∀ τ, ∀ Y ∈ lieAt T τ, ∃ L' : X →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L' x)) ∧ (∀ x h g, HasDerivAt (fun t : ℝ => thetaKO om h (g * oneP θ T τ Y t) (L x)) (thetaKO om h g (L' x)) 0) ∧ ∀ g, HasDerivAt (fun t : ℝ => lift om ν 𝓕 (fun h => L (F h)) (g * oneP θ T τ Y t)) (lift om ν 𝓕 (fun h => L' (F h)) g) 0 := by
  intro D ψ S T χS χT om hom θ hθ hpos X _ _ _ L hL F hF hinv ν 𝓕 hν h𝓕
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hpos
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  obtain ⟨hc, hiS, hiT⟩ := kernel_continuous_invariant hom L hL hF hinv
  refine ⟨⟨?_, fun γ hγ g => ?_⟩, fun τ Y hY => ?_⟩
  · exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (GQ S) ν 𝓕 C h𝓕 hC hcov
      (fun g h => thetaKO om h g (L (F h))) hc hiS
  · simp only [GlobalTheory.DefLift.lift, hiT γ hγ]
  · obtain ⟨Gn, hGn⟩ := GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ Y hY
    have hL' : ∀ x, IsThetaFunO ψ S T ((Gn ∘ₗ L) x) := fun x => (hGn _ (hL x)).1
    have hd : ∀ x h g, HasDerivAt (fun t : ℝ => thetaKO om h (g * oneP θ T τ Y t) (L x))
        (thetaKO om h g ((Gn ∘ₗ L) x)) 0 := by
      intro x h g
      have := (hGn _ (hL x)).2.2.2 (h, g) 0
      simp only [Prod.mk_mul_mk, mul_one] at this
      exact this
    refine ⟨Gn ∘ₗ L, hL', hd, fun g => ?_⟩
    obtain ⟨hc', hiS', -⟩ := kernel_continuous_invariant hom (Gn ∘ₗ L) hL' hF hinv
    have hp : Continuous fun t : ℝ => g * oneP θ T τ Y t :=
      continuous_const.mul (GlobalTheory.Mem.Lift.continuous_oneP hθ hY)
    have key := hasDerivAt_integral_of_cocompact (GQ S) ν 𝓕 C h𝓕 hC hcov
      (fun t h => thetaKO om h (g * oneP θ T τ Y t) (L (F h)))
      (fun t h => thetaKO om h (g * oneP θ T τ Y t) ((Gn ∘ₗ L) (F h)))
      (fun t => hc.comp (Continuous.prodMk_right (g * oneP θ T τ Y t)))
      (hc'.comp (hp.prodMap continuous_id))
      (fun γ hγ t h => hiS γ hγ _ h) (fun γ hγ t h => hiS' γ hγ _ h)
      (fun t h => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hY (φ := fun g => thetaKO om h g (L (F h)))
        (φ' := fun g => thetaKO om h g ((Gn ∘ₗ L) (F h))) (hd (F h) h) g t) 0
    simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at key
    exact key

end GlobalTheory.DefLiftDer
