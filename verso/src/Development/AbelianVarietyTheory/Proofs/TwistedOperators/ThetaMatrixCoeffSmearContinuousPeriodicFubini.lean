import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMeanSmear

/- English proof (translation)
Take `⟨-, -, -, -, -, K, hK, hcov⟩` from `GlobalTheory.MixModel.lattice_Mx D W.rank V.rank`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hG.cont.continuousOn`. Use `⟨C, fun u => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγm, hγ⟩` from `hcov u`. Take `⟨γ0, rfl⟩` from `hγm`.

Establish `e : ((incA D).toAddMonoidHom.mapMatrix (m` using `Fin W.rank) (n := Fin V.rank)) γ0 = ratW W V γ0 := rfl`. Establish `h1` using `hC _ hγ`. Rewrite `h1` using `[e, hG.quasi, norm_mul, hψ.1.2.1, one_mul]`. Conclude with `h1`.
-/
theorem exists_bound {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D}
    {G : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) : ∃ C, ∀ u, ‖G u‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hcov⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG.cont.continuousOn
  refine ⟨C, fun u => ?_⟩
  obtain ⟨γ, hγm, hγ⟩ := hcov u
  obtain ⟨γ0, rfl⟩ := hγm
  have e : ((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ0 = ratW W V γ0 := rfl
  have h1 := hC _ hγ
  rw [e, hG.quasi, norm_mul, hψ.1.2.1, one_mul] at h1
  exact h1

/- English proof (translation)
Unfold `GlobalTheory.IsoMean.emb`. Conclude with `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`.
-/
theorem continuous_emb {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) : Continuous (GlobalTheory.IsoMean.emb V W P Q) := by
  unfold GlobalTheory.IsoMean.emb
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

end GlobalTheory.IsoMeanSmear

namespace GlobalTheory.IsoMeanSmear

/- English proof (translation)
Introduce `D V W a b P Q ψ hψ μ 𝓨 hμ ν 𝓕 hν h𝓕 G G' hG hG'`. Take `⟨hHaar, -, h1⟩` from `hμ`. Take `⟨-, -, s1, -, -, -⟩` from `GlobalTheory.MixModel.lattice_Mx D a b`. Take `⟨-, -, s2, -, -, K, hK, hcov⟩` from `GlobalTheory.MixModel.lattice_Mx D W.rank V.rank`. Use `haveI := s1`.

Use `haveI := s2`. Use `haveI : FirstCountableTopology (WO V W) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology (WO V W)`. Use `haveI : BorelSpace (Mx D a b) := ⟨rfl⟩`. Use `haveI : BorelSpace (WO V W) := ⟨rfl⟩`. Use `haveI hfμ : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩`.

Use `haveI : Countable D.host.E := by haveI : FiniteDimensional ℚ D.host.E := inferInstance`. Conclude with `(Module.finBasis ℚ D.host.E).equivFun.injective.countable`. Use `haveI : Countable (Matrix (Fin W.rank) (Fin V.rank) D.host.E) := inferInstanceAs (Countable (Fin W.rank → Fin V.rank → D.host.E))`. Use `haveI : Countable (ratL W V) := (Set.countable_range _).to_subtype`. Establish `hνF : ν 𝓕 < ⊤`.

Establish `hcov' : ∀ x : WO V W, ∃ γ ∈ ratL W V, γ + x ∈ K` using `hcov`. Conclude with `GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (ratL W V) hK hcov' ν h𝓕`. Use `haveI hfν : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hνF⟩`. Use `haveI : SFinite (ν.restrict 𝓕) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfν)`. Use `haveI : SFinite (μ.restrict 𝓨) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfμ)`.

Take `⟨C, hC⟩` from `exists_bound hψ hG`. Take `⟨C', hC'⟩` from `exists_bound hψ hG'`. Use `set Φ : Mx D a b × WO V W → ℂ := fun p => heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q p.1) G p.2 * star (G' p.2) with hΦ`. Establish `he` using `continuous_emb V W P Q`. Establish `hcont : Continuous Φ`.

Simplify using `only [hΦ, heisO]`. Conclude with `((hψ.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_snd (he.comp continuous_fst))).mul (hG.cont.comp (continuous_snd.add (he.comp continuous_fst)))).mul (hG'.cont.comp continuous_snd).star`. Establish `hbd : ∀ p, ‖Φ p‖ ≤ C * C'`. Introduce `p`. Simplify using `only [hΦ, heisO, norm_mul, norm_star, hψ.1.2.1, one_mul]`.

Conclude with `mul_le_mul (hC _) (hC' _) (norm_nonneg _) ((norm_nonneg _).trans (hC 0))`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `continuous_of_dominated (bound := fun _ => C * C') (fun u => ?_) (fun u => ?_) (integrable_const _) ?_` and prove the remaining obligations. Establish `hu : Continuous fun ξ => Φ (ξ, u)` using `hcont.comp (continuous_id.prodMk continuous_const)`. Conclude with `hu.aestronglyMeasurable`.

Conclude with `Filter.Eventually.of_forall fun ξ => hbd (ξ, u)`. Use `Filter.Eventually.of_forall fun ξ => ?_` and prove the remaining obligations. Establish `hξ : Continuous fun u => Φ (ξ, u)` using `hcont.comp (continuous_const.prodMk continuous_id)`. Conclude with `hξ`. Introduce `γ hγ u`.

Take `⟨γ0, rfl⟩` from `hγ`. Establish `er : ((incA D).toAddMonoidHom.mapMatrix (m` using `Fin W.rank) (n := Fin V.rank)) γ0 = ratW W V γ0 := rfl`. Rewrite using `[er]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)` and prove the remaining obligations. Establish `hH` using `GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hG (GlobalTheory.IsoMean.emb V W P Q ξ)`.

Simplify using `only`. Rewrite using `[hH.quasi, hG'.quasi, star_mul]`. Establish `hn : ψ (-(symplOH V W (ratW W V γ0) u)) * star (ψ (-(symplOH V W (ratW W V γ0) u))) = 1`. Establish `h1` using `hψ.1.2.1 (-(symplOH V W (ratW W V γ0) u))`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]`.

Evaluate the numerical expressions. Take the linear combination `(heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G u * star (G' u)) * hn`. Introduce `φ hφ hφ1`. Establish `hint : Integrable (Function.uncurry fun ξ u => φ u * Φ (ξ, u)) ((μ.restrict 𝓨).prod (ν.restrict 𝓕))`. Use `Integrable.of_bound ?_ (C * C') (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations.

Conclude with `((hφ.comp continuous_snd).mul hcont).aestronglyMeasurable`. Simplify using `only [Function.uncurry, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `(integral_integral_swap hint).trans ?_` and prove the remaining obligations. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations.

Conclude with `integral_const_mul _ _`.
-/
theorem smear : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Continuous (fun u => ∫ ξ in 𝓨, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G u * star (G' u) ∂μ) ∧ (∀ γ ∈ ratL W V, ∀ u, ∫ ξ in 𝓨, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G (γ + u) * star (G' (γ + u)) ∂μ = ∫ ξ in 𝓨, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G u * star (G' u) ∂μ) ∧ ∀ φ : WO V W → ℂ, Continuous φ → (∀ u, ‖φ u‖ ≤ 1) → ∫ ξ in 𝓨, (∫ u in 𝓕, φ u * (heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G u * star (G' u)) ∂ν) ∂μ = ∫ u in 𝓕, φ u * (∫ ξ in 𝓨, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G u * star (G' u) ∂μ) ∂ν := by
  intro D V W a b P Q ψ hψ μ 𝓨 hμ ν 𝓕 hν h𝓕 G G' hG hG'
  obtain ⟨hHaar, -, h1⟩ := hμ
  obtain ⟨-, -, s1, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D a b
  obtain ⟨-, -, s2, -, -, K, hK, hcov⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  haveI := s1
  haveI := s2
  haveI : FirstCountableTopology (WO V W) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology (WO V W)
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  haveI hfμ : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  haveI : Countable D.host.E := by
    haveI : FiniteDimensional ℚ D.host.E := inferInstance
    exact (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin W.rank) (Fin V.rank) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin V.rank → D.host.E))
  haveI : Countable (ratL W V) := (Set.countable_range _).to_subtype
  have hνF : ν 𝓕 < ⊤ := by
    have hcov' : ∀ x : WO V W, ∃ γ ∈ ratL W V, γ + x ∈ K := hcov
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (ratL W V) hK hcov' ν h𝓕
  haveI hfν : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hνF⟩
  haveI : SFinite (ν.restrict 𝓕) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfν)
  haveI : SFinite (μ.restrict 𝓨) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfμ)
  obtain ⟨C, hC⟩ := exists_bound hψ hG
  obtain ⟨C', hC'⟩ := exists_bound hψ hG'
  set Φ : Mx D a b × WO V W → ℂ := fun p => heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q p.1) G p.2 * star (G' p.2) with hΦ
  have he := continuous_emb V W P Q
  have hcont : Continuous Φ := by
    simp only [hΦ, heisO]
    exact ((hψ.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_snd (he.comp continuous_fst))).mul
      (hG.cont.comp (continuous_snd.add (he.comp continuous_fst)))).mul (hG'.cont.comp continuous_snd).star
  have hbd : ∀ p, ‖Φ p‖ ≤ C * C' := by
    intro p
    simp only [hΦ, heisO, norm_mul, norm_star, hψ.1.2.1, one_mul]
    exact mul_le_mul (hC _) (hC' _) (norm_nonneg _) ((norm_nonneg _).trans (hC 0))
  refine ⟨?_, ?_, ?_⟩
  · refine continuous_of_dominated (bound := fun _ => C * C') (fun u => ?_) (fun u => ?_) (integrable_const _) ?_
    · have hu : Continuous fun ξ => Φ (ξ, u) := hcont.comp (continuous_id.prodMk continuous_const)
      exact hu.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ξ => hbd (ξ, u)
    · refine Filter.Eventually.of_forall fun ξ => ?_
      have hξ : Continuous fun u => Φ (ξ, u) := hcont.comp (continuous_const.prodMk continuous_id)
      exact hξ
  · intro γ hγ u
    obtain ⟨γ0, rfl⟩ := hγ
    have er : ((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ0 = ratW W V γ0 := rfl
    rw [er]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    have hH := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hG (GlobalTheory.IsoMean.emb V W P Q ξ)
    simp only
    rw [hH.quasi, hG'.quasi, star_mul]
    have hn : ψ (-(symplOH V W (ratW W V γ0) u)) * star (ψ (-(symplOH V W (ratW W V γ0) u))) = 1 := by
      have h1 := hψ.1.2.1 (-(symplOH V W (ratW W V γ0) u))
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
      norm_num
    linear_combination (heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G u * star (G' u)) * hn
  · intro φ hφ hφ1
    have hint : Integrable (Function.uncurry fun ξ u => φ u * Φ (ξ, u)) ((μ.restrict 𝓨).prod (ν.restrict 𝓕)) := by
      refine Integrable.of_bound ?_ (C * C') (Filter.Eventually.of_forall fun p => ?_)
      · exact ((hφ.comp continuous_snd).mul hcont).aestronglyMeasurable
      · simp only [Function.uncurry, norm_mul]
        calc ‖φ p.2‖ * ‖Φ (p.1, p.2)‖ ≤ 1 * (C * C') :=
              mul_le_mul (hφ1 _) (hbd _) (norm_nonneg _) zero_le_one
          _ = C * C' := one_mul _
    refine (integral_integral_swap hint).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    exact integral_const_mul _ _

end GlobalTheory.IsoMeanSmear
