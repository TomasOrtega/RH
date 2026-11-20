import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay

/- English proof (translation)
Establish `hw : w.IsReal` using `hF.isReal w`. Set `e` to `InfinitePlace.Completion.ringEquivRealOfIsReal hw`. Set `ρ : ℝ →+* ℝ` to `(e : w.Completion →+* ℝ).comp ((Pi.evalRingHom _ w).comp θ)`. Establish `hρ : ρ ε = ε`. Establish `: ρ = RingHom.id ℝ` using `Subsingleton.elim _ _`.

Rewrite using `[this]`. Both sides reduce to the same expression. Establish `hnorm : ‖θ ε w‖ = ‖e (θ ε w)‖`. Rewrite using `[InfinitePlace.Completion.ringEquivRealOfIsReal_apply]`. Conclude with `((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _).symm`.

Rewrite using `[hnorm]`. Express the relevant statement in the definitionally equal form `‖ρ ε‖ = |ε|`. Rewrite using `[hρ, Real.norm_eq_abs]`.
-/
theorem norm_theta {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F) (θ : ℝ →+* Ainf F)
    (ε : ℝ) (w : InfinitePlace F) : ‖θ ε w‖ = |ε| := by
  have hw : w.IsReal := hF.isReal w
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let ρ : ℝ →+* ℝ := (e : w.Completion →+* ℝ).comp ((Pi.evalRingHom _ w).comp θ)
  have hρ : ρ ε = ε := by
    have : ρ = RingHom.id ℝ := Subsingleton.elim _ _
    rw [this]; rfl
  have hnorm : ‖θ ε w‖ = ‖e (θ ε w)‖ := by
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _) _).symm
  rw [hnorm]
  change ‖ρ ε‖ = |ε|
  rw [hρ, Real.norm_eq_abs]

/- English proof (translation)
Introduce `F _ _ hF θ _ r hr`. Use `⟨norm_theta hF θ, fun δ hδ => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hr δ hδ`. Establish `hmd : md (r δ) = (∏ w : InfinitePlace F, ‖(r δ : AF F).1 w‖ ^ w.mult) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(r δ : AF F).2 v‖` using `IdeleGroup.ideleModule_eq _`. Establish `hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(r δ : AF F).2 v‖ = 1`.

Use `finprod_eq_one_of_forall_eq_one fun v => ?_` and prove the remaining obligations. Rewrite using `[h2]`. Conclude with `norm_one`. Rewrite using `[hmd, hfin, mul_one, h1]`. Simplify using `only [norm_theta hF θ δ, abs_of_pos hδ]`.

Rewrite using `[Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]`.
-/
theorem norm_md_ray : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F,
    Continuous θ → ∀ r, IsRay θ r → (∀ (ε : ℝ) (w : InfinitePlace F), ‖θ ε w‖ = |ε|) ∧
      ∀ δ : ℝ, 0 < δ → md (r δ) = δ ^ Module.finrank ℚ F := by
  intro F _ _ hF θ _ r hr
  refine ⟨norm_theta hF θ, fun δ hδ => ?_⟩
  obtain ⟨h1, h2⟩ := hr δ hδ
  have hmd : md (r δ) = (∏ w : InfinitePlace F, ‖(r δ : AF F).1 w‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(r δ : AF F).2 v‖ := IdeleGroup.ideleModule_eq _
  have hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(r δ : AF F).2 v‖ = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    rw [h2]
    exact norm_one
  rw [hmd, hfin, mul_one, h1]
  simp only [norm_theta hF θ δ, abs_of_pos hδ]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay

end
