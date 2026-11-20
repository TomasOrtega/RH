import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchemeModelsSpreadStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSpreadsOutStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsProperSpreadsOutStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreading
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.SmoothProperModel

/- English proof (translation)
Introduce `k _ X f hsm hpr`. Take `⟨R₀, _, φ, X₀, f₀, π, hm⟩` from `GlobalTheory.T.scheme_models_spread k X f inferInstance inferInstance inferInstance`. Take `⟨R₁, _, ψ₁, φ₁, e₁, ft₁, sm₁⟩` from `GlobalTheory.T.smooth_spreads_out k R₀ φ X X₀ f f₀ π hm hsm`. Establish `m₁` using `GlobalTheory.CompanionTheory.CubeModels.model_refine' e₁ ft₁ hm`. Take `⟨R₂, _, ψ₂, φ₂, e₂, ft₂, pr₂⟩` from `GlobalTheory.T.isProper_spreads_out k R₁ φ₁ X _ f _ _ m₁ hpr`.

Establish `m₂` using `GlobalTheory.CompanionTheory.CubeModels.model_refine' e₂ ft₂ m₁`. Establish `sm₁' : Smooth (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))` using `sm₁`. Establish `pr₂' : IsProper (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁))) (Spec.map (CommRingCat.ofHom ψ₂)))` using `pr₂`. Establish `sm₂' : Smooth (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁))) (Spec.map (CommRingCat.ofHom ψ₂)))` using `inferInstance`. Set `ψ₃ : R₂ →+* φ₂.range` to `φ₂.rangeRestrict`.

Establish `e₃ : φ₂.range.subtype.comp ψ₃ = φ₂` using `by ext x; rfl`. Establish `ft₃ : Algebra.FiniteType ℤ φ₂.range` using `haveI := ft₂ Algebra.FiniteType.of_surjective ψ₃.toIntAlgHom φ₂.rangeRestrict_surjective`. Establish `m₃` using `GlobalTheory.CompanionTheory.CubeModels.model_refine' e₃ ft₃ m₂`. Conclude with `⟨φ₂.range, _, _, _, ft₃, inferInstance, inferInstance, m₃.2.2.2.2⟩`.
-/
theorem exists_smooth_proper_model : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f →
    ∃ (R : Subring k) (X₀ : Scheme.{0}) (f₀ : X₀ ⟶ Sp R) (π : X ⟶ X₀), Algebra.FiniteType ℤ R ∧ Smooth f₀ ∧
      IsProper f₀ ∧ IsPullback π f f₀ (spMap R.subtype) := by
  intro k _ X f hsm hpr
  obtain ⟨R₀, _, φ, X₀, f₀, π, hm⟩ := GlobalTheory.T.scheme_models_spread k X f inferInstance inferInstance inferInstance
  obtain ⟨R₁, _, ψ₁, φ₁, e₁, ft₁, sm₁⟩ := GlobalTheory.T.smooth_spreads_out k R₀ φ X X₀ f f₀ π hm hsm
  have m₁ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₁ ft₁ hm
  obtain ⟨R₂, _, ψ₂, φ₂, e₂, ft₂, pr₂⟩ := GlobalTheory.T.isProper_spreads_out k R₁ φ₁ X _ f _ _ m₁ hpr
  have m₂ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₂ ft₂ m₁
  have sm₁' : Smooth (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁))) := sm₁
  have pr₂' : IsProper (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) := pr₂
  have sm₂' : Smooth (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) := inferInstance
  let ψ₃ : R₂ →+* φ₂.range := φ₂.rangeRestrict
  have e₃ : φ₂.range.subtype.comp ψ₃ = φ₂ := by ext x; rfl
  have ft₃ : Algebra.FiniteType ℤ φ₂.range :=
    haveI := ft₂
    Algebra.FiniteType.of_surjective ψ₃.toIntAlgHom φ₂.rangeRestrict_surjective
  have m₃ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₃ ft₃ m₂
  exact ⟨φ₂.range, _, _, _, ft₃, inferInstance, inferInstance, m₃.2.2.2.2⟩

end GlobalTheory.SmoothProperModel
