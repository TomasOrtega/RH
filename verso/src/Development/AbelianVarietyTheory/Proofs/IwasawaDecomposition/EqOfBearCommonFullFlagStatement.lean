import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfBearCommonFullFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FEqOfBearCommonFullFlag.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.eq_of_bear_common_fullFlag : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (K : Type) [Field K] (p p' : Sp K ⟶ Y₁.X) (q : Sp K ⟶ Y₂.X), p ≫ f₁ = q ≫ f₂ → p' ≫ f₁ = q ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p q → CoBear Eb S₁ φ₁ S₂ φ₂ (p' ≫ f₁) p' q → p = p' := by
  first | exact @GlobalTheory.FlagBundle.eq_of_coBear | exact GlobalTheory.FlagBundle.eq_of_coBear | (intros; apply GlobalTheory.FlagBundle.eq_of_coBear <;> assumption)
