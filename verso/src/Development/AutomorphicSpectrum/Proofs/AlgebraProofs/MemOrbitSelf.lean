import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.FreeQuotProof

/- English proof (translation)
Establish `h1 : lift (1 : X ⟶ G) (𝟙 X) ≫ snd G X = 𝟙 X` using `lift_snd _ _`. Establish `h2 : lift (1 : X ⟶ G) (𝟙 X) ≫ (γ[G, X] : G ⊗ X ⟶ X) = 𝟙 X`. Use `one_smul (X ⟶ G) (𝟙 X)` as an intermediate fact. Rewrite `this` using `[Hom.smul_def]`. Then use the resulting hypothesis. Establish `h1' : (lift (1 : X ⟶ G) (𝟙 X)).left ≫ (snd G X).left = 𝟙 X.left`.

Rewrite using `[← Over.comp_left, h1, Over.id_left]`. Establish `h2' : (lift (1 : X ⟶ G) (𝟙 X)).left ≫ (γ[G, X] : G ⊗ X ⟶ X).left = 𝟙 X.left`. Rewrite using `[← Over.comp_left, h2, Over.id_left]`. Use `⟨(lift (1 : X ⟶ G) (𝟙 X)).left x, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(snd G X).left ((lift (1 : X ⟶ G) (𝟙 X)).left x) = x`.

Rewrite using `[← Scheme.Hom.comp_apply, h1']`. Both sides reduce to the same expression. Rewrite using `[← Scheme.Hom.comp_apply, h2']`. Both sides reduce to the same expression.
-/
theorem mem_orbit_self {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] (x : X.left) :
    x ∈ orbit G X x := by
  have h1 : lift (1 : X ⟶ G) (𝟙 X) ≫ snd G X = 𝟙 X := lift_snd _ _
  have h2 : lift (1 : X ⟶ G) (𝟙 X) ≫ (γ[G, X] : G ⊗ X ⟶ X) = 𝟙 X := by
    have := one_smul (X ⟶ G) (𝟙 X)
    rwa [Hom.smul_def] at this
  have h1' : (lift (1 : X ⟶ G) (𝟙 X)).left ≫ (snd G X).left = 𝟙 X.left := by
    rw [← Over.comp_left, h1, Over.id_left]
  have h2' : (lift (1 : X ⟶ G) (𝟙 X)).left ≫ (γ[G, X] : G ⊗ X ⟶ X).left = 𝟙 X.left := by
    rw [← Over.comp_left, h2, Over.id_left]
  refine ⟨(lift (1 : X ⟶ G) (𝟙 X)).left x, ?_, ?_⟩
  · change (snd G X).left ((lift (1 : X ⟶ G) (𝟙 X)).left x) = x
    rw [← Scheme.Hom.comp_apply, h1']; rfl
  · rw [← Scheme.Hom.comp_apply, h2']; rfl

end GlobalTheory.CompanionTheory.FreeQuotProof
