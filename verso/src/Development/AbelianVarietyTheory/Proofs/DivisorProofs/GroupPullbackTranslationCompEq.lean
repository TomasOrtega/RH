import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomOfDerivation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningFieldStructure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TranslPull

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Introduce a local definition for the expression. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem transl_comp_of_isGrpPullback : ∀ {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (x : 𝟙_ (Over S') ⟶ G') (s : 𝟙_ (Over S) ⟶ G), x.left ≫ φ = f ≫ s.left → (lift (toUnit G' ≫ x) (𝟙 G') ≫ μ[G']).left ≫ φ = φ ≫ (lift (toUnit G ≫ s) (𝟙 G) ≫ μ[G]).left := by
  intro S S' G' _ G _ f φ h x s hx
  have hu' : ∀ (Y : Over S'), (toUnit Y).left = Y.hom := fun Y => by
    simpa using Over.w (toUnit Y)
  have hu : ∀ (Y : Over S), (toUnit Y).left = Y.hom := fun Y => by
    simpa using Over.w (toUnit Y)
  have hs : s.left ≫ G.hom = 𝟙 S := by simpa using Over.w s
  let x₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk (G'.hom ≫ f ≫ s.left) (by
    simp [hs])
  let y₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ (by simpa using h.1.w)
  have key := h.2 G' (toUnit G' ≫ x) (𝟙 G') x₀ y₀ (by
      simp [x₀, hu', hx]) (by simp [y₀])
  have e1 : lift (toUnit G' ≫ x) (𝟙 G') ≫ μ[G'] = (toUnit G' ≫ x) * 𝟙 G' := rfl
  have e2 : x₀ * y₀ = (Over.homMk φ (by simpa using h.1.w) : Over.mk (G'.hom ≫ f) ⟶ G) ≫ (lift (toUnit G ≫ s) (𝟙 G) ≫ μ[G]) := by
    rw [← Category.assoc, comp_lift, Category.comp_id]
    have hx0 : x₀ = ((Over.homMk φ (by simpa using h.1.w) : Over.mk (G'.hom ≫ f) ⟶ G) ≫ toUnit G) ≫ s := by
      apply Over.OverMorphism.ext
      simp [x₀, hu]
    rw [hx0]
    rfl
  rw [e1, ← key, e2]
  rfl
end GlobalTheory.TranslPull
