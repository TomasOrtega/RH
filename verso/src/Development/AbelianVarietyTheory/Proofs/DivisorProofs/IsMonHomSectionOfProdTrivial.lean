import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Prove the components needed by the constructor for the conclusion. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem isMonHom_section_of_prod_trivial :
    ∀ (S : Scheme.{0}) (B B₁ B₂ : Over S) [GrpObj B] [GrpObj B₁] [GrpObj B₂] (p₁ : B ⟶ B₁) (p₂ : B ⟶ B₂) (i₁ : B₁ ⟶ B), IsMonHom p₁ → IsMonHom p₂ → IsIso (lift p₁ p₂) → i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[B₂] → IsMonHom i₁ := by
  intro S B B₁ B₂ _ _ _ p₁ p₂ i₁ h₁ h₂ hiso hi₁ hi₂
  have key : ∀ {X : Over S} (f g : X ⟶ B), f ≫ p₁ = g ≫ p₁ → f ≫ p₂ = g ≫ p₂ → f = g := by
    intro X f g e₁ e₂
    rw [← cancel_mono (lift p₁ p₂)]
    ext <;> simp [e₁, e₂]
  constructor
  · apply key
    · simp [hi₁]
    · simp only [Category.assoc, hi₂, IsMonHom.one_hom]
  · apply key
    · simp only [Category.assoc, hi₁, IsMonHom.mul_hom, Category.comp_id]
      rw [tensorHom_comp_tensorHom_assoc, hi₁, tensorHom_id, id_whiskerRight, Category.id_comp]
    · simp only [Category.assoc, hi₂, IsMonHom.mul_hom]
      rw [tensorHom_comp_tensorHom_assoc, hi₂]

end GlobalTheory
