import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
open GlobalTheory.KZ GlobalTheory.Ord2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V
open scoped MatrixGroups

namespace GlobalTheory.KZ

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. By extensionality, compare the relevant components. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem Tower.kmap_refl {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (l : ℕ) [Fact l.Prime] (x : X.Khat l) : X.kmap l (RingEquiv.refl X.K) x = x := by
  unfold Tower.kmap
  have : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map (RingEquiv.refl X.K).toMonoidHom))) =
      (LinearMap.id : Additive X.Kˣ →ₗ[ℤ] Additive X.Kˣ) := by
    ext x; rfl
  rw [this, LinearMap.baseChange_id, AdicCompletion.map_id]
  rfl

end GlobalTheory.KZ
