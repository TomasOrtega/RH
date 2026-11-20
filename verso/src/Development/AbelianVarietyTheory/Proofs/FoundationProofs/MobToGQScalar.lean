import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
open GlobalTheory.KZ GlobalTheory.Ord2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V
open scoped MatrixGroups

namespace GlobalTheory.KZ

/- English proof (translation)
Unfold `Tower.kmap`. Establish `: (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map (RingEquiv.refl X.K).toMonoidHom))) = (LinearMap.id : Additive X.Kˣ →ₗ[ℤ] Additive X.Kˣ)`. Use extensionality with `x`. Both sides reduce to the same expression. Rewrite using `[this, LinearMap.baseChange_id, AdicCompletion.map_id]`.

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
