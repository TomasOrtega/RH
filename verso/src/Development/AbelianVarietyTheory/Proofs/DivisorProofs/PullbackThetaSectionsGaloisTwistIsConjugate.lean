import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem comp_mTw_left_eq {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R)))
    (σ : Kb R →ₐ[FractionRing R] Kb R) {Z : Scheme.{0}} {p p' : Z ⟶ (TFK (R := R) (Kb R) ⊗ A.A).left}
    (h₂ : p' ≫ (snd (TFK (R := R) (Kb R)) A.A).left = p ≫ (snd (TFK (R := R) (Kb R)) A.A).left)
    (h₁ : p' ≫ (fst (TFK (R := R) (Kb R)) A.A).left =
      p ≫ (fst (TFK (R := R) (Kb R)) A.A).left ≫ spMap σ.toRingHom) :
    p ≫ (mTw A σ).left = p' := by
  refine pullback.hom_ext (f := (TFK (R := R) (Kb R)).hom) (g := A.A.hom) ?_ ?_
  · change (p ≫ (mTw A σ).left) ≫ (fst (TFK (R := R) (Kb R)) A.A).left = p' ≫ (fst (TFK (R := R) (Kb R)) A.A).left
    rw [Category.assoc, mTw_fst_left, h₁]
  · change (p ≫ (mTw A σ).left) ≫ (snd (TFK (R := R) (Kb R)) A.A).left = p' ≫ (snd (TFK (R := R) (Kb R)) A.A).left
    rw [Category.assoc, mTw_snd_left, h₂]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem secTw_isTwist (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (t : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) :
    SecTw σ t (secTw A N σ t) := by
  intro Z p p' h₂ h₁ z J hJ
  rw [← comp_mTw_left_eq A σ h₂ h₁]
  exact GlobalTheory.FieldBaseChange.sval_pullOver (mTw_fst_left A σ) (fun _ => (mTw_snd_left A σ).symm) t p hJ

end GlobalTheory.Mum.Conj
