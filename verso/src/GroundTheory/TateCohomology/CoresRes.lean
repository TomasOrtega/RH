import Mathlib
import GroundTheory.TateCohomology.ResCores
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Additive

variable [Fintype G]

instance tateCohomologyFunctor_additive (n : ℤ) :
    (tateCohomologyFunctor (R := k) (G := G) n).Additive := by
  unfold tateCohomologyFunctor
  infer_instance

end Additive

section Rep

variable (S : Subgroup G) [S.FiniteIndex] [DecidableRel (QuotientGroup.rightRel S)]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

omit [S.FiniteIndex] [DecidableRel (QuotientGroup.rightRel S)] in

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((indResHomEquiv _ _ _).symm (𝟙 _)).hom _ = _`. Simplify using the standard rewrite rules.
-/
theorem indResAdjunction_counit_app_hom_mk (A : Rep.{u} k G) (g : G) (a : A) :
    ((indResAdjunction k S.subtype).counit.app A).hom
      (Representation.IndV.mk S.subtype (res S.subtype A).ρ g a) = A.ρ g⁻¹ a := by
  change ((indResHomEquiv _ _ _).symm (𝟙 _)).hom _ = _
  simp

/- English proof (translation)
Use extensionality with `a`. Express the relevant statement in the definitionally equal form `((indResAdjunction k S.subtype).counit.app A).hom (coindToInd (res S.subtype A) (((resCoindAdjunction.{u, u} k S.subtype).unit.app A).hom a)) = S.index • a`. Rewrite using `[coindToInd_apply, map_sum]`. Use `(Finset.sum_congr rfl (g := fun _ => a) fun x _ => ?_).trans ?_` and prove the remaining obligations. Proceed by induction on `x using Quotient.inductionOn with`.

Consider the case `h g`. Rewrite using `[Quotient.liftOn_mk, indResAdjunction_counit_app_hom_mk]`. Express the relevant statement in the definitionally equal form `A.ρ g⁻¹ (A.ρ g a) = a`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Rewrite using `[Finset.sum_const, Finset.card_univ]`.

Use `congr 1`. Rewrite using `[← Nat.card_eq_fintype_card, Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)]`. Both sides reduce to the same expression.
-/
theorem unit_comp_indCoindIso_inv_comp_counit (A : Rep.{u} k G) :
    (resCoindAdjunction.{u, u} k S.subtype).unit.app A ≫ (indCoindIso (res S.subtype A)).inv ≫
      (indResAdjunction.{u} k S.subtype).counit.app A = S.index • 𝟙 A := by
  ext a
  change ((indResAdjunction k S.subtype).counit.app A).hom
      (coindToInd (res S.subtype A) (((resCoindAdjunction.{u, u} k S.subtype).unit.app A).hom a)) =
    S.index • a
  rw [coindToInd_apply, map_sum]
  refine (Finset.sum_congr rfl (g := fun _ => a) fun x _ => ?_).trans ?_
  · induction x using Quotient.inductionOn with
    | h g =>
      rw [Quotient.liftOn_mk, indResAdjunction_counit_app_hom_mk]
      change A.ρ g⁻¹ (A.ρ g a) = a
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · rw [Finset.sum_const, Finset.card_univ]
    congr 1
    rw [← Nat.card_eq_fintype_card,
      Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)]
    rfl

end Rep

section Tate

variable [Fintype G] (S : Subgroup G) [Fintype S]

open scoped Classical in

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tateIndIso_inv_eq (B : Rep.{u} k S) (n : ℤ) :
    (tateIndIso S B n).inv =
      (tateCoindIso S B n).inv ≫ (tateCohomologyFunctor n).map (indCoindIso.{u, u, u} B).inv :=
  rfl

/- English proof (translation)
Rewrite using `[tateRes_app, tateCores_app, tateIndIso_inv_eq, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, ← Functor.map_comp, unit_comp_indCoindIso_inv_comp_counit, Functor.map_nsmul]`. Conclude with `congrArg (S.index • ·) ((tateCohomologyFunctor n).map_id A)`.
-/
theorem tateRes_app_comp_tateCores_app (A : Rep.{u} k G) (n : ℤ) :
    (tateRes S n).app A ≫ (tateCores S n).app A = S.index • 𝟙 (tateCohomology A n) := by
  rw [tateRes_app, tateCores_app, tateIndIso_inv_eq, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, ← Functor.map_comp, ← Functor.map_comp,
    unit_comp_indCoindIso_inv_comp_counit, Functor.map_nsmul]
  exact congrArg (S.index • ·) ((tateCohomologyFunctor n).map_id A)

end Tate

end GroundTheory.GroupCoh
