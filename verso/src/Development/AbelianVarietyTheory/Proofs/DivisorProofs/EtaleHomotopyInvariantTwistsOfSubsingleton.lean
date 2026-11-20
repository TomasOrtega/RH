import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

/- English proof (translation)
Introduce `n`. Use `Function.bijective_iff_has_inverse.mpr ⟨pull R (inv f) F n, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Rewrite using `[← pull_comp, IsIso.inv_hom_id, pull_id]`. Introduce `x`.

Rewrite using `[← pull_comp, IsIso.hom_inv_id, pull_id]`.
-/
theorem eqv_of_isIso {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) :
    Eqv R f F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R (inv f) F n, ?_, ?_⟩
  · intro x
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · intro x
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]

/- English proof (translation)
Introduce `q _ A _ hA i`. Establish `hb : Function.Bijective (Polynomial.C : A →+* Polynomial A)` using `⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ _⟩⟩`. Set `e : A ≃+* Polynomial A` to `RingEquiv.ofBijective _ hb`. Use `haveI : IsIso (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) := (RingEquiv.toCommRingCatIso e).isIso_hom`. Use `haveI : IsIso (spMap (Polynomial.C : A →+* Polynomial A)) := by`.

Unfold `spMap`. Use `infer_instance`. Conclude with `eqv_of_isIso _ _`.
-/
theorem hInv_of_subsingleton : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], Subsingleton A → HInv q A := by
  intro q _ A _ hA i
  have hb : Function.Bijective (Polynomial.C : A →+* Polynomial A) :=
    ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  let e : A ≃+* Polynomial A := RingEquiv.ofBijective _ hb
  haveI : IsIso (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) :=
    (RingEquiv.toCommRingCatIso e).isIso_hom
  haveI : IsIso (spMap (Polynomial.C : A →+* Polynomial A)) := by
    unfold spMap; infer_instance
  exact eqv_of_isIso _ _

end GlobalTheory.EtC
