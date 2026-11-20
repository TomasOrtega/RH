import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.DimChart

/- English proof (translation)
Use `(ConcreteCategory.isIso_iff_bijective _).mpr ⟨(j.residueFieldMap x).hom.injective, ?_⟩` and prove the remaining obligations. Introduce `a`. Take `⟨b, rfl⟩` from `X.residue_surjective x a`. Take `⟨c, rfl⟩` from `j.stalkMap_surjective x b`. Use `⟨Y.residue _ c, ?_⟩` and prove the remaining obligations.

Rewrite using `[← CommRingCat.comp_apply, Scheme.residue_residueFieldMap]`. Both sides reduce to the same expression.
-/
theorem isIso_residueFieldMap {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) :
    IsIso (j.residueFieldMap x) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨(j.residueFieldMap x).hom.injective, ?_⟩
  intro a
  obtain ⟨b, rfl⟩ := X.residue_surjective x a
  obtain ⟨c, rfl⟩ := j.stalkMap_surjective x b
  refine ⟨Y.residue _ c, ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap]
  rfl

noncomputable def residueFieldEquiv {Y : Scheme.{0}} {B : Type} [CommRing B] (j : Spec (.of B) ⟶ Y)
    [IsOpenImmersion j] (q : PrimeSpectrum B) :
    Y.residueField (j q) ≃+* q.asIdeal.ResidueField :=
  haveI := isIso_residueFieldMap j q
  (asIso (j.residueFieldMap q) ≪≫ Scheme.Spec.residueFieldIso (.of B) q).commRingCatIsoToRingEquiv

/- English proof (translation)
Take `rfl : ‹Algebra ℤ A› = Ring.toIntAlgebra A` from `Subsingleton.elim _ _`. Take `rfl : ‹Algebra ℤ L› = Ring.toIntAlgebra L` from `Subsingleton.elim _ _`. Establish `: FaithfulSMul A L` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective A L)`. Establish `: FaithfulSMul ℤ A` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hA`. Establish `: Algebra.IsAlgebraic A L` using `IsLocalization.isAlgebraic L (nonZeroDivisors A)`.

Rewrite using `[← trdeg_add_eq ℤ A (A := L), trdeg_eq_zero (R := A) (A := L), add_zero]`.
-/
theorem trdeg_int_eq_of_isFractionRing (A : Type) [CommRing A] [IsDomain A] [Algebra ℤ A] (L : Type)
    [Field L] [Algebra ℤ L] [Algebra A L] [IsFractionRing A L]
    (hA : Function.Injective (algebraMap ℤ A)) :
    Algebra.trdeg ℤ A = Algebra.trdeg ℤ L := by
  obtain rfl : ‹Algebra ℤ A› = Ring.toIntAlgebra A := Subsingleton.elim _ _
  obtain rfl : ‹Algebra ℤ L› = Ring.toIntAlgebra L := Subsingleton.elim _ _
  have : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective A L)
  have : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).2 hA
  have : Algebra.IsAlgebraic A L := IsLocalization.isAlgebraic L (nonZeroDivisors A)
  rw [← trdeg_add_eq ℤ A (A := L), trdeg_eq_zero (R := A) (A := L), add_zero]

/- English proof (translation)
Take `rfl : ‹Algebra ℤ L› = Ring.toIntAlgebra L` from `Subsingleton.elim _ _`. Take `rfl : ‹Algebra ℤ L'› = Ring.toIntAlgebra L'` from `Subsingleton.elim _ _`. Conclude with `e.toIntAlgEquiv.trdeg_eq`.
-/
theorem trdeg_int_eq_of_ringEquiv {L L' : Type} [CommRing L] [CommRing L'] [Algebra ℤ L]
    [Algebra ℤ L'] (e : L ≃+* L') : Algebra.trdeg ℤ L = Algebra.trdeg ℤ L' := by
  obtain rfl : ‹Algebra ℤ L› = Ring.toIntAlgebra L := Subsingleton.elim _ _
  obtain rfl : ‹Algebra ℤ L'› = Ring.toIntAlgebra L' := Subsingleton.elim _ _
  exact e.toIntAlgEquiv.trdeg_eq

/- English proof (translation)
Establish `e` using `residueFieldEquiv j q`. Establish `: CharZero q.asIdeal.ResidueField` using `charZero_of_injective_ringHom (f := e.toRingHom) e.injective`. Establish `hinj : Function.Injective (algebraMap ℤ (B ⧸ q.asIdeal))`. Establish `hK : Function.Injective ((algebraMap (B ⧸ q.asIdeal) q.asIdeal.ResidueField).comp (algebraMap ℤ (B ⧸ q.asIdeal)))`. Rewrite using `[show (algebraMap (B ⧸ q.asIdeal) q.asIdeal.ResidueField).comp (algebraMap ℤ (B ⧸ q.asIdeal)) = Int.castRingHom _ from Subsingleton.elim _ _]`.

Conclude with `Int.cast_injective`. Rewrite `hK` using `[RingHom.coe_comp]`. Conclude with `Function.Injective.of_comp hK`. Establish `: Algebra.FiniteType ℤ (B ⧸ q.asIdeal)` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ q.asIdeal) (Ideal.Quotient.mkₐ_surjective _ _)`. Rewrite using `[GroundTheory.Heights₂.Heights.IntDomainDim.proof (B ⧸ q.asIdeal) hinj, trdeg_int_eq_of_isFractionRing (B ⧸ q.asIdeal) q.asIdeal.ResidueField hinj, trdeg_int_eq_of_ringEquiv e.symm]`.
-/
theorem ringKrullDim_quotient_eq (Y : Scheme.{0}) (B : Type) [CommRing B] [Algebra ℤ B]
    [Algebra.FiniteType ℤ B] (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B)
    (h0 : CharZero (Y.residueField (j q))) :
    ringKrullDim (B ⧸ q.asIdeal) =
      (((Algebra.trdeg ℤ (Y.residueField (j q))).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  have e := residueFieldEquiv j q
  have : CharZero q.asIdeal.ResidueField := charZero_of_injective_ringHom (f := e.toRingHom) e.injective
  have hinj : Function.Injective (algebraMap ℤ (B ⧸ q.asIdeal)) := by
    have hK : Function.Injective
        ((algebraMap (B ⧸ q.asIdeal) q.asIdeal.ResidueField).comp (algebraMap ℤ (B ⧸ q.asIdeal))) := by
      rw [show (algebraMap (B ⧸ q.asIdeal) q.asIdeal.ResidueField).comp
        (algebraMap ℤ (B ⧸ q.asIdeal)) = Int.castRingHom _ from Subsingleton.elim _ _]
      exact Int.cast_injective
    rw [RingHom.coe_comp] at hK
    exact Function.Injective.of_comp hK
  have : Algebra.FiniteType ℤ (B ⧸ q.asIdeal) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ q.asIdeal) (Ideal.Quotient.mkₐ_surjective _ _)
  rw [GroundTheory.Heights₂.Heights.IntDomainDim.proof (B ⧸ q.asIdeal) hinj,
    trdeg_int_eq_of_isFractionRing (B ⧸ q.asIdeal) q.asIdeal.ResidueField hinj,
    trdeg_int_eq_of_ringEquiv e.symm]

end GlobalTheory.CompanionTheory.DimChart
