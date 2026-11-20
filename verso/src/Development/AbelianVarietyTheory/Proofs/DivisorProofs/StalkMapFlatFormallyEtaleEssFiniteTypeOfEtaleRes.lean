import Mathlib
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

universe u

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ringHom_formallyEtale_of_ringEquiv {S T : Type u} [CommRing S] [CommRing T]
    (e : S ≃+* T) : (e : S →+* T).FormallyEtale := by
  algebraize [(e : S →+* T)]
  exact Algebra.FormallyEtale.of_equiv (R := S) (A := S) (B := T)
    (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl))

/- English proof (translation)
Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem ringHom_formallyEtale_respectsIso : RingHom.RespectsIso.{u} @RingHom.FormallyEtale := by
  have hiso := @ringHom_formallyEtale_of_ringEquiv.{u}
  constructor
  · intro R S T _ _ _ f e hf
    exact RingHom.FormallyEtale.comp hf (hiso e)
  · intro R S T _ _ _ f e hf
    exact RingHom.FormallyEtale.comp (hiso e) hf

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem formallyEtale_localRingHom_of_etale {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Etale) (J : Ideal S) [J.IsPrime] :
    (Localization.localRingHom (J.comap f) J f rfl).FormallyEtale := by
  algebraize [f]
  let Rₓ := Localization.AtPrime (J.comap f)
  let Sₓ := Localization.AtPrime J
  let : Algebra Rₓ Sₓ := (Localization.localRingHom _ _ _ rfl).toAlgebra
  have : IsScalarTower R Rₓ Sₓ := .of_algebraMap_eq
    fun x ↦ (Localization.localRingHom_to_map _ _ _ rfl x).symm
  have : Algebra.FormallyEtale R Sₓ := inferInstance
  have : Algebra.FormallyEtale Rₓ Sₓ :=
    Algebra.FormallyEtale.localization_base (J.comap f).primeCompl
  exact (RingHom.formallyEtale_algebraMap (R := Rₓ) (S := Sₓ)).2 this

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem formallyEtale_stalkMap_of_etale {X Y : Scheme.{0}} (g : X ⟶ Y) [Etale g] (x : X) :
    (g.stalkMap x).hom.FormallyEtale :=
  HasRingHomProperty.stalkMap_of_respectsIso (P := @Etale) (Q := RingHom.Etale)
    ringHom_formallyEtale_respectsIso
    (fun f hf J _ => formallyEtale_localRingHom_of_etale f hf J) ‹_› x

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict :
    ∀ (M W : Scheme.{0}) (f : M ⟶ W) (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U,
      (f.stalkMap y).hom.Flat ∧ (f.stalkMap y).hom.FormallyEtale ∧
        (f.stalkMap y).hom.EssFiniteType := by
  intro M W f U hg y hy
  have key : ∀ (x : M) (z : U), U.ι z = x →
      (f.stalkMap x).hom.Flat ∧ (f.stalkMap x).hom.FormallyEtale ∧
        (f.stalkMap x).hom.EssFiniteType := by
    intro x z hz
    subst hz
    have h1 := Flat.stalkMap (U.ι ≫ f) z
    have h2 := formallyEtale_stalkMap_of_etale (U.ι ≫ f) z
    have h3 := LocallyOfFiniteType.stalkMap (U.ι ≫ f) z
    have e := Scheme.Hom.stalkMap_comp U.ι f z
    rw [e] at h1 h2 h3
    have : IsIso (U.ι.stalkMap z) := (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
    refine ⟨?_, ?_, ?_⟩
    · exact (RingHom.Flat.respectsIso.cancel_right_isIso _ _).1 h1
    · exact (ringHom_formallyEtale_respectsIso.cancel_right_isIso _ _).1 h2
    · exact (RingHom.EssFiniteType.respectsIso.cancel_right_isIso _ _).1 h3
  exact key y ⟨y, hy⟩ (by simp)

end GlobalTheory
