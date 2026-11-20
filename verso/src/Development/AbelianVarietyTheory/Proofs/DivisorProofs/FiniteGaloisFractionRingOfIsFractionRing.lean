import Mathlib

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Equip the data with the indicated structure. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.finiteGalois_fractionRing_of_isFractionRing :
    ∀ (A K L : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra A L], (∀ a : A, algebraMap A L a = algebraMap K L (algebraMap A K a)) → ∃ (_ : Algebra (FractionRing A) L) (_ : IsScalarTower A (FractionRing A) L), FiniteDimensional (FractionRing A) L ∧ IsGalois (FractionRing A) L ∧ ∀ (σ : L ≃ₐ[FractionRing A] L) (x : K), σ (algebraMap K L x) = algebraMap K L x := by
  intro A K L _ _ _ _ _ _ _ _ _ _ h
  let e : FractionRing A ≃ₐ[A] K := FractionRing.algEquiv A K
  letI alg : Algebra (FractionRing A) L := ((algebraMap K L).comp e.toRingHom).toAlgebra
  have hmap : ∀ y : FractionRing A, algebraMap (FractionRing A) L y = algebraMap K L (e y) :=
    fun _ => rfl
  have hcomp : (algebraMap (FractionRing A) L).comp (e.symm.toRingEquiv : K →+* FractionRing A) =
      ((RingEquiv.refl L : L ≃+* L) : L →+* L).comp (algebraMap K L) := by
    ext x; simp [hmap]
  refine ⟨alg, IsScalarTower.of_algebraMap_eq fun a => ?_, ?_, ?_, ?_⟩
  · rw [hmap, AlgEquiv.commutes, h]
  · exact Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl L) hcomp
  · exact IsGalois.of_equiv_equiv (f := e.symm.toRingEquiv) (g := RingEquiv.refl L) hcomp
  · intro σ x
    have := σ.commutes (e.symm x)
    simpa [hmap] using this

end GlobalTheory
