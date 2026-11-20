import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAlgebrasOverHenselianAndComplete

noncomputable section

namespace GlobalTheory

open IsLocalRing

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isLocalHom_algebraMap_of_moduleFinite (R T : Type) [CommRing R] [IsLocalRing R]
    [CommRing T] [IsLocalRing T] [Algebra R T] [Module.Finite R T] :
    IsLocalHom (algebraMap R T) := by
  constructor
  intro a ha
  by_contra hna
  haveI : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  haveI hmax : (Ideal.comap (algebraMap R T) (maximalIdeal T)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal T)
  have heq := IsLocalRing.eq_maximalIdeal hmax
  have hm : a ∈ Ideal.comap (algebraMap R T) (maximalIdeal T) := by
    rw [heq]; exact (mem_maximalIdeal a).2 hna
  exact (mem_maximalIdeal _).1 hm ha

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isSepClosed_residueField_of_moduleFinite (R T : Type) [CommRing R] [IsLocalRing R]
    [IsSepClosed (ResidueField R)] [CommRing T] [IsLocalRing T] [Algebra R T]
    [Module.Finite R T] : IsSepClosed (ResidueField T) := by
  haveI := isLocalHom_algebraMap_of_moduleFinite R T
  haveI : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  haveI : Algebra.IsIntegral (ResidueField R) (ResidueField T) := inferInstance
  haveI : Algebra.IsAlgebraic (ResidueField R) (ResidueField T) := inferInstance
  exact Algebra.IsAlgebraic.isSepClosed (F := ResidueField R)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem finite_algebra_strictly_henselian_pi : ∀ (R S : Type) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (ResidueField R)] [CommRing S] [Algebra R S] [Module.Finite R S],
    ∃ (ι : Type) (_ : Finite ι) (T : ι → Type) (_ : ∀ i, CommRing (T i))
      (_ : ∀ i, Algebra R (T i)) (_ : S ≃ₐ[R] Π i, T i) (_ : ∀ i, HenselianLocalRing (T i)),
      ∀ i, IsSepClosed (ResidueField (T i)) ∧ Module.Finite R (T i) := by
  intro R S _ _ _ _ _ _
  obtain ⟨ι, hι, T, hT, hA, e, h⟩ := ((finite_algebras_over_henselian R).1 S).1
  refine ⟨ι, hι, T, hT, hA, e, fun i ↦ (h i).1, fun i ↦ ⟨?_, (h i).2⟩⟩
  haveI := (h i).1
  haveI := (h i).2
  exact isSepClosed_residueField_of_moduleFinite R (T i)

end GlobalTheory
