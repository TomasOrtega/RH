import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.InclRAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.LocalSum
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction.

Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Apply the first step, then apply the next step to every resulting obligation. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Equip the data with the indicated structure. A detailed English derivation is pending.
-/
theorem unitChoice_of_isArtinianRing_isReduced :
    ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsReduced R], PIW.AdelicOrbitU.UnitChoice R := by
  intro R _ _ _ k f hf
  classical
  let φ := IsArtinianRing.equivPi R
  have hex : ∀ I : MaximalSpectrum R, ∃ i, φ (f i) I ≠ 0 := by
    intro I
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    let ψ : R →+* R ⧸ I.asIdeal :=
      (Pi.evalRingHom (fun J : MaximalSpectrum R => R ⧸ J.asIdeal) I).comp φ.toRingHom
    have hle : Ideal.span (Set.range f) ≤ RingHom.ker ψ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (RingHom.mem_ker).2 (h i)
    rw [hf] at hle
    have h1 : ψ 1 = 0 := (RingHom.mem_ker).1 (hle Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  choose c hc using hex
  let E : Fin k → ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal := fun i I => if c I = i then 1 else 0
  refine ⟨fun i => φ.symm (E i), ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← map_mul]
    congr 1
    funext I
    simp only [E, Pi.mul_apply]
    split_ifs <;> simp
  · intro i j hij
    rw [← map_mul, ← map_zero φ.symm]
    congr 1
    funext I
    simp only [E, Pi.mul_apply, Pi.zero_apply]
    split_ifs with h1 h2 <;> simp_all
  · rw [← map_sum, ← map_one φ.symm]
    congr 1
    funext I
    simp only [E, Finset.sum_apply, Pi.one_apply]
    rw [Finset.sum_ite_eq]
    simp
  · rw [← isUnit_map_iff φ, map_sum, Pi.isUnit_iff]
    intro I
    have hcomp : (∑ i, φ (φ.symm (E i) * f i)) I = φ (f (c I)) I := by
      simp only [map_mul, AlgEquiv.apply_symm_apply, Finset.sum_apply, Pi.mul_apply, E, ite_mul,
        one_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp
    rw [hcomp]
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    letI := Ideal.Quotient.field I.asIdeal
    exact isUnit_iff_ne_zero.2 (hc I)

end GlobalTheory.CompanionTheory.SW
