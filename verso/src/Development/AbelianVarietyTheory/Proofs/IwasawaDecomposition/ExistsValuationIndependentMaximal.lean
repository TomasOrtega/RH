import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsValuationSubringCentre

namespace GlobalTheory.GenPert

open MvPolynomial

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Equip the data with the indicated structure.

Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Establish an intermediate fact.

Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem exists_valuationSubring_algebraicIndependent_maximalIdeal :
    ∀ (K : Type) [Field K] (J : Type) [Fintype J], ∃ (Ω : Type) (_ : Field Ω) (R : ValuationSubring Ω)
    (ι : K →+* R) (s : J → R), (∀ j, s j ∈ IsLocalRing.maximalIdeal R) ∧
      (letI : Algebra K Ω := (R.subtype.comp ι).toAlgebra; AlgebraicIndependent K fun j => (s j : Ω)) := by
  intro K _ J _
  have hP : (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial J K →+* K)).IsPrime :=
    RingHom.ker_isPrime _
  obtain ⟨V, ιV, hιV, hmax, -⟩ := GlobalTheory.LocM.Lift.exists_valuationSubring_centre (MvPolynomial J K)
    (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial J K →+* K))
  refine ⟨FractionRing (MvPolynomial J K), inferInstance, V, ιV.comp MvPolynomial.C,
    fun j => ιV (X j), fun j => hmax _ (by simp), ?_⟩
  letI : Algebra K (FractionRing (MvPolynomial J K)) := (V.subtype.comp (ιV.comp C)).toAlgebra
  let f : MvPolynomial J K →ₐ[K] FractionRing (MvPolynomial J K) :=
    { algebraMap (MvPolynomial J K) (FractionRing (MvPolynomial J K)) with
      commutes' := fun r => by
        show algebraMap (MvPolynomial J K) (FractionRing (MvPolynomial J K)) (C r) =
          V.subtype (ιV (C r))
        rw [← hιV]; rfl }
  have hf : Function.Injective f := IsFractionRing.injective _ _
  have h := (MvPolynomial.algebraicIndependent_X J K).map' hf
  convert h using 1
  funext j
  show (V.subtype.comp ιV) (X j) = _
  rw [hιV]; rfl
  all_goals rfl

end GlobalTheory.GenPert
