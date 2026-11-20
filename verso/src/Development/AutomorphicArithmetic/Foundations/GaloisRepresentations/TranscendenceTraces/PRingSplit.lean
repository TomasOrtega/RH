import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianIndEtaleOverPrimeStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Equip the data with the indicated structure. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Introduce a local definition for the expression. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.TranscendenceTraces.ringSplit_of :
    FinSec → IndDesc → RingSplit := by
  intro hF hI A B C _ _ _ _ _ _ _ _ P
  obtain ⟨O, _, _, _, hSH, hInd, hP⟩ := GlobalTheory.T.exists_strictlyHenselian_indEtale_over_prime A P.asIdeal
  letI : Algebra B (O ⊗[A] B) := (Algebra.TensorProduct.includeRight : B →ₐ[A] O ⊗[A] B).toRingHom.toAlgebra
  obtain ⟨s⟩ := hF O (O ⊗[A] B) ((O ⊗[A] B) ⊗[B] C) hSH
  have t0 : C →ₐ[B] O ⊗[A] B :=
    (s.restrictScalars B).comp (Algebra.TensorProduct.includeRight : C →ₐ[B] (O ⊗[A] B) ⊗[B] C)
  let c : O ⊗[A] B →ₐ[B] B ⊗[A] O :=
    { (Algebra.TensorProduct.comm A O B).toAlgHom.toRingHom with
      commutes' := fun b => by
        show Algebra.TensorProduct.comm A O B ((1 : O) ⊗ₜ[A] b) = b ⊗ₜ[A] (1 : O)
        simp }
  obtain ⟨E, _, _, hE, ⟨φ⟩, hC⟩ := hI A O B C hInd ⟨c.comp t0⟩
  refine ⟨E, inferInstance, inferInstance, hE, ?_, hC⟩
  haveI : (Ideal.comap (φ : E →+* O) (IsLocalRing.maximalIdeal O)).IsPrime := Ideal.comap_isPrime _ _
  refine ⟨⟨Ideal.comap (φ : E →+* O) (IsLocalRing.maximalIdeal O), inferInstance⟩, ?_⟩
  ext1
  show Ideal.comap (algebraMap A E) (Ideal.comap (φ : E →+* O) (IsLocalRing.maximalIdeal O)) = P.asIdeal
  rw [Ideal.comap_comap, ← hP]
  congr 1
  exact φ.comp_algebraMap
