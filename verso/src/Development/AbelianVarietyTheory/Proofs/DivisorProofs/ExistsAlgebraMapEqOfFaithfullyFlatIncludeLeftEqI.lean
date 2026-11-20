import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_algebraMap_eq_of_includeLeft_eq_includeRight :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B] (b : B),
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) b =
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) b →
      ∃ a : A, algebraMap A B a = b := by
  intro A B _ _ _ _ b hb
  have h := Algebra.IsEffective.of_faithfullyFlat A B
  have h0 : Algebra.TensorProduct.includeLeftSubRight A B b = 0 := by
    rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]
    simpa using hb
  obtain ⟨a, ha⟩ := (h b).mp h0
  exact ⟨a, by simpa using ha⟩

end GlobalTheory.EtC
