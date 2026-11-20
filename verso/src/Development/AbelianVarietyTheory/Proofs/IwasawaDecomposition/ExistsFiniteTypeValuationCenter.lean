import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteTypeSubalgebraValuationLeOne
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one`. Consider the case `exact _root_.GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one`. Consider the case `(apply _root_.GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one ..)`.
-/
theorem valuativeChart_exists_fg_subalgebra :
    ∀ (A B k : Type) [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
      [Algebra.EssFiniteType A B] [Field k] (φ : B →+* k) (V : ValuationSubring k),
      RingHom.ker φ = maximalIdeal B → (∀ a : A, V.valuation (φ (algebraMap A B a)) ≤ 1) →
      ∃ C : Subalgebra A B, Algebra.FiniteType A C ∧ (∀ c ∈ C, V.valuation (φ c) ≤ 1) ∧
        ∀ b : B, ∃ a ∈ C, ∃ s ∈ C, IsUnit s ∧ s * b = a := by
  first
  | exact @_root_.GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one
  | exact _root_.GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one
  | (apply _root_.GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one ..)

end GlobalTheory
