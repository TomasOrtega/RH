import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstAndFinite
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

/- English proof (translation)
Unfold `firstAndFinite`. Apply `Algebra.IsIntegral.adjoin` to reduce the goal to its premises. Introduce and unpack `x (⟨a, rfl⟩ | hx)`. Conclude with `(Algebra.IsIntegral.isIntegral a).map _`. Take `⟨i, hi⟩` from `Set.mem_iUnion.mp hx`.

Take `⟨a, -, rfl⟩` from `hi`. Conclude with `(Algebra.IsIntegral.isIntegral a).map _`.
-/
theorem firstAndFinite_isIntegral (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.IsIntegral R A] (k : ℕ) (F : Finset A) :
    Algebra.IsIntegral R (firstAndFinite R A k F) := by
  unfold firstAndFinite
  apply Algebra.IsIntegral.adjoin
  rintro x (⟨a, rfl⟩ | hx)
  · exact (Algebra.IsIntegral.isIntegral a).map _
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨a, -, rfl⟩ := hi
    exact (Algebra.IsIntegral.isIntegral a).map _

end GlobalTheory.EtC

/- English proof (translation)
The claim follows from `GlobalTheory.EtC.firstAndFinite_isIntegral`.
-/
example : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A] (k : ℕ) (F : Finset A), Algebra.IsIntegral R (firstAndFinite R A k F) := GlobalTheory.EtC.firstAndFinite_isIntegral
