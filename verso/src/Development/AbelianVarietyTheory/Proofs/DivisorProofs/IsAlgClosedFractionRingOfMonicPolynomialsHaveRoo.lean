import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRing
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing`. Consider the case `exact _root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing`. Consider the case `(apply _root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing ..)`.
-/
theorem isAlgClosed_fractionRing_of_AIC : ∀ (A : Type) [CommRing A] [IsDomain A], AIC A → IsAlgClosed (FractionRing A) := by
  first
  | exact @_root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing
  | exact _root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing
  | (apply _root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing <;> assumption)
  | (intros; apply _root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing ..)

end GlobalTheory
