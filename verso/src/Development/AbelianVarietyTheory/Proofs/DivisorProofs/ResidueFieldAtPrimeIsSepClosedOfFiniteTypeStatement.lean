import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldAtPrimeIsSepClosedOfFiniteType
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | (exact @GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType) | (exact GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType) | (intros; apply GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.residueField_atPrime_isSepClosed_of_finiteType : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B] (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) := by
  first | (exact @GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType) | (exact GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType) | (intros; apply GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType <;> assumption)
