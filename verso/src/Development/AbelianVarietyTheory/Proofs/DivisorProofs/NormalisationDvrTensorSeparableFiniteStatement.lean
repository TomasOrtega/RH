import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisationDvrTensorSeparableFinite
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.NormFin.main | exact GlobalTheory.NormFin.main | (intros; apply GlobalTheory.NormFin.main <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.normalisation_dvr_tensor_separable_finite : ∀ (S K L D : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Algebra S D] [Module.Finite S D] [FaithfulSMul S D],
    Module.Finite D (integralClosure D (TensorProduct S D L)) := by
  first | exact @GlobalTheory.NormFin.main | exact GlobalTheory.NormFin.main | (intros; apply GlobalTheory.NormFin.main <;> assumption)
