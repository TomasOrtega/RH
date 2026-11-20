import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleHeightOneOfRegularLocalRing
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BranchPurity.etale_of_etale_height_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEtaleOfEtaleHeightOneOfRegularLocalRing.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.etale_of_etale_height_one_of_regularLocalRing : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → 1 ≤ ringKrullDim R → ¬ IsField R → (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  first | exact @GlobalTheory.BranchPurity.etale_of_etale_height_one | exact GlobalTheory.BranchPurity.etale_of_etale_height_one | (intros; apply GlobalTheory.BranchPurity.etale_of_etale_height_one <;> assumption)
