import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtaleAwayOfEtaleOffMaximalIdeal
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFormallyEtaleAwayOfEtaleOffMaximalIdeal.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.formallyEtale_away_of_etale_off_maximalIdeal : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ∀ g ∈ maximalIdeal R, Algebra.FormallyEtale (Localization.Away g) (TensorProduct R (Localization.Away g) A) := by
  first | exact @GlobalTheory.EtaleAway.formallyEtale_away | exact GlobalTheory.EtaleAway.formallyEtale_away | (intros; apply GlobalTheory.EtaleAway.formallyEtale_away <;> assumption)
