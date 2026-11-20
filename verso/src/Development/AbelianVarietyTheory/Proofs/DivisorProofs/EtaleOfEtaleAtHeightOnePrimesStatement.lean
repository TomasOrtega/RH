import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleAtHeightOnePrimes
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEtaleOfEtaleAtHeightOnePrimes.lean&line=167#L167)
-/
theorem _root_.GlobalTheory.T.etale_of_etale_at_height_one_primes : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A], ¬ IsField R → (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  first | exact @GlobalTheory.PurityDisc.etale_of_etale_height_one | exact GlobalTheory.PurityDisc.etale_of_etale_height_one | (intros; apply GlobalTheory.PurityDisc.etale_of_etale_height_one <;> assumption)
