import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHenselianFlatOverPrime
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FExistsHenselianFlatOverPrime.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_henselian_flat_over_prime : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (P : Ideal R) [P.IsPrime], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : HenselianLocalRing R') (_ : Algebra R R'), IsIntegrallyClosed R' ∧ Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime | exact GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime | (intros; apply GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime <;> assumption)
