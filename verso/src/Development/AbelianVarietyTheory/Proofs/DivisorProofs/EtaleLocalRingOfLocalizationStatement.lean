import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalRingOfLocalization
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEtaleLocalRingOfLocalization.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.etale_local_ring_of_localization : ∀ (R A E : Type) [CommRing R] [CommRing A] [CommRing E] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime] [Algebra (Localization.AtPrime q) E] [Algebra.Etale (Localization.AtPrime q) E] [Algebra R E] [IsScalarTower R (Localization.AtPrime q) E] (P : Ideal E) [P.IsPrime], (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P)) := by
  first | exact @GlobalTheory.essEtale_atPrime_of_etale_over_atPrime | exact GlobalTheory.essEtale_atPrime_of_etale_over_atPrime | (intros; apply GlobalTheory.essEtale_atPrime_of_etale_over_atPrime <;> assumption)
