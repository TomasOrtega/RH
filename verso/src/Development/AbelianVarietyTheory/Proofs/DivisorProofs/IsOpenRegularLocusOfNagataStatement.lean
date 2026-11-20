import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenRegularLocusOfNagata
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isOpen_regularLocus_of_nagata` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsOpenRegularLocusOfNagata.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.isOpen_regularLocus_of_nagata' : ∀ (B : Type) [CommRing B] [IsNoetherianRing B], (∀ (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q)))) → IsOpen {Q : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime Q.asIdeal)} := by
  first | exact @GlobalTheory.isOpen_regularLocus_of_nagata | exact GlobalTheory.isOpen_regularLocus_of_nagata | (intros; apply GlobalTheory.isOpen_regularLocus_of_nagata <;> assumption)
