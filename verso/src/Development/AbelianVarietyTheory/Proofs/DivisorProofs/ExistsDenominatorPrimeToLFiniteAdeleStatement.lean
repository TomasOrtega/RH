import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorPrimeToLFiniteAdele
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsDenominatorPrimeToLFiniteAdele.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.exists_denominator_prime_to_l_finiteAdele : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (z : Af E), l.Prime → (∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → Valued.v (z w) ≤ 1) → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((algebraMap E (Af E) (M : E) * z) w) ≤ 1 := by
  first | exact @GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to | exact GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to | (intros; apply GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to <;> assumption)
