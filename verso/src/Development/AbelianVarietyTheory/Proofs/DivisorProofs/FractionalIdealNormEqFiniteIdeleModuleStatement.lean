import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealNormEqFiniteIdeleModule
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LatVal.nrm_eq_modF_of_isInvIdealOf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFractionalIdealNormEqFiniteIdeleModule.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.fractionalIdealNorm_eq_finiteIdeleModule : ∀ {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h : IsInvIdealOf t 𝔞), nrm 𝔞 = modF t := by
  first | exact @GlobalTheory.LatVal.nrm_eq_modF_of_isInvIdealOf | exact GlobalTheory.LatVal.nrm_eq_modF_of_isInvIdealOf | (intros; apply GlobalTheory.LatVal.nrm_eq_modF_of_isInvIdealOf <;> assumption)
