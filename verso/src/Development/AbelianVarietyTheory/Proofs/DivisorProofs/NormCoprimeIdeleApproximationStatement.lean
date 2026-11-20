import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoprimeIdeleApproximation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFMulPosPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSectionIntegralFiniteIdeleUpToUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option autoImplicit false

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormCoprimeIdeleApproximation.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.norm_coprime_idele_approximation : ∀ {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (k n : ℕ), 0 < n → k ∣ n → ∀ m : K, m ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 K),
      (algebraMap K (Af K) (n : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)) v ∈
        v.adicCompletionIntegers K) →
    ∃ b : ℕ, 0 < b ∧ Nat.Coprime b k ∧ |((Algebra.norm ℚ m : ℚ) : ℝ)| = b / modF t := by
  first | exact @GlobalTheory.CMVal.NormCongr.absNorm_eq_div_modF | exact GlobalTheory.CMVal.NormCongr.absNorm_eq_div_modF | (intros; apply GlobalTheory.CMVal.NormCongr.absNorm_eq_div_modF <;> assumption)
