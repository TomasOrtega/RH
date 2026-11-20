import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealGeneratedPrimeToL
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFractionalIdealGeneratedPrimeToL.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.fractional_ideal_generated_prime_to_l : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (l : ℕ) [Fact l.Prime],
    ∃ c₀ : 𝔠.elt, (c₀ : F) ≠ 0 ∧ ∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 F), n.Coprime l ∧ n • c = t • c₀ := by
  first | exact @GlobalTheory.FracGen.exists_gen | exact GlobalTheory.FracGen.exists_gen | (intros; apply GlobalTheory.FracGen.exists_gen <;> assumption)
