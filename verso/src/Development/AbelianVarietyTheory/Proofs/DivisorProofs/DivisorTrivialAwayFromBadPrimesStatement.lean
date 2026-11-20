import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorTrivialAwayFromBadPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDivisorTrivialAwayFromBadPrimes.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.divisor_trivial_away_from_bad_primes : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (M : HermLB V.p) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ) (r : M.B.ι → V.X.functionFieldˣ) (hr : IsRatSec M.B r), NormsX V M lg r hr → ∀ S : Finset ℕ, (∀ v, resP v ∉ S → ∀ e y, lg v e y = 0) → ∀ x, (∀ p ∈ S, ¬ Ov p x) → (M.div hr).IsEqn x 1 := by
  first | exact @GlobalTheory.LatChain.isEqn_one_off | exact GlobalTheory.LatChain.isEqn_one_off | (intros; apply GlobalTheory.LatChain.isEqn_one_off <;> assumption)
