import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeOddSplitUnramifiedPrime
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OscSplit.oscLe_split` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDepthOscillationLeOddSplitUnramifiedPrime.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.depth_oscillation_le_odd_split_unramified_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ (p : ℤ) ∣ discr E → SplitInK H p → OscLe Xo c p cx ((F * m * Mb + Sm) / ((p : ℝ) - 1)) := by
  first | exact @GlobalTheory.OscSplit.oscLe_split | exact GlobalTheory.OscSplit.oscLe_split | (intros; apply GlobalTheory.OscSplit.oscLe_split <;> assumption)
