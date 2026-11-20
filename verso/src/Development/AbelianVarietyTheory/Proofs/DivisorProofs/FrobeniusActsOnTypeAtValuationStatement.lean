import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusActsOnTypeAtValuation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PrimePart.frobOnType_all` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFrobeniusActsOnTypeAtValuation.lean&line=149#L149)
-/
theorem _root_.GlobalTheory.T.frobenius_acts_on_type_at_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), FrobOnType io X := by
  first | exact @GlobalTheory.PrimePart.frobOnType_all | exact GlobalTheory.PrimePart.frobOnType_all | (intros; apply GlobalTheory.PrimePart.frobOnType_all <;> assumption)
