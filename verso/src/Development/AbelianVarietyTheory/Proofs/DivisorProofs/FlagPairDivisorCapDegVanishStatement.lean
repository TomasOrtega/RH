import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairDivisorCapDegVanish
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeSymmetric
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagPairDivisorCapDegVanish.lean&line=232#L232)
-/
theorem _root_.GlobalTheory.T.flag_pair_divisor_capDeg_vanish : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (W W' : B.X.Modules) (ψ : B.GenIso W W') (R R' : GlobalTheory.Vert.Model.FlagPair ψ 2) (y : PicSym B.X), B.capDeg_vp p (GlobalTheory.Vert.Model.toQ (R.div 1).cls - GlobalTheory.Vert.Model.toQ (R'.div 0).cls) ((c1 (R.fl.root 0) (R.fl.isLB_root 0) - c1 (R'.fl.root 0) (R'.fl.isLB_root 0)) * y) + B.capDeg_vp p (GlobalTheory.Vert.Model.toQ (R.div 0).cls - GlobalTheory.Vert.Model.toQ (R'.div 0).cls) ((c1 (R'.fl'.root 1) (R'.fl'.isLB_root 1) - c1 (R.fl'.root 0) (R.fl'.isLB_root 0)) * y) = 0 := by
  first | exact @GlobalTheory.FlagRankTwoStar.capDeg_rank_two_rel | exact GlobalTheory.FlagRankTwoStar.capDeg_rank_two_rel | (intros; apply GlobalTheory.FlagRankTwoStar.capDeg_rank_two_rel <;> assumption)
