import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassPullbackFibreDegree
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHomPull
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PresPullCk.ck_pull` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChernClassPullbackFibreDegree.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.chern_class_pullback_fibre_degree : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B B' : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → GlobalTheory.IsNormalScheme B'.X → ∀ (f : GlobalTheory.Vert.Model.Hom B' B), f.relDim = 0 → ∀ (P : Pres B) (k : ℕ) (Q : PicSym B.X), (P.pull f).ck p k (picSymPull f.f Q) = f.fibreDeg 1 * P.ck p k Q := by
  first | exact @GlobalTheory.PresPullCk.ck_pull | exact GlobalTheory.PresPullCk.ck_pull | (intros; apply GlobalTheory.PresPullCk.ck_pull <;> assumption)
