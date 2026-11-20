import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankAtStalkInvariantDifferentials
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupSche
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveOfLocalBasis
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WmodRank.rankAtStalk_wmod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRankAtStalkInvariantDifferentials.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.rank_at_stalk_invariant_differentials : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A] (d : ℕ), GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega A) d → ∀ p : PrimeSpectrum O, Module.rankAtStalk (R := O) (GlobalTheory.SqZeroPt.Wmod A) p = d := by
  first | exact @GlobalTheory.WmodRank.rankAtStalk_wmod | exact GlobalTheory.WmodRank.rankAtStalk_wmod | (intros; apply GlobalTheory.WmodRank.rankAtStalk_wmod <;> assumption)
