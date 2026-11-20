import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoInclLast
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsIsoInclLast.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.isIso_incl_last' : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι), IsIso (incl ι N τ (Fin.last N)) := by
  first | exact @GlobalTheory.FlagZ.Univ.isIso_incl_last | exact GlobalTheory.FlagZ.Univ.isIso_incl_last | (intros; apply GlobalTheory.FlagZ.Univ.isIso_incl_last <;> assumption)
