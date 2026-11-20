import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottChernFormSplitZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondCountableTopologySphere
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory OnePoint
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BcUnique.bcFld_eq_zero_of_isSplit` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBottChernFormSplitZero.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.bott_chern_form_split_zero : ∀ {M : Type} [TopologicalSpace M] {n r s : ℕ} (A : HolAtlas M n) (T : HermSeq A r s), T.IsSplit → bcFld T = 0 := by
  first | exact @GlobalTheory.BcUnique.bcFld_eq_zero_of_isSplit | exact GlobalTheory.BcUnique.bcFld_eq_zero_of_isSplit | (intros; apply GlobalTheory.BcUnique.bcFld_eq_zero_of_isSplit <;> assumption)
