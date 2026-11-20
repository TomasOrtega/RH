import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottChernFormReal
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
Apply `GlobalTheory.BcUnique.isRealForm_bcFld` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBottChernFormReal.lean&line=116#L116)
-/
theorem _root_.GlobalTheory.T.bott_chern_form_real : ∀ {M : Type} [TopologicalSpace M] {n r s : ℕ} (A : HolAtlas M n) (T : HermSeq A r s), A.IsRealForm 1 (bcFld T) := by
  first | exact @GlobalTheory.BcUnique.isRealForm_bcFld | exact GlobalTheory.BcUnique.isRealForm_bcFld | (intros; apply GlobalTheory.BcUnique.isRealForm_bcFld <;> assumption)
