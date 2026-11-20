import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffBlockSymbolDetPowCayley
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockSymApply

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.topCoeff_blockSym_det_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FTopDegreeFormCoeffBlockSymbolDetPowCayley.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_blockSymbolDet_pow_cayley : ∀ (p q : ℕ) (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q), GlobalTheory.GoodMetric.topCoeff ((GlobalTheory.DomainDens.blockSym h1 ()).det ^ q) = ∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial) := by
  first | exact @GlobalTheory.topCoeff_blockSym_det_pow | exact GlobalTheory.topCoeff_blockSym_det_pow | (intros; apply GlobalTheory.topCoeff_blockSym_det_pow <;> assumption)
