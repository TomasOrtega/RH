import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerFromCoordinatesProductLaw
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FCommonStabilizerFromCoordinatesProductLaw.lean&line=142#L142)
-/
theorem _root_.GlobalTheory.T.commonStabilizerFromCoordinates_product_law : ∀ (k r j : ℕ) (β : Fin r → ℕ), crd k r j β 0 = 1 ∧ ∀ p q w : (UTin β → ℂ) × PTop k r j, crd k r j β p * crd k r j β q = crd k r j β w → (∀ i : UTin β, (∀ l : UTin β, l.1.1.2.val - l.1.1.1.val < i.1.1.2.val - i.1.1.1.val → p.1 l = 0) → w.1 i = p.1 i + q.1 i) ∧ (p.1 = 0 → w.2.1 = p.2.1 + q.2.1) ∧ (p.1 = 0 → p.2.1 = 0 → w.2.2 = p.2.2 + q.2.2) := by
  first | exact @GlobalTheory.DegVol.RefCovMul.crd_mul | exact GlobalTheory.DegVol.RefCovMul.crd_mul | (intros; apply GlobalTheory.DegVol.RefCovMul.crd_mul <;> assumption)
