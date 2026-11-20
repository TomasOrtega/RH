import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
open Matrix
open scoped ComplexOrder
open GlobalTheory.HodgeLocGeo

namespace GlobalTheory.GradedGramRe

/- English proof (translation)
Introduce `n M hM i`. Establish `h0 : 0 < ReciprocityTheory.ChartRestriction.G.FD.lminor M i.castSucc` using `GlobalTheory.GradedNorm.lminor_pos hM _`. Establish `h1 : ReciprocityTheory.ChartRestriction.G.FD.lminor M i.castSucc = (GlobalTheory.HermFrame.firstGram i.2.le M).det` using `rfl`. Establish `h2 : ReciprocityTheory.ChartRestriction.G.FD.lminor M i.succ = (GlobalTheory.HermFrame.firstGram (k` using `i + 1) i.2 M).det := rfl`. Establish `hu : IsUnit (GlobalTheory.HermFrame.firstGram i.2.le M).det`.

Rewrite using `[← h1]`. Conclude with `(ne_of_gt h0).isUnit`. Establish `h` using `GlobalTheory.HermFrame.det_firstGram_succ M i hu`. Rewrite using `[GlobalTheory.GradedNorm.grSq, h2, h, ← h1, mul_div_cancel_left₀ _ (ne_of_gt h0)]`.
-/
theorem gradedGram_re_eq_grSq : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ), M.PosDef → ∀ i : Fin n,
    (GlobalTheory.HermFrame.gradedGram M i () ()).re = GlobalTheory.GradedNorm.grSq M i := by
  intro n M hM i
  have h0 : 0 < ReciprocityTheory.ChartRestriction.G.FD.lminor M i.castSucc := GlobalTheory.GradedNorm.lminor_pos hM _
  have h1 : ReciprocityTheory.ChartRestriction.G.FD.lminor M i.castSucc = (GlobalTheory.HermFrame.firstGram i.2.le M).det := rfl
  have h2 : ReciprocityTheory.ChartRestriction.G.FD.lminor M i.succ = (GlobalTheory.HermFrame.firstGram (k := i + 1) i.2 M).det := rfl
  have hu : IsUnit (GlobalTheory.HermFrame.firstGram i.2.le M).det := by
    rw [← h1]; exact (ne_of_gt h0).isUnit
  have h := GlobalTheory.HermFrame.det_firstGram_succ M i hu
  rw [GlobalTheory.GradedNorm.grSq, h2, h, ← h1, mul_div_cancel_left₀ _ (ne_of_gt h0)]

end GlobalTheory.GradedGramRe
