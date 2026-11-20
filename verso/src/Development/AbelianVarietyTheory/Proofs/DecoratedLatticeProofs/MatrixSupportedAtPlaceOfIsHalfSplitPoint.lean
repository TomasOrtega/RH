import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.FinPl.SplitHalfSupp

/- English proof (translation)
Introduce `D k _ _ _ _ q m n w hw i j`. Take `⟨ε, hε, heq⟩` from `q.above`. Rewrite using `[(placeIdem_acts D q.v ε hε).1, ← heq]`. Conclude with `hw i j`.
-/
theorem mxAt_of_isHalf_above : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) (m n : ℕ) (w : Mx D m n), IsHalf (q.e + cA D q.e) w → MxAt (· = q.v) w := by
  intro D k _ _ _ _ q m n w hw i j
  obtain ⟨ε, hε, heq⟩ := q.above
  rw [(placeIdem_acts D q.v ε hε).1, ← heq]
  exact hw i j

end GlobalTheory.FinPl.SplitHalfSupp

end
