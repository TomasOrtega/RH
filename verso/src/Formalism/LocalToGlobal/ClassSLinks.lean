import Formalism.LocalToGlobal.ClassS

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2

/- English proof (translation)
Take `⟨x0, hx0⟩` from `h`. Use `⟨max x0 (Fm.x1 + 1), fun x hx i hx1 => ?_⟩` and prove the remaining obligations. Take `⟨T⟩` from `hx0 x hx1 ((le_max_left _ _).trans hx) i`. Conclude with `⟨T.g⟩`.
-/
theorem gTiedF_of_C2S {eps : ℝ} (Fm : FamP eps) (h : LinkedFamiliesLevelClass Fm) : G.GroupCompatibilityFamily Fm := by
  obtain ⟨x0, hx0⟩ := h
  refine ⟨max x0 (Fm.x1 + 1), fun x hx i hx1 => ?_⟩
  obtain ⟨T⟩ := hx0 x hx1 ((le_max_left _ _).trans hx) i
  exact ⟨T.g⟩

end Formalism.L2
