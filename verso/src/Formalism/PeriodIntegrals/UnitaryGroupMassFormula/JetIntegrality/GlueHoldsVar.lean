import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.TwoUnit

noncomputable section

namespace PI.JetsPhW.W

open PI.JetsPhW

/- English proof (translation)
Introduce `hI hH hO hT`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `p _ W wq ex ph h1 h2 h3 h4 h6 hW hex hl hc i hi1 hi2`. Conclude with `hH p (PI.JetsPhW.flog W wq) ex ph ⟨hex, hl, hI p W wq h1 h2 h3 h4 h6 hW⟩ hc i hi1 hi2`. Introduce `p _ W wq ex ph h1 h2 h3 h4 h6 hW hex hl hp hc`.

Conclude with `hO p (PI.JetsPhW.flog W wq) ex ph ⟨hex, hl, hI p W wq h1 h2 h3 h4 h6 hW⟩ hp hc`. Introduce `p _ W wq ex ph a b h1 h2 h3 h4 h6 hW hex hl hc`. Conclude with `hT p (PI.JetsPhW.flog W wq) ex ph a b ⟨hex, hl, hI p W wq h1 h2 h3 h4 h6 hW⟩ hc`.
-/
theorem glue_holds_var : Glue := by
  intro hI hH hO hT
  refine ⟨?_, ?_, ?_⟩
  · intro p _ W wq ex ph h1 h2 h3 h4 h6 hW hex hl hc i hi1 hi2
    exact hH p (PI.JetsPhW.flog W wq) ex ph ⟨hex, hl, hI p W wq h1 h2 h3 h4 h6 hW⟩ hc i hi1 hi2
  · intro p _ W wq ex ph h1 h2 h3 h4 h6 hW hex hl hp hc
    exact hO p (PI.JetsPhW.flog W wq) ex ph ⟨hex, hl, hI p W wq h1 h2 h3 h4 h6 hW⟩ hp hc
  · intro p _ W wq ex ph a b h1 h2 h3 h4 h6 hW hex hl hc
    exact hT p (PI.JetsPhW.flog W wq) ex ph a b ⟨hex, hl, hI p W wq h1 h2 h3 h4 h6 hW⟩ hc

end PI.JetsPhW.W
