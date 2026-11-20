import Formalism.GradedWeylDivisibility.StatementB
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LGradedLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `r n M hM f hf μ`. Take `⟨h, hhM, hh⟩` from `lgraded_multi M hM μ Finset.univ f hf`. Use `hhM using 1` and compare the differences between its conclusion and the goal. Use extensionality with `m`. Rewrite using `[coeff_weightedHomogeneousComponent, hh]`.

Use `congr 1`. Apply `propext` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Introduce `hm a _`. Rewrite using `[← lgraded_weight_rowW, hm]`.

Introduce `hm`. Use function extensionality and compare the values at `a`. Rewrite using `[lgraded_weight_rowW]`. Conclude with `hm a (Finset.mem_univ a)`.
-/
theorem row_divided_closed_graded : RowDivClosedGraded := by
  intro r n M hM f hf μ
  obtain ⟨h, hhM, hh⟩ := lgraded_multi M hM μ Finset.univ f hf
  convert hhM using 1
  ext m
  rw [coeff_weightedHomogeneousComponent, hh]
  congr 1
  apply propext
  constructor
  · intro hm a _
    rw [← lgraded_weight_rowW, hm]
  · intro hm
    funext a
    rw [lgraded_weight_rowW]
    exact hm a (Finset.mem_univ a)

end Formalism.GradedWeylDivisibility
