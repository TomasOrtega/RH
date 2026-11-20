import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockbLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `σ f hf`. Rewrite using `[LFockb_fockF_self]`. Use `⟨?_, Complex.ofReal_im _⟩` and prove the remaining obligations. Rewrite using `[Complex.ofReal_re]`. Apply `Finset.sum_pos` to reduce the goal to its premises.

Introduce `m hm`. Apply `mul_pos` to reduce the goal to its premises. Conclude with `Complex.normSq_pos.mpr (mem_support_iff.mp hm)`. Conclude with `Nat.cast_pos.mpr (Finset.prod_pos fun k _ => Nat.factorial_pos _)`. Conclude with `Finset.nonempty_of_ne_empty fun h => hf (support_eq_empty.mp h)`.
-/
theorem fischerInnerPos : FockPos := by
  intro σ f hf
  rw [LFockb_fockF_self]
  refine ⟨?_, Complex.ofReal_im _⟩
  rw [Complex.ofReal_re]
  apply Finset.sum_pos
  · intro m hm
    apply mul_pos
    · exact Complex.normSq_pos.mpr (mem_support_iff.mp hm)
    · exact Nat.cast_pos.mpr (Finset.prod_pos fun k _ => Nat.factorial_pos _)
  · exact Finset.nonempty_of_ne_empty fun h => hf (support_eq_empty.mp h)

end Formalism.GradedWeylDivisibility
