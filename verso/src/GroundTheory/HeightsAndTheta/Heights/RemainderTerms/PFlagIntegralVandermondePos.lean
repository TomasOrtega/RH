import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagBasic
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

/- English proof (translation)
Introduce `f N`. Unfold `flagIntegral`. Establish `hne : (blockVandermonde f N).support.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]`. Conclude with `Flag.blockVandermonde_ne_zero f N`.

Use `Finset.sum_pos (fun α hα => ?_) hne` and prove the remaining obligations. Establish `hc : coeff α (blockVandermonde f N) ≠ 0` using `mem_support_iff.mp hα`. Use `mul_pos (mul_self_pos.mpr hc) ?_` and prove the remaining obligations. Unfold `Finsupp.prod`. Conclude with `Finset.prod_pos fun i _ => by simp only; exact_mod_cast Nat.factorial_pos _`.
-/
theorem FlagIntegralVandermondePos.proof : FlagIntegralVandermondePos.Statement := by
  intro f N
  unfold flagIntegral
  have hne : (blockVandermonde f N).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact Flag.blockVandermonde_ne_zero f N
  refine Finset.sum_pos (fun α hα => ?_) hne
  have hc : coeff α (blockVandermonde f N) ≠ 0 := mem_support_iff.mp hα
  refine mul_pos (mul_self_pos.mpr hc) ?_
  unfold Finsupp.prod
  exact Finset.prod_pos fun i _ => by simp only; exact_mod_cast Nat.factorial_pos _

end RestTerms

end GroundTheory.Heights₂.Heights
