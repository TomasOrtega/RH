import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceOrderCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldFiniteSupportSumOrderEqZeroStatement

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

/- English proof (translation)
Introduce `k F _ _ _ _ _ hFF n g hg`. Take `⟨hdet, hfin⟩` from `hg`. Use `⟨hfin.subset ?_, fun w hw => ⟨?_, fun v h => hw (Matrix.eq_zero_of_mulVec_eq_zero (hdet v) h)⟩⟩` and prove the remaining obligations. Introduce `v hv hu`. Apply `hv` to reduce the goal to its premises.

Simplify using `[ord, hu.2]`. Set `S : Set (Place k F)` to `{v | ¬ Unimod v (g v)} ∪ ⋃ i ∈ {i : Fin n | w i ≠ 0}, {v : Place k F | v.1 (w i) ≠ 1}`. Establish `hS : S.Finite` using `hfin.union (Set.Finite.biUnion (Set.toFinite _) fun i hi => ((GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hFF (w i) hi).1))`. Use `hS.subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hvS`.

Simplify using `only [S, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_not, not_exists] at hvS`. Take `⟨hu, hw1⟩` from `hvS`. Apply `hv` to reduce the goal to its premises. Rewrite using `[(((GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.2.2.2.2.2.1) n (g v) w hu)]`. Choose the witnesses or unpack the hypotheses as in `⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hw (funext h)`. Establish `h1 : ∀ i, v.1 (w i) ≤ 1`. Introduce `i`.

Distinguish the cases in `hi : w i = 0`. Simplify using `[hi]`. Conclude with `le_of_eq (hw1 i hi)`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `Finset.sup_le fun i _ => h1 i`.

Use `Finset.le_sup (f := fun i => v.1 (w i)) (Finset.mem_univ i0)` as an intermediate fact. Establish `e : v.1 (w i0) = 1` using `hw1 i0 hi0`. Rewrite `this` using `[e]`. Conclude with `this`.
-/
theorem lineFin : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → {v : Place k F | ord v (g v).det ≠ 0}.Finite ∧ ∀ w : Fin n → F, w ≠ 0 → {v : Place k F | nrm v ((g v).mulVec w) ≠ 1}.Finite ∧ ∀ v, (g v).mulVec w ≠ 0 := by
  intro k F _ _ _ _ _ hFF n g hg
  obtain ⟨hdet, hfin⟩ := hg
  refine ⟨hfin.subset ?_, fun w hw => ⟨?_, fun v h => hw (Matrix.eq_zero_of_mulVec_eq_zero (hdet v) h)⟩⟩
  · intro v hv hu
    apply hv
    simp [ord, hu.2]
  · let S : Set (Place k F) := {v | ¬ Unimod v (g v)} ∪
      ⋃ i ∈ {i : Fin n | w i ≠ 0}, {v : Place k F | v.1 (w i) ≠ 1}
    have hS : S.Finite := hfin.union (Set.Finite.biUnion (Set.toFinite _)
      fun i hi => ((GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hFF (w i) hi).1))
    refine hS.subset fun v hv => ?_
    by_contra hvS
    simp only [S, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_not, not_exists] at hvS
    obtain ⟨hu, hw1⟩ := hvS
    apply hv
    rw [(((GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.2.2.2.2.2.1) n (g v) w hu)]
    obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
      by_contra h; push_neg at h; exact hw (funext h)
    have h1 : ∀ i, v.1 (w i) ≤ 1 := by
      intro i
      by_cases hi : w i = 0
      · simp [hi]
      · exact le_of_eq (hw1 i hi)
    apply le_antisymm
    · exact Finset.sup_le fun i _ => h1 i
    · have := Finset.le_sup (f := fun i => v.1 (w i)) (Finset.mem_univ i0)
      have e : v.1 (w i0) = 1 := hw1 i0 hi0
      rw [e] at this; exact this

end GlobalTheory.Nef
