import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockFnField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.StepTStA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

/- English proof (translation)
The claim follows from `IntermediateField.subset_adjoin ℚ _ ⟨p, q, Subsingleton.elim _ _, rfl⟩`.
-/
theorem TwoBlockFnField.ratio_mem {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (x : Ix κ → Ω)
    (p q : Ix κ) : x p / x q ∈ blockFnField (ι := GlobalTheory κ) x :=
  IntermediateField.subset_adjoin ℚ _ ⟨p, q, Subsingleton.elim _ _, rfl⟩

/- English proof (translation)
Rewrite using `[blockFnField, IntermediateField.adjoin_le_iff]`. Introduce and unpack `t ⟨p, q, -, rfl⟩`. Distinguish the cases in `h0 : ∀ j, x j = 0`. Establish `: matAct A x p = 0` using `by simp [matAct, h0]`. Rewrite using `[this, zero_div]`.

Conclude with `zero_mem _`. Take `⟨c, hc⟩` from `not_forall.mp h0`. Establish `key : ∀ i, matAct A x i / x c ∈ blockFnField (ι` using `GlobalTheory κ) x := by`. Introduce `i`. Establish `: matAct A x i / x c = ∑ j, (A i j : Ω) * (x j / x c)`.

Simplify using `only [matAct, Finset.sum_div, mul_div_assoc]`. Rewrite using `[this]`. Use `sum_mem fun j _ => mul_mem ?_ (TwoBlockFnField.ratio_mem x j c)` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `: matAct A x p / matAct A x q = (matAct A x p / x c) / (matAct A x q / x c)`.

Rewrite using `[div_div_div_cancel_right₀ hc]`. Rewrite using `[this]`. Conclude with `div_mem (key p) (key q)`.
-/
theorem TwoBlockFnField.matAct_le {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (x : Ix κ → Ω)
    (A : Matrix (Ix κ) (Ix κ) ℚ) :
    blockFnField (ι := GlobalTheory κ) (matAct A x) ≤ blockFnField (ι := GlobalTheory κ) x := by
  rw [blockFnField, IntermediateField.adjoin_le_iff]
  rintro t ⟨p, q, -, rfl⟩
  by_cases h0 : ∀ j, x j = 0
  · have : matAct A x p = 0 := by simp [matAct, h0]
    rw [this, zero_div]
    exact zero_mem _
  · obtain ⟨c, hc⟩ := not_forall.mp h0
    have key : ∀ i, matAct A x i / x c ∈ blockFnField (ι := GlobalTheory κ) x := by
      intro i
      have : matAct A x i / x c = ∑ j, (A i j : Ω) * (x j / x c) := by
        simp only [matAct, Finset.sum_div, mul_div_assoc]
      rw [this]
      refine sum_mem fun j _ => mul_mem ?_ (TwoBlockFnField.ratio_mem x j c)
      simp
    have : matAct A x p / matAct A x q = (matAct A x p / x c) / (matAct A x q / x c) := by
      rw [div_div_div_cancel_right₀ hc]
    rw [this]
    exact div_mem (key p) (key q)

/- English proof (translation)
Take `⟨B', -, h⟩` from `isInvMat_mul hB`. Use `le_antisymm (TwoBlockFnField.matAct_le x B) ?_` and prove the remaining obligations. Use `TwoBlockFnField.matAct_le (matAct B x) B'` as an intermediate fact. Rewrite `this` using `[matAct_matAct h]`. Then use the resulting hypothesis.
-/
theorem TwoBlockFnField.matAct_eq {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (hB : IsInvMat B) :
    blockFnField (ι := GlobalTheory κ) (matAct B x) = blockFnField (ι := GlobalTheory κ) x := by
  classical
  obtain ⟨B', -, h⟩ := isInvMat_mul hB
  refine le_antisymm (TwoBlockFnField.matAct_le x B) ?_
  have := TwoBlockFnField.matAct_le (matAct B x) B'
  rwa [matAct_matAct h] at this

/- English proof (translation)
Introduce `Ω _ _ κ _ x B hB`. Establish `hE` using `TwoBlockFnField.matAct_eq x B hB`. Use `⟨le_antisymm ?_ ?_, hE⟩` and prove the remaining obligations. Rewrite using `[blockFnField, IntermediateField.adjoin_le_iff]`. Introduce and unpack `t ⟨p, q, hpq, rfl⟩`.

Take `⟨b, i⟩` from `p`. Take `⟨b', j⟩` from `q`. Simplify using `only at hpq`. Substitute `hpq` using the available equality. Distinguish the cases in `hb : b = 0`.

Substitute `hb` using the available equality. Simplify `TwoBlockFnField.ratio_mem x ⟨(), i⟩ ⟨(), j⟩` using `[pair]`. Simplify using `only [pair, hb, if_false]`. Rewrite using `[← hE]`. Conclude with `TwoBlockFnField.ratio_mem (matAct B x) ⟨(), i⟩ ⟨(), j⟩`.

Use `IntermediateField.adjoin_le_iff.mpr ?_` and prove the remaining obligations. Introduce and unpack `t ⟨⟨u, i⟩, ⟨u', j⟩, -, rfl⟩`. Consider the cases of `u`. Consider the cases of `u'`. Use `IntermediateField.subset_adjoin ℚ _ ⟨⟨0, i⟩, ⟨0, j⟩, rfl, ?_⟩` and prove the remaining obligations.

Simplify using `[pair]`.
-/
theorem TwoBlockFnField.proof : TwoBlockFnField.Statement := by
  intro Ω _ _ κ _ x B hB
  have hE := TwoBlockFnField.matAct_eq x B hB
  refine ⟨le_antisymm ?_ ?_, hE⟩
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨p, q, hpq, rfl⟩
    obtain ⟨b, i⟩ := p
    obtain ⟨b', j⟩ := q
    simp only at hpq
    subst hpq
    by_cases hb : b = 0
    · subst hb
      simpa [pair] using TwoBlockFnField.ratio_mem x ⟨(), i⟩ ⟨(), j⟩
    · simp only [pair, hb, if_false]
      rw [← hE]
      exact TwoBlockFnField.ratio_mem (matAct B x) ⟨(), i⟩ ⟨(), j⟩
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro t ⟨⟨u, i⟩, ⟨u', j⟩, -, rfl⟩
    cases u; cases u'
    refine IntermediateField.subset_adjoin ℚ _ ⟨⟨0, i⟩, ⟨0, j⟩, rfl, ?_⟩
    simp [pair]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
