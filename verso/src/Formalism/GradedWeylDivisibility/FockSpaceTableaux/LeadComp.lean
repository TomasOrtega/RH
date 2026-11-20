import Formalism.GradedWeylDivisibility.StatementC

open MvPolynomial

open scoped MonomialOrder

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `R _ r n M _ w f`. Distinguish the cases in `hf : f = 0`. Substitute `hf` using the available equality. Simplify using the standard rewrite rules. Establish `hd : (colLex r n).degree f ∈ (weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f).support`.

Rewrite using `[mem_support_iff, coeff_weightedHomogeneousComponent, if_pos rfl]`. Conclude with `(colLex r n).coeff_degree_ne_zero_iff.mpr hf`. Establish `hg0 : weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f ≠ 0`. Introduce `h`. Rewrite `hd` using `[h]`.

Simplify using `at hd`. Establish `h1` using `(colLex r n).le_degree hd`. Establish `h2 : (colLex r n).toSyn ((colLex r n).degree (weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f)) ≤ (colLex r n).toSyn ((colLex r n).degree f)`. Apply `(colLex r n).le_degree` to reduce the goal to its premises. Establish `h3` using `(colLex r n).degree_mem_support hg0`.

Rewrite `h3` using `[mem_support_iff, coeff_weightedHomogeneousComponent]`. Use `split_ifs at h3 with h`. Conclude with `mem_support_iff.mpr h3`. Conclude with `absurd rfl h3`. Conclude with `(colLex r n).toSyn.injective (le_antisymm h2 h1)`.
-/
theorem leadingComponent : LeadComp := by
  intro R _ r n M _ w f
  classical
  by_cases hf : f = 0
  · subst hf; simp
  have hd : (colLex r n).degree f ∈
      (weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f).support := by
    rw [mem_support_iff, coeff_weightedHomogeneousComponent, if_pos rfl]
    exact (colLex r n).coeff_degree_ne_zero_iff.mpr hf
  have hg0 : weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f ≠ 0 := by
    intro h; rw [h] at hd; simp at hd
  have h1 := (colLex r n).le_degree hd
  have h2 : (colLex r n).toSyn ((colLex r n).degree
      (weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f)) ≤
      (colLex r n).toSyn ((colLex r n).degree f) := by
    apply (colLex r n).le_degree
    have h3 := (colLex r n).degree_mem_support hg0
    rw [mem_support_iff, coeff_weightedHomogeneousComponent] at h3
    split_ifs at h3 with h
    · exact mem_support_iff.mpr h3
    · exact absurd rfl h3
  exact (colLex r n).toSyn.injective (le_antisymm h2 h1)

end Formalism.GradedWeylDivisibility
