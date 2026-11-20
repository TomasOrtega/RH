import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HcParamGapGeIndex
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelTau
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelTwist

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem kType_exists_of_dom (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hint : ∀ a, ∃ m : ℤ, Λ a = m)
    (hdom : ∀ a b, a < b → ε a = ε b → Λ b ≤ Λ a) : Nonempty (KType ε Λ) := by
  choose m hm using hint
  set C : ℤ := ∑ a, |m a| with hC
  have hle : ∀ a, -C ≤ m a := by
    intro a
    have h1 : |m a| ≤ C :=
      Finset.single_le_sum (f := fun a => |m a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
    have h2 := neg_abs_le (m a)
    linarith
  have hm' : NonnegDom ε (fun a => m a + C) := by
    refine ⟨fun a b hab he => ?_, fun a => by linarith [hle a]⟩
    have h1 := hdom a b hab he
    rw [hm a, hm b] at h1
    have h2 : m b ≤ m a := by exact_mod_cast h1
    show m b + C ≤ m a + C
    linarith
  obtain ⟨T⟩ := model_exists ε hm'
  obtain ⟨T'⟩ := kType_twist T (-C)
  have e : (fun a => (((m a + C : ℤ)) : ℝ) + ((-C : ℤ) : ℝ)) = Λ := by
    funext a
    rw [hm a]
    push_cast
    ring
  rw [← e]
  exact ⟨T'⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kType_exists (ε : Fin n → Bool) (lam : Fin n → ℝ) (hlam : IsHCParam lam) :
    Nonempty (KType ε (lowK ε lam)) := kType_exists_of_dom ε _ (lowK_int_dom ε lam hlam).1 (lowK_int_dom ε lam hlam).2

end ReciprocityTheory.ChartRestriction.DS.HW
