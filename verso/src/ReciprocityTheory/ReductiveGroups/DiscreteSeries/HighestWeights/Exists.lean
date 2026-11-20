import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HcParamGapGeIndex
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelTau
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelTwist

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Use `choose m hm using hint`. Use `set C : ℤ := ∑ a, |m a| with hC`. Establish `hle : ∀ a, -C ≤ m a`. Introduce `a`. Establish `h1 : |m a| ≤ C` using `Finset.single_le_sum (f := fun a => |m a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)`.

Establish `h2` using `neg_abs_le (m a)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm' : NonnegDom ε (fun a => m a + C)`. Use `⟨fun a b hab he => ?_, fun a => by linarith [hle a]⟩` and prove the remaining obligations. Establish `h1` using `hdom a b hab he`.

Rewrite `h1` using `[hm a, hm b]`. Establish `h2 : m b ≤ m a` using `by exact_mod_cast h1`. Use `show m b + C ≤ m a + C`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨T⟩` from `model_exists ε hm'`.

Take `⟨T'⟩` from `kType_twist T (-C)`. Establish `e : (fun a => (((m a + C : ℤ)) : ℝ) + ((-C : ℤ) : ℝ)) = Λ`. Use function extensionality and compare the values at `a`. Rewrite using `[hm a]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← e]`. Conclude with `⟨T'⟩`.
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
The claim follows from `kType_exists_of_dom ε _ (lowK_int_dom ε lam hlam).1 (lowK_int_dom ε lam hlam).2`.
-/
theorem kType_exists (ε : Fin n → Bool) (lam : Fin n → ℝ) (hlam : IsHCParam lam) :
    Nonempty (KType ε (lowK ε lam)) := kType_exists_of_dom ε _ (lowK_int_dom ε lam hlam).1 (lowK_int_dom ε lam hlam).2

end ReciprocityTheory.ChartRestriction.DS.HW
