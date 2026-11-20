import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Near1

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Supply the required witnesses or components. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Win.exc :
    ∀ (l R : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀], ABound l R L₀ →
      ∃ c : ℕ, (∃ ζ : L₀, IsPrimitiveRoot ζ (l ^ c)) ∧ ∀ Z : ℕ, ∃ Exc : Finset ℕ, FirstBound l R c L₀ Z Exc := by
  intro l R _ L₀ _ h
  classical
  obtain ⟨⟨K, _, _, hU, c, R', s, hR', hζ, hb⟩, -⟩ := h
  refine ⟨c, hζ, fun Z => ?_⟩
  obtain ⟨near, hnear⟩ : ∃ near : Fin R' → Finset ℕ, near = fun i =>
      (Finset.Icc 1 Z : Finset ℕ).filter
        (fun e : ℕ => ‖s i - (e : K)‖ < (l : ℝ) ^ (-(Nat.log l Z : ℤ))) :=
    ⟨_, rfl⟩
  refine ⟨Finset.univ.biUnion near, ?_⟩
  unfold FirstBound
  refine ⟨?_, ?_⟩
  · have hone : ∀ i : Fin R', (near i).card ≤ 1 := by
      intro i
      rw [Finset.card_le_one]
      intro a ha b hb'
      rw [hnear] at ha hb'
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha hb'
      exact near1 l K (s i) Z a b ha.1.1 ha.1.2 hb'.1.1 hb'.1.2 ha.2 hb'.2
    calc (Finset.univ.biUnion near).card ≤ ∑ i : Fin R', (near i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin R', 1 := Finset.sum_le_sum (fun i _ => hone i)
      _ = R' := by simp
      _ ≤ R := hR'
  · intro e he1 heZ hne m L₁ _ _ _ hL
    have hfar : ∀ i : Fin R', (l : ℝ) ^ (-(Nat.log l Z : ℤ)) ≤ ‖s i - (e : K)‖ := by
      intro i
      by_contra hlt
      push_neg at hlt
      apply hne
      rw [hnear]
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨i, ⟨he1, heZ⟩, hlt⟩
    have h1 := hb e he1 m L₁ hL (Nat.log l Z) hfar
    exact h1.trans (by gcongr)
