import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.
-/
theorem UpperTheory.Reformulated.B.ProdSubProdLeOfFactorsClose.main.{u_1} :
    ∀ {ι : Type u_1} (ν : Valuation ℂ NNReal) (s : Finset ι) (f g : ι → ℂ) (m : NNReal),
      (∀ i ∈ s, (ν : ℂ → NNReal) (f i) ≤ (1 : NNReal)) →
        (∀ i ∈ s, (ν : ℂ → NNReal) (g i) ≤ (1 : NNReal)) →
          (∀ i ∈ s, (ν : ℂ → NNReal) (f i - g i) ≤ m) →
            (ν : ℂ → NNReal) (∏ i ∈ s, f i) ≤ (1 : NNReal) ∧
              (ν : ℂ → NNReal) (∏ i ∈ s, g i) ≤ (1 : NNReal) ∧ (ν : ℂ → NNReal) (∏ i ∈ s, f i - ∏ i ∈ s, g i) ≤ m := by
  classical
  intro ι ν s f g m
  induction s using Finset.induction_on with
  | empty =>
    intro _ _ _
    simp
  | insert a s ha ih =>
    intro hf hg hfg
    obtain ⟨h1, h2, h3⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
    have fa := hf a (Finset.mem_insert_self a s)
    have ga := hg a (Finset.mem_insert_self a s)
    have fga := hfg a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    refine ⟨?_, ?_, ?_⟩
    · rw [map_mul]
      calc ν (f a) * ν (∏ i ∈ s, f i) ≤ 1 * 1 := mul_le_mul' fa h1
        _ = 1 := one_mul 1
    · rw [map_mul]
      calc ν (g a) * ν (∏ i ∈ s, g i) ≤ 1 * 1 := mul_le_mul' ga h2
        _ = 1 := one_mul 1
    · have e : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i
          = f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
      rw [e]
      refine le_trans (Valuation.map_add ν _ _) (max_le ?_ ?_)
      · rw [map_mul]
        calc ν (f a) * ν (∏ i ∈ s, f i - ∏ i ∈ s, g i) ≤ 1 * m := mul_le_mul' fa h3
          _ = m := one_mul m
      · rw [map_mul]
        calc ν (f a - g a) * ν (∏ i ∈ s, g i) ≤ m * 1 := mul_le_mul' fga h2
          _ = m := mul_one m
