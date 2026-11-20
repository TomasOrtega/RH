import Mathlib

namespace GlobalTheory

/- English proof (translation)
Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem expand_pi_of_expand_each {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (K : ∀ i, Set (X i)) (m : ι → ℕ)
    (k : ∀ i, Fin (m i) → X i) (hk : ∀ i j, k i j ∈ K i) (c : ∀ i, Fin (m i) → X i → ℂ)
    (f : (∀ i, X i) → ℂ)
    (hf : ∀ i (g : ∀ i, X i), (∀ i, g i ∈ K i) → f g = ∑ j, f (Function.update g i (k i j)) * c i j (g i))
    (g : ∀ i, X i) (hg : ∀ i, g i ∈ K i) :
    f g = ∑ J : (∀ i, Fin (m i)), f (fun i => k i (J i)) * ∏ i, c i (J i) (g i) := by
  classical
  by_cases hm : ∃ i, m i = 0
  · obtain ⟨i0, hi0⟩ := hm
    have h1 : f g = 0 := by
      rw [hf i0 g hg]
      apply Finset.sum_eq_zero
      intro j _
      exact absurd j.2 (by omega)
    haveI : IsEmpty (∀ i, Fin (m i)) := ⟨fun J => by have := (J i0).2; omega⟩
    rw [h1, Finset.univ_eq_empty, Finset.sum_empty]
  push_neg at hm
  let j0 : ∀ i, Fin (m i) := fun i => ⟨0, Nat.pos_of_ne_zero (hm i)⟩
  let T : Finset ι → ∀ i, Finset (Fin (m i)) := fun s i => if i ∈ s then Finset.univ else {j0 i}
  let H : Finset ι → (∀ i, Fin (m i)) → (∀ i, X i) → (∀ i, X i) :=
    fun s J g i => if i ∈ s then k i (J i) else g i
  have hmem : ∀ s (J : ∀ i, Fin (m i)), J ∈ Fintype.piFinset (T s) ↔ ∀ i, i ∉ s → J i = j0 i := by
    intro s J
    rw [Fintype.mem_piFinset]
    apply forall_congr'
    intro i
    by_cases hi : i ∈ s <;> simp [T, hi]
  have key : ∀ s : Finset ι, ∀ g : ∀ i, X i, (∀ i, g i ∈ K i) →
      f g = ∑ J ∈ Fintype.piFinset (T s), f (H s J g) * ∏ i ∈ s, c i (J i) (g i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg
      have hT : T ∅ = fun i => {j0 i} := by funext i; simp [T]
      rw [hT, Fintype.piFinset_singleton, Finset.sum_singleton, Finset.prod_empty, mul_one]
      congr 1
    | insert a s ha ih =>
      intro g hg
      have hHK : ∀ J, ∀ i, H s J g i ∈ K i := by
        intro J i
        simp only [H]
        split_ifs
        exacts [hk _ _, hg i]
      rw [ih g hg]
      have step : ∀ J ∈ Fintype.piFinset (T s), f (H s J g) * ∏ i ∈ s, c i (J i) (g i)
          = ∑ j, f (H (insert a s) (Function.update J a j) g)
              * ∏ i ∈ insert a s, c i (Function.update J a j i) (g i) := by
        intro J _
        rw [hf a _ (hHK J), Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        have e1 : Function.update (H s J g) a (k a j) = H (insert a s) (Function.update J a j) g := by
          funext i
          by_cases hia : i = a
          · subst hia
            simp [H]
          · simp [H, Function.update_of_ne hia, Finset.mem_insert, hia]
        have e2 : H s J g a = g a := by simp [H, ha]
        rw [e1, e2, Finset.prod_insert ha, Function.update_self]
        have e3 : ∏ i ∈ s, c i (Function.update J a j i) (g i) = ∏ i ∈ s, c i (J i) (g i) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have : i ≠ a := fun h => ha (h ▸ hi)
          rw [Function.update_of_ne this]
        rw [e3]
        ring
      rw [Finset.sum_congr rfl step, ← Finset.sum_product']
      refine Finset.sum_nbij' (fun p => Function.update p.1 a p.2)
        (fun J' => (Function.update J' a (j0 a), J' a)) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨J, j⟩ hp
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product, hmem] at hp
        simp only [Finset.mem_coe, hmem]
        intro i hi
        rw [Finset.mem_insert, not_or] at hi
        rw [Function.update_of_ne hi.1]
        exact hp.1 i hi.2
      · intro J' hJ'
        simp only [Finset.mem_coe, hmem] at hJ'
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product,
          Finset.mem_univ, and_true, hmem]
        intro i hi
        by_cases hia : i = a
        · subst hia
          simp
        · rw [Function.update_of_ne hia]
          exact hJ' i (by simp [hia, hi])
      · rintro ⟨J, j⟩ hp
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product, hmem] at hp
        simp only [Function.update_idem, Function.update_self, Prod.mk.injEq, and_true]
        funext i
        by_cases hia : i = a
        · subst hia
          rw [Function.update_self]
          exact (hp.1 _ ha).symm
        · rw [Function.update_of_ne hia]
      · intro J' _
        simp only [Function.update_idem, Function.update_eq_self]
      · rintro ⟨J, j⟩ _
        rfl
  rw [key Finset.univ g hg]
  have hTu : T Finset.univ = fun _ => Finset.univ := by funext i; simp [T]
  rw [hTu, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun J _ => ?_
  congr 2
  funext i
  simp [H]

end GlobalTheory
