import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Consider separately whether the proposition holds or fails. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Consider separately whether the proposition holds or fails. Prove the first alternative.

Prove the second alternative. Assume the hypotheses and unpack their components. Establish an intermediate fact. Substitute using the available equality. Supply the required witnesses or components.

Supply the required witnesses or components. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem stepSum_surj_of_initial {r : ℕ} {S : Finset (Fin r)} (hS : ∀ k ∈ S, ∀ i, i ≤ k → i ∈ S)
    (v : Fin r → ℝ) (hv : ∀ i ∉ S, v i = 0) : ∃ u, stepSum S u = v := by
  classical
  let w : ℕ → ℝ := fun n => if h : n < r then v ⟨n, h⟩ else 0
  refine ⟨fun k => w k.val - w (k.val + 1), ?_⟩
  have key : ∀ d : ℕ, ∀ i : Fin r, r - i.val = d → stepSum S (fun k => w k.val - w (k.val + 1)) i = v i := by
    intro d
    induction d with
    | zero => intro i hi; have := i.2; omega
    | succ d ih =>
      intro i hi
      unfold stepSum
      by_cases hiS : i ∈ S
      · by_cases h : i.val + 1 < r
        · set j : Fin r := ⟨i.val + 1, h⟩ with hj
          have hset : S.filter (fun k => i ≤ k) = insert i (S.filter (fun k => j ≤ k)) := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_insert, Fin.le_def, hj, Fin.ext_iff]
            constructor
            · rintro ⟨hk, hik⟩
              by_cases hki : k.val = i.val
              · exact Or.inl hki
              · exact Or.inr ⟨hk, by omega⟩
            · rintro (hki | ⟨hk, hjk⟩)
              · have : k = i := Fin.ext hki
                subst this; exact ⟨hiS, le_refl _⟩
              · exact ⟨hk, by omega⟩
          have hnot : i ∉ S.filter (fun k => j ≤ k) := by
            simp [Fin.le_def, hj]
          have hj' := ih j (by simp [hj]; omega)
          unfold stepSum at hj'
          rw [hset, Finset.sum_insert hnot, hj']
          simp only [w, dif_pos i.2, dif_pos h]
          ring
        · have hset : S.filter (fun k => i ≤ k) = {i} := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_singleton, Fin.le_def]
            constructor
            · rintro ⟨hk, hik⟩; exact Fin.ext (by have := k.2; omega)
            · rintro rfl; exact ⟨hiS, le_refl _⟩
          rw [hset, Finset.sum_singleton]
          simp only [w, dif_pos i.2, dif_neg h]
          ring
      · rw [hv i hiS]
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_filter] at hk
        exact absurd (hS k hk.1 i hk.2) hiS
  funext i
  exact key _ i rfl

end GlobalTheory
