import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_perm_of_block_bijection : ∀ (r : ℕ) (b b' : Fin r → ℕ) (R : ℕ → ℕ → Prop), (∀ c ∈ Set.range b, ∃! c', c' ∈ Set.range b' ∧ R c c') → (∀ c' ∈ Set.range b', ∃! c, c ∈ Set.range b ∧ R c c') → (∀ c ∈ Set.range b, ∀ c' ∈ Set.range b', R c c' → (block b c).card = (block b' c').card) → ∃ w : Equiv.Perm (Fin r), (∀ i, R (b i) (b' (w i))) ∧ ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j) := by
  classical
  intro r b b' R h1 h2 h3
  have h1' : ∀ i : Fin r, ∃ c', c' ∈ Set.range b' ∧ R (b i) c' :=
    fun i => (h1 (b i) ⟨i, rfl⟩).exists
  choose f hf1 hf2 using h1'
  have hiff : ∀ i c c', c ∈ Set.range b → c' ∈ Set.range b' → R c c' → (f i = c' ↔ b i = c) := by
    intro i c c' hc hc' hR
    constructor
    · intro h
      exact (h2 c' hc').unique ⟨⟨i, rfl⟩, h ▸ hf2 i⟩ ⟨hc, hR⟩
    · intro h
      subst h
      exact (h1 (b i) hc).unique ⟨hf1 i, hf2 i⟩ ⟨hc', hR⟩
  have hcard : ∀ c' : ℕ, Fintype.card {i // f i = c'} = Fintype.card {i // b' i = c'} := by
    intro c'
    rw [Fintype.card_subtype, Fintype.card_subtype]
    by_cases hc' : c' ∈ Set.range b'
    · obtain ⟨c, hc, hR⟩ := (h2 c' hc').exists
      have h := h3 c hc c' hc' hR
      unfold block at h
      rw [← h]
      congr 1
      ext i
      simp [hiff i c c' hc hc' hR]
    · rw [Finset.filter_eq_empty_iff.2, Finset.filter_eq_empty_iff.2]
      · intro i _ h
        exact hc' ⟨i, h⟩
      · intro i _ h
        exact hc' (h ▸ hf1 i)
  let e : ∀ c' : ℕ, {i // f i = c'} ≃ {i // b' i = c'} := fun c' => Fintype.equivOfCardEq (hcard c')
  have hw : ∀ i, b' (Equiv.ofFiberEquiv e i) = f i := fun i => Equiv.ofFiberEquiv_map e i
  refine ⟨Equiv.ofFiberEquiv e, fun i => ?_, fun i j => ?_⟩
  · rw [hw]; exact hf2 i
  · rw [hw, hw]
    exact (hiff i (b j) (f j) ⟨j, rfl⟩ (hf1 j) (hf2 j)).symm

end GlobalTheory
