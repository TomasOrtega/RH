import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardSubspacesSupEqTop
open Matrix GlobalTheory.ExportSeries

namespace GlobalTheory.ExportSeries

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem sum_univCoef_eq_prim : ∀ (k C : Type) [Field k] [Finite k] [AddCommGroup C] [Fintype C] (r n : ℕ), r ≤ n →
    ∀ (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (y : Matrix (Fin r) (Fin n) k), ∑ c, univCoef β κ c y = prim y := by
  intro k C _ _ _ _ r n hrn β κ y
  classical
  letI := Fintype.ofFinite (Planes k r n)

  have hterm : ∀ U : Planes k r n, ∑ c, (univTerm β κ y U).coeff c = if Compl U.1 y then 1 else 0 := by
    intro U
    unfold univTerm
    by_cases h : Compl U.1 y
    · rw [dif_pos h, if_pos h]
      simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    · rw [dif_neg h, if_neg h]
      simp
  have hsum : ∑ c, univCoef β κ c y = ((Nat.card k : ℚ) ^ (r * (n - r)))⁻¹ *
      (Nat.card {U : Planes k r n // Compl U.1 y} : ℚ) := by
    simp only [univCoef, univ, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, AddMonoidAlgebra.coeff_sum,
      Finsupp.finset_sum_apply]
    rw [← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl fun U _ => hterm U, Finset.sum_boole]
    congr 2
    rw [Nat.card_eq_fintype_card (α := {U : Planes k r n // Compl U.1 y}), Fintype.card_subtype]
  rw [hsum]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrn
  have ht : r + t - r = t := by omega
  rw [ht]
  set R := Submodule.span k (Set.range y.row) with hR
  have hRle : Module.finrank k R ≤ r := by
    have := finrank_range_le_card (R := k) y.row
    rw [Fintype.card_fin] at this
    exact this
  have hcard : Nat.card {U : Planes k r (r + t) // Compl U.1 y} =
      Nat.card {U : Submodule k (Fin (r + t) → k) // Module.finrank k U = t ∧ R ⊔ U = ⊤} := by
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter _ (fun U => Compl U y)).trans
      (Equiv.subtypeEquivRight fun U => ?_))
    simp only [Compl, hR]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  rw [hcard, GlobalTheory.card_subspaces_sup_eq_top k r t R hRle]
  have hq : ((Nat.card k : ℚ) ^ (r * t)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.card_pos.ne')
  have hli : LinearIndependent k y.row ↔ Module.finrank k R = r := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank, eq_comm]
  unfold prim
  by_cases h : Module.finrank k R = r
  · rw [if_pos h, if_pos (hli.2 h)]
    push_cast
    exact inv_mul_cancel₀ hq
  · rw [if_neg h, if_neg (fun h' => h (hli.1 h'))]
    simp

end GlobalTheory.ExportSeries
