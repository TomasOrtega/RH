import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Matrix

namespace GlobalTheory.InertZeta

/- English proof (translation)
The claim follows from `P.smul_mem (⟨x, hx⟩ : Formalism.UG.intL L) hw`.
-/
theorem smul_mem_integral_submodule_of_valuation_le_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    {P : Submodule (Formalism.UG.intL L) (Fin n → L)} {x : L} (hx : Valued.v x ≤ 1) {w : Fin n → L} (hw : w ∈ P) :
    x • w ∈ P :=
  P.smul_mem (⟨x, hx⟩ : Formalism.UG.intL L) hw

/- English proof (translation)
Introduce `L _ _ n M k ρ e hM hρ he`. Break down `he with rfl | ⟨i₀, hi₀⟩` into its components or cases. Use `⟨M, by simpa using hM, ?_⟩` and prove the remaining obligations. Use `sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 (mem_rowLat.2 ⟨ρ, fun i => ?_, rfl⟩))` and prove the remaining obligations. Conclude with `(by simpa using hρ i : Valued.v (ρ i) ≤ 1)`.

Establish `h0 : ρ i₀ ≠ 0` using `fun h => by rw [h, map_zero] at hi₀; exact WithZero.exp_ne_zero hi₀.symm`. Use `⟨M.updateRow i₀ (ρ ᵥ* M), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.vecMul_eq_sum, Matrix.det_updateRow_sum, smul_eq_mul, map_mul, hi₀, hM, ← WithZero.exp_add, add_comm]`. Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le (rowLat_le.2 fun i => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)` and prove the remaining obligations.

Distinguish the cases in `hi : i = i₀`. Substitute `hi` using the available equality. Establish `hs : ρ ᵥ* M = ρ i • M i + ∑ j ∈ Finset.univ.erase i, ρ j • M j`. Rewrite using `[Matrix.vecMul_eq_sum]`. Conclude with `(Finset.add_sum_erase _ (fun j => ρ j • M j) (Finset.mem_univ _)).symm`.

Establish `: M i = (ρ i)⁻¹ • (M.updateRow i (ρ ᵥ* M)) i - ∑ j ∈ Finset.univ.erase i, ((ρ i)⁻¹ * ρ j) • (M.updateRow i (ρ ᵥ* M)) j`. Rewrite using `[Matrix.updateRow_self, hs, smul_add, smul_smul, inv_mul_cancel₀ h0, one_smul, Finset.smul_sum]`. Rewrite using `[add_sub_assoc, ← Finset.sum_sub_distrib]`. Rewrite using `[Finset.sum_eq_zero, add_zero]`. Introduce `j hj`.

Rewrite using `[Matrix.updateRow_ne (Finset.ne_of_mem_erase hj), smul_smul, sub_self]`. Rewrite using `[this]`. Establish `hv : Valued.v (ρ i)⁻¹ = WithZero.exp (-(e : ℤ))` using `by rw [map_inv₀, hi₀, WithZero.exp_neg]`. Use `Submodule.sub_mem _ (smul_mem_integral_submodule_of_valuation_le_one ?_ (row_mem_rowLat _ _)) (Submodule.sum_mem _ fun j _ => smul_mem_integral_submodule_of_valuation_le_one ?_ (row_mem_rowLat _ _))` and prove the remaining obligations. Rewrite using `[hv, ← WithZero.exp_zero, WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[map_mul, hv]`. Combine the equalities or inequalities in the displayed calculation. Use `row_mem_rowLat (M.updateRow i₀ (ρ ᵥ* M)) i` as an intermediate fact. Rewrite `this` using `[Matrix.updateRow_ne hi]`. Then use the resulting hypothesis.

Use `row_mem_rowLat (M.updateRow i₀ (ρ ᵥ* M)) i₀` as an intermediate fact. Rewrite `this` using `[Matrix.updateRow_self]`. Then use the resulting hypothesis. Use `rowLat_le.2 fun i => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = i₀`. Substitute `hi` using the available equality.

Rewrite using `[Matrix.updateRow_self]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Rewrite using `[Matrix.updateRow_ne hi]`. Conclude with `Submodule.mem_sup_left (row_mem_rowLat _ _)`.
-/
theorem addVec : AddVec := by
  intro L _ _ n M k ρ e hM hρ he
  rcases he with rfl | ⟨i₀, hi₀⟩
  · refine ⟨M, by simpa using hM, ?_⟩
    refine sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 (mem_rowLat.2 ⟨ρ, fun i => ?_, rfl⟩))
    exact (by simpa using hρ i : Valued.v (ρ i) ≤ 1)
  · have h0 : ρ i₀ ≠ 0 := fun h => by rw [h, map_zero] at hi₀; exact WithZero.exp_ne_zero hi₀.symm
    refine ⟨M.updateRow i₀ (ρ ᵥ* M), ?_, ?_⟩
    · rw [Matrix.vecMul_eq_sum, Matrix.det_updateRow_sum, smul_eq_mul, map_mul, hi₀, hM, ← WithZero.exp_add, add_comm]
    · apply le_antisymm
      · refine sup_le (rowLat_le.2 fun i => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
        · by_cases hi : i = i₀
          · subst hi
            have hs : ρ ᵥ* M = ρ i • M i + ∑ j ∈ Finset.univ.erase i, ρ j • M j := by
              rw [Matrix.vecMul_eq_sum]; exact (Finset.add_sum_erase _ (fun j => ρ j • M j) (Finset.mem_univ _)).symm
            have : M i = (ρ i)⁻¹ • (M.updateRow i (ρ ᵥ* M)) i -
                ∑ j ∈ Finset.univ.erase i, ((ρ i)⁻¹ * ρ j) • (M.updateRow i (ρ ᵥ* M)) j := by
              rw [Matrix.updateRow_self, hs, smul_add, smul_smul, inv_mul_cancel₀ h0, one_smul, Finset.smul_sum]
              rw [add_sub_assoc, ← Finset.sum_sub_distrib]
              rw [Finset.sum_eq_zero, add_zero]
              intro j hj
              rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hj), smul_smul, sub_self]
            rw [this]
            have hv : Valued.v (ρ i)⁻¹ = WithZero.exp (-(e : ℤ)) := by rw [map_inv₀, hi₀, WithZero.exp_neg]
            refine Submodule.sub_mem _ (smul_mem_integral_submodule_of_valuation_le_one ?_ (row_mem_rowLat _ _)) (Submodule.sum_mem _ fun j _ => smul_mem_integral_submodule_of_valuation_le_one ?_ (row_mem_rowLat _ _))
            · rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
            · rw [map_mul, hv]
              calc WithZero.exp (-(e : ℤ)) * Valued.v (ρ j) ≤ WithZero.exp (-(e : ℤ)) * WithZero.exp (e : ℤ) :=
                    mul_le_mul' le_rfl (hρ j)
                _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
          · have := row_mem_rowLat (M.updateRow i₀ (ρ ᵥ* M)) i
            rwa [Matrix.updateRow_ne hi] at this
        · have := row_mem_rowLat (M.updateRow i₀ (ρ ᵥ* M)) i₀
          rwa [Matrix.updateRow_self] at this
      · refine rowLat_le.2 fun i => ?_
        by_cases hi : i = i₀
        · subst hi
          rw [Matrix.updateRow_self]
          exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
        · rw [Matrix.updateRow_ne hi]
          exact Submodule.mem_sup_left (row_mem_rowLat _ _)

end GlobalTheory.InertZeta
