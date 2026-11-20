import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

open GlobalTheory.InertZeta Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.InertZeta

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_intL_iff {x : L} : x ∈ Formalism.UG.intL L ↔ Valued.v x ≤ 1 := Iff.rfl

/- English proof (translation)
Rewrite using `[← Matrix.det_transpose, ← Matrix.updateCol_transpose, Matrix.transpose_one, ← Matrix.cramer_apply, Matrix.cramer_one]`. Both sides reduce to the same expression.
-/
theorem det_updateRow_one (i : Fin n) (ρ : Fin n → L) :
    ((1 : Matrix (Fin n) (Fin n) L).updateRow i ρ).det = ρ i := by
  rw [← Matrix.det_transpose, ← Matrix.updateCol_transpose, Matrix.transpose_one, ← Matrix.cramer_apply,
    Matrix.cramer_one]
  rfl

/- English proof (translation)
Use `set w := ρ ᵥ* M with hw`. Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le (rowLat_le.2 fun j => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)` and prove the remaining obligations. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Use `mem_rowLat.2 ⟨fun l => if l = j then (ρ j)⁻¹ else -(ρ l * (ρ j)⁻¹), fun l => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hl : l = j`. Simplify using `only [if_pos hl]`. Conclude with `h1`. Simplify using `only [hl, if_false]`.

Use `neg_mem ?_` and prove the remaining obligations. Rewrite using `[mem_intL_iff, map_mul, map_inv₀]`. Conclude with `mul_inv_le_one_of_le₀ (h2 l) zero_le'`. Rewrite using `[Matrix.vecMul_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]`. Establish `e1 : ∑ l ∈ Finset.univ.erase j, (if l = j then (ρ j)⁻¹ else -(ρ l * (ρ j)⁻¹)) • (M.updateRow j w) l = ∑ l ∈ Finset.univ.erase j, (-(ρ l * (ρ j)⁻¹)) • M l` using `Finset.sum_congr rfl fun l hl => by`.

Use `Finset.ne_of_mem_erase hl` as an intermediate fact. Simplify using `[this, Matrix.updateRow_ne]`. Establish `e2 : w = ρ j • M j + ∑ l ∈ Finset.univ.erase j, ρ l • M l`. Rewrite using `[hw, Matrix.vecMul_eq_sum]`. Conclude with `(Finset.add_sum_erase _ (fun l => ρ l • M l) (Finset.mem_univ j)).symm`.

Rewrite using `[e1]`. Simplify using `only [if_true, Matrix.updateRow_self]`. Rewrite using `[e2, smul_add, smul_smul, inv_mul_cancel₀ h0, one_smul, Finset.smul_sum, add_assoc, ← Finset.sum_add_distrib]`. Simplify using `only [smul_smul, neg_smul]`. Establish `: ∀ l, (ρ j)⁻¹ * ρ l = ρ l * (ρ j)⁻¹` using `fun l => mul_comm _ _`.

Simplify using `[this]`. Use `row_mem_rowLat (M.updateRow i w) j` as an intermediate fact. Rewrite `this` using `[Matrix.updateRow_ne hj]`. Then use the resulting hypothesis. Use `row_mem_rowLat (M.updateRow i w) i` as an intermediate fact. Rewrite `this` using `[Matrix.updateRow_self]`. Then use the resulting hypothesis.

Use `rowLat_le.2 fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Rewrite using `[Matrix.updateRow_self]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`.

Rewrite using `[Matrix.updateRow_ne hj]`. Conclude with `Submodule.mem_sup_left (row_mem_rowLat M j)`.
-/
theorem rowLat_updateRow {M : Matrix (Fin n) (Fin n) L} {ρ : Fin n → L} {i : Fin n}
    (h0 : ρ i ≠ 0) (h1 : Valued.v (ρ i)⁻¹ ≤ 1) (h2 : ∀ j, Valued.v (ρ j) ≤ Valued.v (ρ i)) :
    rowLat M ⊔ Submodule.span (Formalism.UG.intL L) {ρ ᵥ* M} = rowLat (M.updateRow i (ρ ᵥ* M)) := by
  set w := ρ ᵥ* M with hw
  apply le_antisymm
  · refine sup_le (rowLat_le.2 fun j => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
    · by_cases hj : j = i
      · subst hj
        refine mem_rowLat.2 ⟨fun l => if l = j then (ρ j)⁻¹ else -(ρ l * (ρ j)⁻¹), fun l => ?_, ?_⟩
        · by_cases hl : l = j
          · simp only [if_pos hl]
            exact h1
          · simp only [hl, if_false]
            refine neg_mem ?_
            rw [mem_intL_iff, map_mul, map_inv₀]
            exact mul_inv_le_one_of_le₀ (h2 l) zero_le'
        · rw [Matrix.vecMul_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
          have e1 : ∑ l ∈ Finset.univ.erase j, (if l = j then (ρ j)⁻¹ else -(ρ l * (ρ j)⁻¹)) • (M.updateRow j w) l
              = ∑ l ∈ Finset.univ.erase j, (-(ρ l * (ρ j)⁻¹)) • M l :=
            Finset.sum_congr rfl fun l hl => by
              have := Finset.ne_of_mem_erase hl
              simp [this, Matrix.updateRow_ne]
          have e2 : w = ρ j • M j + ∑ l ∈ Finset.univ.erase j, ρ l • M l := by
            rw [hw, Matrix.vecMul_eq_sum]
            exact (Finset.add_sum_erase _ (fun l => ρ l • M l) (Finset.mem_univ j)).symm
          rw [e1]
          simp only [if_true, Matrix.updateRow_self]
          rw [e2, smul_add, smul_smul, inv_mul_cancel₀ h0, one_smul, Finset.smul_sum, add_assoc,
            ← Finset.sum_add_distrib]
          simp only [smul_smul, neg_smul]
          have : ∀ l, (ρ j)⁻¹ * ρ l = ρ l * (ρ j)⁻¹ := fun l => mul_comm _ _
          simp [this]
      · have := row_mem_rowLat (M.updateRow i w) j
        rwa [Matrix.updateRow_ne hj] at this
    · have := row_mem_rowLat (M.updateRow i w) i
      rwa [Matrix.updateRow_self] at this
  · refine rowLat_le.2 fun j => ?_
    by_cases hj : j = i
    · subst hj
      rw [Matrix.updateRow_self]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · rw [Matrix.updateRow_ne hj]
      exact Submodule.mem_sup_left (row_mem_rowLat M j)

/- English proof (translation)
Introduce `L _ _ n M k ρ e hM hρ he`. Distinguish the cases in `e0 : e = 0`. Substitute `e0` using the available equality. Use `⟨M, by simpa using hM, ?_⟩` and prove the remaining obligations. Use `sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 (mem_rowLat.2 ⟨ρ, fun i => ?_, rfl⟩))` and prove the remaining obligations.

Conclude with `mem_intL_iff.2 (by simpa using hρ i)`. Take `⟨i, hi⟩` from `he.resolve_left e0`. Establish `h0 : ρ i ≠ 0` using `fun h => by`. Rewrite `hi` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero hi.symm`.

Establish `hone : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (e : ℤ)`. Rewrite using `[← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `h1 : Valued.v (ρ i)⁻¹ ≤ 1`. Rewrite using `[map_inv₀, hi]`.

Conclude with `inv_le_one_of_one_le₀ hone`. Use `⟨M.updateRow i (ρ ᵥ* M), ?_, rowLat_updateRow h0 h1 fun j => hi ▸ hρ j⟩` and prove the remaining obligations. Establish `e1 : M.updateRow i (ρ ᵥ* M) = (1 : Matrix (Fin n) (Fin n) L).updateRow i ρ * M`. Use extensionality with `a b`. Distinguish the cases in `ha : a = i`.

Substitute `ha` using the available equality. Simplify using `[Matrix.mul_apply, Matrix.vecMul, dotProduct]`. Simplify using `[Matrix.updateRow_ne ha, Matrix.mul_apply, Matrix.one_apply]`. Rewrite using `[e1, Matrix.det_mul, det_updateRow_one, map_mul, hi, hM, ← WithZero.exp_add, add_comm]`.
-/
theorem addVec : AddVec := by
  intro L _ _ n M k ρ e hM hρ he
  by_cases e0 : e = 0
  · subst e0
    refine ⟨M, by simpa using hM, ?_⟩
    refine sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 (mem_rowLat.2 ⟨ρ, fun i => ?_, rfl⟩))
    exact mem_intL_iff.2 (by simpa using hρ i)
  · obtain ⟨i, hi⟩ := he.resolve_left e0
    have h0 : ρ i ≠ 0 := fun h => by
      rw [h, map_zero] at hi
      exact WithZero.exp_ne_zero hi.symm
    have hone : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (e : ℤ) := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    have h1 : Valued.v (ρ i)⁻¹ ≤ 1 := by
      rw [map_inv₀, hi]
      exact inv_le_one_of_one_le₀ hone
    refine ⟨M.updateRow i (ρ ᵥ* M), ?_, rowLat_updateRow h0 h1 fun j => hi ▸ hρ j⟩
    have e1 : M.updateRow i (ρ ᵥ* M) = (1 : Matrix (Fin n) (Fin n) L).updateRow i ρ * M := by
      ext a b
      by_cases ha : a = i
      · subst ha
        simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
      · simp [Matrix.updateRow_ne ha, Matrix.mul_apply, Matrix.one_apply]
    rw [e1, Matrix.det_mul, det_updateRow_one, map_mul, hi, hM, ← WithZero.exp_add, add_comm]

end GlobalTheory.CompanionTheory.InertZeta

end
