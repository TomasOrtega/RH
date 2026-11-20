import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.MainNotions.S Matrix

section

variable {K : Type} [Field K] {n : ℕ}

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cinv_det_up {U : Matrix (Fin n) (Fin n) K} (hU : IsUpUni U) : U.det = 1 := by
  have hT : U.BlockTriangular id := fun i j hij => (hU i j).1 hij
  rw [Matrix.det_of_upperTriangular hT]
  exact Finset.prod_eq_one (fun i _ => (hU i i).2 rfl)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem cinv_inv_up {U : Matrix (Fin n) (Fin n) K} (hU : IsUpUni U) : IsUpUni U⁻¹ := by
  have hdet : IsUnit U.det := by rw [cinv_det_up hU]; exact isUnit_one
  have hT : U.BlockTriangular id := fun i j hij => (hU i j).1 hij
  haveI : Invertible U := Matrix.invertibleOfIsUnitDet U hdet
  have hI : (U⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hT
  intro i j
  refine ⟨fun h => hI (show id j < id i from h), ?_⟩
  rintro rfl
  have h1 : (U⁻¹ * U) i i = 1 := by rw [Matrix.nonsing_inv_mul _ hdet]; simp
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · rwa [(hU i i).2 rfl, mul_one] at h1
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hI (show id k < id i from h), zero_mul]
    · rw [(hU k i).1 h, mul_zero]
  · simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem cinv_mul_left {U A : Matrix (Fin n) (Fin n) K} (hU : IsUpUni U) (hA : StrictUp A) :
    StrictUp (U * A) ∧ ∀ (a : Fin n) (h : a.val + 1 < n), (U * A) a ⟨a.val + 1, h⟩ = A a ⟨a.val + 1, h⟩ := by
  constructor
  · intro a b hba
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_or_ge k a with h | h
    · rw [(hU a k).1 h, zero_mul]
    · rw [hA k b (le_trans hba h), mul_zero]
  · intro a h
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [(hU a a).2 rfl, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h1 | h1
      · rw [(hU a k).1 h1, zero_mul]
      · rw [hA k _ (Fin.le_def.2 (Nat.succ_le_of_lt (Fin.lt_def.1 h1))), mul_zero]
    · simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem cinv_mul_right {U A : Matrix (Fin n) (Fin n) K} (hU : IsUpUni U) (hA : StrictUp A) :
    StrictUp (A * U) ∧ ∀ (a : Fin n) (h : a.val + 1 < n), (A * U) a ⟨a.val + 1, h⟩ = A a ⟨a.val + 1, h⟩ := by
  constructor
  · intro a b hba
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases le_or_gt k a with h | h
    · rw [hA a k h, zero_mul]
    · rw [(hU k b).1 (lt_of_le_of_lt hba h), mul_zero]
  · intro a h
    rw [Matrix.mul_apply, Finset.sum_eq_single (⟨a.val + 1, h⟩ : Fin n)]
    · rw [(hU _ _).2 rfl, mul_one]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h1 | h1
      · rw [hA a k (Fin.le_def.2 (Nat.le_of_lt_succ (Fin.lt_def.1 h1))), zero_mul]
      · rw [(hU k _).1 h1, mul_zero]
    · simp

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem cinv_supSum_congr {A B : Matrix (Fin n) (Fin n) K}
    (h : ∀ (a : Fin n) (h : a.val + 1 < n), B a ⟨a.val + 1, h⟩ = A a ⟨a.val + 1, h⟩) : supSum B = supSum A := by
  unfold supSum
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs with h1
  · exact h a h1
  · rfl

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem cinv_conj {U A : Matrix (Fin n) (Fin n) K} (hU : IsUpUni U) (hA : StrictUp A) :
    StrictUp (U⁻¹ * A * U) ∧ supSum (U⁻¹ * A * U) = supSum A := by
  have b1 := cinv_mul_left (cinv_inv_up hU) hA
  have b2 := cinv_mul_right hU b1.1
  exact ⟨b2.1, cinv_supSum_congr (fun a h => (b2.2 a h).trans (b1.2 a h))⟩

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem cell_inv : RelevanceUnipotentInvariant := by
  intro K _ _ n L Z U hL hU hrel A A' hA hA' hAA
  have hV : IsUpUni Lᴴ := by
    intro i j
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [Matrix.conjTranspose_apply, (hL j i).1 h, star_zero]
    · rw [Matrix.conjTranspose_apply, (hL j i).2 h.symm, star_one]
  have dU : IsUnit U.det := by rw [cinv_det_up hU]; exact isUnit_one
  have dL : IsUnit L.det := by
    have h : L.det = star (Lᴴ).det := by rw [Matrix.det_conjTranspose, star_star]
    rw [h, cinv_det_up hV, star_one]
    exact isUnit_one
  have b := cinv_conj hV hA
  have c := cinv_conj hU hA'
  have e1 : ((Lᴴ)⁻¹ * A * Lᴴ)ᴴ = L * Aᴴ * L⁻¹ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have e2 : L * Aᴴ * L⁻¹ * (L * Z * U) = L * (Aᴴ * Z) * U := by
    calc L * Aᴴ * L⁻¹ * (L * Z * U) = L * Aᴴ * (L⁻¹ * L) * Z * U := by simp only [Matrix.mul_assoc]
      _ = L * (Aᴴ * Z) * U := by rw [Matrix.nonsing_inv_mul _ dL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e3 : L * Z * U * (U⁻¹ * A' * U) = L * (Z * A') * U := by
    calc L * Z * U * (U⁻¹ * A' * U) = L * Z * (U * U⁻¹) * A' * U := by simp only [Matrix.mul_assoc]
      _ = L * (Z * A') * U := by rw [Matrix.mul_nonsing_inv _ dU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have key := hrel ((Lᴴ)⁻¹ * A * Lᴴ) (U⁻¹ * A' * U) b.1 c.1 (by
    rw [e1, e2, e3, ← Matrix.add_mul, ← Matrix.mul_add, hAA, Matrix.mul_zero, Matrix.zero_mul])
  rwa [b.2, c.2] at key

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem cell_sign : ColumnScalingBruhatShape := by
  intro K _ n ε L U σ t hε hU
  refine ⟨diagonal (fun a => (ε a)⁻¹) * U * diagonal ε, ?_, ?_⟩
  · intro i j
    have e : (diagonal (fun a => (ε a)⁻¹) * U * diagonal ε) i j = (ε i)⁻¹ * U i j * ε j := by
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    refine ⟨fun h => by rw [e, (hU i j).1 h]; ring, fun h => ?_⟩
    subst h
    rw [e, (hU i i).2 rfl, mul_one, inv_mul_cancel₀ (hε i)]
  · have hm : mono σ (fun b => ε b * t b) = mono σ t * diagonal ε := by
      ext a b
      rw [Matrix.mul_diagonal]
      unfold mono
      split_ifs <;> ring
    have hd : diagonal ε * diagonal (fun a => (ε a)⁻¹) = (1 : Matrix (Fin n) (Fin n) K) := by
      rw [Matrix.diagonal_mul_diagonal]
      have h1 : (fun i => ε i * (ε i)⁻¹) = fun _ => (1 : K) := funext fun i => mul_inv_cancel₀ (hε i)
      rw [h1, Matrix.diagonal_one]
    have hl : (fun a b => ε b * (L * mono σ t * U) a b) = L * mono σ t * U * diagonal ε := by
      funext a b
      rw [Matrix.mul_diagonal, mul_comm]
    refine hl.trans ?_
    rw [hm]
    calc L * mono σ t * U * diagonal ε = L * mono σ t * 1 * U * diagonal ε := by rw [Matrix.mul_one]
      _ = L * (mono σ t * diagonal ε) * (diagonal (fun a => (ε a)⁻¹) * U * diagonal ε) := by
        rw [← hd]; simp only [Matrix.mul_assoc]

end Formalism.MainNotions.BridgeLemma

end
