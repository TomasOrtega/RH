import Mathlib
import Formalism.PeriodIntegrals.WeylForU

noncomputable section

namespace PI.WeylForUWork

open Finset PI.UpqRep Formalism.BasicNotions

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem denom_range (n : ℕ) :
    ∏ i ∈ range n, ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ)) =
      ∏ i ∈ range n, ((i.factorial : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∀ i ∈ range n, ∏ j ∈ Ico (i + 1) (n + 1), ((j : ℝ) - (i : ℝ)) =
        (∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ))) * ((n : ℝ) - (i : ℝ)) := by
      intro i hi
      exact Finset.prod_Ico_succ_top (Nat.succ_le_of_lt (Finset.mem_range.mp hi)) _
    have h2 : ∀ k : ℕ, ∏ i ∈ range k, ((k : ℝ) - (i : ℝ)) = ((k.factorial : ℕ) : ℝ) := by
      intro k
      induction k with
      | zero => simp
      | succ k ihk =>
        have e : ∀ i ∈ range k, (((k + 1 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ)) = (k : ℝ) - (i : ℝ) := by
          intro i _
          push_cast
          ring
        rw [Finset.prod_range_succ', Finset.prod_congr rfl e, ihk, Nat.factorial_succ]
        push_cast
        ring
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.Ico_self, Finset.prod_empty, mul_one,
      Finset.prod_congr rfl h1, Finset.prod_mul_distrib, ih, h2 n]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem row_fin (n : ℕ) (a : Fin n) :
    ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ j ∈ Ico ((a : ℕ) + 1) n, ((j : ℝ) - ((a : ℕ) : ℝ)) := by
  refine Finset.prod_nbij (fun b : Fin n => (b : ℕ)) ?_ ?_ ?_ ?_
  · intro b hb
    rw [Finset.mem_filter] at hb
    rw [Finset.mem_Ico]
    exact ⟨hb.2, b.isLt⟩
  · intro x _ y _ h
    exact Fin.ext h
  · intro j hj
    rw [Finset.mem_coe, Finset.mem_Ico] at hj
    refine ⟨⟨j, hj.2⟩, ?_, rfl⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hj.1⟩
  · intro b _
    rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem denom_fin (n : ℕ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ i ∈ range n, ((i.factorial : ℕ) : ℝ) := by
  refine (Finset.prod_congr rfl (fun a _ => row_fin n a)).trans ?_
  exact (Fin.prod_univ_eq_prod_range (fun i : ℕ => ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ))) n).trans
    (denom_range n)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  unfold Formalism.BasicNotions.DomWeight.natW
  exact Int.toNat_le_toNat (sub_le_sub_right (lam.2 hij) _)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem natW_cast {N : ℕ} (lam : DomWeight N) (i : Fin N) :
    ((lam.natW i : ℕ) : ℤ) = lam.w i - lam.detShift := by
  have hN0 : 0 < N := Fin.pos i
  have hle : lam.w ⟨N - 1, by omega⟩ ≤ lam.w i :=
    lam.anti (Fin.le_iff_val_le_val.mpr (by simp only; omega))
  unfold DomWeight.natW DomWeight.detShift
  rw [dif_pos hN0]
  exact Int.toNat_of_nonneg (by omega)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem natW_cast_real {N : ℕ} (lam : DomWeight N) (i : Fin N) :
    ((lam.natW i : ℕ) : ℝ) = ((lam.w i : ℤ) : ℝ) - ((lam.detShift : ℤ) : ℝ) := by
  exact_mod_cast natW_cast lam i

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weylForU_of : PI.ModelIso → PI.NablaDim → PI.WeylForU := by
  intro hM hN N Λ H _ _ σ S hU hK
  obtain ⟨lam, hΛ, hdim⟩ := hM N Λ H σ S hU hK
  rw [hdim]
  have h2 : ((Module.finrank ℂ ↥(nablaSq ℂ N lam) : ℕ) : ℚ) =
      (∏ i : Fin N, ∏ j ∈ univ.filter (fun j : Fin N => i < j), (((lam.natW i : ℕ) : ℚ) -
        ((lam.natW j : ℕ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))) /
      ∏ i : Fin N, ∏ j ∈ univ.filter (fun j : Fin N => i < j), (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) := by
    rw [← Finset.prod_div_distrib]
    refine (hN N lam.natW (natW_anti lam)).trans (Finset.prod_congr rfl (fun i _ => ?_))
    rw [← Finset.prod_div_distrib, Finset.prod_filter]
  have h3 := congrArg (fun q : ℚ => (q : ℝ)) h2
  push_cast at h3
  rw [h3, denom_fin]
  congr 1
  refine Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun b _ => ?_))
  rw [natW_cast_real, natW_cast_real, hΛ a, hΛ b]
  ring

end PI.WeylForUWork
