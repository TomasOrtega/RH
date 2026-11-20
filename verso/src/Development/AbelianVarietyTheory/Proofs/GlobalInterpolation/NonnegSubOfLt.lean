import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InterlacingEquivariance
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX

open MvPolynomial NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance GlobalTheory.BranchFormula

namespace GlobalTheory.BranchMembers

variable {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lamTrue_lo (u : Word) (τ : X.Tau) (i : Fin (R.N R.m)) (j : Fin R.k) (h : i.1 = j.1) :
    ((W.lamTrue u R.m τ).w i : ℚ) =
      (W.hc u τ).u j - ((R.k : ℚ) - 1) / 2 + (j.1 : ℚ) - (R.m : ℚ) * (((R.t : ℚ) + 1) / 2) := by
  have hi : i.1 < R.k := h ▸ j.2
  have e : (⟨i.1, hi⟩ : Fin R.k) = j := Fin.ext h
  rw [Wts.lamTrue_eq, Wts.lamN_eq W u le_rfl, dif_pos hi, e]
  unfold hcToWeightQ rhoVec
  ring

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem lamTrue_hi (u : Word) (τ : X.Tau) (i : Fin (R.N R.m)) (B ρ : ℕ) (hρ : ρ < R.t + 1)
    (h : i.1 = R.k + B * (R.t + 1) + ρ) :
    ((W.lamTrue u R.m τ).w i : ℚ) =
      -(RowPar.of (W.hc u τ)).eAt B + (R.k : ℚ) / 2 + (2 * (B : ℚ) + 1) * (((R.t : ℚ) + 1) / 2) -
        (R.m : ℚ) * (((R.t : ℚ) + 1) / 2) := by
  have hi : ¬ i.1 < R.k := by omega
  have e1 : (i.1 - R.k) / (R.t + 1) = B := by
    have : i.1 - R.k = B * (R.t + 1) + ρ := by omega
    rw [this]
    exact (divmod (R.t + 1) B ρ hρ).1
  have hB : B < R.m := e1 ▸ R.blk_lt le_rfl i hi
  rw [Wts.lamTrue_eq, Wts.lamN_eq W u le_rfl, dif_neg hi, RowPar.eAt_of _ hB]
  simp only [e1]
  unfold wG
  push_cast
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sgTrue_entry (hW : W.Ok) (u : Word) (τ : X.Tau) (i : Fin (R.N R.m - 1)) :
    ((W.sgTrue τ).w i : ℚ) =
      (RowPar.of (W.hc u τ)).sgHC i.1 - RowPar.sh R - ((R.k : ℚ) - 2) / 2 - (R.m : ℚ) * (((R.t : ℚ) + 1) / 2) + (i.1 : ℚ) := by
  unfold Wts.sgTrue
  rw [← hW.hc_row u τ, RowPar.sgTrue_eq]
  unfold rhoVec
  have c1 : ((R.N R.m - 1 : ℕ) : ℚ) = (R.k : ℚ) + (R.m : ℚ) * ((R.t : ℚ) + 1) - 1 := by
    rw [Nat.cast_sub (R.N_pos R.m)]
    unfold Ranks.N
    push_cast
    ring
  rw [c1]
  ring

/- English proof (translation)
Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem nonneg_sub_of_lt {a b : ℤ} (h : (b : ℚ) - 1 < a) : 0 ≤ a - b := by
  have : b - 1 < a := by exact_mod_cast h
  omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Consider separately whether the proposition holds or fails. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Rewrite the indicated hypotheses using the stated equalities. Move the embeddings inside the algebraic operations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite the indicated hypotheses using the stated equalities. Move the embeddings inside the algebraic operations. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem interlace (hW : W.Ok) (u : Word) (τ : X.Tau) :
    Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) := by
  intro i
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hs := sgTrue_entry W hW u τ i
  have hi : i.1 < R.k + R.m * (R.t + 1) - 1 := i.2
  have hS : (Br.iS (N_m_succ R) i).1 = i.1 + 1 := rfl
  have hC : (Br.iC (N_m_succ R) i).1 = i.1 := rfl
  have ck : ((R.k - 1 : ℕ) : ℚ) = (R.k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  unfold Br.aBr Br.bBr
  by_cases h1 : i.1 < R.k - 1
  · rw [RowPar.sgHC_lo _ h1, RowPar.vb_lo _ h1] at hs
    have a1 := (W.hc u τ).u_gt_v ⟨i.1, h1⟩
    have a2 := (W.hc u τ).v_gt_u ⟨i.1, h1⟩
    have l1 := lamTrue_lo W u τ _ ⟨i.1 + 1, by omega⟩ hS
    have l2 := lamTrue_lo W u τ _ ⟨i.1, by omega⟩ hC
    simp only at a1 a2 l1 l2
    push_cast at l1
    exact ⟨nonneg_sub_of_lt (by linarith), nonneg_sub_of_lt (by linarith)⟩
  · obtain ⟨B, ρ, hρ, hn⟩ : ∃ B ρ, ρ < R.t + 1 ∧ i.1 = R.k - 1 + B * (R.t + 1) + ρ := by
      refine ⟨(i.1 - (R.k - 1)) / (R.t + 1), (i.1 - (R.k - 1)) % (R.t + 1), Nat.mod_lt _ (by omega), ?_⟩
      have := Nat.div_add_mod (i.1 - (R.k - 1)) (R.t + 1)
      rw [Nat.mul_comm] at this
      omega
    have hBm : B < R.m := by
      apply Nat.lt_of_mul_lt_mul_right (a := R.t + 1)
      omega
    have l1 := lamTrue_hi W u τ _ B ρ hρ (by rw [hS]; omega : (Br.iS (N_m_succ R) i).1 = _)
    rw [hn] at hs
    rcases Nat.eq_zero_or_pos ρ with rfl | hρ0
    · rw [Nat.add_zero, RowPar.sgHC_b] at hs
      push_cast [ck] at hs
      have g1 := RowPar.gap_be (W.hc u τ) hBm
      refine ⟨nonneg_sub_of_lt (by linarith), nonneg_sub_of_lt ?_⟩
      rcases B with _ | B
      · have l2 := lamTrue_lo W u τ _ ⟨R.k - 1, by omega⟩ (by rw [hC]; simp only; omega : (Br.iC (N_m_succ R) i).1 = _)
        have a1 := (W.hc u τ).u_last_gt (by omega) hBm
        rw [RowPar.bAt_of _ hBm] at hs
        simp only [ck] at l2
        push_cast at hs
        linarith
      · have l2 := lamTrue_hi W u τ _ B R.t (by omega)
          (by rw [hC, hn, Nat.succ_mul]; omega : (Br.iC (N_m_succ R) i).1 = _)
        have g2 := RowPar.gap_eb (W.hc u τ) hBm
        push_cast at hs
        linarith
    · rw [RowPar.sgHC_e _ B ρ hρ0 (by omega)] at hs
      push_cast [ck] at hs
      have l2 := lamTrue_hi W u τ _ B (ρ - 1) (by omega) (by rw [hC]; omega : (Br.iC (N_m_succ R) i).1 = _)
      exact ⟨nonneg_sub_of_lt (by linarith), nonneg_sub_of_lt (by linarith)⟩

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem members : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.Members :=
  fun _ _ _ W hW u τ => ⟨interlace W hW u τ, members_sameShift W hW u τ⟩

end GlobalTheory.BranchMembers
