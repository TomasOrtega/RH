import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.PeriodIntegrals.ZuckTensor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.DualDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.DualChoice

open Matrix Finset
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

variable {n : ℕ}

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private lemma revNum_single (s x : Fin n) :
    (Pi.single (Fin.rev s) (1 : ℝ) : Fin n → ℝ) x = (Pi.single s (1 : ℝ) : Fin n → ℝ) (Fin.rev x) := by
  simp only [Pi.single_apply, Fin.rev_eq_iff]

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem revNum_rhoC (ε : Fin n → Bool) (a : Fin n) : rhoC (revE ε) a = - rhoC ε (Fin.rev a) := by
  have h1 : #(univ.filter fun b => a < b ∧ revE ε b = revE ε a) =
      #(univ.filter fun b => b < Fin.rev a ∧ ε b = ε (Fin.rev a)) := by
    apply Finset.card_nbij' Fin.rev Fin.rev
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.rev_lt_rev.mpr hb.2.1, hb.2.2⟩
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.lt_rev_iff.mpr hb.2.1, by simp only [revE, Fin.rev_rev]; exact hb.2.2⟩
    · intro b _; exact Fin.rev_rev b
    · intro b _; exact Fin.rev_rev b
  have h2 : #(univ.filter fun b => b < a ∧ revE ε b = revE ε a) =
      #(univ.filter fun b => Fin.rev a < b ∧ ε b = ε (Fin.rev a)) := by
    apply Finset.card_nbij' Fin.rev Fin.rev
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.rev_lt_rev.mpr hb.2.1, hb.2.2⟩
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.rev_lt_iff.mpr hb.2.1, by simp only [revE, Fin.rev_rev]; exact hb.2.2⟩
    · intro b _; exact Fin.rev_rev b
    · intro b _; exact Fin.rev_rev b
  simp only [rhoC]
  rw [h1, h2]
  ring

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem revNum_rhoN (ε : Fin n → Bool) (a : Fin n) : rhoN (revE ε) a = - rhoN ε (Fin.rev a) := by
  have h1 : #(univ.filter fun b => a < b ∧ revE ε b ≠ revE ε a) =
      #(univ.filter fun b => b < Fin.rev a ∧ ε b ≠ ε (Fin.rev a)) := by
    apply Finset.card_nbij' Fin.rev Fin.rev
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.rev_lt_rev.mpr hb.2.1, hb.2.2⟩
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.lt_rev_iff.mpr hb.2.1, by simp only [revE, Fin.rev_rev]; exact hb.2.2⟩
    · intro b _; exact Fin.rev_rev b
    · intro b _; exact Fin.rev_rev b
  have h2 : #(univ.filter fun b => b < a ∧ revE ε b ≠ revE ε a) =
      #(univ.filter fun b => Fin.rev a < b ∧ ε b ≠ ε (Fin.rev a)) := by
    apply Finset.card_nbij' Fin.rev Fin.rev
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.rev_lt_rev.mpr hb.2.1, hb.2.2⟩
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.rev_lt_iff.mpr hb.2.1, by simp only [revE, Fin.rev_rev]; exact hb.2.2⟩
    · intro b _; exact Fin.rev_rev b
    · intro b _; exact Fin.rev_rev b
  simp only [rhoN]
  rw [h1, h2]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem harish_chandra_holds : HCRev := by
  intro n lam ⟨hs, hz⟩
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · show -lam (Fin.rev b) < -lam (Fin.rev a)
    exact neg_lt_neg (hs (Fin.rev_lt_rev.mpr hab))
  · obtain ⟨m, hm⟩ := hz (Fin.rev a)
    refine ⟨-m - (n : ℤ) + 1, ?_⟩
    simp only [revP]
    push_cast
    linarith

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem spectral_gap_holds : GapRev := by
  intro n ε lam h hg a b hab
  have := hg (Fin.rev a) (Fin.rev b) hab
  have e : revP lam a - revP lam b = -(lam (Fin.rev a) - lam (Fin.rev b)) := by
    simp only [revP]; ring
  rw [e, abs_neg]
  exact this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lowest_k_type_holds : LowKRev := by
  intro n ε lam
  funext a
  simp only [lowK, revP, Pi.add_apply, Pi.sub_apply, revNum_rhoC, revNum_rhoN]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem revNum_nsq (u : Fin n → ℝ) : nsq (revP u) = nsq u := by
  simp only [nsq, dot, revP, neg_mul_neg]
  exact Equiv.sum_comp Fin.revPerm (fun a => u a * u a)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem vector_norm_holds : VNormRev := by
  intro n ε ν
  have e : revP ν + (2 : ℝ) • rhoC (revE ε) = revP (ν + (2 : ℝ) • rhoC ε) := by
    funext a
    simp only [revP, Pi.add_apply, Pi.smul_apply, smul_eq_mul, revNum_rhoC]
    ring
  simp only [vNormSq]
  rw [e, revNum_nsq]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem compact_dominant_holds : CDomRev := by
  intro n ε μ Λ ⟨c, hc, hsum⟩
  refine ⟨fun a b => c (Fin.rev b) (Fin.rev a), fun a b h => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hc _ _ h
    exact ⟨Fin.rev_lt_rev.mp h1, h2.symm⟩
  · funext x
    have key : ∀ a b : Fin n, root (Fin.rev b) (Fin.rev a) x = - root a b (Fin.rev x) := by
      intro a b
      simp only [root, Pi.sub_apply, revNum_single]
      ring
    have hx := congrFun hsum (Fin.rev x)
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx
    have re : (∑ a : Fin n, ∑ b : Fin n, (c (Fin.rev b) (Fin.rev a) : ℝ) * root a b x) =
        ∑ a : Fin n, ∑ b : Fin n, (c a b : ℝ) * root (Fin.rev b) (Fin.rev a) x := by
      rw [Finset.sum_comm]
      refine Fintype.sum_equiv Fin.revPerm _ _ (fun b => ?_)
      refine Fintype.sum_equiv Fin.revPerm _ _ (fun a => ?_)
      simp only [Fin.revPerm_apply, Fin.rev_rev]
    simp only [Pi.sub_apply, revP, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [re]
    simp only [key, mul_neg, Finset.sum_neg_distrib, ← hx]
    ring

end PI.ZuckTensorWork
end
