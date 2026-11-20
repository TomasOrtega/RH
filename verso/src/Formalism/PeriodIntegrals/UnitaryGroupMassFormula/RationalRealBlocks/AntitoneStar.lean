import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.EvenStep

open MvPolynomial Matrix

noncomputable section

namespace PI.BlockRatReal

/- English proof (translation)
By extensionality, compare the relevant components. Both sides reduce to the same expression.
-/
theorem reM_rfl {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) : reM (m := m) rfl A = A := by
  ext i j
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem detShift_eq {m : ℕ} (w : Fin (m + 1) → ℤ) : detShift w = w (Fin.last m) := by
  rw [detShift, dif_pos (Nat.succ_pos m)]
  rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.
-/
theorem natW_eq {m : ℕ} (w : Fin (m + 1) → ℤ) : natW w = nuOf w := by
  funext i
  rw [natW, nuOf, detShift_eq]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem antitone_star {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone fun i : Fin (m + 1) => -lam i.rev :=
  fun _ _ hij => neg_le_neg (h (Fin.rev_le_rev.mpr hij))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem stmt_of (hE : EvenStep) (hO : OddStep) : Stmt := by
  intro nV n' m lam0 Tau _ n LL _ h pos G M embLL lam hanti htie hM
  subst h
  intro v s f hf
  set τ := pos ⟨v, s⟩ with hτ
  have hl : lam0 v s = lam τ := funext fun i => by rw [htie v s i]; rfl
  obtain ⟨M0, hM0⟩ := hM τ
  have hf' : f ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf (lam τ)) := by
    rw [← natW_eq]; exact hf
  by_cases hs : Even s.val
  · have hla : lamAt (lam0 v) s = lam τ := by rw [lamAt, if_pos hs, hl]
    obtain ⟨F, hF, hFe⟩ := hE m LL embLL (lam τ) (hanti τ) M0 f hf'
    refine ⟨F, ?_, fun y => ?_⟩
    · rw [blkMod, hla, if_pos (hanti τ)]; exact hF
    · have h1 := hFe (y.1 τ) (y.2 τ)
      rw [zAt, if_pos hs, reM_rfl, eAt, hla, detShift_eq, hM0]
      exact h1
  · have hla : lamAt (lam0 v) s = fun i => -lam τ i.rev := by rw [lamAt, if_neg hs, hl]
    obtain ⟨F, hF, hFe⟩ := hO m LL embLL (lam τ) (hanti τ) M0 f hf'
    refine ⟨F, ?_, fun y => ?_⟩
    · rw [blkMod, hla, if_pos (antitone_star (hanti τ))]; exact hF
    · have h1 := hFe (y.1 τ) (y.2 τ)
      rw [zAt, if_neg hs, reM_rfl, eAt, hla, detShift_eq, hM0]
      exact h1

end PI.BlockRatReal
