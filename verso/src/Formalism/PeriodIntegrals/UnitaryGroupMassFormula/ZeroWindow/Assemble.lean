import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.FinsumMemLeFinsumMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.Jensen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.RightOne

namespace PI.ZW

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rightChi : RightChi := rightChi_of jensenCount

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rightOne : RightOne := rightOne_of jensenCount

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Replace the relevant objects with their definitions.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact. Replace the relevant objects with their definitions.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact. Replace the relevant objects with their definitions.

Supply the required witnesses or components.
-/
theorem zerosWindow_of_transfer (hT : Transfer) :
    PI.LBoundRight → PI.ZetaBoundRight → PI.LInvRight → PI.ZerosWindow := by
  intro hL hZ hI
  obtain ⟨C₁, h₁⟩ := rightChi hL hI
  obtain ⟨C₂, h₂⟩ := rightOne hZ hI
  have hlog : ∀ (N : ℕ) [NeZero N] (t : ℝ), 0 ≤ Real.log (↑N * (|t| + 2)) := by
    intro N _ t
    apply Real.log_nonneg
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    nlinarith [abs_nonneg t, mul_nonneg (sub_nonneg.mpr hN) (add_nonneg (abs_nonneg t) zero_le_two)]
  have h₁' : RightChiWith (max C₁ 1) := by
    unfold RightChiWith at h₁ ⊢
    intro N _ χ hχ t
    obtain ⟨hf, hs⟩ := h₁ N χ hχ t
    exact ⟨hf, hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlog N t))⟩
  have h₂' : RightOneWith (max C₂ 1) := by
    unfold RightOneWith at h₂ ⊢
    intro N _ χ hχ t
    obtain ⟨hf, hs⟩ := h₂ N χ hχ t
    exact ⟨hf, hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlog N t))⟩
  have hw := zerosWindowWith_of _ (rightHalf_of _ _ h₁' h₂') hT
  unfold PI.ZerosWindow
  exact ⟨_, mul_pos two_pos (lt_of_lt_of_le one_pos (le_trans (le_max_right C₁ 1) (le_max_left _ _))), hw⟩

end PI.ZW
