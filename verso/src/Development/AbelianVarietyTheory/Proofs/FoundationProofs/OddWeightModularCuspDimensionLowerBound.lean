import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPointSlashEvaluationsIndependentGammaStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEisensteinSlashNeOutsideGammaStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOddWeightFrameDetNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOddFrameNotReducesToSmallerOddWeightStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducesOfDetEvMEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducesToSmallerOddWeightOfLeadingCoeffMatrixDetStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTendstoSlashEvaluationMatrixMulStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualOddFrameCuspFormsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoSmulInvOfMulTendstoInvertibleMatrixStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelOneTwelveMulFinrankModularFormLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalOfGammaLeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlusMinusCosetRepresentativesTwoMulCardStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumFinrankLevelOneLeFinrankOfFrameStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumFinrankLevelOneLeFinrankCuspFormOfFrameStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeMulCardOddFrameWeightsDvdThreeStatement

open UpperHalfPlane Filter GlobalTheory.OddFrame
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[CongruenceSubgroup.Gamma1_mem]`. Establish `h1 : ((2 : ℕ) : ZMod N) = 0`. Use `h.1` as an intermediate fact. Simplify using `at this`.

Use `push_cast`. Take the linear combination `-this`. Rewrite `h1` using `[ZMod.natCast_eq_zero_iff]`. Use `Nat.le_of_dvd (by norm_num) h1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem neg_one_not_mem_Gamma1 {N : ℕ} (hN : 5 ≤ N) : (-1 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma1 N := by
  intro h
  rw [CongruenceSubgroup.Gamma1_mem] at h
  have h1 : ((2 : ℕ) : ZMod N) = 0 := by
    have := h.1
    simp at this
    push_cast
    linear_combination -this
  rw [ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd (by norm_num) h1
  omega

/- English proof (translation)
Rewrite using `[CongruenceSubgroup.Gamma_mem]`. Apply the tactic sequence `interval_cases M <;> simp <;> decide`.
-/
theorem neg_one_mem_Gamma {M : ℕ} (h0 : 0 < M) (hM : M < 3) : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem]
  interval_cases M <;> simp <;> decide

/- English proof (translation)
Establish `hfi` using `finiteIndex_of_Gamma_le hM hΓ`. Establish `hM3 : 3 ≤ M`. Assume the negation of the conclusion as `h`. Conclude with `h1 (hΓ (neg_one_mem_Gamma hM (by omega)))`. Take `⟨τ₀, hτ₀⟩` from `GlobalTheory.T.exists_point_slashEvaluations_independent_gamma M hM (GlobalTheory.T.exists_eisenstein_slash_ne_outside_gamma M hM3)`.

Take `⟨w₀, F₀, hF₀, hd₀⟩` from `GlobalTheory.T.exists_odd_weight_frame_det_ne_zero M Γ r s τ₀ hM hΓ h1 hs hτ₀`. Take `⟨w, F, hF, -, hred⟩` from `GlobalTheory.T.exists_oddFrame_not_reducesToSmallerOddWeight Γ r s w₀ F₀ hfi hF₀ ⟨τ₀, hd₀⟩`. Establish `hdet : ∀ τ, (evM s w F τ).det ≠ 0` using `fun τ h => hred (GlobalTheory.T.reduces_of_det_evM_eq_zero' Γ r s w F τ hs hF h)`. Establish `hlead : (leadM M s w F).det ≠ 0` using `fun h => hred (GlobalTheory.T.reducesToSmallerOddWeight_of_leadingCoeffMatrix_det_zero M Γ r s w F hM hΓ hs hF h)`. Take `⟨U, hU1, hU2⟩` from `GlobalTheory.T.exists_tendsto_slashEvaluationMatrix_mul M Γ r s w F hM hΓ hs hF hlead`.

Take `⟨G, hG, hGd⟩` from `GlobalTheory.T.exists_dual_oddFrame_cuspForms Γ r s w F h1 hs hF hdet (GlobalTheory.T.tendsto_smul_inv_of_mul_tendsto_invertible_matrix r _ U _ _ hlead hU1 hU2)`. Conclude with `⟨w, F, G, hF, hdet, hG, hGd⟩`.
-/
theorem exists_frame (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (hM : 0 < M) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ)
    (h1 : (-1 : SL(2, ℤ)) ∉ Γ) {r : ℕ} {s : Fin r → SL(2, ℤ)} (hs : IsReps Γ s) :
    ∃ (w : Fin r → ℤ) (F G : Fin r → ℍ → ℂ), (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) ∧
      (∀ τ, (evM s w F τ).det ≠ 0) ∧ (∀ j, IsCF Γ (12 - w j) (G j)) ∧
      ∀ τ, (evM s (fun j => 12 - w j) G τ).det ≠ 0 := by
  have hfi := finiteIndex_of_Gamma_le hM hΓ
  have hM3 : 3 ≤ M := by
    by_contra h
    exact h1 (hΓ (neg_one_mem_Gamma hM (by omega)))
  obtain ⟨τ₀, hτ₀⟩ := GlobalTheory.T.exists_point_slashEvaluations_independent_gamma M hM (GlobalTheory.T.exists_eisenstein_slash_ne_outside_gamma M hM3)
  obtain ⟨w₀, F₀, hF₀, hd₀⟩ := GlobalTheory.T.exists_odd_weight_frame_det_ne_zero M Γ r s τ₀ hM hΓ h1 hs hτ₀
  obtain ⟨w, F, hF, -, hred⟩ := GlobalTheory.T.exists_oddFrame_not_reducesToSmallerOddWeight Γ r s w₀ F₀ hfi hF₀ ⟨τ₀, hd₀⟩
  have hdet : ∀ τ, (evM s w F τ).det ≠ 0 := fun τ h => hred (GlobalTheory.T.reduces_of_det_evM_eq_zero' Γ r s w F τ hs hF h)
  have hlead : (leadM M s w F).det ≠ 0 := fun h => hred (GlobalTheory.T.reducesToSmallerOddWeight_of_leadingCoeffMatrix_det_zero M Γ r s w F hM hΓ hs hF h)
  obtain ⟨U, hU1, hU2⟩ := GlobalTheory.T.exists_tendsto_slashEvaluationMatrix_mul M Γ r s w F hM hΓ hs hF hlead
  obtain ⟨G, hG, hGd⟩ := GlobalTheory.T.exists_dual_oddFrame_cuspForms Γ r s w F h1 hs hF hdet (GlobalTheory.T.tendsto_smul_inv_of_mul_tendsto_invertible_matrix r _ U _ _ hlead hU1 hU2)
  exact ⟨w, F, G, hF, hdet, hG, hGd⟩

/- English proof (translation)
Establish `ha` using `GlobalTheory.T.levelOne_twelve_mul_finrank_modularForm_lower_bound (k - j) (hk.sub_odd hj)`. Establish `hb` using `GlobalTheory.T.levelOne_twelve_mul_finrank_modularForm_lower_bound (k - (12 - j)) (hk.sub_odd (Even.sub_odd (by decide) hj))`. Rewrite `hk`, `hj` using `[Int.odd_iff]`. Generalize the expression as in `(Module.finrank ℂ (ModularForm 𝒮ℒ (k - j)) : ℤ) = a at *`. Generalize the expression as in `(Module.finrank ℂ (ModularForm 𝒮ℒ (k - (12 - j))) : ℤ) = b at *`.

Apply the tactic sequence `have e4 : ((if (k - j) % 4 = 0 then 1 else -1) : ℤ) + (if (k - (12 - j)) % 4 = 0 then 1 else -1) = 0 := by split_ifs <;> omega`. Apply the tactic sequence `have e3 : ((if (k - j) % 6 = 0 then 1 else if (k - j) % 6 = 2 then -1 else 0) : ℤ) + (if (k - (12 - j)) % 6 = 0 then 1 else if (k - (12 - j)) % 6 = 2 then -1 else 0) = (if k % 3 = 0 then 1 else if k % 3 = 2 then -1 else 0) * (3 * (if (3 : ℤ) ∣ j then 1 else 0) - 1) := by split_if …`. Rewrite using `[mul_assoc, ← e3]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem levelOne_pair (k j : ℤ) (hk : Odd k) (hj : Odd j) :
    2 * k - 2 + 4 * (if k % 3 = 0 then 1 else if k % 3 = 2 then -1 else 0) * (3 * (if (3 : ℤ) ∣ j then 1 else 0) - 1)
      ≤ 12 * ((Module.finrank ℂ (ModularForm 𝒮ℒ (k - j)) : ℤ) +
        (Module.finrank ℂ (ModularForm 𝒮ℒ (k - (12 - j))) : ℤ)) := by
  have ha := GlobalTheory.T.levelOne_twelve_mul_finrank_modularForm_lower_bound (k - j) (hk.sub_odd hj)
  have hb := GlobalTheory.T.levelOne_twelve_mul_finrank_modularForm_lower_bound (k - (12 - j)) (hk.sub_odd (Even.sub_odd (by decide) hj))
  rw [Int.odd_iff] at hk hj
  generalize (Module.finrank ℂ (ModularForm 𝒮ℒ (k - j)) : ℤ) = a at *
  generalize (Module.finrank ℂ (ModularForm 𝒮ℒ (k - (12 - j))) : ℤ) = b at *
  have e4 : ((if (k - j) % 4 = 0 then 1 else -1) : ℤ) + (if (k - (12 - j)) % 4 = 0 then 1 else -1) = 0 := by
    split_ifs <;> omega
  have e3 : ((if (k - j) % 6 = 0 then 1 else if (k - j) % 6 = 2 then -1 else 0) : ℤ) +
      (if (k - (12 - j)) % 6 = 0 then 1 else if (k - (12 - j)) % 6 = 2 then -1 else 0) =
      (if k % 3 = 0 then 1 else if k % 3 = 2 then -1 else 0) * (3 * (if (3 : ℤ) ∣ j then 1 else 0) - 1) := by
    split_ifs <;> omega
  rw [mul_assoc, ← e3]
  linarith

/- English proof (translation)
Introduce `N M Γ k hN hM hΓ hΓ1 hk hk3`. Take `⟨hfM, hfS⟩` from `GlobalTheory.T.finiteDimensional_modularForm_cuspForm_of_gamma_le M Γ k hM hΓ`. Use `⟨hfM, hfS, ?_⟩` and prove the remaining obligations. Establish `hfi` using `finiteIndex_of_Gamma_le hM hΓ`. Establish `h1 : (-1 : SL(2, ℤ)) ∉ Γ` using `fun h => neg_one_not_mem_Gamma1 hN (hΓ1 h)`.

Take `⟨r, s, hs, hr⟩` from `GlobalTheory.T.exists_plusMinusCosetRepresentatives_two_mul_card Γ hfi h1`. Take `⟨w, F, G, hF, hd, hG, hGd⟩` from `exists_frame M Γ hM hΓ h1 hs`. Establish `hcM` using `GlobalTheory.T.sum_finrank_levelOne_le_finrank_of_frame Γ r s w F k hfi hfM (fun j => (hF j).2) hd`. Establish `hcS` using `GlobalTheory.T.sum_finrank_levelOne_le_finrank_cuspForm_of_frame Γ r s (fun j => 12 - w j) G k hfi hfS hG hGd`. Establish `h3` using `GlobalTheory.T.three_mul_card_oddFrame_weights_dvd_three N Γ r s w F hN hΓ1 hs hF (hd _)`.

Establish `hkz : Odd (k : ℤ)` using `by exact_mod_cast hk`. Establish `hsum` using `Finset.sum_le_sum (s := Finset.univ) fun j _ => levelOne_pair k (w j) hkz (hF j).1`. Establish `h3' : ∑ j, (3 * (if (3 : ℤ) ∣ w j then (1 : ℤ) else 0) - 1) = 0`. Rewrite using `[Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]`.

Establish `: (3 : ℤ) * ((Finset.univ.filter fun j => (3 : ℤ) ∣ w j).card : ℤ) = r` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers. Rewrite `hsum` using `[Finset.sum_add_distrib, ← Finset.mul_sum, h3', ← Finset.mul_sum, Finset.sum_add_distrib]`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_zero, add_zero] at hsum`. Establish `hcM' : ∑ j, (Module.finrank ℂ (ModularForm 𝒮ℒ ((k : ℤ) - w j)) : ℤ) ≤ Module.finrank ℂ (ModularForm Γ (k : ℤ))` using `by exact_mod_cast hcM`.

Establish `hcS' : ∑ j, (Module.finrank ℂ (ModularForm 𝒮ℒ ((k : ℤ) - (12 - w j))) : ℤ) ≤ Module.finrank ℂ (CuspForm Γ (k : ℤ))` using `by exact_mod_cast hcS`. Rewrite using `[← hr]`. Take `⟨m, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Use `zify`. Simplify using `only [Nat.add_sub_cancel]`.

Move the coercions through the operations in `at hsum hcM' hcS' ⊢`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem dim_lower_bound : ∀ (N M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → 0 < M →
    CongruenceSubgroup.Gamma M ≤ Γ → Γ ≤ CongruenceSubgroup.Gamma1 N → Odd k → 3 ≤ k →
    FiniteDimensional ℂ (ModularForm Γ (k : ℤ)) ∧ FiniteDimensional ℂ (CuspForm Γ (k : ℤ)) ∧
      (k - 1) * Γ.index ≤
        12 * (Module.finrank ℂ (ModularForm Γ (k : ℤ)) + Module.finrank ℂ (CuspForm Γ (k : ℤ))) := by
  intro N M Γ k hN hM hΓ hΓ1 hk hk3
  obtain ⟨hfM, hfS⟩ := GlobalTheory.T.finiteDimensional_modularForm_cuspForm_of_gamma_le M Γ k hM hΓ
  refine ⟨hfM, hfS, ?_⟩
  have hfi := finiteIndex_of_Gamma_le hM hΓ
  have h1 : (-1 : SL(2, ℤ)) ∉ Γ := fun h => neg_one_not_mem_Gamma1 hN (hΓ1 h)
  obtain ⟨r, s, hs, hr⟩ := GlobalTheory.T.exists_plusMinusCosetRepresentatives_two_mul_card Γ hfi h1
  obtain ⟨w, F, G, hF, hd, hG, hGd⟩ := exists_frame M Γ hM hΓ h1 hs
  have hcM := GlobalTheory.T.sum_finrank_levelOne_le_finrank_of_frame Γ r s w F k hfi hfM (fun j => (hF j).2) hd
  have hcS := GlobalTheory.T.sum_finrank_levelOne_le_finrank_cuspForm_of_frame Γ r s (fun j => 12 - w j) G k hfi hfS hG hGd
  have h3 := GlobalTheory.T.three_mul_card_oddFrame_weights_dvd_three N Γ r s w F hN hΓ1 hs hF (hd _)
  have hkz : Odd (k : ℤ) := by exact_mod_cast hk
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun j _ => levelOne_pair k (w j) hkz (hF j).1
  have h3' : ∑ j, (3 * (if (3 : ℤ) ∣ w j then (1 : ℤ) else 0) - 1) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have : (3 : ℤ) * ((Finset.univ.filter fun j => (3 : ℤ) ∣ w j).card : ℤ) = r := by exact_mod_cast h3
    omega
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, h3', ← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_zero, add_zero] at hsum
  have hcM' : ∑ j, (Module.finrank ℂ (ModularForm 𝒮ℒ ((k : ℤ) - w j)) : ℤ) ≤
      Module.finrank ℂ (ModularForm Γ (k : ℤ)) := by exact_mod_cast hcM
  have hcS' : ∑ j, (Module.finrank ℂ (ModularForm 𝒮ℒ ((k : ℤ) - (12 - w j))) : ℤ) ≤
      Module.finrank ℂ (CuspForm Γ (k : ℤ)) := by exact_mod_cast hcS
  rw [← hr]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  zify
  simp only [Nat.add_sub_cancel]
  push_cast at hsum hcM' hcS' ⊢
  nlinarith

end GlobalTheory.OddFrame
