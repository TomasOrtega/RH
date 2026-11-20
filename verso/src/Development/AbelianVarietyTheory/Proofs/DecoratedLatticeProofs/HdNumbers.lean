import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk

noncomputable section

namespace GlobalTheory.Core.Rk

/- English proof (translation)
Introduce `D u L C' Cl Cg cb Cu cT CT h`. Take `⟨-, -, hH, hN, -⟩` from `h`. Take `⟨hL1, -, hmf, hfk, -, -, -, -, -, -, -, hg0, -, hg1, -⟩` from `hH`. Take `⟨-, -, -, -, -, -, -, -, hT, hdu, -⟩` from `hN`. Establish `hm : 2 ≤ D.R.m` using `D.R.two_le_m`.

Establish `hm4 : 16 ≤ D.R.m ^ 4`. Combine the equalities or inequalities in the displayed calculation. Establish `hf16 : 16 ≤ D.R.f` using `le_trans hm4 hmf`. Establish `hk16 : 16 ≤ D.R.k` using `le_trans hf16 hfk`. Establish `hmR : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast hm`.

Establish `hfR : (16 : ℝ) ≤ D.R.f` using `by exact_mod_cast hf16`. Establish `hkR : (16 : ℝ) ≤ D.R.k` using `by exact_mod_cast hk16`. Establish `hL : (1 : ℝ) ≤ L` using `hL1.le`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hm5 : (32 : ℝ) ≤ (D.R.m : ℝ) ^ 5`.

Combine the equalities or inequalities in the displayed calculation. Unfold `mfL`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul (mul_le_mul hm5 hfR (by norm_num) (by positivity)) hL (by norm_num) (by positivity)` to reduce the goal to its premises. Establish `hb : (1 : ℝ) ≤ Real.exp L` using `Real.one_le_exp (by linarith)`.

Establish `hkg : ∀ g : ℝ, ((D.R.k : ℝ) * Real.exp L) ^ 8 ≤ g → (D.R.k : ℝ) ^ 8 ≤ g` using `fun g hg => le_trans (pow_le_pow_left₀ (by positivity) (le_mul_of_one_le_right (by positivity) hb) 8) hg`. Establish `h0 : D.R.k ^ 8 ≤ D.host.g 0` using `by exact_mod_cast hkg _ hg0`. Establish `h1 : D.R.k ^ 8 ≤ D.host.g 1` using `by exact_mod_cast hkg _ hg1`. Use `set N := (D.host.g 0 * D.host.g 1) ^ 2 with hNdef`. Establish `hk8 : 4 * D.R.f ≤ D.R.k ^ 8`.

Combine the equalities or inequalities in the displayed calculation. Establish `hkpos : 1 ≤ D.R.k ^ 8` using `Nat.one_le_pow _ _ (by omega)`. Establish `hgg : D.R.k ^ 8 ≤ D.host.g 0 * D.host.g 1` using `le_trans h0 (Nat.le_mul_of_pos_right _ (by omega))`. Establish `hNge : D.host.g 0 * D.host.g 1 ≤ N`. Rewrite using `[hNdef, sq]; exact Nat.le_mul_of_pos_right _ (by omega)`.

Establish `hN4 : 4 * D.R.f ≤ N` using `le_trans hk8 (le_trans hgg hNge)`. Establish `hN2 : 2 ≤ N` using `by omega`. Take `⟨-, hmod⟩` from `hT u`. Rewrite `hmod` using `[Nat.one_mod_eq_one.mpr (by omega)]`. Establish `hTp` using `(D.mem u).A.T_prime`.

Establish `h2` using `hTp.two_le`. Establish `hdiv` using `Nat.div_add_mod ((D.mem u).A.T) N`. Rewrite `hdiv` using `[hmod]`. Establish `hq : (D.mem u).A.T / N ≠ 0`. Introduce `hq0`.

Rewrite `hdiv` using `[hq0]`. Use linear arithmetic over natural numbers and integers. Establish `: N ≤ N * ((D.mem u).A.T / N)` using `Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hq)`. Use linear arithmetic over natural numbers and integers. Rewrite using `[d0_eq]`.

Conclude with `hdu u`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hd_numbers : ∀ (D : D7) (u : D.what₂.Word) (L C' Cl Cg cb Cu cT CT : ℝ), HD D L C' Cl Cg cb Cu cT CT →
    5 ≤ mfL D L ∧ 4 * D.R.f + 1 ≤ (D.mem u).A.T ∧ 0 < d0 D u ∧ 5 ≤ (D.R.f : ℝ) * D.R.k * L := by
  intro D u L C' Cl Cg cb Cu cT CT h
  obtain ⟨-, -, hH, hN, -⟩ := h
  obtain ⟨hL1, -, hmf, hfk, -, -, -, -, -, -, -, hg0, -, hg1, -⟩ := hH
  obtain ⟨-, -, -, -, -, -, -, -, hT, hdu, -⟩ := hN
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hm4 : 16 ≤ D.R.m ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm 4
  have hf16 : 16 ≤ D.R.f := le_trans hm4 hmf
  have hk16 : 16 ≤ D.R.k := le_trans hf16 hfk
  have hmR : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hfR : (16 : ℝ) ≤ D.R.f := by exact_mod_cast hf16
  have hkR : (16 : ℝ) ≤ D.R.k := by exact_mod_cast hk16
  have hL : (1 : ℝ) ≤ L := hL1.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm5 : (32 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := by
      calc (32 : ℝ) = 2 ^ 5 := by norm_num
        _ ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hmR 5
    unfold mfL
    calc (5 : ℝ) ≤ 32 * 16 * 1 := by norm_num
      _ ≤ (D.R.m : ℝ) ^ 5 * D.R.f * L := by
        apply mul_le_mul (mul_le_mul hm5 hfR (by norm_num) (by positivity)) hL (by norm_num) (by positivity)
  · have hb : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp (by linarith)
    have hkg : ∀ g : ℝ, ((D.R.k : ℝ) * Real.exp L) ^ 8 ≤ g → (D.R.k : ℝ) ^ 8 ≤ g := fun g hg =>
      le_trans (pow_le_pow_left₀ (by positivity) (le_mul_of_one_le_right (by positivity) hb) 8) hg
    have h0 : D.R.k ^ 8 ≤ D.host.g 0 := by exact_mod_cast hkg _ hg0
    have h1 : D.R.k ^ 8 ≤ D.host.g 1 := by exact_mod_cast hkg _ hg1
    set N := (D.host.g 0 * D.host.g 1) ^ 2 with hNdef
    have hk8 : 4 * D.R.f ≤ D.R.k ^ 8 := by
      calc 4 * D.R.f ≤ D.R.k * D.R.k := Nat.mul_le_mul (by omega) hfk
        _ = D.R.k ^ 2 := (sq _).symm
        _ ≤ D.R.k ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hkpos : 1 ≤ D.R.k ^ 8 := Nat.one_le_pow _ _ (by omega)
    have hgg : D.R.k ^ 8 ≤ D.host.g 0 * D.host.g 1 :=
      le_trans h0 (Nat.le_mul_of_pos_right _ (by omega))
    have hNge : D.host.g 0 * D.host.g 1 ≤ N := by
      rw [hNdef, sq]; exact Nat.le_mul_of_pos_right _ (by omega)
    have hN4 : 4 * D.R.f ≤ N := le_trans hk8 (le_trans hgg hNge)
    have hN2 : 2 ≤ N := by omega
    obtain ⟨-, hmod⟩ := hT u
    rw [Nat.one_mod_eq_one.mpr (by omega)] at hmod
    have hTp := (D.mem u).A.T_prime
    have h2 := hTp.two_le
    have hdiv := Nat.div_add_mod ((D.mem u).A.T) N
    rw [hmod] at hdiv
    have hq : (D.mem u).A.T / N ≠ 0 := by
      intro hq0; rw [hq0] at hdiv; omega
    have : N ≤ N * ((D.mem u).A.T / N) := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hq)
    omega
  · rw [d0_eq]; exact hdu u
  · calc (5 : ℝ) ≤ 16 * 16 * 1 := by norm_num
      _ ≤ (D.R.f : ℝ) * D.R.k * L :=
        mul_le_mul (mul_le_mul hfR hkR (by norm_num) (by positivity)) hL (by norm_num) (by positivity)

end GlobalTheory.Core.Rk

end
