import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.CountT
import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

/- English proof (translation)
Introduce `D L C' Cl Cg cb Cu cT CT n0 A C cb7 hC hcb hA hn0 hCl2 hCl3 hll hAr hH`. Establish `d1` using `data1 L`. Establish `d11 : SplitsE D (D.host.g 0)` using `hAr.2.1`. Establish `d13 : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2` using `hAr.2.2.2`. Take `⟨-, -, -, -, H5, -, H7, H8, -, -, H11, H12, H13, ContinuousCyclotomicCharacter₂, ContinuityOfCyclotomicCharacter, CyclotomicCharacterContinuous, -, -, H19, LocalHeightDeterminant, H21, -, -, -, -⟩` from `hH`.

Establish `hk5` using `Formalism.MainNotions.S.five_le_k (D := D)`. Establish `hf1` using `Formalism.MainNotions.S.one_le_f (D := D)`. Establish `hkr` using `Formalism.MainNotions.S.k_le_r (D := D)`. Establish `hm2 : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast D.R.two_le_m`. Establish `hL1` using `one_lt_scL L`.

Establish `hlogb` using `log_scb L`. Establish `hb2` using `two_le_scb L`. Establish `hb0 : 0 < L.sc.b` using `lt_of_lt_of_le two_pos hb2`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `swap`.

Establish `h5 : (4 : ℝ) * D.R.r < D.host.g 1` using `four_r_lt_g_of_bounds hk5 (by linarith only [hb2]) r_le_two_k ContinuousCyclotomicCharacter₂`. Conclude with `h5` after adjusting the coercions. Establish `hlr : 1 ≤ Real.log (D.R.r : ℝ)` using `one_le_log_of_five_le (le_trans hk5 hkr)`. Take `⟨hmsq, hLk, hClL⟩` from `k_ge_of_chain_bound hm2 hL1 hCl2 H7`. Establish `hrd2 : 2 ≤ D.host.rdE`.

Establish `h : D.host.v = D.host.rdE / 2` using `rfl`. Rewrite `H19` using `[h]`. Combine the linear relations using `only [H19]`. Establish `hlrd0 : 0 ≤ Real.log D.host.rdE` using `Real.log_nonneg (by linarith only [hrd2])`. Establish `hDel0 : 0 ≤ (D.s.Del : ℝ)` using `le_trans (Real.rpow_nonneg (by positivity) _) LocalHeightDeterminant`.

Establish `hm1 : 1 ≤ D.R.m` using `le_trans (by norm_num) D.R.two_le_m`. Establish `hb1nn : ∀ τ j, 1 ≤ j → j ≤ D.R.m → 0 ≤ bOne D τ j` using `fun τ j h1 h2 => le_trans (by positivity) (H8 τ j h1 h2)`. Establish `hbsq : ∀ τ j, 1 ≤ j → j ≤ D.R.m → bOne D τ j ≤ L.sc.b ^ 2` using `fun τ j h1 h2 => by`. Use `(CyclotomicCharacterContinuous τ j h1 h2).2` as an intermediate fact. Rewrite `this` using `[Real.rpow_two]`. Then use the resulting hypothesis.

Use `⟨d13, ?_, ?_, ?_, ?_, ?_, ?_, d11, ?_, ?_, hb2, ?_⟩` and prove the remaining obligations. Establish `h2 : n0 ≤ D.R.k` using `by exact_mod_cast hn0`. Establish `h3` using `D.R.two_le_m`. Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Use linear arithmetic over natural numbers and integers.

Establish `h1 : D.R.m ^ 2 ≤ D.R.k` using `by exact_mod_cast hmsq`. Establish `h2 : D.R.rS + 1 ≤ D.R.m`. Use `D.R.two_le_m` as an intermediate fact. Unfold `Ranks.rS`. Use linear arithmetic over natural numbers and integers.

Establish `h3 : (D.R.rS + 1) ^ 2 ≤ D.R.m ^ 2` using `Nat.pow_le_pow_left h2 2`. Establish `h4 : D.R.k ≤ D.R.r` using `by exact_mod_cast hkr`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `Real.log_le_self hlrd0`. Establish `h2 : L.sc.L / Cl ≤ L.sc.L` using `div_le_self (by linarith only [hL1]) (by linarith only [hCl2])`.

Combine the linear relations using `only [h1, h2, H11, hLk, hkr]`. Introduce `τ i`. Use `lamS_abs_le τ _ (fun l h1 h2 => ⟨(d1 τ l h1 h2).1, ?_⟩) (fun j h1 h2 => ⟨hb1nn τ j h1 h2, hbsq τ j h1 h2⟩) i` and prove the remaining obligations. Conclude with `le_of_le_four_mul_of_mul_le_chain (by linarith only [hk5]) hDel0 hCl2 hm2 (d1 τ l h1 h2).2 (H8 τ 1 le_rfl hm1) (hbsq τ 1 le_rfl hm1)`. Unfold `gg`.

Establish `h1 : (D.host.g 0 : ℝ) * D.host.g 1 ≤ L.sc.b ^ Cg * L.sc.b ^ Cg` using `mul_le_mul H13 ContinuityOfCyclotomicCharacter (by positivity) (by positivity)`. Rewrite `h1` using `[← Real.rpow_add hb0]`. Conclude with `le_trans h1 (Real.rpow_le_rpow_of_exponent_le (by linarith only [hb2]) (by linarith only [hA]))`. Establish `h5 : (4 : ℝ) * D.R.r < D.host.g 0` using `four_r_lt_g_of_bounds hk5 (by linarith only [hb2]) r_le_two_k H12`. Conclude with `h5` after adjusting the coercions.

Introduce `τ a c hac`. Establish `hX : 0 ≤ (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5` using `by positivity`. Establish `hle` using `gap_product_le_of_bounds hC hX hL1 hCl2 hCl3 H11`. Establish `hG0 : 0 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L` using `by positivity`. Establish `hg` using `gapAtLeast_of τ _ hG0 (fun l h1 h2 => (d1 τ l h1 h2).1) (hb1nn τ 1 le_rfl hm1) (H21 τ) a c hac`.

Rewrite using `[Real.log_mul hb0.ne' (by linarith only [hrd2]), hlogb]`. Combine the linear relations using `only [hle, hg]`. Use `le_trans H5 (Real.sqrt_le_sqrt ?_)` and prove the remaining obligations. Establish `: D.R.rS ≤ D.R.r`. Establish `h4` using `D.R.m_add_three_le_k`.

Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Unfold `Ranks.rS`. Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions. Rewrite using `[hlogb]`.

Establish `h1` using `mul_le_mul_of_nonneg_left (k_le_rank_product hk5 hkr hf1 hlr) hcb.le`. Combine the linear relations using `only [h1, hll]`.
-/
theorem countClauses_of_sizeHyp : ∀ (D : D7) (L : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (n0 : ℕ) (A C cb7 : ℝ),
    0 ≤ C → 0 < cb7 → 2 * Cg ≤ A → (n0 : ℝ) ≤ D.R.k → 2 ≤ Cl → 2 * C ≤ Cl →
    Real.log L.sc.L ≤ cb7 * D.R.k → ArithmeticConditionsOfDatum D → StandingHypotheses D L C' Cl Cg cb Cu cT CT →
    AdmissibleBoundsFromSource.CountTheoremHypotheses D L n0 A C cb7 ∧ 4 * D.R.r < D.host.g 1 := by
  intro D L C' Cl Cg cb Cu cT CT n0 A C cb7 hC hcb hA hn0 hCl2 hCl3 hll hAr hH
  have d1 := data1 L
  have d11 : SplitsE D (D.host.g 0) := hAr.2.1
  have d13 : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 := hAr.2.2.2
  obtain ⟨-, -, -, -, H5, -, H7, H8, -, -, H11, H12, H13, ContinuousCyclotomicCharacter₂, ContinuityOfCyclotomicCharacter, CyclotomicCharacterContinuous, -, -, H19, LocalHeightDeterminant, H21, -, -, -, -⟩ := hH
  have hk5 := Formalism.MainNotions.S.five_le_k (D := D)
  have hf1 := Formalism.MainNotions.S.one_le_f (D := D)
  have hkr := Formalism.MainNotions.S.k_le_r (D := D)
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hL1 := one_lt_scL L
  have hlogb := log_scb L
  have hb2 := two_le_scb L
  have hb0 : 0 < L.sc.b := lt_of_lt_of_le two_pos hb2
  refine ⟨?_, ?_⟩
  swap
  · have h5 : (4 : ℝ) * D.R.r < D.host.g 1 := four_r_lt_g_of_bounds hk5 (by linarith only [hb2]) r_le_two_k ContinuousCyclotomicCharacter₂
    exact_mod_cast h5
  have hlr : 1 ≤ Real.log (D.R.r : ℝ) := one_le_log_of_five_le (le_trans hk5 hkr)
  obtain ⟨hmsq, hLk, hClL⟩ := k_ge_of_chain_bound hm2 hL1 hCl2 H7
  have hrd2 : 2 ≤ D.host.rdE := by
    have h : D.host.v = D.host.rdE / 2 := rfl
    rw [h] at H19; linarith only [H19]
  have hlrd0 : 0 ≤ Real.log D.host.rdE := Real.log_nonneg (by linarith only [hrd2])
  have hDel0 : 0 ≤ (D.s.Del : ℝ) := le_trans (Real.rpow_nonneg (by positivity) _) LocalHeightDeterminant
  have hm1 : 1 ≤ D.R.m := le_trans (by norm_num) D.R.two_le_m
  have hb1nn : ∀ τ j, 1 ≤ j → j ≤ D.R.m → 0 ≤ bOne D τ j := fun τ j h1 h2 =>
    le_trans (by positivity) (H8 τ j h1 h2)
  have hbsq : ∀ τ j, 1 ≤ j → j ≤ D.R.m → bOne D τ j ≤ L.sc.b ^ 2 := fun τ j h1 h2 => by
    have := (CyclotomicCharacterContinuous τ j h1 h2).2
    rwa [Real.rpow_two] at this
  refine ⟨d13, ?_, ?_, ?_, ?_, ?_, ?_, d11, ?_, ?_, hb2, ?_⟩
  · have h2 : n0 ≤ D.R.k := by exact_mod_cast hn0
    have h3 := D.R.two_le_m
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  · have h1 : D.R.m ^ 2 ≤ D.R.k := by exact_mod_cast hmsq
    have h2 : D.R.rS + 1 ≤ D.R.m := by
      have := D.R.two_le_m
      unfold Ranks.rS; omega
    have h3 : (D.R.rS + 1) ^ 2 ≤ D.R.m ^ 2 := Nat.pow_le_pow_left h2 2
    have h4 : D.R.k ≤ D.R.r := by exact_mod_cast hkr
    omega
  · have h1 := Real.log_le_self hlrd0
    have h2 : L.sc.L / Cl ≤ L.sc.L := div_le_self (by linarith only [hL1]) (by linarith only [hCl2])
    linarith only [h1, h2, H11, hLk, hkr]
  · intro τ i
    refine lamS_abs_le τ _ (fun l h1 h2 => ⟨(d1 τ l h1 h2).1, ?_⟩) (fun j h1 h2 => ⟨hb1nn τ j h1 h2, hbsq τ j h1 h2⟩) i
    exact le_of_le_four_mul_of_mul_le_chain (by linarith only [hk5]) hDel0 hCl2 hm2 (d1 τ l h1 h2).2 (H8 τ 1 le_rfl hm1) (hbsq τ 1 le_rfl hm1)
  · unfold gg
    have h1 : (D.host.g 0 : ℝ) * D.host.g 1 ≤ L.sc.b ^ Cg * L.sc.b ^ Cg :=
      mul_le_mul H13 ContinuityOfCyclotomicCharacter (by positivity) (by positivity)
    rw [← Real.rpow_add hb0] at h1
    exact le_trans h1 (Real.rpow_le_rpow_of_exponent_le (by linarith only [hb2]) (by linarith only [hA]))
  · have h5 : (4 : ℝ) * D.R.r < D.host.g 0 := four_r_lt_g_of_bounds hk5 (by linarith only [hb2]) r_le_two_k H12
    exact_mod_cast h5
  · intro τ a c hac
    have hX : 0 ≤ (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 := by positivity
    have hle := gap_product_le_of_bounds hC hX hL1 hCl2 hCl3 H11
    have hG0 : 0 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L := by positivity
    have hg := gapAtLeast_of τ _ hG0 (fun l h1 h2 => (d1 τ l h1 h2).1) (hb1nn τ 1 le_rfl hm1) (H21 τ) a c hac
    rw [Real.log_mul hb0.ne' (by linarith only [hrd2]), hlogb]
    linarith only [hle, hg]
  · refine le_trans H5 (Real.sqrt_le_sqrt ?_)
    have : D.R.rS ≤ D.R.r := by
      have h4 := D.R.m_add_three_le_k
      have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
      unfold Ranks.rS; omega
    exact_mod_cast this
  · rw [hlogb]
    have h1 := mul_le_mul_of_nonneg_left (k_le_rank_product hk5 hkr hf1 hlr) hcb.le
    linarith only [h1, hll]

end GlobalTheory
