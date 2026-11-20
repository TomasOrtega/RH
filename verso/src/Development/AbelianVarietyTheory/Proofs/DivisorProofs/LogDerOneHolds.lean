import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivLFunctionStrip

noncomputable section

open Complex DirichletCharacter

namespace GlobalTheory.LogDerOneProof

/- English proof (translation)
Take `⟨C, hC, H⟩` from `GlobalTheory.LWide.logDeriv_LFunction_strip`. Use `⟨2 * C, fun q _ χ hq hp => ?_⟩` and prove the remaining obligations. Establish `hne : χ ≠ 1`. Introduce `h`. Establish `h1 : χ.conductor = q` using `hp`.

Rewrite `h1` using `[h, DirichletCharacter.conductor_one]`. Use linear arithmetic over natural numbers and integers. Establish `hL : LFunction χ 1 ≠ 0` using `LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by simp)`. Take `⟨hfin, hcount, hmain⟩` from `H q χ hne 1 (by norm_num) (by norm_num) hL`. Simplify using `only [Complex.one_im, abs_zero, zero_add, Complex.ofReal_zero, zero_mul, add_zero] at hfin hcount hmain`.

Use `set D : Set ℂ := {w : ℂ | ‖w - 2‖ ≤ 7 / 2 ∧ LFunction χ w = 0} with hD`. Use `set Z : Set ℂ := GlobalTheory.Mem.An.zerosIn χ 0 1 with hZ`. Establish `hsub : Z ⊆ D`. Introduce and unpack `w ⟨h0, h1, h2, h3⟩`. Use `⟨?_, h3⟩` and prove the remaining obligations.

Establish `h4` using `Complex.norm_le_abs_re_add_abs_im (w - 2)`. Simplify using `only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat, sub_zero] at h4 h2`. Establish `h5 : |w.re - 2| ≤ 2` using `abs_le.2 ⟨by linarith, by linarith⟩`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hZfin : Z.Finite` using `hfin.subset hsub`.

Establish `hsub' : hZfin.toFinset ⊆ hfin.toFinset`. Introduce `w hw`. Simplify using `only [Set.Finite.mem_toFinset] at hw ⊢`. Conclude with `hsub hw`. Rewrite `hcount`, `hmain` using `[finsum_mem_eq_finite_toFinset_sum _ hfin]`.

Establish `hz : GlobalTheory.Mem.An.zsum χ 0 1 (fun ρ => 1 / (1 - ρ)) = ∑ w ∈ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)`. Unfold `GlobalTheory.Mem.An.zsum`. Rewrite using `[← hZ, finsum_mem_eq_finite_toFinset_sum _ hZfin]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `only [GlobalTheory.Mem.An.zmult]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hz]`. Rewrite `hmain` using `[← Finset.sum_sdiff hsub']`. Establish `hrest : ‖∑ w ∈ hfin.toFinset \ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)‖ ≤ ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℝ)`. Use `(norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun w hw => ?_) (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => Nat.cast_nonneg _))` and prove the remaining obligations.

Simplify using `only [Finset.mem_sdiff, Set.Finite.mem_toFinset] at hw`. Take `⟨⟨_, hw0⟩, hwn⟩` from `hw`. Establish `hre : w.re < 1`. Assume the negation of the conclusion as `h`. Conclude with `LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (not_lt.1 h) hw0`.

Establish `h1 : 1 ≤ ‖1 - w‖`. Distinguish the cases in `h0 : 0 < w.re`. Establish `him : 1 < |w.im|`. Assume the negation of the conclusion as `h`. Conclude with `hwn ⟨h0, hre, by simpa using not_lt.1 h, hw0⟩`.

Establish `h4` using `Complex.abs_im_le_norm (1 - w)`. Simplify using `only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h4`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4` using `Complex.re_le_norm (1 - w)`. Simplify using `only [Complex.sub_re, Complex.one_re] at h4`.

Combine the linear relations using `[not_lt.1 h0]`. Rewrite using `[norm_div, Complex.norm_natCast]`. Conclude with `div_le_self (Nat.cast_nonneg _) h1`. Establish `hq' : (1 : ℝ) < q` using `by exact_mod_cast hq`. Establish `hlog : Real.log (q * 2) ≤ Real.log (3 * q)` using `Real.log_le_log (by linarith) (by linarith)`.

Establish `hl2 : C * Real.log (q * 2) ≤ C * Real.log (3 * q)` using `mul_le_mul_of_nonneg_left hlog hC.le`. Use `set A := deriv (LFunction χ) 1 / LFunction χ 1`. Use `set R := ∑ w ∈ hfin.toFinset \ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)`. Use `set S := ∑ w ∈ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)`. Establish `e : A - S = (A - (R + S)) + R` using `by ring`.

Rewrite using `[e]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem logDerOne_holds : GlobalTheory.Mem.An.LogDerOne := by
  classical
  obtain ⟨C, hC, H⟩ := GlobalTheory.LWide.logDeriv_LFunction_strip
  refine ⟨2 * C, fun q _ χ hq hp => ?_⟩
  have hne : χ ≠ 1 := by
    intro h
    have h1 : χ.conductor = q := hp
    rw [h, DirichletCharacter.conductor_one] at h1
    omega
  have hL : LFunction χ 1 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by simp)
  obtain ⟨hfin, hcount, hmain⟩ := H q χ hne 1 (by norm_num) (by norm_num) hL
  simp only [Complex.one_im, abs_zero, zero_add, Complex.ofReal_zero, zero_mul, add_zero] at hfin hcount hmain
  set D : Set ℂ := {w : ℂ | ‖w - 2‖ ≤ 7 / 2 ∧ LFunction χ w = 0} with hD
  set Z : Set ℂ := GlobalTheory.Mem.An.zerosIn χ 0 1 with hZ
  have hsub : Z ⊆ D := by
    rintro w ⟨h0, h1, h2, h3⟩
    refine ⟨?_, h3⟩
    have h4 := Complex.norm_le_abs_re_add_abs_im (w - 2)
    simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat, sub_zero] at h4 h2
    have h5 : |w.re - 2| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hZfin : Z.Finite := hfin.subset hsub
  have hsub' : hZfin.toFinset ⊆ hfin.toFinset := by
    intro w hw
    simp only [Set.Finite.mem_toFinset] at hw ⊢
    exact hsub hw
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hcount hmain
  have hz : GlobalTheory.Mem.An.zsum χ 0 1 (fun ρ => 1 / (1 - ρ)) =
      ∑ w ∈ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w) := by
    unfold GlobalTheory.Mem.An.zsum
    rw [← hZ, finsum_mem_eq_finite_toFinset_sum _ hZfin]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [GlobalTheory.Mem.An.zmult]
    ring
  rw [hz]
  rw [← Finset.sum_sdiff hsub'] at hmain
  have hrest : ‖∑ w ∈ hfin.toFinset \ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)‖ ≤
      ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℝ) := by
    refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun w hw => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => Nat.cast_nonneg _))
    simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset] at hw
    obtain ⟨⟨_, hw0⟩, hwn⟩ := hw
    have hre : w.re < 1 := by
      by_contra h
      exact LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (not_lt.1 h) hw0
    have h1 : 1 ≤ ‖1 - w‖ := by
      by_cases h0 : 0 < w.re
      · have him : 1 < |w.im| := by
          by_contra h
          exact hwn ⟨h0, hre, by simpa using not_lt.1 h, hw0⟩
        have h4 := Complex.abs_im_le_norm (1 - w)
        simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h4
        linarith
      · have h4 := Complex.re_le_norm (1 - w)
        simp only [Complex.sub_re, Complex.one_re] at h4
        linarith [not_lt.1 h0]
    rw [norm_div, Complex.norm_natCast]
    exact div_le_self (Nat.cast_nonneg _) h1
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have hlog : Real.log (q * 2) ≤ Real.log (3 * q) := Real.log_le_log (by linarith) (by linarith)
  have hl2 : C * Real.log (q * 2) ≤ C * Real.log (3 * q) := mul_le_mul_of_nonneg_left hlog hC.le
  set A := deriv (LFunction χ) 1 / LFunction χ 1
  set R := ∑ w ∈ hfin.toFinset \ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)
  set S := ∑ w ∈ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)
  have e : A - S = (A - (R + S)) + R := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  linarith

end GlobalTheory.LogDerOneProof
