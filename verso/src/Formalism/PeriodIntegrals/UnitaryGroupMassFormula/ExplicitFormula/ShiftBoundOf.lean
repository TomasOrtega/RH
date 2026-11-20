import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LogDerivBounds

noncomputable section

namespace PI.EF

open Complex DirichletCharacter

/- English proof (translation)
Introduce `N _ χ hχ u T T' hT hTu hTT' hT'T hg`. Establish `hN1 : (1 : ℝ) ≤ N` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)`. Establish `hu2 : (2 : ℝ) ≤ u` using `hT.trans hTu`. Establish `hT'2 : (2 : ℝ) ≤ T'` using `hT.trans hTT'`. Establish `hT0 : (0 : ℝ) < T` using `by linarith`.

Establish `hlogNT : 0 < Real.log (N * T')` using `Real.log_pos (by nlinarith)`. Establish `hNO : NoOrdinate χ T'`. Introduce `ρ h1 h2 h3 heq`. Establish `h4` using `hg ρ h1 h2 h3`. Rewrite `h4` using `[heq, sub_self, abs_zero]`.

Establish `h5 : 0 < 1 / (κ * Real.log (N * T'))` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogu : 0 < Real.log u` using `Real.log_pos (by linarith)`. Establish `hx1 : 1 < cLine u`. Unfold `cLine`.

Use `one_div_pos.mpr hlogu` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨H, hH⟩` from `hRP N χ hχ (cLine u) T' hx1 (by linarith) hNO`. Establish `hCIe` using `hCI N χ hχ u T' H hu2 hT'2 hNO hH`. Establish `hSe` using `hS N χ hχ u T T' hT hTu hTT' hT'T hg`.

Establish `hRe` using `hR N χ hχ (cLine u) T' H hx1 hT'2 hH`. Use `set R := rectInt (fun s => logDeriv (DirichletCharacter.LFunction χ) s * ((u : ℂ) ^ s / s)) (-1 / 2) (cLine u) (-T') T' with hRdef`. Use `set Z := ∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ with hZ`. Use `set c : ℂ := 2 * Real.pi * I with hc`. Establish `hc0 : c ≠ 0`.

Rewrite using `[hc]`. Conclude with `mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero`. Establish `hcn : ‖c‖ = 2 * Real.pi`. Rewrite using `[hc, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]`. Evaluate the numerical expressions.

Establish `hA : vertInt χ u T' - del1 χ * u + zsum χ T' u = (R + c * vertInt χ u T') / c + (Z - H 0) - eps0 χ * (Real.log u : ℂ) - del1 χ`. Rewrite using `[hCIe]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hA]`.

Establish `hE1 : ‖eps0 χ‖ ≤ 1`. Unfold `eps0`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hD1 : ‖del1 χ‖ ≤ 1`. Unfold `del1`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hS1 : 0 ≤ S1 χ`. Unfold `S1`. Conclude with `finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity`. Establish `hNu : Real.log u ≤ Real.log (N * u)` using `Real.log_le_log (by positivity) (by nlinarith)`.

Establish `h2N : Real.log (2 * N) ≤ Real.log (N * u)` using `Real.log_le_log (by positivity) (by nlinarith)`. Establish `hL : 1 ≤ u * Real.log (N * u * T) ^ 2 / T`. Establish `h4 : (4 : ℝ) ≤ N * u * T`. Combine the equalities or inequalities in the displayed calculation. Establish `hl4 : 1 ≤ Real.log (N * u * T)`.

Establish `h5 : Real.log 4 ≤ Real.log (N * u * T)` using `Real.log_le_log (by norm_num) h4`. Establish `h6 : 1 < Real.log 4`. Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]`. Use `push_cast`. Combine the linear relations using `[Real.log_two_gt_d9]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsq : 1 ≤ Real.log (N * u * T) ^ 2` using `by nlinarith`. Rewrite using `[le_div_iff₀ hT0]`. Use polynomial arithmetic with `[mul_le_mul hTu hsq (by norm_num) (by linarith)]`. Establish `hlogNu : 0 ≤ Real.log (N * u)` using `by linarith`.

Establish `hErr1 : 1 ≤ Err N u T` using `by unfold Err; linarith`. Establish `hErr2 : Real.log u ≤ Err N u T` using `by unfold Err; linarith`. Establish `hErr3 : Real.log (2 * N) ≤ Err N u T` using `by unfold Err; linarith`. Establish `hmain : ‖(R + c * vertInt χ u T') / c‖ ≤ Cs * Err N u T`. Rewrite using `[norm_div, hcn, div_le_iff₀ (by positivity)]`.

Combine the equalities or inequalities in the displayed calculation. Establish `heps : ‖eps0 χ * (Real.log u : ℂ)‖ ≤ Real.log u`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogu]`. Conclude with `mul_le_of_le_one_left hlogu.le hE1`. Combine the equalities or inequalities in the displayed calculation.

Use `(norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)` and prove the remaining obligations. Use `_ ≤ Cs * Err N u T + (Cr * Real.log (2 * N) + S1 χ) + Real.log u + 1 := by gcongr`. Use `_ ≤ (Cs + Cr + 3) * (Err N u T + S1 χ) := by`. Use polynomial arithmetic with `[mul_nonneg hCs hS1, mul_nonneg hCr hS1, mul_le_mul_of_nonneg_left hErr3 hCr]`.
-/
theorem shiftBound_of {κ Cs Cr : ℝ} (hκ : 0 < κ) (hCs : 0 ≤ Cs) (hCr : 0 ≤ Cr) (hRP : RegularPart)
    (hCI : ContourIdentity) (hS : SidesBound κ Cs) (hR : RegAtZero Cr) :
    ShiftBound κ (Cs + Cr + 3) := by
  intro N _ χ hχ u T T' hT hTu hTT' hT'T hg
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hu2 : (2 : ℝ) ≤ u := hT.trans hTu
  have hT'2 : (2 : ℝ) ≤ T' := hT.trans hTT'
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogNT : 0 < Real.log (N * T') := Real.log_pos (by nlinarith)
  have hNO : NoOrdinate χ T' := by
    intro ρ h1 h2 h3 heq
    have h4 := hg ρ h1 h2 h3
    rw [heq, sub_self, abs_zero] at h4
    have h5 : 0 < 1 / (κ * Real.log (N * T')) := by positivity
    linarith
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
  have hx1 : 1 < cLine u := by
    unfold cLine
    have := one_div_pos.mpr hlogu
    linarith
  obtain ⟨H, hH⟩ := hRP N χ hχ (cLine u) T' hx1 (by linarith) hNO
  have hCIe := hCI N χ hχ u T' H hu2 hT'2 hNO hH
  have hSe := hS N χ hχ u T T' hT hTu hTT' hT'T hg
  have hRe := hR N χ hχ (cLine u) T' H hx1 hT'2 hH
  set R := rectInt (fun s => logDeriv (DirichletCharacter.LFunction χ) s * ((u : ℂ) ^ s / s))
    (-1 / 2) (cLine u) (-T') T' with hRdef
  set Z := ∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ with hZ
  set c : ℂ := 2 * Real.pi * I with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hcn : ‖c‖ = 2 * Real.pi := by
    rw [hc, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  have hA : vertInt χ u T' - del1 χ * u + zsum χ T' u =
      (R + c * vertInt χ u T') / c + (Z - H 0) - eps0 χ * (Real.log u : ℂ) - del1 χ := by
    rw [hCIe]
    field_simp
    ring
  rw [hA]
  have hE1 : ‖eps0 χ‖ ≤ 1 := by
    unfold eps0
    split_ifs <;> simp
  have hD1 : ‖del1 χ‖ ≤ 1 := by
    unfold del1
    split_ifs <;> simp
  have hS1 : 0 ≤ S1 χ := by
    unfold S1
    exact finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity
  have hNu : Real.log u ≤ Real.log (N * u) := Real.log_le_log (by positivity) (by nlinarith)
  have h2N : Real.log (2 * N) ≤ Real.log (N * u) := Real.log_le_log (by positivity) (by nlinarith)
  have hL : 1 ≤ u * Real.log (N * u * T) ^ 2 / T := by
    have h4 : (4 : ℝ) ≤ N * u * T := by
      calc (4 : ℝ) = 1 * 2 * 2 := by norm_num
        _ ≤ N * u * T := mul_le_mul (mul_le_mul hN1 hu2 (by norm_num) (by linarith)) hT (by norm_num)
          (by positivity)
    have hl4 : 1 ≤ Real.log (N * u * T) := by
      have h5 : Real.log 4 ≤ Real.log (N * u * T) := Real.log_le_log (by norm_num) h4
      have h6 : 1 < Real.log 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        linarith [Real.log_two_gt_d9]
      linarith
    have hsq : 1 ≤ Real.log (N * u * T) ^ 2 := by nlinarith
    rw [le_div_iff₀ hT0]
    nlinarith [mul_le_mul hTu hsq (by norm_num) (by linarith)]
  have hlogNu : 0 ≤ Real.log (N * u) := by linarith
  have hErr1 : 1 ≤ Err N u T := by unfold Err; linarith
  have hErr2 : Real.log u ≤ Err N u T := by unfold Err; linarith
  have hErr3 : Real.log (2 * N) ≤ Err N u T := by unfold Err; linarith
  have hmain : ‖(R + c * vertInt χ u T') / c‖ ≤ Cs * Err N u T := by
    rw [norm_div, hcn, div_le_iff₀ (by positivity)]
    calc ‖R + c * vertInt χ u T'‖ ≤ Cs * Err N u T := hSe
      _ ≤ Cs * Err N u T * (2 * Real.pi) :=
        le_mul_of_one_le_right (by positivity) (by linarith [Real.pi_gt_three])
  have heps : ‖eps0 χ * (Real.log u : ℂ)‖ ≤ Real.log u := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogu]
    exact mul_le_of_le_one_left hlogu.le hE1
  calc ‖(R + c * vertInt χ u T') / c + (Z - H 0) - eps0 χ * (Real.log u : ℂ) - del1 χ‖
      ≤ ‖(R + c * vertInt χ u T') / c‖ + ‖Z - H 0‖ + ‖eps0 χ * (Real.log u : ℂ)‖ + ‖del1 χ‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ Cs * Err N u T + (Cr * Real.log (2 * N) + S1 χ) + Real.log u + 1 := by
        gcongr
    _ ≤ (Cs + Cr + 3) * (Err N u T + S1 χ) := by
        nlinarith [mul_nonneg hCs hS1, mul_nonneg hCr hS1, mul_le_mul_of_nonneg_left hErr3 hCr]

end PI.EF
