import Mathlib

namespace GlobalTheory.CompanionTheory.ExplChi

open Complex DirichletCharacter

/- English proof (translation)
Establish `hΓ : Gamma (z / 2) ≠ 0` using `Gamma_ne_zero hz`. Establish `hd : DifferentiableAt ℂ Gamma (z / 2)` using `differentiableAt_Gamma _ hz`. Establish `h1 : HasDerivAt (fun w : ℂ => Gamma (w / 2)) (deriv Gamma (z / 2) * (1 / 2)) z` using `hd.hasDerivAt.comp z ((hasDerivAt_id z).div_const 2)`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `h2 : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) ((Real.pi : ℂ) ^ (-z / 2) * Complex.log Real.pi * (-1 / 2)) z` using `((hasDerivAt_id z).neg.div_const 2).const_cpow (Or.inl hpi)`.

Establish `h3` using `h2.mul h1`. Establish `hfun : Gammaℝ = fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Gamma (w / 2)`. Use function extensionality and compare the values at `w`. Rewrite using `[Gammaℝ_def]`. Establish `hval : Gammaℝ z * (-(Real.log Real.pi : ℂ) / 2 + digamma (z / 2) / 2) = (Real.pi : ℂ) ^ (-z / 2) * Complex.log Real.pi * (-1 / 2) * Gamma (z / 2) + (Real.pi : ℂ) ^ (-z / 2) * (deriv Gamma (z / 2) * (1 / 2))`.

Rewrite using `[Gammaℝ_def, digamma_def, logDeriv_apply, Complex.ofReal_log Real.pi_pos.le]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hval, hfun]`. Conclude with `h3`.
-/
theorem hasDerivAt_Gammaℝ_of_ne {z : ℂ} (hz : ∀ n : ℕ, z / 2 ≠ -(n : ℂ)) :
    HasDerivAt Gammaℝ
      (Gammaℝ z * (-(Real.log Real.pi : ℂ) / 2 + digamma (z / 2) / 2)) z := by
  have hΓ : Gamma (z / 2) ≠ 0 := Gamma_ne_zero hz
  have hd : DifferentiableAt ℂ Gamma (z / 2) := differentiableAt_Gamma _ hz
  have h1 : HasDerivAt (fun w : ℂ => Gamma (w / 2)) (deriv Gamma (z / 2) * (1 / 2)) z :=
    hd.hasDerivAt.comp z ((hasDerivAt_id z).div_const 2)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
      ((Real.pi : ℂ) ^ (-z / 2) * Complex.log Real.pi * (-1 / 2)) z :=
    ((hasDerivAt_id z).neg.div_const 2).const_cpow (Or.inl hpi)
  have h3 := h2.mul h1
  have hfun : Gammaℝ = fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Gamma (w / 2) := by
    funext w; rw [Gammaℝ_def]
  have hval : Gammaℝ z * (-(Real.log Real.pi : ℂ) / 2 + digamma (z / 2) / 2) =
      (Real.pi : ℂ) ^ (-z / 2) * Complex.log Real.pi * (-1 / 2) * Gamma (z / 2) +
        (Real.pi : ℂ) ^ (-z / 2) * (deriv Gamma (z / 2) * (1 / 2)) := by
    rw [Gammaℝ_def, digamma_def, logDeriv_apply, Complex.ofReal_log Real.pi_pos.le]
    field_simp
  rw [hval, hfun]
  exact h3

/- English proof (translation)
Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Rewrite using `[Gammaℝ_def]`. Conclude with `mul_ne_zero (by rw [Ne, cpow_eq_zero_iff]; exact fun h => hpi h.1) (Gamma_ne_zero hz)`.
-/
theorem Gammaℝ_ne_zero_of_ne {z : ℂ} (hz : ∀ n : ℕ, z / 2 ≠ -(n : ℂ)) : Gammaℝ z ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Gammaℝ_def]
  exact mul_ne_zero (by rw [Ne, cpow_eq_zero_iff]; exact fun h => hpi h.1) (Gamma_ne_zero hz)

/- English proof (translation)
Establish `hgf : ∀ w, gammaFactor χ w = Gammaℝ (w + a)`. Introduce `w`. Break down `ha with ⟨he, rfl⟩ | ⟨ho, rfl⟩` into its components or cases. Rewrite using `[he.gammaFactor_def, add_zero]`. Rewrite using `[ho.gammaFactor_def]`.

Establish `hG : HasDerivAt (fun w : ℂ => Gammaℝ (w + a)) _ z` using `(hasDerivAt_Gammaℝ_of_ne hz).comp_add_const z a`. Establish `hGne : Gammaℝ (z + a) ≠ 0` using `Gammaℝ_ne_zero_of_ne hz`. Establish `hprod : ∀ w, Gammaℝ (w + a) ≠ 0 → completedLFunction χ w = Gammaℝ (w + a) * LFunction χ w`. Introduce `w hw`. Establish `h` using `LFunction_eq_completed_div_gammaFactor χ w (Or.inr hN)`.

Rewrite `h` using `[hgf]`. Rewrite using `[h]`. Clear the denominators using the available nonvanishing facts. Establish `hev : completedLFunction χ =ᶠ[nhds z] fun w => Gammaℝ (w + a) * LFunction χ w` using `by filter_upwards [hG.continuousAt.eventually_ne hGne] with w hw using hprod w hw`. Establish `hder : HasDerivAt (fun w => Gammaℝ (w + a) * LFunction χ w) _ z` using `hG.mul (differentiable_LFunction hχ z).hasDerivAt`.

Establish `hne : completedLFunction χ z ≠ 0`. Rewrite using `[hprod z hGne]`. Conclude with `mul_ne_zero hGne hL`. Use `⟨hne, ?_⟩` and prove the remaining obligations. Rewrite using `[hev.deriv_eq, hder.deriv, hprod z hGne]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem completed_logDeriv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hN : N ≠ 1)
    (hχ : χ ≠ 1) {a : ℂ} (ha : χ.Even ∧ a = 0 ∨ χ.Odd ∧ a = 1) {z : ℂ}
    (hz : ∀ n : ℕ, (z + a) / 2 ≠ -(n : ℂ)) (hL : LFunction χ z ≠ 0) :
    completedLFunction χ z ≠ 0 ∧
      deriv (completedLFunction χ) z / completedLFunction χ z =
        -(Real.log Real.pi : ℂ) / 2 + digamma ((z + a) / 2) / 2 +
          deriv (LFunction χ) z / LFunction χ z := by
  have hgf : ∀ w, gammaFactor χ w = Gammaℝ (w + a) := by
    intro w
    rcases ha with ⟨he, rfl⟩ | ⟨ho, rfl⟩
    · rw [he.gammaFactor_def, add_zero]
    · rw [ho.gammaFactor_def]
  have hG : HasDerivAt (fun w : ℂ => Gammaℝ (w + a)) _ z :=
    (hasDerivAt_Gammaℝ_of_ne hz).comp_add_const z a
  have hGne : Gammaℝ (z + a) ≠ 0 := Gammaℝ_ne_zero_of_ne hz
  have hprod : ∀ w, Gammaℝ (w + a) ≠ 0 →
      completedLFunction χ w = Gammaℝ (w + a) * LFunction χ w := by
    intro w hw
    have h := LFunction_eq_completed_div_gammaFactor χ w (Or.inr hN)
    rw [hgf] at h
    rw [h]
    field_simp
  have hev : completedLFunction χ =ᶠ[nhds z] fun w => Gammaℝ (w + a) * LFunction χ w := by
    filter_upwards [hG.continuousAt.eventually_ne hGne] with w hw using hprod w hw
  have hder : HasDerivAt (fun w => Gammaℝ (w + a) * LFunction χ w) _ z :=
    hG.mul (differentiable_LFunction hχ z).hasDerivAt
  have hne : completedLFunction χ z ≠ 0 := by
    rw [hprod z hGne]; exact mul_ne_zero hGne hL
  refine ⟨hne, ?_⟩
  rw [hev.deriv_eq, hder.deriv, hprod z hGne]
  field_simp

/- English proof (translation)
Introduce `N _ χ hN hp a ha s hs1 hs2 hL1 hL2`. Establish `hN1 : N ≠ 1` using `hN.ne'`. Establish `hχ : χ ≠ 1`. Introduce and unpack `rfl`. Rewrite `hp` using `[isPrimitive_def, conductor_one]`.

Conclude with `hN1 hp.symm`. Establish `hχi : χ⁻¹ ≠ 1` using `inv_ne_one.mpr hχ`. Establish `ha' : χ⁻¹.Even ∧ a = 0 ∨ χ⁻¹.Odd ∧ a = 1`. Break down `ha with ⟨he, h⟩ | ⟨ho, h⟩` into its components or cases. Use `Or.inl ⟨?_, h⟩` and prove the remaining obligations.

Rewrite using `[DirichletCharacter.Even, MulChar.inv_apply_eq_inv', he, inv_one]`. Use `Or.inr ⟨?_, h⟩` and prove the remaining obligations. Rewrite using `[DirichletCharacter.Odd, MulChar.inv_apply_eq_inv', ho]`. Evaluate the numerical expressions. Take `⟨A0, eA⟩` from `completed_logDeriv χ hN1 hχ ha hs1 hL1`.

Take `⟨B0, eB⟩` from `completed_logDeriv χ⁻¹ hN1 hχi ha' hs2 hL2`. Establish `hN0 : (N : ℂ) ≠ 0` using `by exact_mod_cast NeZero.ne N`. Use `set W := rootNumber χ with hW`. Establish `hfe : ∀ w, completedLFunction χ w = (N : ℂ) ^ ((1 : ℂ) / 2 - w) * W * completedLFunction χ⁻¹ (1 - w)`. Introduce `w`.

Establish `h` using `hp.completedLFunction_one_sub (1 - w)`. Rewrite `h` using `[sub_sub_cancel]`. Rewrite using `[h]`. Use `congr 3`. Expand and normalize the polynomial expressions, which then agree.

Establish `hc : HasDerivAt (fun w : ℂ => (N : ℂ) ^ ((1 : ℂ) / 2 - w)) ((N : ℂ) ^ ((1 : ℂ) / 2 - s) * Complex.log N * (-1)) s` using `((hasDerivAt_id s).const_sub ((1 : ℂ) / 2)).const_cpow (Or.inl hN0)`. Establish `hB : HasDerivAt (fun w : ℂ => completedLFunction χ⁻¹ (1 - w)) (-deriv (completedLFunction χ⁻¹) (1 - s)) s` using `((differentiable_completedLFunction hχi (1 - s)).hasDerivAt).comp_const_sub 1 s`. Establish `hT` using `(hc.mul_const W).mul hB`. Establish `hD : deriv (completedLFunction χ) s = (N : ℂ) ^ ((1 : ℂ) / 2 - s) * Complex.log N * (-1) * W * completedLFunction χ⁻¹ (1 - s) + (N : ℂ) ^ ((1 : ℂ) / 2 - s) * W * (-deriv (completedLFunction χ⁻¹) (1 - s))`. Rewrite using `[funext hfe]`.

Conclude with `hT.deriv`. Establish `hA : completedLFunction χ s = (N : ℂ) ^ ((1 : ℂ) / 2 - s) * W * completedLFunction χ⁻¹ (1 - s)` using `hfe s`. Establish `hcW : (N : ℂ) ^ ((1 : ℂ) / 2 - s) * W ≠ 0`. Introduce `h`. Rewrite `hA` using `[h, zero_mul]`.

Conclude with `A0 hA`. Establish `hlog : deriv (completedLFunction χ) s / completedLFunction χ s = -Complex.log N - deriv (completedLFunction χ⁻¹) (1 - s) / completedLFunction χ⁻¹ (1 - s)`. Establish `hBB : completedLFunction χ⁻¹ (1 - s) * (deriv (completedLFunction χ⁻¹) (1 - s) / completedLFunction χ⁻¹ (1 - s)) = deriv (completedLFunction χ⁻¹) (1 - s)` using `mul_div_cancel₀ _ B0`. Rewrite using `[hD, hA, div_eq_iff (mul_ne_zero hcW B0)]`. Take the linear combination `((N : ℂ) ^ ((1 : ℂ) / 2 - s) * W) * hBB`.

Establish `hNpos : (0 : ℝ) < N` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)`. Establish `l1 : ((Real.log (N / Real.pi) : ℝ) : ℂ) = Complex.log N - (Real.log Real.pi : ℂ)`. Rewrite using `[Real.log_div hNpos.ne' Real.pi_ne_zero, ofReal_sub, Complex.ofReal_log hNpos.le, ofReal_natCast]`. Rewrite `hlog` using `[eA, eB]`. Rewrite using `[l1]`.

Take the linear combination `hlog`.
-/
theorem logDeriv_LFunction_functional_equation :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), 1 < N → χ.IsPrimitive →
      ∀ a : ℂ, (χ.Even ∧ a = 0 ∨ χ.Odd ∧ a = 1) → ∀ s : ℂ,
        (∀ n : ℕ, (s + a) / 2 ≠ -(n : ℂ)) → (∀ n : ℕ, (1 - s + a) / 2 ≠ -(n : ℂ)) →
        DirichletCharacter.LFunction χ s ≠ 0 →
        DirichletCharacter.LFunction χ⁻¹ (1 - s) ≠ 0 →
        deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
          -((Real.log (N / Real.pi) : ℝ) : ℂ) - Complex.digamma ((1 - s + a) / 2) / 2 -
            Complex.digamma ((s + a) / 2) / 2 -
            deriv (DirichletCharacter.LFunction χ⁻¹) (1 - s) /
              DirichletCharacter.LFunction χ⁻¹ (1 - s) := by
  intro N _ χ hN hp a ha s hs1 hs2 hL1 hL2
  have hN1 : N ≠ 1 := hN.ne'
  have hχ : χ ≠ 1 := by
    rintro rfl
    rw [isPrimitive_def, conductor_one] at hp
    exact hN1 hp.symm
  have hχi : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  have ha' : χ⁻¹.Even ∧ a = 0 ∨ χ⁻¹.Odd ∧ a = 1 := by
    rcases ha with ⟨he, h⟩ | ⟨ho, h⟩
    · refine Or.inl ⟨?_, h⟩
      rw [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', he, inv_one]
    · refine Or.inr ⟨?_, h⟩
      rw [DirichletCharacter.Odd, MulChar.inv_apply_eq_inv', ho]
      norm_num
  obtain ⟨A0, eA⟩ := completed_logDeriv χ hN1 hχ ha hs1 hL1
  obtain ⟨B0, eB⟩ := completed_logDeriv χ⁻¹ hN1 hχi ha' hs2 hL2
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  set W := rootNumber χ with hW
  have hfe : ∀ w, completedLFunction χ w =
      (N : ℂ) ^ ((1 : ℂ) / 2 - w) * W * completedLFunction χ⁻¹ (1 - w) := by
    intro w
    have h := hp.completedLFunction_one_sub (1 - w)
    rw [sub_sub_cancel] at h
    rw [h]
    congr 3
    ring
  have hc : HasDerivAt (fun w : ℂ => (N : ℂ) ^ ((1 : ℂ) / 2 - w))
      ((N : ℂ) ^ ((1 : ℂ) / 2 - s) * Complex.log N * (-1)) s :=
    ((hasDerivAt_id s).const_sub ((1 : ℂ) / 2)).const_cpow (Or.inl hN0)
  have hB : HasDerivAt (fun w : ℂ => completedLFunction χ⁻¹ (1 - w))
      (-deriv (completedLFunction χ⁻¹) (1 - s)) s :=
    ((differentiable_completedLFunction hχi (1 - s)).hasDerivAt).comp_const_sub 1 s
  have hT := (hc.mul_const W).mul hB
  have hD : deriv (completedLFunction χ) s =
      (N : ℂ) ^ ((1 : ℂ) / 2 - s) * Complex.log N * (-1) * W * completedLFunction χ⁻¹ (1 - s) +
        (N : ℂ) ^ ((1 : ℂ) / 2 - s) * W * (-deriv (completedLFunction χ⁻¹) (1 - s)) := by
    rw [funext hfe]
    exact hT.deriv
  have hA : completedLFunction χ s =
      (N : ℂ) ^ ((1 : ℂ) / 2 - s) * W * completedLFunction χ⁻¹ (1 - s) := hfe s
  have hcW : (N : ℂ) ^ ((1 : ℂ) / 2 - s) * W ≠ 0 := by
    intro h
    rw [h, zero_mul] at hA
    exact A0 hA
  have hlog : deriv (completedLFunction χ) s / completedLFunction χ s =
      -Complex.log N -
        deriv (completedLFunction χ⁻¹) (1 - s) / completedLFunction χ⁻¹ (1 - s) := by
    have hBB : completedLFunction χ⁻¹ (1 - s) *
        (deriv (completedLFunction χ⁻¹) (1 - s) / completedLFunction χ⁻¹ (1 - s)) =
        deriv (completedLFunction χ⁻¹) (1 - s) := mul_div_cancel₀ _ B0
    rw [hD, hA, div_eq_iff (mul_ne_zero hcW B0)]
    linear_combination ((N : ℂ) ^ ((1 : ℂ) / 2 - s) * W) * hBB
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have l1 : ((Real.log (N / Real.pi) : ℝ) : ℂ) = Complex.log N - (Real.log Real.pi : ℂ) := by
    rw [Real.log_div hNpos.ne' Real.pi_ne_zero, ofReal_sub, Complex.ofReal_log hNpos.le,
      ofReal_natCast]
  rw [eA, eB] at hlog
  rw [l1]
  linear_combination hlog

end GlobalTheory.CompanionTheory.ExplChi
