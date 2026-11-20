import Mathlib
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

open DirichletCharacter

namespace Formalism.HermitianLattices.ThinSetIntegral

/- English proof (translation)
Introduce `h`. Apply `quadraticChar_ne_one (F := ZMod q) (by rwa [ZMod.ringChar_zmod_n])` to reduce the goal to its premises. Use `MulChar.ext fun a => ?_` and prove the remaining obligations. Establish `h1` using `congrArg (fun χ : DirichletCharacter ℂ q => χ (a : ZMod q)) h`. Simplify using `only [Formalism.HermitianLattices.ZeroFreeRegionGL2.qc, MulChar.ringHomComp_apply, Int.coe_castRingHom, MulChar.one_apply_coe] at h1`.

Rewrite using `[MulChar.one_apply_coe]`. Conclude with `h1` after adjusting the coercions.
-/
private lemma qc_ne_one (q : ℕ) [Fact q.Prime] (h2 : q ≠ 2) : Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q ≠ 1 := by
  intro h
  apply quadraticChar_ne_one (F := ZMod q) (by rwa [ZMod.ringChar_zmod_n])
  refine MulChar.ext fun a => ?_
  have h1 := congrArg (fun χ : DirichletCharacter ℂ q => χ (a : ZMod q)) h
  simp only [Formalism.HermitianLattices.ZeroFreeRegionGL2.qc, MulChar.ringHomComp_apply, Int.coe_castRingHom,
    MulChar.one_apply_coe] at h1
  rw [MulChar.one_apply_coe]
  exact_mod_cast h1

/- English proof (translation)
Establish `hd` using `conductor_dvd_level (Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q)`. Break down `(Nat.dvd_prime (Fact.out : q.Prime)).1 hd with h | h` into its components or cases. Conclude with `absurd (eq_one_iff_conductor_eq_one.2 h) (qc_ne_one q h2)`. Conclude with `h`.
-/
private lemma qc_prim (q : ℕ) [Fact q.Prime] (h2 : q ≠ 2) : (Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q).IsPrimitive := by
  have hd := conductor_dvd_level (Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q)
  rcases (Nat.dvd_prime (Fact.out : q.Prime)).1 hd with h | h
  · exact absurd (eq_one_iff_conductor_eq_one.2 h) (qc_ne_one q h2)
  · exact h

/- English proof (translation)
Use `MulChar.ext fun a => ?_` and prove the remaining obligations. Rewrite using `[MulChar.pow_apply_coe, MulChar.one_apply_coe]`. Simplify using `only [Formalism.HermitianLattices.ZeroFreeRegionGL2.qc, MulChar.ringHomComp_apply, Int.coe_castRingHom]`. Rewrite using `[← Int.cast_pow, quadraticChar_sq_one a.ne_zero, Int.cast_one]`.
-/
private lemma qc_sq (q : ℕ) [Fact q.Prime] : Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q ^ 2 = 1 := by
  refine MulChar.ext fun a => ?_
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  simp only [Formalism.HermitianLattices.ZeroFreeRegionGL2.qc, MulChar.ringHomComp_apply, Int.coe_castRingHom]
  rw [← Int.cast_pow, quadraticChar_sq_one a.ne_zero, Int.cast_one]

/- English proof (translation)
Establish `cA : (changeLevel hm χ₁).conductor = m` using `by rw [conductor_changeLevel]; exact h1`. Establish `cB : (changeLevel hn χ₂).conductor = n` using `by rw [conductor_changeLevel]; exact h2`. Generalize the expression as in `changeLevel hm χ₁ = A at *`. Generalize the expression as in `changeLevel hn χ₂ = B at *`. Establish `d1 : m ∣ (A * B).conductor.lcm n`.

Establish `h` using `conductor_mul_dvd_lcm_conductor (A * B) B⁻¹`. Rewrite `h` using `[mul_inv_cancel_right, conductor_inv, cA, cB]`. Then use the resulting hypothesis. Establish `d2 : n ∣ (A * B).conductor.lcm m`. Establish `h` using `conductor_mul_dvd_lcm_conductor (B * A) A⁻¹`. Rewrite `h` using `[mul_inv_cancel_right, conductor_inv, cA, cB, mul_comm B A]`. Then use the resulting hypothesis.

Establish `e1 : m ∣ (A * B).conductor` using `hco.dvd_of_dvd_mul_right (d1.trans (Nat.lcm_dvd_mul _ _))`. Establish `e2 : n ∣ (A * B).conductor` using `hco.symm.dvd_of_dvd_mul_right (d2.trans (Nat.lcm_dvd_mul _ _))`. Rewrite using `[isPrimitive_def]`. Establish `e3 : N ∣ (A * B).conductor`. Establish `h` using `hco.mul_dvd_of_dvd_of_dvd e1 e2`.

Rewrite `h` using `[← hN]`. Then use the resulting hypothesis. Conclude with `Nat.dvd_antisymm (conductor_dvd_level _) e3`.
-/
private lemma prim_mul {N m n : ℕ} [NeZero N] (hm : m ∣ N) (hn : n ∣ N) (hco : m.Coprime n) (hN : N = m * n)
    (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n) (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    (changeLevel hm χ₁ * changeLevel hn χ₂).IsPrimitive := by
  have cA : (changeLevel hm χ₁).conductor = m := by rw [conductor_changeLevel]; exact h1
  have cB : (changeLevel hn χ₂).conductor = n := by rw [conductor_changeLevel]; exact h2
  generalize changeLevel hm χ₁ = A at *
  generalize changeLevel hn χ₂ = B at *
  have d1 : m ∣ (A * B).conductor.lcm n := by
    have h := conductor_mul_dvd_lcm_conductor (A * B) B⁻¹
    rwa [mul_inv_cancel_right, conductor_inv, cA, cB] at h
  have d2 : n ∣ (A * B).conductor.lcm m := by
    have h := conductor_mul_dvd_lcm_conductor (B * A) A⁻¹
    rwa [mul_inv_cancel_right, conductor_inv, cA, cB, mul_comm B A] at h
  have e1 : m ∣ (A * B).conductor :=
    hco.dvd_of_dvd_mul_right (d1.trans (Nat.lcm_dvd_mul _ _))
  have e2 : n ∣ (A * B).conductor :=
    hco.symm.dvd_of_dvd_mul_right (d2.trans (Nat.lcm_dvd_mul _ _))
  rw [isPrimitive_def]
  have e3 : N ∣ (A * B).conductor := by
    have h := hco.mul_dvd_of_dvd_of_dvd e1 e2
    rwa [← hN] at h
  exact Nat.dvd_antisymm (conductor_dvd_level _) e3

/- English proof (translation)
Use `MulChar.ext fun a => ?_` and prove the remaining obligations. Rewrite using `[MulChar.pow_apply_coe, MulChar.one_apply_coe]`. Simplify using `only [Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8, MulChar.ringHomComp_apply, Int.coe_castRingHom]`. Establish `hu : IsUnit (ZMod.χ₈ (a : ZMod 8))`. Rewrite using `[← MulChar.coe_toUnitHom]`.

Conclude with `Units.isUnit _`. Break down `ZMod.isQuadratic_χ₈ (a : ZMod 8) with h | h | h` into its components or cases. Rewrite `hu` using `[h]`. Conclude with `absurd hu not_isUnit_zero`. Rewrite using `[h]`.

Evaluate the numerical expressions. Rewrite using `[h]`. Evaluate the numerical expressions.
-/
private lemma chi_eight_sq : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8 ^ 2 = 1 := by
  refine MulChar.ext fun a => ?_
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  simp only [Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8, MulChar.ringHomComp_apply, Int.coe_castRingHom]
  have hu : IsUnit (ZMod.χ₈ (a : ZMod 8)) := by
    rw [← MulChar.coe_toUnitHom]
    exact Units.isUnit _
  rcases ZMod.isQuadratic_χ₈ (a : ZMod 8) with h | h | h
  · rw [h] at hu
    exact absurd hu not_isUnit_zero
  · rw [h]
    norm_num
  · rw [h]
    norm_num

/- English proof (translation)
Rewrite using `[isPrimitive_def]`. Assume the negation of the conclusion as `hne`. Establish `hd` using `conductor_dvd_level Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8`. Establish `h4 : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.conductor ∣ 4`. Establish `hle : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.conductor ≤ 8` using `Nat.le_of_dvd (by norm_num) hd`.

Generalize the expression as in `Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.conductor = k at *`. Apply the tactic sequence `interval_cases k <;> omega`. Take `⟨hd4, χ₀, h0⟩ : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.FactorsThrough 4` from `(mem_conductorSet_iff_conductor_dvd _ (by norm_num)).2 h4`. Establish `h5 : changeLevel hd4 χ₀ ((5 : ℤ) : ZMod 8) = χ₀ ((5 : ℤ) : ZMod 4)` using `changeLevel_eq_cast_of_dvd' χ₀ hd4 (by`. Rewrite using `[Int.isCoprime_iff_gcd_eq_one]`.

Use the proof step `decide)`. Rewrite `h5` using `[← h0]`. Establish `h6 : ((5 : ℤ) : ZMod 4) = 1` using `by decide`. Establish `h7 : ZMod.χ₈ ((5 : ℤ) : ZMod 8) = -1` using `by decide`. Rewrite `h5` using `[h6, map_one, Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8, MulChar.ringHomComp_apply, h7]`.

Evaluate the numerical expressions using `at h5`.
-/
private lemma chi_eight_primitive : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.IsPrimitive := by
  rw [isPrimitive_def]
  by_contra hne
  have hd := conductor_dvd_level Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8
  have h4 : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.conductor ∣ 4 := by
    have hle : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.conductor ≤ 8 := Nat.le_of_dvd (by norm_num) hd
    generalize Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.conductor = k at *
    interval_cases k <;> omega
  obtain ⟨hd4, χ₀, h0⟩ : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.FactorsThrough 4 :=
    (mem_conductorSet_iff_conductor_dvd _ (by norm_num)).2 h4
  have h5 : changeLevel hd4 χ₀ ((5 : ℤ) : ZMod 8) = χ₀ ((5 : ℤ) : ZMod 4) :=
    changeLevel_eq_cast_of_dvd' χ₀ hd4 (by
      rw [Int.isCoprime_iff_gcd_eq_one]; decide)
  rw [← h0] at h5
  have h6 : ((5 : ℤ) : ZMod 4) = 1 := by decide
  have h7 : ZMod.χ₈ ((5 : ℤ) : ZMod 8) = -1 := by decide
  rw [h6, map_one, Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8, MulChar.ringHomComp_apply, h7] at h5
  norm_num at h5

/- English proof (translation)
Use `⟨⟨chi_eight_primitive, chi_eight_sq⟩, ?_⟩` and prove the remaining obligations. Introduce `t θ q _ hθ h2 hco`. Establish `hq : q.Prime` using `Fact.out`. Establish `ht : t ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hco` using `[Nat.coprime_zero_right]`. Conclude with `hq.one_lt.ne' hco`. Establish `: NeZero t` using `⟨ht⟩`. Establish `hp : (Formalism.HermitianLattices.ZeroFreeRegionGL2.tw θ q).IsPrimitive` using `prim_mul _ _ hco.symm rfl θ (Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q) hθ (qc_prim q h2)`. Use `⟨hp, ?_, ?_⟩` and prove the remaining obligations.

Introduce `h1`. Rewrite `hp` using `[isPrimitive_def, h1, conductor_one]`. Establish `h3 : 2 ≤ q` using `hq.two_le`. Establish `h4 : 1 ≤ t` using `Nat.pos_of_ne_zero ht`. Use the polynomial consequences of the given equalities and inequalities.

Introduce `hs`. Rewrite using `[Formalism.HermitianLattices.ZeroFreeRegionGL2.tw, mul_pow, ← map_pow, ← map_pow, hs, qc_sq, map_one, map_one, one_mul]`.
-/
theorem twist_is_primitive_character : Formalism.HermitianLattices.ZeroFreeRegionGL2.TwPrimitive := by
  refine ⟨⟨chi_eight_primitive, chi_eight_sq⟩, ?_⟩
  intro t θ q _ hθ h2 hco
  have hq : q.Prime := Fact.out
  have ht : t ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_right] at hco
    exact hq.one_lt.ne' hco
  have : NeZero t := ⟨ht⟩
  have hp : (Formalism.HermitianLattices.ZeroFreeRegionGL2.tw θ q).IsPrimitive :=
    prim_mul _ _ hco.symm rfl θ (Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q) hθ (qc_prim q h2)
  refine ⟨hp, ?_, ?_⟩
  · intro h1
    rw [isPrimitive_def, h1, conductor_one] at hp
    have h3 : 2 ≤ q := hq.two_le
    have h4 : 1 ≤ t := Nat.pos_of_ne_zero ht
    nlinarith
  · intro hs
    rw [Formalism.HermitianLattices.ZeroFreeRegionGL2.tw, mul_pow, ← map_pow, ← map_pow, hs, qc_sq, map_one, map_one, one_mul]

/- English proof (translation)
Conclude with `integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hb`.
-/
private lemma K_int (b : ℝ) (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun v : ℝ => v ^ (2 : ℝ) * Real.exp (-b * v ^ (3 / 8 : ℝ))) (Set.Ioi 0) := by
  exact integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hb

/- English proof (translation)
Establish `hv1 : 1 ≤ v` using `by linarith`. Establish `hv0 : 0 < v` using `by linarith`. Establish `hV58 : V ^ (5 / 8 : ℝ) ≤ V`. Establish `h` using `Real.rpow_le_rpow_of_exponent_le hV (show (5 / 8 : ℝ) ≤ 1 by norm_num)`. Rewrite `h` using `[Real.rpow_one]`. Then use the resulting hypothesis.

Establish `hlv : lam ≤ v` using `by linarith`. Establish `h58 : lam ≤ v ^ (5 / 8 : ℝ)` using `le_trans hl (Real.rpow_le_rpow (by linarith) hv.le (by norm_num))`. Establish `hsq : Real.sqrt v ≤ v ^ (5 / 8 : ℝ)`. Rewrite using `[Real.sqrt_eq_rpow]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)`.

Establish `hv58 : 0 < v ^ (5 / 8 : ℝ)` using `by positivity`. Establish `hden : lam + Real.sqrt v ≤ 2 * v ^ (5 / 8 : ℝ)` using `by linarith`. Establish `hdpos : 0 < lam + Real.sqrt v` using `by positivity`. Establish `h38 : v ^ (3 / 8 : ℝ) = v / v ^ (5 / 8 : ℝ)`. Rewrite using `[show (3 / 8 : ℝ) = 1 - 5 / 8 by norm_num, Real.rpow_sub hv0, Real.rpow_one]`.

Establish `h1 : c / 2 * v ^ (3 / 8 : ℝ) ≤ c * v / (lam + Real.sqrt v)`. Rewrite using `[h38]`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Use `_ ≤ c * v / (lam + Real.sqrt v) := div_le_div_of_nonneg_left (by positivity) hdpos hden`.

Establish `h2 : V ^ (3 / 8 : ℝ) ≤ v ^ (3 / 8 : ℝ)` using `Real.rpow_le_rpow (by linarith) hv.le (by norm_num)`. Establish `hexp : Real.exp (-c * v / (lam + Real.sqrt v)) ≤ Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) * Real.exp (-(c / 4) * v ^ (3 / 8 : ℝ))`. Rewrite using `[← Real.exp_add]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Establish `h3 : -c * v / (lam + Real.sqrt v) = -(c * v / (lam + Real.sqrt v))` using `by ring`.

Rewrite using `[h3]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hpoly : (v + lam) ^ 2 ≤ 4 * v ^ (2 : ℝ)`. Rewrite using `[show (v ^ (2 : ℝ)) = v ^ 2 by norm_cast]`. Use the polynomial consequences of the given equalities and inequalities.

Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma ptwise (c lam V v : ℝ) (hc : 0 < c) (hV : 1 ≤ V) (hl1 : 1 ≤ lam) (hl : lam ≤ V ^ (5 / 8 : ℝ))
    (hv : V < v) :
    (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) ≤
      4 * Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) * (v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (3 / 8 : ℝ))) := by
  have hv1 : 1 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hV58 : V ^ (5 / 8 : ℝ) ≤ V := by
    have h := Real.rpow_le_rpow_of_exponent_le hV (show (5 / 8 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hlv : lam ≤ v := by linarith
  have h58 : lam ≤ v ^ (5 / 8 : ℝ) :=
    le_trans hl (Real.rpow_le_rpow (by linarith) hv.le (by norm_num))
  have hsq : Real.sqrt v ≤ v ^ (5 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
  have hv58 : 0 < v ^ (5 / 8 : ℝ) := by positivity
  have hden : lam + Real.sqrt v ≤ 2 * v ^ (5 / 8 : ℝ) := by linarith
  have hdpos : 0 < lam + Real.sqrt v := by positivity
  have h38 : v ^ (3 / 8 : ℝ) = v / v ^ (5 / 8 : ℝ) := by
    rw [show (3 / 8 : ℝ) = 1 - 5 / 8 by norm_num, Real.rpow_sub hv0, Real.rpow_one]
  have h1 : c / 2 * v ^ (3 / 8 : ℝ) ≤ c * v / (lam + Real.sqrt v) := by
    rw [h38]
    calc c / 2 * (v / v ^ (5 / 8 : ℝ)) = c * v / (2 * v ^ (5 / 8 : ℝ)) := by
          field_simp
      _ ≤ c * v / (lam + Real.sqrt v) :=
          div_le_div_of_nonneg_left (by positivity) hdpos hden
  have h2 : V ^ (3 / 8 : ℝ) ≤ v ^ (3 / 8 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hv.le (by norm_num)
  have hexp : Real.exp (-c * v / (lam + Real.sqrt v)) ≤
      Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) * Real.exp (-(c / 4) * v ^ (3 / 8 : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h3 : -c * v / (lam + Real.sqrt v) = -(c * v / (lam + Real.sqrt v)) := by ring
    rw [h3]
    nlinarith
  have hpoly : (v + lam) ^ 2 ≤ 4 * v ^ (2 : ℝ) := by
    rw [show (v ^ (2 : ℝ)) = v ^ 2 by norm_cast]
    nlinarith
  calc (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))
      ≤ (4 * v ^ (2 : ℝ)) * (Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) * Real.exp (-(c / 4) * v ^ (3 / 8 : ℝ))) :=
        mul_le_mul hpoly hexp (by positivity) (by positivity)
    _ = 4 * Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) * (v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (3 / 8 : ℝ))) := by
        ring

/- English proof (translation)
Rewrite using `[Real.div_rpow hy (by norm_num)]`. Establish `h2 : (2 : ℝ) ^ a ≤ 2`. Combine the equalities or inequalities in the displayed calculation. Establish `hpos : 0 < (2 : ℝ) ^ a` using `Real.rpow_pos_of_pos (by norm_num) a`. Conclude with `div_le_div_of_nonneg_left (Real.rpow_nonneg hy a) hpos h2`.
-/
private lemma half_rpow (y a : ℝ) (hy : 0 ≤ y) (ha1 : a ≤ 1) : y ^ a / 2 ≤ (y / 2) ^ a := by
  rw [Real.div_rpow hy (by norm_num)]
  have h2 : (2 : ℝ) ^ a ≤ 2 := by
    calc (2 : ℝ) ^ a ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ha1
      _ = 2 := Real.rpow_one 2
  have hpos : 0 < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy a) hpos h2

/- English proof (translation)
Introduce `ε c hε hc`. Establish `hb : 0 < c / 4` using `by positivity`. Establish `hKi` using `K_int (c / 4) hb`. Use `set g : ℝ → ℝ := fun v : ℝ => v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (3 / 8 : ℝ)) with hg`. Use `set K := ∫ v in Set.Ioi (0 : ℝ), g v with hK`.

Establish `E1 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x` using `Filter.eventually_ge_atTop 1`. Establish `E3 : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ x ^ (ε / 3)` using `(tendsto_rpow_atTop (by positivity)).eventually_ge_atTop 2`. Establish `E2a : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ 1 * ‖x ^ (ε / 480)‖` using `(isLittleO_log_rpow_atTop (show 0 < ε / 480 by positivity)).bound one_pos`. Establish `E2b : ∀ᶠ x : ℝ in Filter.atTop, 4 ≤ x ^ (ε / 240)` using `(tendsto_rpow_atTop (by positivity)).eventually_ge_atTop 4`. Establish `E4 : ∀ᶠ x : ℝ in Filter.atTop, 4 * K ≤ Real.exp (c / 16 * x ^ (ε / 8))` using `(Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (show 0 < ε / 8 by positivity)).const_mul_atTop (show 0 < c / 16 by positivity))).eventually_ge_atTop (4 * K)`.

Take `⟨x₀, hx₀⟩` from `Filter.eventually_atTop.1 (E1.and (E3.and (E2a.and (E2b.and E4))))`. Use `⟨c / 16, x₀, by positivity, ?_⟩` and prove the remaining obligations. Introduce `x hx V lam hV hl1 hl`. Take `⟨h1, h3, h2a, h2b, h4⟩` from `hx₀ x hx`. Establish `hx0 : 0 < x` using `by linarith`.

Establish `hV1 : 1 ≤ V` using `by linarith`. Establish `hV0 : 0 ≤ x ^ (ε / 3) / 2` using `by positivity`. Establish `hlV : lam ≤ V ^ (5 / 8 : ℝ)`. Establish `hlog0 : 0 ≤ Real.log x` using `Real.log_nonneg h1`. Establish `hr0 : 0 < x ^ (ε / 480)` using `Real.rpow_pos_of_pos hx0 _`.

Establish `hlog : Real.log x ≤ x ^ (ε / 480)`. Rewrite `h2a` using `[Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hr0.le, one_mul]`. Conclude with `h2a`. Establish `hlog2 : Real.log x ^ 2 ≤ x ^ (ε / 240)`. Establish `e : x ^ (ε / 240) = (x ^ (ε / 480)) ^ 2`.

Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hx0.le]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `gcongr`. Establish `e5 : (x ^ (ε / 3)) ^ (5 / 8 : ℝ) = x ^ (ε / 5) * x ^ (ε / 240) * x ^ (ε / 240)`. Rewrite using `[← Real.rpow_mul hx0.le, ← Real.rpow_add hx0, ← Real.rpow_add hx0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hh` using `half_rpow (x ^ (ε / 3)) (5 / 8) (by positivity) (by norm_num)`. Establish `hm : (x ^ (ε / 3) / 2) ^ (5 / 8 : ℝ) ≤ V ^ (5 / 8 : ℝ)` using `Real.rpow_le_rpow hV0 hV (by norm_num)`. Establish `ha : 0 < x ^ (ε / 5)` using `Real.rpow_pos_of_pos hx0 _`. Establish `hb' : 0 < x ^ (ε / 240)` using `Real.rpow_pos_of_pos hx0 _`. Establish `s1 : 2 * x ^ (ε / 5) * Real.log x ^ 2 ≤ 2 * x ^ (ε / 5) * x ^ (ε / 240)` using `by gcongr`.

Establish `s2 : 2 * x ^ (ε / 5) * x ^ (ε / 240) * 4 ≤ 2 * x ^ (ε / 5) * x ^ (ε / 240) * x ^ (ε / 240)` using `by gcongr`. Rewrite `hh` using `[e5]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hW : x ^ (ε / 8) / 2 ≤ V ^ (3 / 8 : ℝ)`. Establish `e3 : (x ^ (ε / 3)) ^ (3 / 8 : ℝ) = x ^ (ε / 8)`.

Rewrite using `[← Real.rpow_mul hx0.le]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hh` using `half_rpow (x ^ (ε / 3)) (3 / 8) (by positivity) (by norm_num)`. Establish `hm : (x ^ (ε / 3) / 2) ^ (3 / 8 : ℝ) ≤ V ^ (3 / 8 : ℝ)` using `Real.rpow_le_rpow hV0 hV (by norm_num)`.

Rewrite `hh` using `[e3]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set A : ℝ := 4 * Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) with hA`. Establish `hA0 : 0 ≤ A` using `by positivity`. Establish `hpt : ∀ v ∈ Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) ≤ A * g v` using `fun v hv => ptwise c lam V v hc hV1 hl1 hlV hv`.

Establish `hgV : MeasureTheory.IntegrableOn (fun v => A * g v) (Set.Ioi V)` using `(hKi.mono_set (Set.Ioi_subset_Ioi (by linarith))).const_mul A`. Establish `hcont : Continuous (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)))`. Establish `hne : ∀ v : ℝ, lam + Real.sqrt v ≠ 0` using `fun v => by`. Use `Real.sqrt_nonneg v` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `fun_prop (disch := exact hne _)`. Establish `hfi : MeasureTheory.IntegrableOn (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) (Set.Ioi V)`. Use `MeasureTheory.Integrable.mono' hgV hcont.aestronglyMeasurable ?_` and prove the remaining obligations. Use `(MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun v hv => ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_of_nonneg (by positivity)]`.

Conclude with `hpt v hv`. Use `⟨hfi, ?_⟩` and prove the remaining obligations. Establish `hg0 : ∀ v ∈ Set.Ioi (0 : ℝ), 0 ≤ g v` using `fun v hv => by`. Establish `: (0 : ℝ) < v` using `hv`. Simplify using `only [hg]`.

Check the signs of the components of the expression. Establish `hK0 : 0 ≤ K` using `MeasureTheory.setIntegral_nonneg measurableSet_Ioi hg0`. Establish `i1 : (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) ≤ ∫ v in Set.Ioi V, A * g v` using `MeasureTheory.setIntegral_mono_on hfi hgV measurableSet_Ioi hpt`. Establish `i2 : (∫ v in Set.Ioi V, A * g v) = A * ∫ v in Set.Ioi V, g v` using `MeasureTheory.integral_const_mul _ _`. Establish `i3 : (∫ v in Set.Ioi V, g v) ≤ K` using `MeasureTheory.setIntegral_mono_set hKi ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hg0)) (Set.Ioi_subset_Ioi (by linarith : (0 : ℝ) ≤ V)).eventuallyLE`.

Establish `i4 : A * K ≤ Real.exp (-(c / 16) * x ^ (ε / 8))`. Establish `j1 : Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) ≤ Real.exp (-(c / 16) * x ^ (ε / 8)) * Real.exp (-(c / 16 * x ^ (ε / 8)))`. Rewrite using `[← Real.exp_add]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.

Establish `j2 : 4 * K * Real.exp (-(c / 16 * x ^ (ε / 8))) ≤ 1`. Rewrite using `[Real.exp_neg]`. Use `Real.exp_pos (c / 16 * x ^ (ε / 8))` as an intermediate fact. Rewrite using `[← div_eq_mul_inv, div_le_one this]`. Conclude with `h4`.

Establish `j3` using `Real.exp_pos (-(c / 16) * x ^ (ε / 8))`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem thin_set_integral : Formalism.HermitianLattices.ZeroFreeRegionGL2.ThinIntegral := by
  intro ε c hε hc
  have hb : 0 < c / 4 := by positivity
  have hKi := K_int (c / 4) hb
  set g : ℝ → ℝ := fun v : ℝ => v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (3 / 8 : ℝ)) with hg
  set K := ∫ v in Set.Ioi (0 : ℝ), g v with hK
  have E1 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x := Filter.eventually_ge_atTop 1
  have E3 : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ x ^ (ε / 3) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop 2
  have E2a : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ 1 * ‖x ^ (ε / 480)‖ :=
    (isLittleO_log_rpow_atTop (show 0 < ε / 480 by positivity)).bound one_pos
  have E2b : ∀ᶠ x : ℝ in Filter.atTop, 4 ≤ x ^ (ε / 240) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop 4
  have E4 : ∀ᶠ x : ℝ in Filter.atTop, 4 * K ≤ Real.exp (c / 16 * x ^ (ε / 8)) :=
    (Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (show 0 < ε / 8 by positivity)).const_mul_atTop
      (show 0 < c / 16 by positivity))).eventually_ge_atTop (4 * K)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 (E1.and (E3.and (E2a.and (E2b.and E4))))
  refine ⟨c / 16, x₀, by positivity, ?_⟩
  intro x hx V lam hV hl1 hl
  obtain ⟨h1, h3, h2a, h2b, h4⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hV1 : 1 ≤ V := by linarith
  have hV0 : 0 ≤ x ^ (ε / 3) / 2 := by positivity

  have hlV : lam ≤ V ^ (5 / 8 : ℝ) := by
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg h1
    have hr0 : 0 < x ^ (ε / 480) := Real.rpow_pos_of_pos hx0 _
    have hlog : Real.log x ≤ x ^ (ε / 480) := by
      rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hr0.le, one_mul] at h2a
      exact h2a
    have hlog2 : Real.log x ^ 2 ≤ x ^ (ε / 240) := by
      have e : x ^ (ε / 240) = (x ^ (ε / 480)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
      rw [e]
      gcongr
    have e5 : (x ^ (ε / 3)) ^ (5 / 8 : ℝ) = x ^ (ε / 5) * x ^ (ε / 240) * x ^ (ε / 240) := by
      rw [← Real.rpow_mul hx0.le, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
    have hh := half_rpow (x ^ (ε / 3)) (5 / 8) (by positivity) (by norm_num)
    have hm : (x ^ (ε / 3) / 2) ^ (5 / 8 : ℝ) ≤ V ^ (5 / 8 : ℝ) := Real.rpow_le_rpow hV0 hV (by norm_num)
    have ha : 0 < x ^ (ε / 5) := Real.rpow_pos_of_pos hx0 _
    have hb' : 0 < x ^ (ε / 240) := Real.rpow_pos_of_pos hx0 _
    have s1 : 2 * x ^ (ε / 5) * Real.log x ^ 2 ≤ 2 * x ^ (ε / 5) * x ^ (ε / 240) := by gcongr
    have s2 : 2 * x ^ (ε / 5) * x ^ (ε / 240) * 4 ≤ 2 * x ^ (ε / 5) * x ^ (ε / 240) * x ^ (ε / 240) := by gcongr
    rw [e5] at hh
    linarith

  have hW : x ^ (ε / 8) / 2 ≤ V ^ (3 / 8 : ℝ) := by
    have e3 : (x ^ (ε / 3)) ^ (3 / 8 : ℝ) = x ^ (ε / 8) := by
      rw [← Real.rpow_mul hx0.le]; congr 1; ring
    have hh := half_rpow (x ^ (ε / 3)) (3 / 8) (by positivity) (by norm_num)
    have hm : (x ^ (ε / 3) / 2) ^ (3 / 8 : ℝ) ≤ V ^ (3 / 8 : ℝ) := Real.rpow_le_rpow hV0 hV (by norm_num)
    rw [e3] at hh
    linarith
  set A : ℝ := 4 * Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) with hA
  have hA0 : 0 ≤ A := by positivity
  have hpt : ∀ v ∈ Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) ≤ A * g v :=
    fun v hv => ptwise c lam V v hc hV1 hl1 hlV hv
  have hgV : MeasureTheory.IntegrableOn (fun v => A * g v) (Set.Ioi V) :=
    (hKi.mono_set (Set.Ioi_subset_Ioi (by linarith))).const_mul A
  have hcont : Continuous (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) := by
    have hne : ∀ v : ℝ, lam + Real.sqrt v ≠ 0 := fun v => by
      have := Real.sqrt_nonneg v
      linarith
    fun_prop (disch := exact hne _)
  have hfi : MeasureTheory.IntegrableOn
      (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) (Set.Ioi V) := by
    refine MeasureTheory.Integrable.mono' hgV hcont.aestronglyMeasurable ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun v hv => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt v hv
  refine ⟨hfi, ?_⟩
  have hg0 : ∀ v ∈ Set.Ioi (0 : ℝ), 0 ≤ g v := fun v hv => by
    have : (0 : ℝ) < v := hv
    simp only [hg]
    positivity
  have hK0 : 0 ≤ K := MeasureTheory.setIntegral_nonneg measurableSet_Ioi hg0
  have i1 : (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) ≤
      ∫ v in Set.Ioi V, A * g v := MeasureTheory.setIntegral_mono_on hfi hgV measurableSet_Ioi hpt
  have i2 : (∫ v in Set.Ioi V, A * g v) = A * ∫ v in Set.Ioi V, g v := MeasureTheory.integral_const_mul _ _
  have i3 : (∫ v in Set.Ioi V, g v) ≤ K :=
    MeasureTheory.setIntegral_mono_set hKi
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hg0))
      (Set.Ioi_subset_Ioi (by linarith : (0 : ℝ) ≤ V)).eventuallyLE
  have i4 : A * K ≤ Real.exp (-(c / 16) * x ^ (ε / 8)) := by
    have j1 : Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) ≤
        Real.exp (-(c / 16) * x ^ (ε / 8)) * Real.exp (-(c / 16 * x ^ (ε / 8))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith
    have j2 : 4 * K * Real.exp (-(c / 16 * x ^ (ε / 8))) ≤ 1 := by
      rw [Real.exp_neg]
      have := Real.exp_pos (c / 16 * x ^ (ε / 8))
      rw [← div_eq_mul_inv, div_le_one this]
      exact h4
    have j3 := Real.exp_pos (-(c / 16) * x ^ (ε / 8))
    calc A * K = 4 * K * Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) := by rw [hA]; ring
      _ ≤ 4 * K * (Real.exp (-(c / 16) * x ^ (ε / 8)) * Real.exp (-(c / 16 * x ^ (ε / 8)))) := by gcongr
      _ = Real.exp (-(c / 16) * x ^ (ε / 8)) * (4 * K * Real.exp (-(c / 16 * x ^ (ε / 8)))) := by ring
      _ ≤ Real.exp (-(c / 16) * x ^ (ε / 8)) * 1 := by gcongr
      _ = _ := mul_one _
  calc _ ≤ A * ∫ v in Set.Ioi V, g v := by rw [← i2]; exact i1
    _ ≤ A * K := by gcongr
    _ ≤ _ := i4

end Formalism.HermitianLattices.ThinSetIntegral
