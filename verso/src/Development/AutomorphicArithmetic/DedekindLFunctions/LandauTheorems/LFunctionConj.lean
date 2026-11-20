import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

namespace LFunctionConjugation

open HurwitzZeta

/- English proof (translation)
Establish `h` using `Complex.conj_cpow (x : ℂ) ((starRingEnd ℂ) s) (by rw [Complex.arg_ofReal_of_nonneg hx]; exact Real.pi_pos.ne)`. Rewrite `h` using `[Complex.conj_ofReal, Complex.conj_conj]`. Then use the resulting hypothesis.
-/
lemma ofReal_cpow_conj {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    (x : ℂ) ^ ((starRingEnd ℂ) s) = (starRingEnd ℂ) ((x : ℂ) ^ s) := by
  have h := Complex.conj_cpow (x : ℂ) ((starRingEnd ℂ) s)
    (by rw [Complex.arg_ofReal_of_nonneg hx]; exact Real.pi_pos.ne)
  rwa [Complex.conj_ofReal, Complex.conj_conj] at h

/- English proof (translation)
Establish `h1 : -(starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (-s / 2)`. Rewrite using `[map_div₀, map_neg, map_ofNat]`. Establish `h2 : (starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (s / 2)`. Rewrite using `[map_div₀, map_ofNat]`. Rewrite using `[Gammaℝ, Gammaℝ, h1, h2, ofReal_cpow_conj Real.pi_pos.le, Complex.Gamma_conj, map_mul]`.
-/
lemma Gammaℝ_conj (s : ℂ) : Gammaℝ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Gammaℝ s) := by
  have h1 : -(starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (-s / 2) := by
    rw [map_div₀, map_neg, map_ofNat]
  have h2 : (starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (s / 2) := by
    rw [map_div₀, map_ofNat]
  rw [Gammaℝ, Gammaℝ, h1, h2, ofReal_cpow_conj Real.pi_pos.le, Complex.Gamma_conj, map_mul]

/- English proof (translation)
Establish `hs' : 1 < ((starRingEnd ℂ) s).re` using `by rwa [Complex.conj_re]`. Rewrite using `[← (hasSum_hurwitzZeta_of_one_lt_re ha hs').tsum_eq, ← (hasSum_hurwitzZeta_of_one_lt_re ha hs).tsum_eq, Complex.conj_tsum]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Establish `hn : (0 : ℝ) ≤ (n : ℝ) + a` using `add_nonneg (Nat.cast_nonneg n) ha.1`. Establish `hc : ((n : ℂ) + (a : ℂ)) = (((n : ℝ) + a : ℝ) : ℂ)` using `by push_cast; rfl`.

Rewrite using `[map_div₀, map_one, hc, ofReal_cpow_conj hn]`.
-/
lemma hurwitz_conj_of_re {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) {s : ℂ} (hs : 1 < s.re) :
    hurwitzZeta a ((starRingEnd ℂ) s) = (starRingEnd ℂ) (hurwitzZeta a s) := by
  have hs' : 1 < ((starRingEnd ℂ) s).re := by rwa [Complex.conj_re]
  rw [← (hasSum_hurwitzZeta_of_one_lt_re ha hs').tsum_eq,
    ← (hasSum_hurwitzZeta_of_one_lt_re ha hs).tsum_eq, Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  have hn : (0 : ℝ) ≤ (n : ℝ) + a := add_nonneg (Nat.cast_nonneg n) ha.1
  have hc : ((n : ℂ) + (a : ℂ)) = (((n : ℝ) + a : ℝ) : ℂ) := by push_cast; rfl
  rw [map_div₀, map_one, hc, ofReal_cpow_conj hn]

def reg (a : UnitAddCircle) (s : ℂ) : ℂ := hurwitzZeta a s - 1 / (s - 1) / Gammaℝ s

/- English proof (translation)
Introduce `s`. Break down `eq_or_ne s 1 with rfl | hs` into its components or cases. Conclude with `differentiableAt_hurwitzZeta_sub_one_div a`. Establish `e : reg a = fun z => hurwitzZeta a z - (z - 1)⁻¹ * (Gammaℝ z)⁻¹`. Use function extensionality and compare the values at `z`.

Rewrite using `[reg, one_div, div_eq_mul_inv]`. Rewrite using `[e]`. Conclude with `(differentiableAt_hurwitzZeta a hs).sub (((differentiableAt_id.sub_const (1 : ℂ)).inv (sub_ne_zero.mpr hs)).mul (differentiable_Gammaℝ_inv s))`.
-/
lemma differentiable_reg (a : UnitAddCircle) : Differentiable ℂ (reg a) := by
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · exact differentiableAt_hurwitzZeta_sub_one_div a
  · have e : reg a = fun z => hurwitzZeta a z - (z - 1)⁻¹ * (Gammaℝ z)⁻¹ := by
      funext z
      rw [reg, one_div, div_eq_mul_inv]
    rw [e]
    exact (differentiableAt_hurwitzZeta a hs).sub
      (((differentiableAt_id.sub_const (1 : ℂ)).inv (sub_ne_zero.mpr hs)).mul
        (differentiable_Gammaℝ_inv s))

/- English proof (translation)
Rewrite using `[Gammaℝ_conj]`. Simplify using `[map_div₀]`.
-/
lemma pole_conj (s : ℂ) : 1 / ((starRingEnd ℂ) s - 1) / Gammaℝ ((starRingEnd ℂ) s)
    = (starRingEnd ℂ) (1 / (s - 1) / Gammaℝ s) := by
  rw [Gammaℝ_conj]
  simp [map_div₀]

/- English proof (translation)
Establish `hreg : ∀ z : ℂ, 1 < z.re → (starRingEnd ℂ) (reg a ((starRingEnd ℂ) z)) = reg a z`. Introduce `z hz`. Establish `h1` using `hurwitz_conj_of_re ha (s := (starRingEnd ℂ) z) (by rwa [Complex.conj_re])`. Establish `h2` using `pole_conj ((starRingEnd ℂ) z)`. Rewrite `h1`, `h2` using `[Complex.conj_conj]`.

Rewrite using `[reg, reg, map_sub, h1, h2]`. Establish `hF : Differentiable ℂ (fun z => (starRingEnd ℂ) (reg a ((starRingEnd ℂ) z)))` using `fun z => differentiableAt_conj_conj_iff.mpr (differentiable_reg a _)`. Establish `heq : (fun z => (starRingEnd ℂ) (reg a ((starRingEnd ℂ) z))) = reg a` using `AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 2) (hF.differentiableOn.analyticOnNhd isOpen_univ) ((differentiable_reg a).differentiableOn.analyticOnNhd isOpen_univ) (eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)) hreg)`. Establish `h3 : (starRingEnd ℂ) (reg a ((starRingEnd ℂ) ((starRingEnd ℂ) s))) = reg a ((starRingEnd ℂ) s)` using `congrFun heq _`. Rewrite `h3` using `[Complex.conj_conj]`.

Establish `e : ∀ w, hurwitzZeta a w = reg a w + 1 / (w - 1) / Gammaℝ w` using `fun w => by`. Rewrite using `[reg, sub_add_cancel]`. Rewrite using `[e ((starRingEnd ℂ) s), e s, map_add, ← h3, pole_conj]`.
-/
lemma hurwitz_conj_real {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (s : ℂ) :
    hurwitzZeta a ((starRingEnd ℂ) s) = (starRingEnd ℂ) (hurwitzZeta a s) := by
  have hreg : ∀ z : ℂ, 1 < z.re → (starRingEnd ℂ) (reg a ((starRingEnd ℂ) z)) = reg a z := by
    intro z hz
    have h1 := hurwitz_conj_of_re ha (s := (starRingEnd ℂ) z) (by rwa [Complex.conj_re])
    have h2 := pole_conj ((starRingEnd ℂ) z)
    rw [Complex.conj_conj] at h1 h2
    rw [reg, reg, map_sub, h1, h2]
  have hF : Differentiable ℂ (fun z => (starRingEnd ℂ) (reg a ((starRingEnd ℂ) z))) :=
    fun z => differentiableAt_conj_conj_iff.mpr (differentiable_reg a _)
  have heq : (fun z => (starRingEnd ℂ) (reg a ((starRingEnd ℂ) z))) = reg a :=
    AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 2) (hF.differentiableOn.analyticOnNhd isOpen_univ)
      ((differentiable_reg a).differentiableOn.analyticOnNhd isOpen_univ)
      (eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)) hreg)
  have h3 : (starRingEnd ℂ) (reg a ((starRingEnd ℂ) ((starRingEnd ℂ) s))) = reg a ((starRingEnd ℂ) s) :=
    congrFun heq _
  rw [Complex.conj_conj] at h3
  have e : ∀ w, hurwitzZeta a w = reg a w + 1 / (w - 1) / Gammaℝ w := fun w => by
    rw [reg, sub_add_cancel]
  rw [e ((starRingEnd ℂ) s), e s, map_add, ← h3, pole_conj]

/- English proof (translation)
Proceed by induction on `a using QuotientAddGroup.induction_on with`. Consider the case `H b`. Establish `hb : ((b : ℝ) : UnitAddCircle) = ((Int.fract b : ℝ) : UnitAddCircle)`. Rewrite using `[QuotientAddGroup.eq]`. Conclude with `⟨-⌊b⌋, by simp only [Int.fract, zsmul_eq_mul, mul_one, Int.cast_neg]; ring⟩`.

Rewrite using `[hb]`. Conclude with `hurwitz_conj_real ⟨Int.fract_nonneg b, (Int.fract_lt_one b).le⟩ s`.
-/
lemma hurwitz_conj (a : UnitAddCircle) (s : ℂ) :
    hurwitzZeta a ((starRingEnd ℂ) s) = (starRingEnd ℂ) (hurwitzZeta a s) := by
  induction a using QuotientAddGroup.induction_on with
  | H b =>
    have hb : ((b : ℝ) : UnitAddCircle) = ((Int.fract b : ℝ) : UnitAddCircle) := by
      rw [QuotientAddGroup.eq]
      exact ⟨-⌊b⌋, by simp only [Int.fract, zsmul_eq_mul, mul_one, Int.cast_neg]; ring⟩
    rw [hb]
    exact hurwitz_conj_real ⟨Int.fract_nonneg b, (Int.fract_lt_one b).le⟩ s

end LFunctionConjugation

/- English proof (translation)
Simplify using `only [DirichletCharacter.LFunction, ZMod.LFunction, map_mul, map_sum]`. Use `congr 1`. Establish `h` using `LFunctionConjugation.ofReal_cpow_conj (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (-s)`. Simplify using `using h`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[LFunctionConjugation.hurwitz_conj, ← MulChar.star_apply']`. Both sides reduce to the same expression.
-/
theorem LFunction_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    DirichletCharacter.LFunction χ⁻¹ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (DirichletCharacter.LFunction χ s) := by
  simp only [DirichletCharacter.LFunction, ZMod.LFunction, map_mul, map_sum]
  congr 1
  · have h := LFunctionConjugation.ofReal_cpow_conj (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (-s)
    simpa using h
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [LFunctionConjugation.hurwitz_conj, ← MulChar.star_apply']
    rfl

end Deduction

end
