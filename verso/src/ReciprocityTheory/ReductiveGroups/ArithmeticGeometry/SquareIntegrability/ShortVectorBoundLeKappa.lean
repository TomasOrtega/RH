import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofCovolLb

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Unfold `Par.ka0 Par.ph RR`. Establish `hph' : 0 < X.ph (th P.q P.R0)` using `hph`. Establish `hf1 : 1 ≤ PT.f E` using `le_trans (Nat.one_le_pow 4 P.m P.hm1) P.hmf`. Establish `hm2 : P.m ^ 2 ≤ PT.f E` using `le_trans (Nat.pow_le_pow_right P.hm1 (by norm_num)) P.hmf`. Establish `hF : (1 : ℝ) ≤ PT.f E` using `by exact_mod_cast hf1`.

Establish `hM2 : (P.m : ℝ) ^ 2 ≤ PT.f E` using `by exact_mod_cast hm2`. Establish `hFR : (PT.f E : ℝ) ≤ PT.rd E` using `P.hfrd`. Establish `hR : (16 : ℝ) ≤ PT.rd E` using `P.hrd`. Establish `hM0 : (0 : ℝ) ≤ P.m` using `Nat.cast_nonneg _`. Establish `hd : (dstar (E` using `E) P.m : ℝ) = 2 * (PT.f E : ℝ) * P.m := by unfold dstar; push_cast; ring`.

Rewrite using `[hd, div_le_iff₀ (by linarith)]`. Establish `key1 : (PT.f E : ℝ) * (P.m : ℝ) ^ 2 ≤ PT.rd E ^ 2`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hM2 (by linarith : (0 : ℝ) ≤ PT.f E), mul_le_mul hFR hFR (by linarith) (by linarith)]`. Establish `h3 : PT.rd E ^ 4 * (PT.f E : ℝ) ≤ PT.rd E ^ 7 * PT.f E` using `mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (by norm_num)) (by linarith)`. Establish `h4` using `mul_le_mul_of_nonneg_left key1 (by positivity : (0 : ℝ) ≤ 4 * PT.rd E ^ 2 * PT.f E)`.

Establish `key2 : PT.rd E ^ 2 * (2 * (PT.f E : ℝ) * P.m) ^ 2 ≤ 8 * PT.rd E ^ 7 * PT.f E`. Use polynomial arithmetic with `[h3, h4, (by positivity : (0 : ℝ) ≤ PT.rd E ^ 7 * PT.f E)]`. Establish `hd2` using `mul_nonneg (sq_nonneg (2 * (PT.f E : ℝ) * P.m)) hph'.le`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right key2 hd2]`.
-/
theorem short_vector_bound_le_kappa [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (hph : 0 < P.ph) :
    PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E) ≤ P.ka0 * P.ph := by
  unfold Par.ka0 Par.ph RR
  have hph' : 0 < X.ph (th P.q P.R0) := hph
  have hf1 : 1 ≤ PT.f E := le_trans (Nat.one_le_pow 4 P.m P.hm1) P.hmf
  have hm2 : P.m ^ 2 ≤ PT.f E := le_trans (Nat.pow_le_pow_right P.hm1 (by norm_num)) P.hmf
  have hF : (1 : ℝ) ≤ PT.f E := by exact_mod_cast hf1
  have hM2 : (P.m : ℝ) ^ 2 ≤ PT.f E := by exact_mod_cast hm2
  have hFR : (PT.f E : ℝ) ≤ PT.rd E := P.hfrd
  have hR : (16 : ℝ) ≤ PT.rd E := P.hrd
  have hM0 : (0 : ℝ) ≤ P.m := Nat.cast_nonneg _
  have hd : (dstar (E := E) P.m : ℝ) = 2 * (PT.f E : ℝ) * P.m := by unfold dstar; push_cast; ring
  rw [hd, div_le_iff₀ (by linarith)]
  have key1 : (PT.f E : ℝ) * (P.m : ℝ) ^ 2 ≤ PT.rd E ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hM2 (by linarith : (0 : ℝ) ≤ PT.f E),
      mul_le_mul hFR hFR (by linarith) (by linarith)]
  have h3 : PT.rd E ^ 4 * (PT.f E : ℝ) ≤ PT.rd E ^ 7 * PT.f E :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (by norm_num)) (by linarith)
  have h4 := mul_le_mul_of_nonneg_left key1 (by positivity : (0 : ℝ) ≤ 4 * PT.rd E ^ 2 * PT.f E)
  have key2 : PT.rd E ^ 2 * (2 * (PT.f E : ℝ) * P.m) ^ 2 ≤ 8 * PT.rd E ^ 7 * PT.f E := by
    nlinarith [h3, h4, (by positivity : (0 : ℝ) ≤ PT.rd E ^ 7 * PT.f E)]
  have hd2 := mul_nonneg (sq_nonneg (2 * (PT.f E : ℝ) * P.m)) hph'.le
  nlinarith [mul_le_mul_of_nonneg_right key2 hd2]

/- English proof (translation)
Establish `hU` using `short_vector_bound_le_kappa P hph`. Establish `hf1 : 1 ≤ PT.f E` using `le_trans (Nat.one_le_pow 4 P.m P.hm1) P.hmf`. Establish `hF : (1 : ℝ) ≤ PT.f E` using `by exact_mod_cast hf1`. Establish `hR : (16 : ℝ) ≤ PT.rd E` using `P.hrd`. Establish `hR0 : (0 : ℝ) < PT.rd E` using `by linarith`.

Establish `hdR : ((dstar (E` using `E) P.m : ℕ) : ℝ) = 2 * (PT.f E : ℝ) * P.m := by`. Unfold `dstar`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hm1 : (1 : ℝ) ≤ P.m` using `by exact_mod_cast P.hm1`.

Establish `hd1 : (1 : ℝ) ≤ ((dstar (E` using `E) P.m : ℕ) : ℝ) := by rw [hdR]; nlinarith`. Establish `hph2` using `hph`. Unfold `Par.ph PT.ph at hph2`. Use `split_ifs at hph2 with hlt`. Use `swap`.

Conclude with `absurd hph2 (lt_irrefl 0)`. Establish `hL0 : 0 ≤ X.la1`. Unfold `PT.la1`. Conclude with `Real.sInf_nonneg (by rintro t ⟨x, -, -, rfl⟩; exact norm_nonneg x)`. Establish `hla : 0 < X.la1 ^ 2`.

Break down `(sq_nonneg X.la1).lt_or_eq with h | h` into its components or cases. Conclude with `h`. Rewrite `hph2` using `[← h]`. Simplify using `at hph2`. Establish `hC1` using `P.C1`.

Establish `hom : (1 : ℝ) ≤ omStar (E` using `E) := by`. Unfold `omStar`. Use `first`. Consider the case `nlinarith [Real.one_le_rpow hF (by norm_num : (0 : ℝ) ≤ 3 / 2)]`. Consider the case `nlinarith [one_le_pow₀ (n := 3 / 2) hF]`.

Consider the case `(norm_num; nlinarith)`. Establish `hZ : (1 : ℝ) ≤ ((dstar (E` using `E) P.m : ℕ) : ℝ) ^ 2 * omStar (E := E) := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd1) hom`. Establish `h2` using `mul_self_lt_mul_self hL0 hlt`. Establish `hth : X.la1 ^ 2 < 1`. Use polynomial arithmetic with `[hC1, hZ, h2, mul_nonneg (sub_nonneg.mpr hZ) (lt_of_le_of_lt (mul_self_nonneg X.la1) h2).le]`.

Establish `hK1 : 1 ≤ P.ka0 * P.ph`. Unfold `Par.ka0 Par.ph PT.ph RR`. Rewrite using `[if_pos hlt]`. Establish `hden : PT.rd E ^ 2 * X.la1 ^ 2 ≠ 0` using `(mul_pos (pow_pos hR0 2) hla).ne'`. Establish `hY` using `div_mul_cancel₀ (2 * (PT.f E : ℝ)) hden`.

Use `set Y : ℝ := 2 * (PT.f E : ℝ) / (PT.rd E ^ 2 * X.la1 ^ 2) with hYd`. Establish `hY0 : 0 < Y` using `hph2`. Establish `h5 : 2 * (PT.f E : ℝ) ≤ Y * PT.rd E ^ 2`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hth.le) (mul_pos hY0 (pow_pos hR0 2)).le]`. Establish `h6 : (1 : ℝ) ≤ PT.rd E ^ 5 * ((dstar (E` using `E) P.m : ℕ) : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ hd1)`.

Use polynomial arithmetic with `[mul_le_mul h6 h5 (by positivity) (by linarith)]`. Use `set K : ℝ := P.ka0 * P.ph with hKd`. Establish `hK0 : 0 ≤ K` using `by linarith`. Establish `hsK : 1 ≤ √K`. Rewrite using `[show (1 : ℝ) = √1 from Real.sqrt_one.symm]`.

Conclude with `Real.sqrt_le_sqrt hK1`. Establish `e1` using `by first`. Consider the case `exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hU) n`. Consider the case `exact pow_le_pow_left (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hU) n`. Establish `e2 : √K ^ n ≤ √K ^ (dstar (E` using `E) P.m) := by first`.

Consider the case `exact pow_le_pow_right₀ hsK hn`. Consider the case `exact pow_le_pow_right hsK hn`. Establish `hcK : 1 ≤ c * √K ^ (dstar (E` using `E) P.m) := h1.trans (mul_le_mul_of_nonneg_left (e1.trans e2) hc.le)`. Establish `hpow : (K ^ (((dstar (E` using `E) P.m : ℕ) : ℝ) / 4)) ^ 2 = √K ^ (dstar (E := E) P.m) := by`. Rewrite using `[Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast (K ^ (1 / 2 : ℝ)), ← Real.rpow_mul hK0, ← Real.rpow_mul hK0]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hE : (1 : ℝ) ≤ Real.exp ((dstar (E` using `E) P.m : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (-(n : ℝ) / 2) := by`. Rewrite using `[Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul, ← Real.exp_add]`.

Use `le_trans ?_ (Real.add_one_le_exp _)` and prove the remaining obligations. Establish `hl2 : Real.log 2 ≤ 1`. Use `Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hl0 : 0 ≤ Real.log 2` using `Real.log_nonneg (by norm_num)`.

Establish `hnd : (n : ℝ) ≤ ((dstar (E` using `E) P.m : ℕ) : ℝ) := by exact_mod_cast hn`. Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Use `push_cast`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hl2 hn0]`. Establish `hc2 : 0 < c * (2 : ℝ) ^ (-(n : ℝ) / 2)` using `mul_pos hc (Real.rpow_pos_of_pos (by norm_num) _)`.

Establish `hA : 0 < √(c * (2 : ℝ) ^ (-(n : ℝ) / 2))` using `Real.sqrt_pos.mpr hc2`. Rewrite using `[div_le_iff₀ hA]`. Establish `hx0 : 0 ≤ Real.exp ((dstar (E` using `E) P.m : ℕ) : ℝ) * K ^ (((dstar (E := E) P.m : ℕ) : ℝ) / 4) * √(c * (2 : ℝ) ^ (-(n : ℝ) / 2)) := mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hK0 _)) (Real.sqrt_nonneg _)`. Establish `hsq : (Real.exp ((dstar (E` using `E) P.m : ℕ) : ℝ) * K ^ (((dstar (E := E) P.m : ℕ) : ℝ) / 4) * √(c * (2 : ℝ) ^ (-(n : ℝ) / 2))) ^ 2 = (c * √K ^ (dstar (E := E) P.m)) * (Real.exp ((dstar (E := E) P.m : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (-(n : ℝ) / 2)) := by`. Rewrite using `[mul_pow, mul_pow, Real.sq_sqrt hc2.le, hpow]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hge` using `one_le_mul_of_one_le_of_one_le hcK hE`. Rewrite `hge` using `[← hsq]`. Use polynomial arithmetic with `[hge, hx0]`.
-/
theorem tof_inv_sqrt_le [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (hph : 0 < P.ph) (n : ℕ)
    (hn : n ≤ dstar (E := E) P.m) (c : ℝ) (hc : 0 < c)
    (h1 : 1 ≤ c * Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ n) :
    1 / Real.sqrt (c * (2 : ℝ) ^ (-(n : ℝ) / 2)) ≤
      Real.exp (dstar (E := E) P.m) * (P.ka0 * P.ph) ^ ((dstar (E := E) P.m : ℝ) / 4) := by
  have hU := short_vector_bound_le_kappa P hph
  have hf1 : 1 ≤ PT.f E := le_trans (Nat.one_le_pow 4 P.m P.hm1) P.hmf
  have hF : (1 : ℝ) ≤ PT.f E := by exact_mod_cast hf1
  have hR : (16 : ℝ) ≤ PT.rd E := P.hrd
  have hR0 : (0 : ℝ) < PT.rd E := by linarith
  have hdR : ((dstar (E := E) P.m : ℕ) : ℝ) = 2 * (PT.f E : ℝ) * P.m := by
    unfold dstar; push_cast; ring
  have hm1 : (1 : ℝ) ≤ P.m := by exact_mod_cast P.hm1
  have hd1 : (1 : ℝ) ≤ ((dstar (E := E) P.m : ℕ) : ℝ) := by rw [hdR]; nlinarith
  have hph2 := hph
  unfold Par.ph PT.ph at hph2
  split_ifs at hph2 with hlt
  swap
  · exact absurd hph2 (lt_irrefl 0)
  have hL0 : 0 ≤ X.la1 := by
    unfold PT.la1
    exact Real.sInf_nonneg (by rintro t ⟨x, -, -, rfl⟩; exact norm_nonneg x)
  have hla : 0 < X.la1 ^ 2 := by
    rcases (sq_nonneg X.la1).lt_or_eq with h | h
    · exact h
    · rw [← h] at hph2; simp at hph2
  have hC1 := P.C1
  have hom : (1 : ℝ) ≤ omStar (E := E) := by
    unfold omStar
    first
      | nlinarith [Real.one_le_rpow hF (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      | nlinarith [one_le_pow₀ (n := 3 / 2) hF]
      | (norm_num; nlinarith)
  have hZ : (1 : ℝ) ≤ ((dstar (E := E) P.m : ℕ) : ℝ) ^ 2 * omStar (E := E) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd1) hom
  have h2 := mul_self_lt_mul_self hL0 hlt
  have hth : X.la1 ^ 2 < 1 := by
    nlinarith [hC1, hZ, h2, mul_nonneg (sub_nonneg.mpr hZ) (lt_of_le_of_lt (mul_self_nonneg X.la1) h2).le]
  have hK1 : 1 ≤ P.ka0 * P.ph := by
    unfold Par.ka0 Par.ph PT.ph RR
    rw [if_pos hlt]
    have hden : PT.rd E ^ 2 * X.la1 ^ 2 ≠ 0 := (mul_pos (pow_pos hR0 2) hla).ne'
    have hY := div_mul_cancel₀ (2 * (PT.f E : ℝ)) hden
    set Y : ℝ := 2 * (PT.f E : ℝ) / (PT.rd E ^ 2 * X.la1 ^ 2) with hYd
    have hY0 : 0 < Y := hph2
    have h5 : 2 * (PT.f E : ℝ) ≤ Y * PT.rd E ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hth.le) (mul_pos hY0 (pow_pos hR0 2)).le]
    have h6 : (1 : ℝ) ≤ PT.rd E ^ 5 * ((dstar (E := E) P.m : ℕ) : ℝ) ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ hd1)
    nlinarith [mul_le_mul h6 h5 (by positivity) (by linarith)]
  set K : ℝ := P.ka0 * P.ph with hKd
  have hK0 : 0 ≤ K := by linarith
  have hsK : 1 ≤ √K := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hK1
  have e1 := by
    first
      | exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hU) n
      | exact pow_le_pow_left (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hU) n
  have e2 : √K ^ n ≤ √K ^ (dstar (E := E) P.m) := by
    first
      | exact pow_le_pow_right₀ hsK hn
      | exact pow_le_pow_right hsK hn
  have hcK : 1 ≤ c * √K ^ (dstar (E := E) P.m) :=
    h1.trans (mul_le_mul_of_nonneg_left (e1.trans e2) hc.le)
  have hpow : (K ^ (((dstar (E := E) P.m : ℕ) : ℝ) / 4)) ^ 2 = √K ^ (dstar (E := E) P.m) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast (K ^ (1 / 2 : ℝ)),
      ← Real.rpow_mul hK0, ← Real.rpow_mul hK0]
    congr 1
    push_cast
    ring
  have hE : (1 : ℝ) ≤ Real.exp ((dstar (E := E) P.m : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (-(n : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul, ← Real.exp_add]
    refine le_trans ?_ (Real.add_one_le_exp _)
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hnd : (n : ℝ) ≤ ((dstar (E := E) P.m : ℕ) : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hl2 hn0]
  have hc2 : 0 < c * (2 : ℝ) ^ (-(n : ℝ) / 2) := mul_pos hc (Real.rpow_pos_of_pos (by norm_num) _)
  have hA : 0 < √(c * (2 : ℝ) ^ (-(n : ℝ) / 2)) := Real.sqrt_pos.mpr hc2
  rw [div_le_iff₀ hA]
  have hx0 : 0 ≤ Real.exp ((dstar (E := E) P.m : ℕ) : ℝ) * K ^ (((dstar (E := E) P.m : ℕ) : ℝ) / 4) *
      √(c * (2 : ℝ) ^ (-(n : ℝ) / 2)) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hK0 _)) (Real.sqrt_nonneg _)
  have hsq : (Real.exp ((dstar (E := E) P.m : ℕ) : ℝ) * K ^ (((dstar (E := E) P.m : ℕ) : ℝ) / 4) *
      √(c * (2 : ℝ) ^ (-(n : ℝ) / 2))) ^ 2 =
      (c * √K ^ (dstar (E := E) P.m)) *
        (Real.exp ((dstar (E := E) P.m : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (-(n : ℝ) / 2)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hc2.le, hpow]
    ring
  have hge := one_le_mul_of_one_le_of_one_le hcK hE
  rw [← hsq] at hge
  nlinarith [hge, hx0]

end

end ReciprocityTheory.ChartRestriction.G.I2
