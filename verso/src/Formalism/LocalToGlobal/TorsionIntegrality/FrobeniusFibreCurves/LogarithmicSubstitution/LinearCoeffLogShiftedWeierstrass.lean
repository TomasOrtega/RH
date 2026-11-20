import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalD
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementI

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.Iso

open PowerSeries
open Formalism.L2.Th1.C (wpShift HasSecondLogDeriv)

/- English proof (translation)
Introduce `G _ G1 β β' hβ hβ' hinj t0 t' t'' h0 h1 h2 h3 h4`. Establish `key : t0 ∉ G1`. Introduce `hm`. Establish `h5 : β' t0 = t''` using `by rw [h0, map_add, h1, h2, zero_add]`. Establish `h6 : t'' ∈ G1` using `h5 ▸ hβ' t0 hm`.

Conclude with `h3 (hinj t'' h6 h4)`. Use `⟨key, ?_⟩` and prove the remaining obligations. Introduce `Q hQ hm`. Conclude with `key (hQ ▸ hβ Q hm)`.
-/
theorem curve_not_reduced : NotReduce := by
  intro G _ G1 β β' hβ hβ' hinj t0 t' t'' h0 h1 h2 h3 h4
  have key : t0 ∉ G1 := by
    intro hm
    have h5 : β' t0 = t'' := by rw [h0, map_add, h1, h2, zero_add]
    have h6 : t'' ∈ G1 := h5 ▸ hβ' t0 hm
    exact h3 (hinj t'' h6 h4)
  refine ⟨key, ?_⟩
  intro Q hQ hm
  exact key (hQ ▸ hβ Q hm)

variable {K : Type} [Field K] [CharZero K]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[dz, coeff_derivative, coeff_rescale, coeff_C_mul, coeff_rescale, coeff_derivative]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dz_rescale (a : K) (f : PowerSeries K) :
    dz (rescale a f) = C a * rescale a (dz f) := by
  ext n
  rw [dz, coeff_derivative, coeff_rescale, coeff_C_mul, coeff_rescale, coeff_derivative]
  ring

/- English proof (translation)
Rewrite using `[dz_rescale, dz_mul, dz_C, dz_rescale, map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem second_derivative_rescale (a : K) (f : PowerSeries K) :
    dz (dz (rescale a f)) = C (a ^ 2) * rescale a (dz (dz f)) := by
  rw [dz_rescale, dz_mul, dz_C, dz_rescale, map_pow]
  ring

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[coeff_rescale, coeff_C]`. Use `split_ifs with h`. Rewrite using `[h, pow_zero, one_mul]`. Rewrite using `[mul_zero]`.
-/
theorem rescale_C' (a c : K) : rescale a (C c : PowerSeries K) = C c := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h
  · rw [h, pow_zero, one_mul]
  · rw [mul_zero]

/- English proof (translation)
The claim follows from `map_nsmul _ n f`.
-/
theorem dz_nsmul (n : ℕ) (f : PowerSeries K) : dz (n • f) = n • dz f := map_nsmul _ n f

/- English proof (translation)
Rewrite using `[dz_nsmul, dz_nsmul]`.
-/
theorem second_derivative_nsmul (n : ℕ) (f : PowerSeries K) : dz (dz (n • f)) = n • dz (dz f) := by
  rw [dz_nsmul, dz_nsmul]

/- English proof (translation)
Establish `h : fExp (0 : PowerSeries K) * fExp (0 : PowerSeries K) = fExp (0 : PowerSeries K)`. Rewrite using `[← fExp_add (map_zero _) (map_zero _), add_zero]`. Establish `h1 : constantCoeff (fExp (0 : PowerSeries K)) = 1` using `constantCoeff_fExp (map_zero _)`. Establish `hne : fExp (0 : PowerSeries K) ≠ 0` using `ne_zero_of_constantCoeff (by rw [h1]; exact one_ne_zero)`. Conclude with `mul_left_cancel₀ hne (by rw [h, mul_one])`.
-/
theorem fExp_zero : fExp (0 : PowerSeries K) = 1 := by
  have h : fExp (0 : PowerSeries K) * fExp (0 : PowerSeries K) = fExp (0 : PowerSeries K) := by
    rw [← fExp_add (map_zero _) (map_zero _), add_zero]
  have h1 : constantCoeff (fExp (0 : PowerSeries K)) = 1 := constantCoeff_fExp (map_zero _)
  have hne : fExp (0 : PowerSeries K) ≠ 0 := ne_zero_of_constantCoeff (by rw [h1]; exact one_ne_zero)
  exact mul_left_cancel₀ hne (by rw [h, mul_one])

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_smul, pow_zero, fExp_zero]`. Consider the case `succ m ih`. Establish `hm : constantCoeff (m • f) = 0` using `by rw [map_nsmul, hf, smul_zero]`. Rewrite using `[succ_nsmul, fExp_add hm hf, ih, pow_succ]`.
-/
theorem fExp_nsmul {f : PowerSeries K} (hf : constantCoeff f = 0) (n : ℕ) :
    fExp (n • f) = fExp f ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, fExp_zero]
  | succ m ih =>
    have hm : constantCoeff (m • f) = 0 := by rw [map_nsmul, hf, smul_zero]
    rw [succ_nsmul, fExp_add hm hf, ih, pow_succ]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty, Finset.prod_empty, fExp_zero]`. Consider the case `insert a s ha ih`. Establish `hs : constantCoeff (∑ i ∈ s, f i) = 0`. Rewrite using `[map_sum]`.

Conclude with `Finset.sum_eq_zero fun i _ => hf i`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha, fExp_add (hf a) hs, ih]`.
-/
theorem fExp_sum {ι : Type} (s : Finset ι) (f : ι → PowerSeries K)
    (hf : ∀ i, constantCoeff (f i) = 0) : fExp (∑ i ∈ s, f i) = ∏ i ∈ s, fExp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, fExp_zero]
  | insert a s ha ih =>
    have hs : constantCoeff (∑ i ∈ s, f i) = 0 := by
      rw [map_sum]; exact Finset.sum_eq_zero fun i _ => hf i
    rw [Finset.sum_insert ha, Finset.prod_insert ha, fExp_add (hf a) hs, ih]

/- English proof (translation)
Establish `hne : f ≠ 0` using `ne_zero_of_constantCoeff (by rw [hf]; exact one_ne_zero)`. Establish `hL1 : f * dz (fLog f) = dz f` using `Sq.mul_dz_fLog hf`. Establish `hL2 : f * dz (dz (fLog f)) + dz (fLog f) * dz f = dz (dz f)`. Use `congrArg dz hL1` as an intermediate fact. Rewrite `this` using `[dz_mul]`. Then use the resulting hypothesis.

Establish `h' : dz (dz f) * f - dz f ^ 2 = g * f ^ 2` using `h`. Apply `mul_left_cancel₀ (pow_ne_zero 2 hne)` to reduce the goal to its premises. Take the linear combination `f * hL2 - dz f * hL1 + h'`.
-/
theorem second_derivative_formal_log {f g : PowerSeries K} (hf : constantCoeff f = 1) (h : HasSecondLogDeriv f g) :
    dz (dz (fLog f)) = g := by
  have hne : f ≠ 0 := ne_zero_of_constantCoeff (by rw [hf]; exact one_ne_zero)
  have hL1 : f * dz (fLog f) = dz f := Sq.mul_dz_fLog hf
  have hL2 : f * dz (dz (fLog f)) + dz (fLog f) * dz f = dz (dz f) := by
    have := congrArg dz hL1
    rwa [dz_mul] at this
  have h' : dz (dz f) * f - dz f ^ 2 = g * f ^ 2 := h
  apply mul_left_cancel₀ (pow_ne_zero 2 hne)
  linear_combination f * hL2 - dz f * hL1 + h'

/- English proof (translation)
Simplify using `[wpShift]`.
-/
theorem constantCoeff_wpShift (P : PowerSeries K) (c : K) : constantCoeff (wpShift P c) = 1 := by
  simp [wpShift]

/- English proof (translation)
Use `dz_X_pow (K := K) 1` as an intermediate fact. Move the coercions through the operations in `at this`. Take the linear combination `this`.
-/
theorem dz_X_sq : dz ((X : PowerSeries K) ^ 2) = 2 * X := by
  have := dz_X_pow (K := K) 1; push_cast at this; linear_combination this

/- English proof (translation)
Establish `h` using `congrArg constantCoeff (Sq.mul_dz_fLog (constantCoeff_wpShift P c))`. Rewrite `h` using `[map_mul, constantCoeff_wpShift, one_mul]`. Rewrite using `[h, wpShift, dz_add, dz_mul, dz_one, dz_X_sq]`. Simplify using the standard rewrite rules.
-/
theorem linear_coeff_log_shifted_weierstrass (P : PowerSeries K) (c : K) :
    constantCoeff (dz (fLog (wpShift P c))) = 0 := by
  have h := congrArg constantCoeff (Sq.mul_dz_fLog (constantCoeff_wpShift P c))
  rw [map_mul, constantCoeff_wpShift, one_mul] at h
  rw [h, wpShift, dz_add, dz_mul, dz_one, dz_X_sq]
  simp

/- English proof (translation)
Take `⟨hF1, hF2⟩` from `weierstrassReducedEquations K g2 g3 P hP`. Establish `hZW : wpShift P e1 = 1 + X ^ 2 * P - C e1 * X ^ 2` using `by rw [wpShift]; ring`. Rewrite using `[hZW]`. Use `set Ze : PowerSeries K := 1 + X ^ 2 * P - C e1 * X ^ 2 with hZe`. Establish `hZ0 : constantCoeff Ze = 1` using `by simp [hZe]`.

Establish `hZ0' : constantCoeff Ze ≠ 0` using `by rw [hZ0]; exact one_ne_zero`. Establish `hw : wOf e1 P * Ze = X ^ 2`. Unfold `wOf`. Rewrite using `[mul_assoc, PowerSeries.inv_mul_cancel _ hZ0', mul_one]`. Establish `e2 : dz ((X : PowerSeries K) ^ 2) = 2 * X` using `dz_X_sq`.

Establish `hZ1 : dz Ze = X ^ 2 * dz P + P * (2 * X) - C e1 * (2 * X)`. Rewrite using `[hZe]`. Simplify using `only [dz_sub, dz_add, dz_mul, dz_one, dz_C, e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hZ2 : dz (dz Ze) = X ^ 2 * dz (dz P) + 4 * X * dz P + 2 * P - 2 * C e1`.

Rewrite using `[hZ1]`. Simplify using `only [dz_sub, dz_add, dz_mul, dz_two, dz_X, dz_C, e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `c2 : 2 * (C (3 * e1 ^ 2 - g2 / 4) : PowerSeries K) = 6 * C e1 ^ 2 - C (g2 / 2)`. Simplify using `only [← map_ofNat (C (R := K)), ← map_mul, ← map_pow, ← map_sub]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `c3 : 2 * C (g2 / 2) = (C g2 : PowerSeries K)`. Rewrite using `[← map_ofNat (C (R := K)) 2, ← map_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `he' : 4 * (C e1 : PowerSeries K) ^ 3 - C g2 * C e1 - C g3 = 0`. Simplify using `only [← map_ofNat (C (R := K)), ← map_mul, ← map_pow, ← map_sub]`. Rewrite using `[he, map_zero]`. Generalize the expression as in `3 * e1 ^ 2 - g2 / 4 = kap at c2 ⊢`.

Establish `hB : Ze * dz (dz Ze) - dz Ze ^ 2 = (2 * P - 2 * C e1) * Ze ^ 2 - 2 * C kap * X ^ 2 * Ze`. Rewrite using `[hZ2, hZ1, hZe]`. Take the linear combination `(-1 : PowerSeries K) * hF1 + (1 + X ^ 2 * P - C e1 * X ^ 2) * hF2 - X ^ 4 * he' + X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) * c2 - X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) * c3`. Use `show dz (dz Ze) * Ze - dz Ze ^ 2 = _`. Take the linear combination `hB + 2 * C kap * Ze * hw`.
-/
theorem second_log_derivative_two_isogeny (g2 g3 e1 : K) (P : PowerSeries K) (hP : IsWp g2 g3 P)
    (he : 4 * e1 ^ 3 - g2 * e1 - g3 = 0) :
    HasSecondLogDeriv (wpShift P e1) (2 * P - 2 * (C e1 + C (3 * e1 ^ 2 - g2 / 4) * wOf e1 P)) := by
  obtain ⟨hF1, hF2⟩ := weierstrassReducedEquations K g2 g3 P hP
  have hZW : wpShift P e1 = 1 + X ^ 2 * P - C e1 * X ^ 2 := by rw [wpShift]; ring
  rw [hZW]
  set Ze : PowerSeries K := 1 + X ^ 2 * P - C e1 * X ^ 2 with hZe
  have hZ0 : constantCoeff Ze = 1 := by simp [hZe]
  have hZ0' : constantCoeff Ze ≠ 0 := by rw [hZ0]; exact one_ne_zero
  have hw : wOf e1 P * Ze = X ^ 2 := by
    unfold wOf
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ hZ0', mul_one]
  have e2 : dz ((X : PowerSeries K) ^ 2) = 2 * X := dz_X_sq
  have hZ1 : dz Ze = X ^ 2 * dz P + P * (2 * X) - C e1 * (2 * X) := by
    rw [hZe]; simp only [dz_sub, dz_add, dz_mul, dz_one, dz_C, e2]; ring
  have hZ2 : dz (dz Ze) = X ^ 2 * dz (dz P) + 4 * X * dz P + 2 * P - 2 * C e1 := by
    rw [hZ1]; simp only [dz_sub, dz_add, dz_mul, dz_two, dz_X, dz_C, e2]; ring
  have c2 : 2 * (C (3 * e1 ^ 2 - g2 / 4) : PowerSeries K) = 6 * C e1 ^ 2 - C (g2 / 2) := by
    simp only [← map_ofNat (C (R := K)), ← map_mul, ← map_pow, ← map_sub]; congr 1; ring
  have c3 : 2 * C (g2 / 2) = (C g2 : PowerSeries K) := by
    rw [← map_ofNat (C (R := K)) 2, ← map_mul]; congr 1; ring
  have he' : 4 * (C e1 : PowerSeries K) ^ 3 - C g2 * C e1 - C g3 = 0 := by
    simp only [← map_ofNat (C (R := K)), ← map_mul, ← map_pow, ← map_sub]; rw [he, map_zero]
  generalize 3 * e1 ^ 2 - g2 / 4 = kap at c2 ⊢
  have hB : Ze * dz (dz Ze) - dz Ze ^ 2 =
      (2 * P - 2 * C e1) * Ze ^ 2 - 2 * C kap * X ^ 2 * Ze := by
    rw [hZ2, hZ1, hZe]
    linear_combination (-1 : PowerSeries K) * hF1 + (1 + X ^ 2 * P - C e1 * X ^ 2) * hF2 -
      X ^ 4 * he' + X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) * c2 -
      X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) * c3
  show dz (dz Ze) * Ze - dz Ze ^ 2 = _
  linear_combination hB + 2 * C kap * Ze * hw

/- English proof (translation)
Introduce `K _ _ g2 g3 s2 c0 xT al S P ι _ c wp wm hP he hF hS`. Take `⟨hF1, hF2⟩` from `hF`. Establish `hD` using `second_log_derivative_two_isogeny g2 g3 (xT + c0) P hP he`. Unfold `thTw thZ sigma1`. Generalize the expression as in `xT + c0 = e1 at *`.

Generalize the expression as in `3 * e1 ^ 2 - g2 / 4 = kap at *`. Generalize the expression as in `wOf e1 P = w at *`. Use `set n : ℕ := Fintype.card ι with hn`. Establish `hS1 : constantCoeff (sigmaOneSeries e1 kap w) = 0` using `Sq.constantCoeff_sig1S _ _ _`. Establish `hq : constantCoeff (-(C (s2 / 2) * X ^ 2) : PowerSeries K) = 0` using `by simp`.

Rewrite using `[← fExp_add hS1 hq]`. Use `set abelian₂ : PowerSeries K := sigmaOneSeries e1 kap w + -(C (s2 / 2) * X ^ 2) with hLam`. Establish `hL0 : constantCoeff abelian₂ = 0` using `by rw [hLam, map_add, hS1, hq, add_zero]`. Establish `hL1 : dz abelian₂ = -prim (C e1 + C kap * w) - C s2 * X`. Establish `c3 : 2 * C (s2 / 2) = (C s2 : PowerSeries K)`.

Rewrite using `[← map_ofNat (C (R := K)) 2, ← map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hLam, sigmaOneSeries]`. Simplify using `only [dz_add, dz_neg, dz_prim, dz_mul, dz_C, dz_X_sq]`.

Take the linear combination `(-X : PowerSeries K) * c3`. Establish `hL2 : dz (dz abelian₂) = -(C e1 + C kap * w) - C s2`. Rewrite using `[hL1]`. Simplify using `only [dz_sub, dz_neg, dz_prim, dz_mul, dz_C, dz_X]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hL1c : constantCoeff (dz abelian₂) = 0`. Rewrite using `[hL1]`. Simplify using `[constantCoeff_prim]`. Establish `hR0 : constantCoeff (rescale al abelian₂) = 0`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply, hL0, mul_zero]`.

Establish `hZ1 : ∀ a : K, constantCoeff (wpShift P a) = 1` using `constantCoeff_wpShift P`. Establish `hZl : ∀ a : K, constantCoeff (fLog (wpShift P a)) = 0` using `fun a => constantCoeff_fLog (hZ1 a)`. Use `clear_value abelian₂`. Establish `key : rescale al abelian₂ + n • fLog (wpShift P e1) = (2 * n) • abelian₂ + ∑ Q, fLog (wpShift P (c Q))`. Use `derivative.ext (derivative.ext ?_ ?_) ?_` and prove the remaining obligations.

Use `show dz (dz _) = dz (dz _)`. Establish `hsum : dz (dz (∑ Q, fLog (wpShift P (c Q)))) = ∑ Q, (2 * P - wp Q - wm Q)`. Rewrite using `[dz, dz, map_sum, map_sum]`. Conclude with `Finset.sum_congr rfl fun Q _ => second_derivative_formal_log (hZ1 _) (hF1 Q)`. Establish `hsum2 : ∑ Q, (2 * P - wp Q - wm Q) = (n : PowerSeries K) * (2 * P) - ∑ Q, (wp Q + wm Q)`.

Establish `: ∀ Q, 2 * P - wp Q - wm Q = 2 * P - (wp Q + wm Q)` using `fun Q => by ring`. Rewrite using `[Finset.sum_congr rfl fun Q _ => this Q, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Establish `hSC : C (al ^ 2) * C s2 - 2 * (n : PowerSeries K) * C s2 = C S`. Rewrite using `[← hS, ← map_natCast (C (R := K)) n, ← map_ofNat (C (R := K)) 2]`. Simplify using `only [← map_mul, ← map_sub]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[dz_add, dz_add, dz_add, dz_add, hsum, hsum2, second_derivative_rescale, hL2, second_derivative_nsmul, second_derivative_nsmul, hL2, second_derivative_formal_log (hZ1 _) hD, map_sub, map_neg, rescale_C', nsmul_eq_mul, nsmul_eq_mul]`. Use `push_cast`. Take the linear combination `(-1 : PowerSeries K) * hF2 - hSC`.

Use `show constantCoeff (dz _) = constantCoeff (dz _)`. Establish `hsum : constantCoeff (dz (∑ Q, fLog (wpShift P (c Q)))) = 0`. Rewrite using `[dz, map_sum, map_sum]`. Conclude with `Finset.sum_eq_zero fun Q _ => linear_coeff_log_shifted_weierstrass P _`. Establish `hr : constantCoeff (rescale al (dz abelian₂)) = 0`.

Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply, hL1c, mul_zero]`. Rewrite using `[dz_add, dz_add, map_add, map_add, hsum, dz_rescale, map_mul, hr, dz_nsmul, dz_nsmul, map_nsmul, map_nsmul, linear_coeff_log_shifted_weierstrass, hL1c]`. Simplify using the standard rewrite rules. Rewrite using `[map_add, map_add, hR0, map_nsmul, map_nsmul, hZl, hL0, map_sum, Finset.sum_eq_zero fun Q _ => hZl _]`. Simplify using the standard rewrite rules.

Rewrite using `[Sq.rescale_fExp al hL0]`. Establish `e1' : wpShift P e1 ^ n = fExp (n • fLog (wpShift P e1))`. Rewrite using `[fExp_nsmul (hZl _), fExp_fLog (hZ1 _)]`. Establish `e2' : ∏ Q, wpShift P (c Q) = fExp (∑ Q, fLog (wpShift P (c Q)))`. Rewrite using `[fExp_sum _ _ (fun Q => hZl _)]`.

Conclude with `Finset.prod_congr rfl fun Q _ => (fExp_fLog (hZ1 _)).symm`. Establish `hn0 : constantCoeff (n • fLog (wpShift P e1)) = 0` using `by rw [map_nsmul, hZl, smul_zero]`. Establish `hn1 : constantCoeff ((2 * n) • abelian₂) = 0` using `by rw [map_nsmul, hL0, smul_zero]`. Establish `hn2 : constantCoeff (∑ Q, fLog (wpShift P (c Q))) = 0`. Rewrite using `[map_sum]`.

Conclude with `Finset.sum_eq_zero fun Q _ => hZl _`. Rewrite using `[e1', e2', ← fExp_nsmul hL0, ← fExp_add hR0 hn0, ← fExp_add hn1 hn2, key]`.
-/
theorem theta_zero_isogeny_holds : Th0Isogeny := by
  intro K _ _ g2 g3 s2 c0 xT al S P ι _ c wp wm hP he hF hS
  obtain ⟨hF1, hF2⟩ := hF
  have hD := second_log_derivative_two_isogeny g2 g3 (xT + c0) P hP he
  unfold thTw thZ sigma1
  generalize xT + c0 = e1 at *
  generalize 3 * e1 ^ 2 - g2 / 4 = kap at *
  generalize wOf e1 P = w at *
  set n : ℕ := Fintype.card ι with hn
  have hS1 : constantCoeff (sigmaOneSeries e1 kap w) = 0 := Sq.constantCoeff_sig1S _ _ _
  have hq : constantCoeff (-(C (s2 / 2) * X ^ 2) : PowerSeries K) = 0 := by simp
  rw [← fExp_add hS1 hq]
  set abelian₂ : PowerSeries K := sigmaOneSeries e1 kap w + -(C (s2 / 2) * X ^ 2) with hLam
  have hL0 : constantCoeff abelian₂ = 0 := by rw [hLam, map_add, hS1, hq, add_zero]
  have hL1 : dz abelian₂ = -prim (C e1 + C kap * w) - C s2 * X := by
    have c3 : 2 * C (s2 / 2) = (C s2 : PowerSeries K) := by
      rw [← map_ofNat (C (R := K)) 2, ← map_mul]; congr 1; ring
    rw [hLam, sigmaOneSeries]
    simp only [dz_add, dz_neg, dz_prim, dz_mul, dz_C, dz_X_sq]
    linear_combination (-X : PowerSeries K) * c3
  have hL2 : dz (dz abelian₂) = -(C e1 + C kap * w) - C s2 := by
    rw [hL1]
    simp only [dz_sub, dz_neg, dz_prim, dz_mul, dz_C, dz_X]
    ring
  have hL1c : constantCoeff (dz abelian₂) = 0 := by
    rw [hL1]; simp [constantCoeff_prim]
  have hR0 : constantCoeff (rescale al abelian₂) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply, hL0,
      mul_zero]
  have hZ1 : ∀ a : K, constantCoeff (wpShift P a) = 1 := constantCoeff_wpShift P
  have hZl : ∀ a : K, constantCoeff (fLog (wpShift P a)) = 0 := fun a => constantCoeff_fLog (hZ1 a)
  clear_value abelian₂
  have key : rescale al abelian₂ + n • fLog (wpShift P e1) =
      (2 * n) • abelian₂ + ∑ Q, fLog (wpShift P (c Q)) := by
    refine derivative.ext (derivative.ext ?_ ?_) ?_
    · show dz (dz _) = dz (dz _)
      have hsum : dz (dz (∑ Q, fLog (wpShift P (c Q)))) = ∑ Q, (2 * P - wp Q - wm Q) := by
        rw [dz, dz, map_sum, map_sum]
        exact Finset.sum_congr rfl fun Q _ => second_derivative_formal_log (hZ1 _) (hF1 Q)
      have hsum2 : ∑ Q, (2 * P - wp Q - wm Q) =
          (n : PowerSeries K) * (2 * P) - ∑ Q, (wp Q + wm Q) := by
        have : ∀ Q, 2 * P - wp Q - wm Q = 2 * P - (wp Q + wm Q) := fun Q => by ring
        rw [Finset.sum_congr rfl fun Q _ => this Q, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
      have hSC : C (al ^ 2) * C s2 - 2 * (n : PowerSeries K) * C s2 = C S := by
        rw [← hS, ← map_natCast (C (R := K)) n, ← map_ofNat (C (R := K)) 2]
        simp only [← map_mul, ← map_sub]
        congr 1; ring
      rw [dz_add, dz_add, dz_add, dz_add, hsum, hsum2, second_derivative_rescale, hL2, second_derivative_nsmul, second_derivative_nsmul, hL2,
        second_derivative_formal_log (hZ1 _) hD, map_sub, map_neg, rescale_C', nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      linear_combination (-1 : PowerSeries K) * hF2 - hSC
    · show constantCoeff (dz _) = constantCoeff (dz _)
      have hsum : constantCoeff (dz (∑ Q, fLog (wpShift P (c Q)))) = 0 := by
        rw [dz, map_sum, map_sum]
        exact Finset.sum_eq_zero fun Q _ => linear_coeff_log_shifted_weierstrass P _
      have hr : constantCoeff (rescale al (dz abelian₂)) = 0 := by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply,
          hL1c, mul_zero]
      rw [dz_add, dz_add, map_add, map_add, hsum, dz_rescale, map_mul, hr, dz_nsmul, dz_nsmul,
        map_nsmul, map_nsmul, linear_coeff_log_shifted_weierstrass, hL1c]
      simp
    · rw [map_add, map_add, hR0, map_nsmul, map_nsmul, hZl, hL0, map_sum,
        Finset.sum_eq_zero fun Q _ => hZl _]
      simp
  rw [Sq.rescale_fExp al hL0]
  have e1' : wpShift P e1 ^ n = fExp (n • fLog (wpShift P e1)) := by
    rw [fExp_nsmul (hZl _), fExp_fLog (hZ1 _)]
  have e2' : ∏ Q, wpShift P (c Q) = fExp (∑ Q, fLog (wpShift P (c Q))) := by
    rw [fExp_sum _ _ (fun Q => hZl _)]
    exact Finset.prod_congr rfl fun Q _ => (fExp_fLog (hZ1 _)).symm
  have hn0 : constantCoeff (n • fLog (wpShift P e1)) = 0 := by rw [map_nsmul, hZl, smul_zero]
  have hn1 : constantCoeff ((2 * n) • abelian₂) = 0 := by rw [map_nsmul, hL0, smul_zero]
  have hn2 : constantCoeff (∑ Q, fLog (wpShift P (c Q))) = 0 := by
    rw [map_sum]; exact Finset.sum_eq_zero fun Q _ => hZl _
  rw [e1', e2', ← fExp_nsmul hL0, ← fExp_add hR0 hn0, ← fExp_add hn1 hn2, key]

end Formalism.L2.Th1.B.Iso
