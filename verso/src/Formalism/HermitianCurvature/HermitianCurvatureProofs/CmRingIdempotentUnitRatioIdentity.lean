import Formalism.HermitianCurvature.StatementSz

open Formalism.FourierDecayAlt.Sz Finset

namespace Formalism.FourierDecayAlt.P

namespace Sz8

/- English proof (translation)
Establish `h1 : ∏ w, F w ≤ ∏ w, (K * t w)` using `Finset.prod_le_prod (fun w _ => (hF w).1) (fun w _ => (hF w).2)`. Rewrite `h1` using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]`. Establish `h2 : K ^ Fintype.card ι * ∏ w, t w ≤ K ^ Fintype.card ι * Ct` using `mul_le_mul_of_nonneg_left ht (pow_nonneg hK _)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma prodBound {ι : Type} [Fintype ι] (F t : ι → ℝ) (K Ct : ℝ) (hK : 0 ≤ K)
    (hF : ∀ w, 0 ≤ F w ∧ F w ≤ K * t w) (ht : ∏ w, t w ≤ Ct) :
    ∏ w, F w ≤ Ct * K ^ Fintype.card ι := by
  have h1 : ∏ w, F w ≤ ∏ w, (K * t w) :=
    Finset.prod_le_prod (fun w _ => (hF w).1) (fun w _ => (hF w).2)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at h1
  have h2 : K ^ Fintype.card ι * ∏ w, t w ≤ K ^ Fintype.card ι * Ct :=
    mul_le_mul_of_nonneg_left ht (pow_nonneg hK _)
  linarith

/- English proof (translation)
Establish `hTh' : 0 < Th⁻¹` using `inv_pos.mpr hTh`. Establish `hf0 : f ≠ 0` using `by omega`. Establish `hCtf : Ct ≤ Ct ^ f`. Combine the equalities or inequalities in the displayed calculation. Establish `hZf : 0 ≤ Z ^ f` using `pow_nonneg hZ f`.

Establish `key : Th⁻¹ ^ f ≤ (Ct * Z) ^ f`. Rewrite using `[inv_pow, mul_pow]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(pow_le_pow_iff_left₀ hTh'.le (mul_nonneg (by linarith) hZ) hf0).mp key`.
-/
lemma cmRing_idempotent_unitRatio_identity (f : ℕ) (hf : 1 ≤ f) (Ct Z Th : ℝ) (hCt : 1 ≤ Ct) (hZ : 0 ≤ Z) (hTh : 0 < Th)
    (h : (Th ^ f)⁻¹ ≤ Ct * Z ^ f) : Th⁻¹ ≤ Ct * Z := by
  have hTh' : 0 < Th⁻¹ := inv_pos.mpr hTh
  have hf0 : f ≠ 0 := by omega
  have hCtf : Ct ≤ Ct ^ f := by
    calc Ct = Ct ^ 1 := (pow_one Ct).symm
      _ ≤ Ct ^ f := pow_le_pow_right₀ hCt hf
  have hZf : 0 ≤ Z ^ f := pow_nonneg hZ f
  have key : Th⁻¹ ^ f ≤ (Ct * Z) ^ f := by
    rw [inv_pow, mul_pow]
    calc (Th ^ f)⁻¹ ≤ Ct * Z ^ f := h
      _ ≤ Ct ^ f * Z ^ f := mul_le_mul_of_nonneg_right hCtf hZf
  exact (pow_le_pow_iff_left₀ hTh'.le (mul_nonneg (by linarith) hZ) hf0).mp key

/- English proof (translation)
Establish `hk0 : (1:ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hf0 : (1:ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hkpos : (0:ℝ) < k` using `by linarith`. Establish `hfl : 1 ≤ (f:ℝ) * lb` using `by nlinarith`. Establish `e1 : ((k : ℝ) * f * lb) ^ CDel = (k:ℝ) ^ CDel * ((f:ℝ) * lb) ^ CDel`.

Rewrite using `[mul_assoc, Real.mul_rpow hkpos.le (by positivity)]`. Establish `e2 : (k : ℝ) ^ 4 * (k : ℝ) ^ (CDel - 4) = (k:ℝ) ^ CDel`. Establish `: (k:ℝ) ^ (4:ℝ) * (k:ℝ) ^ (CDel - 4) = (k:ℝ) ^ CDel`. Rewrite using `[← Real.rpow_add hkpos]`. Put the polynomial expressions in normal form.

Rewrite using `[← this]`. Use `norm_cast`. Establish `e3 : (f:ℝ) ^ 4 ≤ ((f:ℝ) * lb) ^ CDel`. Combine the equalities or inequalities in the displayed calculation. Apply `pow_le_pow_left₀ (by linarith); nlinarith` to reduce the goal to its premises.

Use `_ = ((f:ℝ) * lb) ^ (4:ℝ) := by norm_cast`. Use `_ ≤ ((f:ℝ) * lb) ^ CDel := Real.rpow_le_rpow_of_exponent_le hfl hC.le`. Establish `hkC : 0 ≤ (k:ℝ) ^ CDel` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma delLower (k f : ℕ) (lb CDel Del : ℝ) (hk : 1 ≤ k) (hf : 1 ≤ f) (hlb : 1 ≤ lb)
    (hC : 4 < CDel) (h : ((k : ℝ) * f * lb) ^ CDel ≤ Del) :
    (k : ℝ) ^ 4 * (f : ℝ) ^ 4 * (k : ℝ) ^ (CDel - 4) ≤ Del := by
  have hk0 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hf0 : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hkpos : (0:ℝ) < k := by linarith
  have hfl : 1 ≤ (f:ℝ) * lb := by nlinarith
  have e1 : ((k : ℝ) * f * lb) ^ CDel = (k:ℝ) ^ CDel * ((f:ℝ) * lb) ^ CDel := by
    rw [mul_assoc, Real.mul_rpow hkpos.le (by positivity)]
  have e2 : (k : ℝ) ^ 4 * (k : ℝ) ^ (CDel - 4) = (k:ℝ) ^ CDel := by
    have : (k:ℝ) ^ (4:ℝ) * (k:ℝ) ^ (CDel - 4) = (k:ℝ) ^ CDel := by
      rw [← Real.rpow_add hkpos]; ring_nf
    rw [← this]; norm_cast
  have e3 : (f:ℝ) ^ 4 ≤ ((f:ℝ) * lb) ^ CDel := by
    calc (f:ℝ) ^ 4 ≤ ((f:ℝ) * lb) ^ 4 := by
          apply pow_le_pow_left₀ (by linarith); nlinarith
      _ = ((f:ℝ) * lb) ^ (4:ℝ) := by norm_cast
      _ ≤ ((f:ℝ) * lb) ^ CDel := Real.rpow_le_rpow_of_exponent_le hfl hC.le
  have hkC : 0 ≤ (k:ℝ) ^ CDel := by positivity
  calc (k : ℝ) ^ 4 * (f : ℝ) ^ 4 * (k : ℝ) ^ (CDel - 4)
      = (k:ℝ) ^ CDel * (f:ℝ) ^ 4 := by rw [← e2]; ring
    _ ≤ (k:ℝ) ^ CDel * ((f:ℝ) * lb) ^ CDel := mul_le_mul_of_nonneg_left e3 hkC
    _ = ((k : ℝ) * f * lb) ^ CDel := e1.symm
    _ ≤ Del := h

/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Establish `hbb0 : 0 < bb` using `lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hbb`. Establish `e1 : x * x ^ (cT * Cb - 1) = x ^ (cT * Cb)` using `by conv_lhs => arg 1; rw [← Real.rpow_one x]`. Rewrite using `[← Real.rpow_add hx0]`. Put the polynomial expressions in normal form.

Rewrite using `[e1]`. Establish `hs : bb ^ (cT * mr) ≤ Real.sqrt TT`. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Conclude with `hTT`. Establish `h2 : (x ^ (Cb / 2)) ^ (cT * mr) ≤ bb ^ (cT * mr)` using `Real.rpow_le_rpow (by positivity) hbb (by positivity)`.

Establish `h3 : (x ^ (Cb / 2)) ^ (cT * mr) = x ^ (Cb / 2 * (cT * mr))`. Rewrite using `[← Real.rpow_mul hx0.le]`. Establish `h4 : x ^ (cT * Cb) ≤ x ^ (Cb / 2 * (cT * mr))`. Apply `Real.rpow_le_rpow_of_exponent_le hx` to reduce the goal to its premises. Establish `: cT * Cb * 2 ≤ cT * Cb * mr` using `mul_le_mul_of_nonneg_left hm (by positivity)`.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma sqrtTTLower (x bb cT Cb mr TT : ℝ) (hx : 1 ≤ x) (hcT : 0 < cT) (hCb : 0 < Cb) (hm : 2 ≤ mr)
    (hbb : x ^ (Cb / 2) ≤ bb) (hTT : (bb ^ (cT * mr)) ^ 2 ≤ TT) :
    x * x ^ (cT * Cb - 1) ≤ Real.sqrt TT := by
  have hx0 : 0 < x := by linarith
  have hbb0 : 0 < bb := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hbb
  have e1 : x * x ^ (cT * Cb - 1) = x ^ (cT * Cb) := by
    conv_lhs => arg 1; rw [← Real.rpow_one x]
    rw [← Real.rpow_add hx0]; ring_nf
  rw [e1]
  have hs : bb ^ (cT * mr) ≤ Real.sqrt TT := by
    apply Real.le_sqrt_of_sq_le; exact hTT
  have h2 : (x ^ (Cb / 2)) ^ (cT * mr) ≤ bb ^ (cT * mr) :=
    Real.rpow_le_rpow (by positivity) hbb (by positivity)
  have h3 : (x ^ (Cb / 2)) ^ (cT * mr) = x ^ (Cb / 2 * (cT * mr)) := by
    rw [← Real.rpow_mul hx0.le]
  have h4 : x ^ (cT * Cb) ≤ x ^ (Cb / 2 * (cT * mr)) := by
    apply Real.rpow_le_rpow_of_exponent_le hx
    have : cT * Cb * 2 ≤ cT * Cb * mr := mul_le_mul_of_nonneg_left hm (by positivity)
    nlinarith
  linarith

/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Break down `le_or_gt P 0 with hP | hP` into its components or cases. Establish `: 0 ≤ Real.sqrt (Del / (x * (10 * mr) ^ 3)) / W` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[le_div_iff₀ hW]`.

Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Rewrite using `[le_div_iff₀ (by positivity)]`. Establish `hK : 0 ≤ K` using `le_trans (sq_nonneg P) hPK`. Establish `hm3 : mr ^ 3 ≤ fr ^ 4`. Combine the equalities or inequalities in the displayed calculation.

Establish `hx3 : x ≤ x ^ 3`. Combine the equalities or inequalities in the displayed calculation. Establish `A1 : (P * W) ^ 2 * (x * (10 * mr) ^ 3) = P ^ 2 * (1000 * W ^ 2) * x * mr ^ 3` using `by ring`. Rewrite using `[A1]`. Establish `B1 : P ^ 2 * (1000 * W ^ 2) * x * mr ^ 3 ≤ P ^ 2 * x * x * fr ^ 4`.

Use `mul_le_mul hWx hm3 (by positivity) hx0.le` as an intermediate fact. Establish `hp2 : 0 ≤ P ^ 2` using `sq_nonneg P`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left this (mul_nonneg hp2 hx0.le)]`. Establish `B2 : P ^ 2 * x * x * fr ^ 4 ≤ x ^ 4 * fr ^ 4 * K`. Establish `hxx : x * x ≤ x ^ 4` using `by nlinarith`.

Establish `: P ^ 2 * (x * x) * fr ^ 4 ≤ K * x ^ 4 * fr ^ 4`. Apply `mul_le_mul_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Conclude with `mul_le_mul hPK hxx (by positivity) hK`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma quantOne (x fr mr K P W Del : ℝ) (hx : 1 ≤ x) (hm : 0 < mr) (hmf : mr ≤ fr) (hf : 1 ≤ fr)
    (hPK : P ^ 2 ≤ K) (hW : 0 < W) (hWx : 1000 * W ^ 2 ≤ x)
    (hDel : x ^ 4 * fr ^ 4 * K ≤ Del) :
    P ≤ Real.sqrt (Del / (x * (10 * mr) ^ 3)) / W := by
  have hx0 : 0 < x := by linarith
  rcases le_or_gt P 0 with hP | hP
  · have : 0 ≤ Real.sqrt (Del / (x * (10 * mr) ^ 3)) / W := by positivity
    linarith
  rw [le_div_iff₀ hW]
  apply Real.le_sqrt_of_sq_le
  rw [le_div_iff₀ (by positivity)]
  have hK : 0 ≤ K := le_trans (sq_nonneg P) hPK
  have hm3 : mr ^ 3 ≤ fr ^ 4 := by
    calc mr ^ 3 ≤ fr ^ 3 := pow_le_pow_left₀ hm.le hmf 3
      _ ≤ fr ^ 4 := pow_le_pow_right₀ hf (by norm_num)
  have hx3 : x ≤ x ^ 3 := by
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ 3 := pow_le_pow_right₀ hx (by norm_num)
  have A1 : (P * W) ^ 2 * (x * (10 * mr) ^ 3) = P ^ 2 * (1000 * W ^ 2) * x * mr ^ 3 := by ring
  rw [A1]
  have B1 : P ^ 2 * (1000 * W ^ 2) * x * mr ^ 3 ≤ P ^ 2 * x * x * fr ^ 4 := by
    have := mul_le_mul hWx hm3 (by positivity) hx0.le
    have hp2 : 0 ≤ P ^ 2 := sq_nonneg P
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hp2 hx0.le)]
  have B2 : P ^ 2 * x * x * fr ^ 4 ≤ x ^ 4 * fr ^ 4 * K := by
    have hxx : x * x ≤ x ^ 4 := by nlinarith
    have : P ^ 2 * (x * x) * fr ^ 4 ≤ K * x ^ 4 * fr ^ 4 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hPK hxx (by positivity) hK
    nlinarith
  linarith

/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Establish `hK : 0 ≤ K` using `le_trans hP hPK`. Establish `hV' : V ≤ x / 40` using `by linarith`. Establish `h1 : V * s ≤ x / 40 * x` using `mul_le_mul hV' hs hs0 (by linarith)`. Establish `h2 : V * s * (10 * mr) ≤ x / 40 * x * (10 * fr)` using `mul_le_mul h1 (by linarith) (by linarith) (by positivity)`.

Establish `h3 : P * (V * s * (10 * mr)) ≤ K * (x / 40 * x * (10 * fr))` using `mul_le_mul hPK h2 (by positivity) hK`. Establish `hx2 : x ^ 2 ≤ x ^ 4` using `pow_le_pow_right₀ hx (by norm_num)`. Establish `hf1 : fr ≤ fr ^ 4`. Combine the equalities or inequalities in the displayed calculation. Establish `h4 : K * (x / 40 * x * (10 * fr)) ≤ x ^ 4 * fr ^ 4 * K / 4`.

Establish `: x ^ 2 * fr ≤ x ^ 4 * fr ^ 4` using `mul_le_mul hx2 hf1 (by linarith) (by positivity)`. Use `mul_le_mul_of_nonneg_left this hK` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma quantitative_fourth_power_bound (x fr mr K P V s Del : ℝ) (hx : 1 ≤ x) (hm : 0 < mr) (hmf : mr ≤ fr)
    (hf : 1 ≤ fr) (hP : 0 ≤ P) (hPK : P ≤ K) (hV : 0 < V) (hVx : 40 * V ≤ x) (hs0 : 0 ≤ s)
    (hs : s ≤ x) (hDel : x ^ 4 * fr ^ 4 * K ≤ Del) :
    P * (V * s * (10 * mr)) ≤ Del / 4 := by
  have hx0 : 0 < x := by linarith
  have hK : 0 ≤ K := le_trans hP hPK
  have hV' : V ≤ x / 40 := by linarith
  have h1 : V * s ≤ x / 40 * x := mul_le_mul hV' hs hs0 (by linarith)
  have h2 : V * s * (10 * mr) ≤ x / 40 * x * (10 * fr) :=
    mul_le_mul h1 (by linarith) (by linarith) (by positivity)
  have h3 : P * (V * s * (10 * mr)) ≤ K * (x / 40 * x * (10 * fr)) :=
    mul_le_mul hPK h2 (by positivity) hK
  have hx2 : x ^ 2 ≤ x ^ 4 := pow_le_pow_right₀ hx (by norm_num)
  have hf1 : fr ≤ fr ^ 4 := by
    calc fr = fr ^ 1 := (pow_one fr).symm
      _ ≤ fr ^ 4 := pow_le_pow_right₀ hf (by norm_num)
  have h4 : K * (x / 40 * x * (10 * fr)) ≤ x ^ 4 * fr ^ 4 * K / 4 := by
    have : x ^ 2 * fr ≤ x ^ 4 * fr ^ 4 := mul_le_mul hx2 hf1 (by linarith) (by positivity)
    have := mul_le_mul_of_nonneg_left this hK
    nlinarith
  linarith

/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Break down `le_or_gt P 0 with hP | hP` into its components or cases. Establish `: 0 ≤ Real.sqrt (sT / (M * Real.sqrt x))` using `Real.sqrt_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises.

Establish `hsx : 0 < Real.sqrt x` using `Real.sqrt_pos.mpr hx0`. Rewrite using `[le_div_iff₀ (by positivity)]`. Establish `hMs : M ≤ Real.sqrt x` using `Real.le_sqrt_of_sq_le hMx`. Establish `hMsx : M * Real.sqrt x ≤ x`. Combine the equalities or inequalities in the displayed calculation.

Establish `hE : 0 ≤ E` using `le_trans (sq_nonneg P) hPE`. Use `mul_le_mul hPE hMsx (by positivity) hE` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma quantThree (x E P M sT : ℝ) (hx : 1 ≤ x) (hPE : P ^ 2 ≤ E) (hM : 0 < M)
    (hMx : M ^ 2 ≤ x) (hsT : x * E ≤ sT) :
    P ≤ Real.sqrt (sT / (M * Real.sqrt x)) := by
  have hx0 : 0 < x := by linarith
  rcases le_or_gt P 0 with hP | hP
  · have : 0 ≤ Real.sqrt (sT / (M * Real.sqrt x)) := Real.sqrt_nonneg _
    linarith
  apply Real.le_sqrt_of_sq_le
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  rw [le_div_iff₀ (by positivity)]
  have hMs : M ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hMx
  have hMsx : M * Real.sqrt x ≤ x := by
    calc M * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_right hMs hsx.le
      _ = x := Real.mul_self_sqrt hx0.le
  have hE : 0 ≤ E := le_trans (sq_nonneg P) hPE
  have := mul_le_mul hPE hMsx (by positivity) hE
  nlinarith

end Sz8

/- English proof (translation)
Introduce `E A _ _ ψ O La g hg`. Establish `key : ∀ x y : E, g ^ 2 * x * y / g = x * (g * y)`. Introduce `x y`. Clear the denominators using the available nonvanishing facts. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, key]`. Introduce `hO y hy x hx`. Use `hy (g ^ 2 * x) (hO x hx)` as an intermediate fact. Rewrite `this` using `[key]`. Then use the resulting hypothesis.
-/
theorem dual_lattice_bound : DualLattice := by
  intro E A _ _ ψ O La g hg
  have key : ∀ x y : E, g ^ 2 * x * y / g = x * (g * y) := by
    intro x y; field_simp
  refine ⟨?_, ?_⟩
  · ext y; simp only [Set.mem_setOf_eq, key]
  · intro hO y hy x hx
    have := hy (g ^ 2 * x) (hO x hx)
    rwa [key] at this

/- English proof (translation)
Introduce `m i s C ka N I A TT g hm hi hs hka hg`. Take `⟨p, rfl⟩ : ∃ p, m = p + 1` from `⟨m - 1, by omega⟩`. Take `⟨q, rfl⟩ : ∃ q, i = q + 1` from `⟨i - 1, by omega⟩`. Take `⟨u, rfl⟩ : ∃ u, s = u + 1` from `⟨s - 1, by omega⟩`. Establish `e1 : 2 * (q + 1) - 2 = 2 * q` using `by omega`.

Establish `e2 : 2 * (q + 1 - 1) + (u + 1) - 1 = 2 * q + u` using `by omega`. Establish `e3 : 2 * (q + 1) - 1 = 2 * q + 1` using `by omega`. Establish `e4 : 2 * (q + 1 - 1) = 2 * q` using `by omega`. Simplify using `only [xThreshold, lamThreshold, lamPrimeSq, Nat.add_sub_cancel, e1, e2, e3, e4]`. Establish `hg0 : g ≠ 0` using `hg.ne'`.

Establish `hka0 : ka ≠ 0` using `hka.ne'`. Establish `e5 : 2 * q + (u + 1) - 1 = 2 * q + u` using `by omega`. Simplify using `only [e5]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [div_pow, inv_pow, mul_pow, mul_inv, inv_inv, div_eq_mul_inv]`.

Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Simplify using `only [div_pow, inv_pow, mul_pow, mul_inv, inv_inv, div_eq_mul_inv]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`.

Simplify using `only [div_pow, inv_pow, mul_pow, mul_inv, inv_inv, div_eq_mul_inv]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Simplify using `only [div_pow, inv_pow, mul_pow, mul_inv, inv_inv, div_eq_mul_inv]`. Clear the denominators using the available nonvanishing facts.

Apply the tactic sequence `try ring`.
-/
theorem g_power_bounds : GPowers := by
  intro m i s C ka N I A TT g hm hi hs hka hg
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, i = q + 1 := ⟨i - 1, by omega⟩
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
  have e1 : 2 * (q + 1) - 2 = 2 * q := by omega
  have e2 : 2 * (q + 1 - 1) + (u + 1) - 1 = 2 * q + u := by omega
  have e3 : 2 * (q + 1) - 1 = 2 * q + 1 := by omega
  have e4 : 2 * (q + 1 - 1) = 2 * q := by omega
  simp only [xThreshold, lamThreshold, lamPrimeSq, Nat.add_sub_cancel, e1, e2, e3, e4]
  have hg0 : g ≠ 0 := hg.ne'
  have hka0 : ka ≠ 0 := hka.ne'
  have e5 : 2 * q + (u + 1) - 1 = 2 * q + u := by omega
  simp only [e5]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [div_pow, inv_pow, mul_pow, mul_inv, inv_inv, div_eq_mul_inv]; field_simp; try ring
  · simp only [div_pow, inv_pow, mul_pow, mul_inv, inv_inv, div_eq_mul_inv]; field_simp; try ring
  · simp only [div_pow, inv_pow, mul_pow, mul_inv, inv_inv, div_eq_mul_inv]; field_simp; try ring
  · simp only [div_pow, inv_pow, mul_pow, mul_inv, inv_inv, div_eq_mul_inv]; field_simp; try ring

/- English proof (translation)
Introduce `k r m N Del hm hN hmk hk hDel`. Establish `hm' : (m:ℝ) = 2 * r + 2` using `by rw [hm]; push_cast; ring`. Establish `hmk' : (m:ℝ) ≤ k` using `by exact_mod_cast hmk`. Establish `hk' : (4:ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hr0 : (0:ℝ) ≤ r` using `Nat.cast_nonneg r`.

Establish `hm2 : (2:ℝ) ≤ m` using `by linarith`. Establish `hN20 : 20 ≤ N` using `by rw [hN]; linarith`. Establish `hNk : N ≤ 10 * k` using `by rw [hN]; linarith`. Establish `hN0 : 0 ≤ N` using `by linarith`. Establish `hk0 : (0:ℝ) ≤ k` using `by linarith`.

Establish `hk3 : (k:ℝ) ^ 3 ≤ (k:ℝ) ^ 4` using `pow_le_pow_right₀ (by linarith) (by norm_num)`. Establish `hN3 : N ^ 3 ≤ 1000 * (k:ℝ) ^ 3`. Use `pow_le_pow_left₀ hN0 hNk 3` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hk4 : (256:ℝ) ≤ (k:ℝ) ^ 4`.

Use `pow_le_pow_left₀ (by norm_num) hk' 4; norm_num at this; linarith` as an intermediate fact. Establish `hN3b : (8000:ℝ) ≤ N ^ 3`. Use `pow_le_pow_left₀ (by norm_num) hN20 3; norm_num at this; linarith` as an intermediate fact. Establish `hr1 : (r:ℝ) + 1 ≤ k / 2` using `by linarith`. Establish `hr1' : 0 ≤ (r:ℝ) + 1` using `by linarith`.

Establish `hrr : ((r:ℝ) + 1) ^ 2 ≤ (k / 2) ^ 2` using `pow_le_pow_left₀ hr1' hr1 2`. Use `⟨by linarith, ?_, by linarith, by linarith, ?_⟩` and prove the remaining obligations. Introduce `j hj`. Establish `hj0 : (0:ℝ) ≤ j` using `Nat.cast_nonneg j`. Establish `: (j:ℝ) * N ^ 2 ≤ (N - 1) * N ^ 2` using `mul_le_mul_of_nonneg_right hj (sq_nonneg N)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `t1 : (k:ℝ) * N * ((r:ℝ) + 1) ^ 2 ≤ (k:ℝ) * (10 * k) * (k / 2) ^ 2`. Apply `mul_le_mul _ hrr (sq_nonneg _) (by positivity)` to reduce the goal to its premises. Conclude with `mul_le_mul_of_nonneg_left hNk hk0`. Establish `t2 : N ^ 2 * ((r:ℝ) + 1) ^ 2 ≤ (10 * k) ^ 2 * (k / 2) ^ 2` using `mul_le_mul (pow_le_pow_left₀ hN0 hNk 2) hrr (sq_nonneg _) (by positivity)`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem lattice_placement : Placement := by
  intro k r m N Del hm hN hmk hk hDel
  have hm' : (m:ℝ) = 2 * r + 2 := by rw [hm]; push_cast; ring
  have hmk' : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hk' : (4:ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hm2 : (2:ℝ) ≤ m := by linarith
  have hN20 : 20 ≤ N := by rw [hN]; linarith
  have hNk : N ≤ 10 * k := by rw [hN]; linarith
  have hN0 : 0 ≤ N := by linarith
  have hk0 : (0:ℝ) ≤ k := by linarith
  have hk3 : (k:ℝ) ^ 3 ≤ (k:ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hN3 : N ^ 3 ≤ 1000 * (k:ℝ) ^ 3 := by
    have := pow_le_pow_left₀ hN0 hNk 3
    nlinarith
  have hk4 : (256:ℝ) ≤ (k:ℝ) ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hk' 4; norm_num at this; linarith
  have hN3b : (8000:ℝ) ≤ N ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hN20 3; norm_num at this; linarith
  have hr1 : (r:ℝ) + 1 ≤ k / 2 := by linarith
  have hr1' : 0 ≤ (r:ℝ) + 1 := by linarith
  have hrr : ((r:ℝ) + 1) ^ 2 ≤ (k / 2) ^ 2 := pow_le_pow_left₀ hr1' hr1 2
  refine ⟨by linarith, ?_, by linarith, by linarith, ?_⟩
  · intro j hj
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
    have : (j:ℝ) * N ^ 2 ≤ (N - 1) * N ^ 2 := mul_le_mul_of_nonneg_right hj (sq_nonneg N)
    nlinarith
  · have t1 : (k:ℝ) * N * ((r:ℝ) + 1) ^ 2 ≤ (k:ℝ) * (10 * k) * (k / 2) ^ 2 := by
      apply mul_le_mul _ hrr (sq_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left hNk hk0
    have t2 : N ^ 2 * ((r:ℝ) + 1) ^ 2 ≤ (10 * k) ^ 2 * (k / 2) ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ hN0 hNk 2) hrr (sq_nonneg _) (by positivity)
    nlinarith

/- English proof (translation)
Introduce `m i s C ka N I A TT g hm hi hs hka hg hC hA hI hN hTT`. Take `⟨p, rfl⟩ : ∃ p, m = p + 1` from `⟨m - 1, by omega⟩`. Take `⟨q, rfl⟩ : ∃ q, i = q + 1` from `⟨i - 1, by omega⟩`. Take `⟨u, rfl⟩ : ∃ u, s = u + 1` from `⟨s - 1, by omega⟩`. Establish `e1 : 2 * (q + 1) - 2 = 2 * q` using `by omega`.

Establish `e2 : 2 * (q + 1 - 1) + (u + 1) - 1 = 2 * q + u` using `by omega`. Establish `e3 : 2 * (q + 1) - 1 = 2 * q + 1` using `by omega`. Establish `e4 : 2 * (q + 1 - 1) = 2 * q` using `by omega`. Simplify using `only [xThreshold, lamThreshold, lamPrimeSq, xHat, lamHat, lamPrimeHat, Nat.add_sub_cancel, e1, e2, e3, e4]`. Establish `hg0 : g ≠ 0` using `hg.ne'`.

Establish `hka0 : ka ≠ 0` using `hka.ne'`. Establish `hI0 : I ≠ 0` using `hI.ne'`. Establish `e5 : 2 * q + (u + 1) - 1 = 2 * q + u` using `by omega`. Simplify using `only [e5]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [div_pow, inv_pow, mul_pow, mul_inv, inv_inv, div_eq_mul_inv]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Simplify using `only [div_pow, inv_pow, mul_pow, mul_inv, inv_inv, div_eq_mul_inv]`. Clear the denominators using the available nonvanishing facts.

Apply the tactic sequence `try ring`. Establish `hsq : ∀ X : ℝ, g * Real.sqrt X = Real.sqrt (g ^ 2 * X)` using `fun X => by`. Rewrite using `[Real.sqrt_mul (sq_nonneg g), Real.sqrt_sq hg.le]`. Rewrite using `[hsq]`. Use `congr 1`.

Simplify using `only [div_pow, inv_pow, mul_pow, mul_inv, inv_inv, div_eq_mul_inv]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`.
-/
theorem normalised_forms : NormalisedForms := by
  intro m i s C ka N I A TT g hm hi hs hka hg hC hA hI hN hTT
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, i = q + 1 := ⟨i - 1, by omega⟩
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
  have e1 : 2 * (q + 1) - 2 = 2 * q := by omega
  have e2 : 2 * (q + 1 - 1) + (u + 1) - 1 = 2 * q + u := by omega
  have e3 : 2 * (q + 1) - 1 = 2 * q + 1 := by omega
  have e4 : 2 * (q + 1 - 1) = 2 * q := by omega
  simp only [xThreshold, lamThreshold, lamPrimeSq, xHat, lamHat, lamPrimeHat, Nat.add_sub_cancel, e1, e2, e3, e4]
  have hg0 : g ≠ 0 := hg.ne'
  have hka0 : ka ≠ 0 := hka.ne'
  have hI0 : I ≠ 0 := hI.ne'
  have e5 : 2 * q + (u + 1) - 1 = 2 * q + u := by omega
  simp only [e5]
  refine ⟨?_, ?_, ?_⟩
  · simp only [div_pow, inv_pow, mul_pow, mul_inv, inv_inv, div_eq_mul_inv]; field_simp; try ring
  · simp only [div_pow, inv_pow, mul_pow, mul_inv, inv_inv, div_eq_mul_inv]; field_simp; try ring
  · have hsq : ∀ X : ℝ, g * Real.sqrt X = Real.sqrt (g ^ 2 * X) := fun X => by
      rw [Real.sqrt_mul (sq_nonneg g), Real.sqrt_sq hg.le]
    rw [hsq]
    congr 1
    simp only [div_pow, inv_pow, mul_pow, mul_inv, inv_inv, div_eq_mul_inv]; field_simp; try ring

/- English proof (translation)
Introduce `ι _ t B1 B k C A0 Ct ka N I g Del TT i s hC hA0 hCt hka hkapi hN hI hg hDel hTT hCN ht htp hB1 hB hi`. Establish `hC0 : 0 ≤ C` using `by linarith`. Establish `hg0 : 0 < g` using `by linarith`. Establish `hq0 : 0 ≤ C * Real.pi * N / I` using `by positivity`. Establish `hbase0 : 0 ≤ C * ka * N / (g * I)` using `by positivity`.

Establish `hbase : C * ka * N / (g * I) ≤ C * Real.pi * N / I`. Rewrite using `[div_le_div_iff₀ (by positivity) hI]`. Establish `h1 : C * ka * N ≤ C * Real.pi * N`. Apply `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkapi hC0) hN.le` to reduce the goal to its premises. Establish `h2 : C * Real.pi * N ≤ C * Real.pi * N * g` using `le_mul_of_one_le_right (by positivity) hg`.

Establish `h3 : C * ka * N * I ≤ C * Real.pi * N * g * I` using `mul_le_mul_of_nonneg_right (le_trans h1 h2) hI.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbase1 : C * ka * N / (g * I) ≤ 1` using `le_trans hbase hCN`. Establish `hsk : 0 ≤ Real.sqrt k` using `Real.sqrt_nonneg _`. Establish `hCB : ∀ w, C * B w ≤ C * A0 * Real.sqrt k * t w` using `fun w => by`.

Use `mul_le_mul_of_nonneg_left (hB w).2 hC0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e : ∀ b, xHat 1 C ka N I g b = C * b` using `fun b => by simp [xHat]`. Establish `hs : Real.sqrt (k * N ^ 3 / Del) = Real.sqrt k * Real.sqrt (N ^ 3 / Del)`.

Rewrite using `[mul_div_assoc, Real.sqrt_mul (Nat.cast_nonneg k)]`. Use `Sz8.prodBound (fun w => xHat 1 C ka N I g (B1 w)) t (C * A0 * Real.sqrt (k * N ^ 3 / Del)) Ct (by positivity) (fun w => by` as an intermediate fact. Simplify using `only [e]`. Use `⟨mul_nonneg hC0 (hB1 w).1, ?_⟩` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left (hB1 w).2 hC0` as an intermediate fact.

Rewrite using `[hs]`. Use the proof step `linarith) htp`. Combine the equalities or inequalities in the displayed calculation. Introduce `hi2`. Establish `hex : 2 ≤ 2 * i - 2` using `by omega`.

Use `Sz8.prodBound (fun w => xHat i C ka N I g (B w)) t (C * A0 * Real.sqrt k * (C * Real.pi * N / I) ^ 2) Ct (by positivity) (fun w => by` as an intermediate fact. Simplify using `only [xHat]`. Establish `hp1 : (C * ka * N / (g * I)) ^ (2 * i - 2) ≤ (C * ka * N / (g * I)) ^ 2` using `pow_le_pow_of_le_one hbase0 hbase1 hex`. Establish `hp2 : (C * ka * N / (g * I)) ^ 2 ≤ (C * Real.pi * N / I) ^ 2` using `pow_le_pow_left₀ hbase0 hbase 2`. Establish `hCB0 : 0 ≤ C * B w` using `mul_nonneg hC0 (hB w).1`.

Use `⟨mul_nonneg hCB0 (pow_nonneg hbase0 _), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Introduce `hs2`. Establish `hex : 1 ≤ 2 * (i - 1) + s - 1` using `by omega`.

Use `Sz8.prodBound (fun w => lamHat i s C ka N I g (B w)) t (C * A0 * Real.sqrt k * (C * Real.pi * N / I)) Ct (by positivity) (fun w => by` as an intermediate fact. Simplify using `only [lamHat]`. Establish `hp1 : (C * ka * N / (g * I)) ^ (2 * (i - 1) + s - 1) ≤ (C * ka * N / (g * I)) ^ 1` using `pow_le_pow_of_le_one hbase0 hbase1 hex`. Rewrite `hp1` using `[pow_one]`. Establish `hCB0 : 0 ≤ C * B w` using `mul_nonneg hC0 (hB w).1`.

Use `⟨mul_nonneg hCB0 (pow_nonneg hbase0 _), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Establish `hsT : 0 < Real.sqrt TT` using `Real.sqrt_pos.mpr hTT`. Establish `hst : ∏ w, Real.sqrt (t w) ≤ Real.sqrt Ct`.

Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Rewrite using `[← Finset.prod_pow]`. Establish `e : ∀ w, Real.sqrt (t w) ^ 2 = t w` using `fun w => Real.sq_sqrt (ht w)`. Simplify using `only [e]`. Conclude with `htp`.

Establish `hQ : 0 ≤ Real.pi * C * A0 * Real.sqrt k / Real.sqrt TT` using `by positivity`. Use `Sz8.prodBound (fun w => lamPrimeHat i C ka N I g (B w) TT) (fun w => Real.sqrt (t w)) (Real.sqrt (Real.pi * C * A0 * Real.sqrt k / Real.sqrt TT)) (Real.sqrt Ct) (Real.sqrt_nonneg _) (fun w => by` as an intermediate fact. Simplify using `only [lamPrimeHat]`. Use `⟨Real.sqrt_nonneg _, ?_⟩` and prove the remaining obligations. Rewrite using `[← Real.sqrt_mul hQ]`.

Apply `Real.sqrt_le_sqrt` to reduce the goal to its premises. Establish `e : C * B w * (g ^ (2 * i - 2))⁻¹ * ka * (C * ka * N / I) ^ (2 * (i - 1)) * (Real.sqrt TT)⁻¹ = (C * B w * ka * (Real.sqrt TT)⁻¹) * (C * ka * N / (g * I)) ^ (2 * (i - 1))`. Rewrite using `[show 2 * i - 2 = 2 * (i - 1) by omega, div_pow, div_pow, mul_pow]; ring`. Rewrite using `[e]`. Establish `hCB0 : 0 ≤ C * B w` using `mul_nonneg hC0 (hB w).1`.

Establish `hX0 : 0 ≤ C * B w * ka * (Real.sqrt TT)⁻¹` using `by positivity`. Establish `hp : (C * ka * N / (g * I)) ^ (2 * (i - 1)) ≤ 1` using `pow_le_one₀ hbase0 hbase1`. Establish `h1 : C * B w * ka * (Real.sqrt TT)⁻¹ ≤ (C * A0 * Real.sqrt k * t w) * Real.pi * (Real.sqrt TT)⁻¹`. Apply `mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hsT.le)` to reduce the goal to its premises. Conclude with `mul_le_mul (hCB w) hkapi hka.le (by nlinarith [hCB w])`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `this`.
-/
theorem threshold_products : ThresholdProducts := by
  intro ι _ t B1 B k C A0 Ct ka N I g Del TT i s hC hA0 hCt hka hkapi hN hI hg hDel hTT hCN ht htp hB1 hB hi
  have hC0 : 0 ≤ C := by linarith
  have hg0 : 0 < g := by linarith
  have hq0 : 0 ≤ C * Real.pi * N / I := by positivity
  have hbase0 : 0 ≤ C * ka * N / (g * I) := by positivity
  have hbase : C * ka * N / (g * I) ≤ C * Real.pi * N / I := by
    rw [div_le_div_iff₀ (by positivity) hI]
    have h1 : C * ka * N ≤ C * Real.pi * N := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkapi hC0) hN.le
    have h2 : C * Real.pi * N ≤ C * Real.pi * N * g := le_mul_of_one_le_right (by positivity) hg
    have h3 : C * ka * N * I ≤ C * Real.pi * N * g * I :=
      mul_le_mul_of_nonneg_right (le_trans h1 h2) hI.le
    linarith
  have hbase1 : C * ka * N / (g * I) ≤ 1 := le_trans hbase hCN
  have hsk : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
  have hCB : ∀ w, C * B w ≤ C * A0 * Real.sqrt k * t w := fun w => by
    have := mul_le_mul_of_nonneg_left (hB w).2 hC0
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : ∀ b, xHat 1 C ka N I g b = C * b := fun b => by simp [xHat]
    have hs : Real.sqrt (k * N ^ 3 / Del) = Real.sqrt k * Real.sqrt (N ^ 3 / Del) := by
      rw [mul_div_assoc, Real.sqrt_mul (Nat.cast_nonneg k)]
    have := Sz8.prodBound (fun w => xHat 1 C ka N I g (B1 w)) t
      (C * A0 * Real.sqrt (k * N ^ 3 / Del)) Ct (by positivity) (fun w => by
        simp only [e]
        refine ⟨mul_nonneg hC0 (hB1 w).1, ?_⟩
        have := mul_le_mul_of_nonneg_left (hB1 w).2 hC0
        rw [hs]; linarith) htp
    calc _ ≤ _ := this
      _ = _ := by rw [mul_pow, mul_assoc]
  · intro hi2
    have hex : 2 ≤ 2 * i - 2 := by omega
    have := Sz8.prodBound (fun w => xHat i C ka N I g (B w)) t
      (C * A0 * Real.sqrt k * (C * Real.pi * N / I) ^ 2) Ct (by positivity) (fun w => by
        simp only [xHat]
        have hp1 : (C * ka * N / (g * I)) ^ (2 * i - 2) ≤ (C * ka * N / (g * I)) ^ 2 :=
          pow_le_pow_of_le_one hbase0 hbase1 hex
        have hp2 : (C * ka * N / (g * I)) ^ 2 ≤ (C * Real.pi * N / I) ^ 2 :=
          pow_le_pow_left₀ hbase0 hbase 2
        have hCB0 : 0 ≤ C * B w := mul_nonneg hC0 (hB w).1
        refine ⟨mul_nonneg hCB0 (pow_nonneg hbase0 _), ?_⟩
        calc C * B w * (C * ka * N / (g * I)) ^ (2 * i - 2)
            ≤ (C * A0 * Real.sqrt k * t w) * (C * Real.pi * N / I) ^ 2 :=
              mul_le_mul (hCB w) (le_trans hp1 hp2) (pow_nonneg hbase0 _) (by nlinarith [hCB w])
          _ = _ := by ring) htp
    calc _ ≤ _ := this
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  · intro hs2
    have hex : 1 ≤ 2 * (i - 1) + s - 1 := by omega
    have := Sz8.prodBound (fun w => lamHat i s C ka N I g (B w)) t
      (C * A0 * Real.sqrt k * (C * Real.pi * N / I)) Ct (by positivity) (fun w => by
        simp only [lamHat]
        have hp1 : (C * ka * N / (g * I)) ^ (2 * (i - 1) + s - 1) ≤ (C * ka * N / (g * I)) ^ 1 :=
          pow_le_pow_of_le_one hbase0 hbase1 hex
        rw [pow_one] at hp1
        have hCB0 : 0 ≤ C * B w := mul_nonneg hC0 (hB w).1
        refine ⟨mul_nonneg hCB0 (pow_nonneg hbase0 _), ?_⟩
        calc C * B w * (C * ka * N / (g * I)) ^ (2 * (i - 1) + s - 1)
            ≤ (C * A0 * Real.sqrt k * t w) * (C * Real.pi * N / I) :=
              mul_le_mul (hCB w) (le_trans hp1 hbase) (pow_nonneg hbase0 _) (by nlinarith [hCB w])
          _ = _ := by ring) htp
    calc _ ≤ _ := this
      _ = _ := by rw [mul_pow]; ring
  · have hsT : 0 < Real.sqrt TT := Real.sqrt_pos.mpr hTT
    have hst : ∏ w, Real.sqrt (t w) ≤ Real.sqrt Ct := by
      apply Real.le_sqrt_of_sq_le
      rw [← Finset.prod_pow]
      have e : ∀ w, Real.sqrt (t w) ^ 2 = t w := fun w => Real.sq_sqrt (ht w)
      simp only [e]; exact htp
    have hQ : 0 ≤ Real.pi * C * A0 * Real.sqrt k / Real.sqrt TT := by positivity
    have := Sz8.prodBound (fun w => lamPrimeHat i C ka N I g (B w) TT) (fun w => Real.sqrt (t w))
      (Real.sqrt (Real.pi * C * A0 * Real.sqrt k / Real.sqrt TT)) (Real.sqrt Ct) (Real.sqrt_nonneg _)
      (fun w => by
        simp only [lamPrimeHat]
        refine ⟨Real.sqrt_nonneg _, ?_⟩
        rw [← Real.sqrt_mul hQ]
        apply Real.sqrt_le_sqrt
        have e : C * B w * (g ^ (2 * i - 2))⁻¹ * ka * (C * ka * N / I) ^ (2 * (i - 1)) * (Real.sqrt TT)⁻¹
            = (C * B w * ka * (Real.sqrt TT)⁻¹) * (C * ka * N / (g * I)) ^ (2 * (i - 1)) := by
          rw [show 2 * i - 2 = 2 * (i - 1) by omega, div_pow, div_pow, mul_pow]; ring
        rw [e]
        have hCB0 : 0 ≤ C * B w := mul_nonneg hC0 (hB w).1
        have hX0 : 0 ≤ C * B w * ka * (Real.sqrt TT)⁻¹ := by positivity
        have hp : (C * ka * N / (g * I)) ^ (2 * (i - 1)) ≤ 1 := pow_le_one₀ hbase0 hbase1
        have h1 : C * B w * ka * (Real.sqrt TT)⁻¹ ≤ (C * A0 * Real.sqrt k * t w) * Real.pi * (Real.sqrt TT)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hsT.le)
          exact mul_le_mul (hCB w) hkapi hka.le (by nlinarith [hCB w])
        calc (C * B w * ka * (Real.sqrt TT)⁻¹) * (C * ka * N / (g * I)) ^ (2 * (i - 1))
            ≤ (C * B w * ka * (Real.sqrt TT)⁻¹) * 1 := mul_le_mul_of_nonneg_left hp hX0
          _ ≤ (C * A0 * Real.sqrt k * t w) * Real.pi * (Real.sqrt TT)⁻¹ := by rw [mul_one]; exact h1
          _ = _ := by ring) hst
    exact this

/- English proof (translation)
Introduce `f k C A0 Ct N I Del TT Th hf hk hC hA0 hCt hN hI hDel hTT hTh hCN h`. Establish `hk0 : (0:ℝ) < k` using `by have : (1:ℝ) ≤ k := by exact_mod_cast hk`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hC0 : 0 < C` using `by linarith`. Establish `hCt0 : 0 < Ct` using `by linarith`.

Establish `hinv : ∀ X : ℝ, 0 < X → Th⁻¹ ≤ X → X⁻¹ ≤ Th` using `fun X hX hX' => by`. Use `inv_anti₀ (inv_pos.mpr hTh) hX'` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Establish `hq0 : 0 < C * Real.pi * N / I` using `by positivity`. Establish `hsk : 0 < Real.sqrt k` using `Real.sqrt_pos.mpr hk0`.

Establish `hs0 : 0 < Real.sqrt (k * N ^ 3 / Del)` using `Real.sqrt_pos.mpr (by positivity)`. Establish `hsT : 0 < Real.sqrt TT` using `Real.sqrt_pos.mpr hTT`. Establish `hmin1 : min (min (Real.sqrt (Del / (k * N ^ 3)) / (Ct * C * A0)) (I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N))) (Real.sqrt (Real.sqrt TT / (Real.pi * Ct * C * A0 * Real.sqrt k))) ≤ Real.sqrt (Del / (k * N ^ 3)) / (Ct * C * A0)` using `le_trans (min_le_left _ _) (min_le_left _ _)`. Establish `hmin2 : min (min (Real.sqrt (Del / (k * N ^ 3)) / (Ct * C * A0)) (I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N))) (Real.sqrt (Real.sqrt TT / (Real.pi * Ct * C * A0 * Real.sqrt k))) ≤ I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N)` using `le_trans (min_le_left _ _) (min_le_right _ _)`. Establish `hmin3 : min (min (Real.sqrt (Del / (k * N ^ 3)) / (Ct * C * A0)) (I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N))) (Real.sqrt (Real.sqrt TT / (Real.pi * Ct * C * A0 * Real.sqrt k))) ≤ Real.sqrt (Real.sqrt TT / (Real.pi * Ct * C * A0 * Real.sqrt k))` using `min_le_right _ _`.

Establish `c23 : Th⁻¹ ≤ Ct * (C * A0 * Real.sqrt k * (C * Real.pi * N / I)) → I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N) ≤ Th` using `fun h' => by`. Apply the tactic sequence `have e : I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N) = (Ct * (C * A0 * Real.sqrt k * (C * Real.pi * N / I)))⁻¹ := by field_simp; try ring`. Rewrite using `[e]; exact hinv _ (by positivity) h'`. Break down `h with h | h | h | h` into its components or cases. Establish `h'` using `Sz8.cmRing_idempotent_unitRatio_identity f hf Ct (C * A0 * Real.sqrt (k * N ^ 3 / Del)) Th hCt (by positivity) hTh (by rw [mul_pow, ← mul_assoc]; exact h)`.

Establish `e : Real.sqrt (Del / (k * N ^ 3)) / (Ct * C * A0) = (Ct * (C * A0 * Real.sqrt (k * N ^ 3 / Del)))⁻¹`. Rewrite using `[show Del / (k * N ^ 3) = (k * N ^ 3 / Del)⁻¹ from (inv_div _ _).symm, Real.sqrt_inv]`. Clear the denominators using the available nonvanishing facts. Conclude with `le_trans hmin1 (by rw [e]; exact hinv _ (by positivity) h')`. Establish `h'` using `Sz8.cmRing_idempotent_unitRatio_identity f hf Ct (C * A0 * Real.sqrt k * (C * Real.pi * N / I) ^ 2) Th hCt (by positivity) hTh (by rw [mul_pow, ← pow_mul, ← mul_assoc]; exact h)`.

Establish `hq2 : (C * Real.pi * N / I) ^ 2 ≤ C * Real.pi * N / I`. Rewrite using `[sq]`. Conclude with `mul_le_of_le_one_left hq0.le hCN`. Establish `h'' : Th⁻¹ ≤ Ct * (C * A0 * Real.sqrt k * (C * Real.pi * N / I))`. Use `le_trans h' (mul_le_mul_of_nonneg_left ?_ hCt0.le)` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_left hq2 (by positivity)`. Conclude with `le_trans hmin2 (c23 h'')`. Establish `h'` using `Sz8.cmRing_idempotent_unitRatio_identity f hf Ct (C * A0 * Real.sqrt k * (C * Real.pi * N / I)) Th hCt (by positivity) hTh (by rw [mul_pow, ← mul_assoc]; exact h)`. Conclude with `le_trans hmin2 (c23 h')`. Establish `hsCt : 1 ≤ Real.sqrt Ct` using `Real.one_le_sqrt.mpr hCt`.

Establish `h'` using `Sz8.cmRing_idempotent_unitRatio_identity f hf (Real.sqrt Ct) (Real.sqrt (Real.pi * C * A0 * Real.sqrt k / Real.sqrt TT)) Th hsCt (Real.sqrt_nonneg _) hTh h`. Establish `e : Real.sqrt (Real.sqrt TT / (Real.pi * Ct * C * A0 * Real.sqrt k)) = (Real.sqrt Ct * Real.sqrt (Real.pi * C * A0 * Real.sqrt k / Real.sqrt TT))⁻¹`. Rewrite using `[← Real.sqrt_mul hCt0.le, ← Real.sqrt_inv]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Establish `hpos : 0 < Real.sqrt Ct * Real.sqrt (Real.pi * C * A0 * Real.sqrt k / Real.sqrt TT)`. Apply `mul_pos (Real.sqrt_pos.mpr hCt0) (Real.sqrt_pos.mpr (by positivity))` to reduce the goal to its premises. Conclude with `le_trans hmin3 (by rw [e]; exact hinv _ hpos h')`.
-/
theorem theta_lower_bound : ThetaLower := by
  intro f k C A0 Ct N I Del TT Th hf hk hC hA0 hCt hN hI hDel hTT hTh hCN h
  have hk0 : (0:ℝ) < k := by have : (1:ℝ) ≤ k := by exact_mod_cast hk
                             linarith
  have hC0 : 0 < C := by linarith
  have hCt0 : 0 < Ct := by linarith
  have hinv : ∀ X : ℝ, 0 < X → Th⁻¹ ≤ X → X⁻¹ ≤ Th := fun X hX hX' => by
    have := inv_anti₀ (inv_pos.mpr hTh) hX'; rwa [inv_inv] at this
  have hq0 : 0 < C * Real.pi * N / I := by positivity
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hs0 : 0 < Real.sqrt (k * N ^ 3 / Del) := Real.sqrt_pos.mpr (by positivity)
  have hsT : 0 < Real.sqrt TT := Real.sqrt_pos.mpr hTT
  have hmin1 : min (min (Real.sqrt (Del / (k * N ^ 3)) / (Ct * C * A0))
        (I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N)))
      (Real.sqrt (Real.sqrt TT / (Real.pi * Ct * C * A0 * Real.sqrt k))) ≤
      Real.sqrt (Del / (k * N ^ 3)) / (Ct * C * A0) := le_trans (min_le_left _ _) (min_le_left _ _)
  have hmin2 : min (min (Real.sqrt (Del / (k * N ^ 3)) / (Ct * C * A0))
        (I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N)))
      (Real.sqrt (Real.sqrt TT / (Real.pi * Ct * C * A0 * Real.sqrt k))) ≤
      I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N) := le_trans (min_le_left _ _) (min_le_right _ _)
  have hmin3 : min (min (Real.sqrt (Del / (k * N ^ 3)) / (Ct * C * A0))
        (I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N)))
      (Real.sqrt (Real.sqrt TT / (Real.pi * Ct * C * A0 * Real.sqrt k))) ≤
      Real.sqrt (Real.sqrt TT / (Real.pi * Ct * C * A0 * Real.sqrt k)) := min_le_right _ _
  have c23 : Th⁻¹ ≤ Ct * (C * A0 * Real.sqrt k * (C * Real.pi * N / I)) →
      I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N) ≤ Th := fun h' => by
    have e : I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N) =
        (Ct * (C * A0 * Real.sqrt k * (C * Real.pi * N / I)))⁻¹ := by
      field_simp; try ring
    rw [e]; exact hinv _ (by positivity) h'
  rcases h with h | h | h | h
  · have h' := Sz8.cmRing_idempotent_unitRatio_identity f hf Ct (C * A0 * Real.sqrt (k * N ^ 3 / Del)) Th hCt (by positivity) hTh
      (by rw [mul_pow, ← mul_assoc]; exact h)
    have e : Real.sqrt (Del / (k * N ^ 3)) / (Ct * C * A0) =
        (Ct * (C * A0 * Real.sqrt (k * N ^ 3 / Del)))⁻¹ := by
      rw [show Del / (k * N ^ 3) = (k * N ^ 3 / Del)⁻¹ from (inv_div _ _).symm, Real.sqrt_inv]
      field_simp
    exact le_trans hmin1 (by rw [e]; exact hinv _ (by positivity) h')
  · have h' := Sz8.cmRing_idempotent_unitRatio_identity f hf Ct (C * A0 * Real.sqrt k * (C * Real.pi * N / I) ^ 2) Th hCt
      (by positivity) hTh (by rw [mul_pow, ← pow_mul, ← mul_assoc]; exact h)
    have hq2 : (C * Real.pi * N / I) ^ 2 ≤ C * Real.pi * N / I := by
      rw [sq]; exact mul_le_of_le_one_left hq0.le hCN
    have h'' : Th⁻¹ ≤ Ct * (C * A0 * Real.sqrt k * (C * Real.pi * N / I)) := by
      refine le_trans h' (mul_le_mul_of_nonneg_left ?_ hCt0.le)
      exact mul_le_mul_of_nonneg_left hq2 (by positivity)
    exact le_trans hmin2 (c23 h'')
  · have h' := Sz8.cmRing_idempotent_unitRatio_identity f hf Ct (C * A0 * Real.sqrt k * (C * Real.pi * N / I)) Th hCt
      (by positivity) hTh (by rw [mul_pow, ← mul_assoc]; exact h)
    exact le_trans hmin2 (c23 h')
  · have hsCt : 1 ≤ Real.sqrt Ct := Real.one_le_sqrt.mpr hCt
    have h' := Sz8.cmRing_idempotent_unitRatio_identity f hf (Real.sqrt Ct) (Real.sqrt (Real.pi * C * A0 * Real.sqrt k / Real.sqrt TT))
      Th hsCt (Real.sqrt_nonneg _) hTh h
    have e : Real.sqrt (Real.sqrt TT / (Real.pi * Ct * C * A0 * Real.sqrt k)) =
        (Real.sqrt Ct * Real.sqrt (Real.pi * C * A0 * Real.sqrt k / Real.sqrt TT))⁻¹ := by
      rw [← Real.sqrt_mul hCt0.le, ← Real.sqrt_inv]; congr 1; field_simp
    have hpos : 0 < Real.sqrt Ct * Real.sqrt (Real.pi * C * A0 * Real.sqrt k / Real.sqrt TT) := by
      apply mul_pos (Real.sqrt_pos.mpr hCt0) (Real.sqrt_pos.mpr (by positivity))
    exact le_trans hmin3 (by rw [e]; exact hinv _ hpos h')

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `C A0 Ct CDel cT Cb hC hA0 hCt hCDel hcT hCb hcb`. Take `⟨k0, hk0⟩ : ∃ k0 : ℕ, max (max (max (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0))) (max ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi))) (Real.exp (2 / Cb)) + 4 ≤ k0` from `exists_nat_ge _`. Use `⟨k0, ?_⟩` and prove the remaining obligations. Introduce `k m f bb N I Del TT hk hm hmf hfk hN hI hbb hDel hTT`. Establish `hkR : (k0:ℝ) ≤ k` using `by exact_mod_cast hk`.

Establish `m1` using `le_max_left (max (max (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0))) (max ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi))) (Real.exp (2 / Cb))`. Establish `m2` using `le_max_right (max (max (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0))) (max ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi))) (Real.exp (2 / Cb))`. Establish `m3` using `le_max_left (max (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0))) (max ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi))`. Establish `m4` using `le_max_right (max (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0))) (max ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi))`. Establish `m5` using `le_max_left (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0))`.

Establish `m6` using `le_max_right (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0))`. Establish `m7` using `le_max_left ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi)`. Establish `m8` using `le_max_right ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi)`. Establish `hpi` using `Real.pi_pos`. Establish `hexp` using `Real.exp_pos (2 / Cb)`.

Establish `hkW : 1000 * (Ct * C * A0) ^ 2 ≤ k` using `by linarith`. Establish `hkV : 40 * (Real.pi * Ct * C ^ 2 * A0) ≤ k` using `by linarith`. Establish `hkM : (Real.pi * Ct * C * A0) ^ 2 ≤ k` using `by linarith`. Establish `hkC : 40 * C * Real.pi ≤ k` using `by linarith`. Establish `hke : Real.exp (2 / Cb) ≤ k` using `by linarith`.

Establish `hk4 : (4:ℝ) ≤ k` using `by nlinarith [sq_nonneg (Ct * C * A0)]`. Establish `hk1 : (1:ℝ) ≤ k` using `by linarith`. Establish `hkpos : (0:ℝ) < k` using `by linarith`. Establish `hk1N : 1 ≤ k` using `by exact_mod_cast hk1`. Establish `hm2 : (2:ℝ) ≤ m` using `by exact_mod_cast hm`.

Establish `hmf' : (m:ℝ) ≤ f` using `by exact_mod_cast hmf`. Establish `hfk' : (f:ℝ) ≤ k` using `by exact_mod_cast hfk`. Establish `hf1 : (1:ℝ) ≤ f` using `by linarith`. Establish `hf1N : 1 ≤ f` using `by omega`. Establish `hbbpos : 0 < bb` using `lt_of_lt_of_le (Real.rpow_pos_of_pos hkpos _) hbb`.

Establish `hlogk : 2 / Cb ≤ Real.log k`. Rewrite using `[← Real.log_exp (2 / Cb)]`. Conclude with `Real.log_le_log (Real.exp_pos _) hke`. Establish `hlb : 1 ≤ Real.log bb`. Establish `h1 : Real.log ((k:ℝ) ^ (Cb / 2)) ≤ Real.log bb` using `Real.log_le_log (Real.rpow_pos_of_pos hkpos _) hbb`.

Rewrite `h1` using `[Real.log_rpow hkpos]`. Establish `h3 : Cb / 2 * (2 / Cb) = 1` using `by field_simp`. Establish `h2 : Cb / 2 * (2 / Cb) ≤ Cb / 2 * Real.log k` using `mul_le_mul_of_nonneg_left hlogk (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hD` using `Sz8.delLower k f (Real.log bb) CDel Del hk1N hf1N hlb hCDel hDel`.

Establish `hf4 : 1 ≤ (f:ℝ) ^ 4` using `one_le_pow₀ hf1`. Establish `hK1 : 1 ≤ (k:ℝ) ^ (CDel - 4)` using `Real.one_le_rpow hk1 (by linarith)`. Establish `hk4D : (k:ℝ) ^ 4 ≤ Del`. Establish `h1 : (1:ℝ) * 1 ≤ (f:ℝ) ^ 4 * (k:ℝ) ^ (CDel - 4)` using `mul_le_mul hf4 hK1 zero_le_one (by positivity)`. Establish `h2` using `mul_le_mul_of_nonneg_left h1 (pow_nonneg hkpos.le 4)`.

Establish `e : (k:ℝ) ^ 4 * ((f:ℝ) ^ 4 * (k:ℝ) ^ (CDel - 4)) = (k:ℝ) ^ 4 * (f:ℝ) ^ 4 * (k:ℝ) ^ (CDel - 4)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk2 : 16 * (k:ℝ) ^ 2 ≤ (k:ℝ) ^ 4`. Establish `h16 : (16:ℝ) ≤ (k:ℝ) ^ 2` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation.

Establish `hk256 : (256:ℝ) ≤ (k:ℝ) ^ 4`. Use `pow_le_pow_left₀ (by norm_num) hk4 4; norm_num at this; linarith` as an intermediate fact. Establish `hI4 : Del / 4 ≤ I` using `by rw [hI]; linarith`. Establish `hIpos : 0 < I` using `by linarith`. Establish `he2a : 2 * cExp CDel cT Cb ≤ CDel - 4`.

Unfold `cExp`. Use `min_le_left ((CDel - 4) / 2) ((cT * Cb - 1) / 4)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `he2b : 2 * cExp CDel cT Cb ≤ cT * Cb - 1`. Unfold `cExp`.

Use `min_le_right ((CDel - 4) / 2) ((cT * Cb - 1) / 4)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `he0 : 0 ≤ cExp CDel cT Cb`. Unfold `cExp`. Establish `: 0 ≤ min ((CDel - 4) / 2) ((cT * Cb - 1) / 4)` using `le_min (by linarith) (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hP2 : ((k:ℝ) ^ cExp CDel cT Cb) ^ 2 = (k:ℝ) ^ (2 * cExp CDel cT Cb)`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hkpos.le]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hNk : N ≤ 10 * k` using `by rw [hN]; linarith`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[div_le_one hIpos]`. Establish `hN0 : 0 ≤ N` using `by rw [hN]; positivity`.

Establish `h1 : C * Real.pi * N ≤ C * Real.pi * (10 * k)` using `mul_le_mul_of_nonneg_left hNk (by positivity)`. Establish `h2 : 40 * C * Real.pi * k ≤ (k:ℝ) * k` using `mul_le_mul_of_nonneg_right hkC hkpos.le`. Establish `hkk : (k:ℝ) * k = (k:ℝ) ^ 2` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Use `le_min (le_min ?_ ?_) ?_` and prove the remaining obligations.

Use `Sz8.quantOne k f m ((k:ℝ) ^ (CDel - 4)) ((k:ℝ) ^ cExp CDel cT Cb) (Ct * C * A0) Del hk1 (by linarith) hmf' hf1 (by rw [hP2]; exact Real.rpow_le_rpow_of_exponent_le hk1 he2a) (by positivity) hkW hD` as an intermediate fact. Rewrite using `[hN]`. Conclude with `this`. Establish `hsk : Real.sqrt k ≤ k`. Combine the equalities or inequalities in the displayed calculation.

Use `Sz8.quantitative_fourth_power_bound k f m ((k:ℝ) ^ (CDel - 4)) ((k:ℝ) ^ cExp CDel cT Cb) (Real.pi * Ct * C ^ 2 * A0) (Real.sqrt k) Del hk1 (by linarith) hmf' hf1 (by positivity) (Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)) (by positivity) hkV (Real.sqrt_nonneg _) hsk hD` as an intermediate fact. Establish `hsk0 : 0 < Real.sqrt k` using `Real.sqrt_pos.mpr hkpos`. Rewrite using `[le_div_iff₀ (by rw [hN]; positivity)]`. Establish `e : (k:ℝ) ^ cExp CDel cT Cb * (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N) = (k:ℝ) ^ cExp CDel cT Cb * (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * (10 * m))` using `by rw [hN]`. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hS` using `Sz8.sqrtTTLower k bb cT Cb m TT hk1 hcT hCb hm2 hbb hTT`. Conclude with `Sz8.quantThree k ((k:ℝ) ^ (cT * Cb - 1)) ((k:ℝ) ^ cExp CDel cT Cb) (Real.pi * Ct * C * A0) (Real.sqrt TT) hk1 (by rw [hP2]; exact Real.rpow_le_rpow_of_exponent_le hk1 he2b) (by positivity) hkM hS`.
-/
theorem theta_power_bound : ThetaPower := by
  intro C A0 Ct CDel cT Cb hC hA0 hCt hCDel hcT hCb hcb
  obtain ⟨k0, hk0⟩ : ∃ k0 : ℕ, max (max (max (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0)))
      (max ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi))) (Real.exp (2 / Cb)) + 4 ≤ k0 :=
    exists_nat_ge _
  refine ⟨k0, ?_⟩
  intro k m f bb N I Del TT hk hm hmf hfk hN hI hbb hDel hTT
  have hkR : (k0:ℝ) ≤ k := by exact_mod_cast hk
  have m1 := le_max_left (max (max (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0)))
      (max ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi))) (Real.exp (2 / Cb))
  have m2 := le_max_right (max (max (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0)))
      (max ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi))) (Real.exp (2 / Cb))
  have m3 := le_max_left (max (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0)))
      (max ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi))
  have m4 := le_max_right (max (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0)))
      (max ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi))
  have m5 := le_max_left (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0))
  have m6 := le_max_right (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0))
  have m7 := le_max_left ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi)
  have m8 := le_max_right ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi)
  have hpi := Real.pi_pos
  have hexp := Real.exp_pos (2 / Cb)
  have hkW : 1000 * (Ct * C * A0) ^ 2 ≤ k := by linarith
  have hkV : 40 * (Real.pi * Ct * C ^ 2 * A0) ≤ k := by linarith
  have hkM : (Real.pi * Ct * C * A0) ^ 2 ≤ k := by linarith
  have hkC : 40 * C * Real.pi ≤ k := by linarith
  have hke : Real.exp (2 / Cb) ≤ k := by linarith
  have hk4 : (4:ℝ) ≤ k := by nlinarith [sq_nonneg (Ct * C * A0)]
  have hk1 : (1:ℝ) ≤ k := by linarith
  have hkpos : (0:ℝ) < k := by linarith
  have hk1N : 1 ≤ k := by exact_mod_cast hk1
  have hm2 : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hmf' : (m:ℝ) ≤ f := by exact_mod_cast hmf
  have hfk' : (f:ℝ) ≤ k := by exact_mod_cast hfk
  have hf1 : (1:ℝ) ≤ f := by linarith
  have hf1N : 1 ≤ f := by omega
  have hbbpos : 0 < bb := lt_of_lt_of_le (Real.rpow_pos_of_pos hkpos _) hbb
  have hlogk : 2 / Cb ≤ Real.log k := by
    rw [← Real.log_exp (2 / Cb)]; exact Real.log_le_log (Real.exp_pos _) hke
  have hlb : 1 ≤ Real.log bb := by
    have h1 : Real.log ((k:ℝ) ^ (Cb / 2)) ≤ Real.log bb :=
      Real.log_le_log (Real.rpow_pos_of_pos hkpos _) hbb
    rw [Real.log_rpow hkpos] at h1
    have h3 : Cb / 2 * (2 / Cb) = 1 := by field_simp
    have h2 : Cb / 2 * (2 / Cb) ≤ Cb / 2 * Real.log k := mul_le_mul_of_nonneg_left hlogk (by positivity)
    linarith
  have hD := Sz8.delLower k f (Real.log bb) CDel Del hk1N hf1N hlb hCDel hDel
  have hf4 : 1 ≤ (f:ℝ) ^ 4 := one_le_pow₀ hf1
  have hK1 : 1 ≤ (k:ℝ) ^ (CDel - 4) := Real.one_le_rpow hk1 (by linarith)
  have hk4D : (k:ℝ) ^ 4 ≤ Del := by
    have h1 : (1:ℝ) * 1 ≤ (f:ℝ) ^ 4 * (k:ℝ) ^ (CDel - 4) := mul_le_mul hf4 hK1 zero_le_one (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (pow_nonneg hkpos.le 4)
    have e : (k:ℝ) ^ 4 * ((f:ℝ) ^ 4 * (k:ℝ) ^ (CDel - 4)) = (k:ℝ) ^ 4 * (f:ℝ) ^ 4 * (k:ℝ) ^ (CDel - 4) := by ring
    linarith
  have hk2 : 16 * (k:ℝ) ^ 2 ≤ (k:ℝ) ^ 4 := by
    have h16 : (16:ℝ) ≤ (k:ℝ) ^ 2 := by nlinarith
    calc 16 * (k:ℝ) ^ 2 ≤ (k:ℝ) ^ 2 * (k:ℝ) ^ 2 := mul_le_mul_of_nonneg_right h16 (sq_nonneg _)
      _ = (k:ℝ) ^ 4 := by ring
  have hk256 : (256:ℝ) ≤ (k:ℝ) ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hk4 4; norm_num at this; linarith
  have hI4 : Del / 4 ≤ I := by rw [hI]; linarith
  have hIpos : 0 < I := by linarith
  have he2a : 2 * cExp CDel cT Cb ≤ CDel - 4 := by
    unfold cExp; have := min_le_left ((CDel - 4) / 2) ((cT * Cb - 1) / 4); linarith
  have he2b : 2 * cExp CDel cT Cb ≤ cT * Cb - 1 := by
    unfold cExp; have := min_le_right ((CDel - 4) / 2) ((cT * Cb - 1) / 4); linarith
  have he0 : 0 ≤ cExp CDel cT Cb := by
    unfold cExp
    have : 0 ≤ min ((CDel - 4) / 2) ((cT * Cb - 1) / 4) := le_min (by linarith) (by linarith)
    linarith
  have hP2 : ((k:ℝ) ^ cExp CDel cT Cb) ^ 2 = (k:ℝ) ^ (2 * cExp CDel cT Cb) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hkpos.le]; congr 1; push_cast; ring
  have hNk : N ≤ 10 * k := by rw [hN]; linarith
  refine ⟨?_, ?_⟩
  · rw [div_le_one hIpos]
    have hN0 : 0 ≤ N := by rw [hN]; positivity
    have h1 : C * Real.pi * N ≤ C * Real.pi * (10 * k) := mul_le_mul_of_nonneg_left hNk (by positivity)
    have h2 : 40 * C * Real.pi * k ≤ (k:ℝ) * k := mul_le_mul_of_nonneg_right hkC hkpos.le
    have hkk : (k:ℝ) * k = (k:ℝ) ^ 2 := by ring
    linarith
  · refine le_min (le_min ?_ ?_) ?_
    · have := Sz8.quantOne k f m ((k:ℝ) ^ (CDel - 4)) ((k:ℝ) ^ cExp CDel cT Cb) (Ct * C * A0) Del
        hk1 (by linarith) hmf' hf1 (by rw [hP2]; exact Real.rpow_le_rpow_of_exponent_le hk1 he2a)
        (by positivity) hkW hD
      rw [hN]; exact this
    · have hsk : Real.sqrt k ≤ k := by
        calc Real.sqrt k ≤ Real.sqrt ((k:ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
          _ = k := Real.sqrt_sq hkpos.le
      have := Sz8.quantitative_fourth_power_bound k f m ((k:ℝ) ^ (CDel - 4)) ((k:ℝ) ^ cExp CDel cT Cb)
        (Real.pi * Ct * C ^ 2 * A0) (Real.sqrt k) Del hk1 (by linarith) hmf' hf1 (by positivity)
        (Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)) (by positivity) hkV (Real.sqrt_nonneg _) hsk hD
      have hsk0 : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkpos
      rw [le_div_iff₀ (by rw [hN]; positivity)]
      have e : (k:ℝ) ^ cExp CDel cT Cb * (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N) =
          (k:ℝ) ^ cExp CDel cT Cb * (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * (10 * m)) := by rw [hN]
      rw [e]; linarith
    · have hS := Sz8.sqrtTTLower k bb cT Cb m TT hk1 hcT hCb hm2 hbb hTT
      exact Sz8.quantThree k ((k:ℝ) ^ (cT * Cb - 1)) ((k:ℝ) ^ cExp CDel cT Cb) (Real.pi * Ct * C * A0)
        (Real.sqrt TT) hk1 (by rw [hP2]; exact Real.rpow_le_rpow_of_exponent_le hk1 he2b)
        (by positivity) hkM hS

/- English proof (translation)
Introduce `C c hC hc`. Take `⟨k0, hk0⟩ : ∃ k0 : ℕ, (2 * C) ^ (16 / c) + 1 ≤ k0` from `exists_nat_ge _`. Use `⟨k0, ?_⟩` and prove the remaining obligations. Introduce `k r f bb Cf Th hk hrf hbb hcf hlog hTh`. Establish `h2C : 0 < 2 * C` using `by linarith`.

Establish `hrp` using `Real.rpow_nonneg h2C.le (16 / c)`. Establish `hkR : (2 * C) ^ (16 / c) + 1 ≤ (k:ℝ)` using `le_trans hk0 (by exact_mod_cast hk)`. Establish `hkpos : (0:ℝ) < k` using `by linarith`. Establish `hk1 : (1:ℝ) ≤ k` using `by linarith`. Take `⟨T, hT⟩ : ∃ T : ℝ, T = (k:ℝ) ^ (c / 16)` from `⟨_, rfl⟩`.

Establish `hT2C : 2 * C ≤ T`. Establish `h1 : ((2 * C) ^ (16 / c)) ^ (c / 16) ≤ (k:ℝ) ^ (c / 16)` using `Real.rpow_le_rpow hrp (by linarith) (by positivity)`. Rewrite `h1` using `[← Real.rpow_mul h2C.le, show 16 / c * (c / 16) = 1 by field_simp, Real.rpow_one]`. Rewrite using `[hT]`. Conclude with `h1`.

Establish `hT1 : 1 ≤ T` using `by linarith`. Establish `hTpos : 0 < T` using `by linarith`. Establish `hkc : (k:ℝ) ^ c = T ^ 16`. Rewrite using `[hT, ← Real.rpow_natCast, ← Real.rpow_mul hkpos.le]`. Use `congr 1`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hThpos : 0 < Th` using `lt_of_lt_of_le (by rw [hkc]; positivity) hTh`. Establish `hu : C / Th ≤ (2 * T ^ 15)⁻¹`. Rewrite using `[div_le_iff₀ hThpos]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hu0 : 0 ≤ C / Th` using `by positivity`. Establish `huf : (C / Th) ^ f ≤ ((2 * T ^ 15)⁻¹) ^ f` using `pow_le_pow_left₀ hu0 hu f`. Establish `hlogbb : Real.log bb ≤ f * Real.log T`. Rewrite using `[hT, Real.log_rpow hkpos]`.

Establish `hlogk0 : 0 ≤ Real.log k` using `Real.log_nonneg hk1`. Establish `hlb0 : 0 ≤ Real.log bb` using `Real.log_nonneg hbb`. Establish `h1 : 16 * Real.log bb ≤ c * Cf * Real.log bb` using `mul_le_mul_of_nonneg_right hcf hlb0`. Establish `h2 : c * (Cf * Real.log bb) ≤ c * (f * Real.log k)` using `mul_le_mul_of_nonneg_left hlog hc.le`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hbbT : bb ≤ T ^ f`. Establish `: Real.log bb ≤ Real.log (T ^ f)` using `by rw [Real.log_pow]; exact hlogbb`. Conclude with `(Real.log_le_log_iff (by linarith) (by positivity)).mp this`. Establish `hf2 : 2 ≤ f` using `by omega`. Establish `hr1 : ((r:ℝ) + 1) ≤ 2 ^ f`.

Establish `: r + 1 < 2 ^ f` using `lt_of_le_of_lt (by omega) Nat.lt_two_pow_self`. Conclude with `this.le` after adjusting the coercions. Establish `hCT : C ≤ T` using `by linarith`. Establish `hTf : T ≤ T ^ (8 * f)` using `le_self_pow₀ hT1 (by omega)`. Establish `hr0 : (0:ℝ) ≤ r` using `Nat.cast_nonneg r`.

Establish `hCr : C * ((r:ℝ) + 1) ≤ T ^ (8 * f) * 2 ^ f` using `mul_le_mul (le_trans hCT hTf) hr1 (by linarith) (by positivity)`. Establish `hbb7 : (bb ^ 7)⁻¹ ≥ ((T ^ f) ^ 7)⁻¹` using `inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hbbT 7)`. Establish `hmain : C * ((r:ℝ) + 1) * (C / Th) ^ f ≤ (bb ^ 7)⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_pow, mul_pow, ← pow_mul, ← pow_mul]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (bb ^ 7)⁻¹ := hbb7`. Use `⟨?_, hmain⟩` and prove the remaining obligations. Establish `h1 : (bb ^ 7)⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ (one_le_pow₀ hbb)`.

Establish `h2 : (r:ℝ) * (C / Th) ^ f ≤ C * ((r:ℝ) + 1) * (C / Th) ^ f`. Apply `mul_le_mul_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem final_smallness : FinalSmall := by
  intro C c hC hc
  obtain ⟨k0, hk0⟩ : ∃ k0 : ℕ, (2 * C) ^ (16 / c) + 1 ≤ k0 := exists_nat_ge _
  refine ⟨k0, ?_⟩
  intro k r f bb Cf Th hk hrf hbb hcf hlog hTh
  have h2C : 0 < 2 * C := by linarith
  have hrp := Real.rpow_nonneg h2C.le (16 / c)
  have hkR : (2 * C) ^ (16 / c) + 1 ≤ (k:ℝ) := le_trans hk0 (by exact_mod_cast hk)
  have hkpos : (0:ℝ) < k := by linarith
  have hk1 : (1:ℝ) ≤ k := by linarith
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = (k:ℝ) ^ (c / 16) := ⟨_, rfl⟩
  have hT2C : 2 * C ≤ T := by
    have h1 : ((2 * C) ^ (16 / c)) ^ (c / 16) ≤ (k:ℝ) ^ (c / 16) :=
      Real.rpow_le_rpow hrp (by linarith) (by positivity)
    rw [← Real.rpow_mul h2C.le, show 16 / c * (c / 16) = 1 by field_simp, Real.rpow_one] at h1
    rw [hT]; exact h1
  have hT1 : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hkc : (k:ℝ) ^ c = T ^ 16 := by
    rw [hT, ← Real.rpow_natCast, ← Real.rpow_mul hkpos.le]; congr 1; push_cast; field_simp
  have hThpos : 0 < Th := lt_of_lt_of_le (by rw [hkc]; positivity) hTh
  have hu : C / Th ≤ (2 * T ^ 15)⁻¹ := by
    rw [div_le_iff₀ hThpos]
    calc C ≤ T / 2 := by linarith
      _ = (2 * T ^ 15)⁻¹ * T ^ 16 := by field_simp; try ring
      _ ≤ (2 * T ^ 15)⁻¹ * Th := mul_le_mul_of_nonneg_left (by rw [← hkc]; exact hTh) (by positivity)
  have hu0 : 0 ≤ C / Th := by positivity
  have huf : (C / Th) ^ f ≤ ((2 * T ^ 15)⁻¹) ^ f := pow_le_pow_left₀ hu0 hu f
  have hlogbb : Real.log bb ≤ f * Real.log T := by
    rw [hT, Real.log_rpow hkpos]
    have hlogk0 : 0 ≤ Real.log k := Real.log_nonneg hk1
    have hlb0 : 0 ≤ Real.log bb := Real.log_nonneg hbb
    have h1 : 16 * Real.log bb ≤ c * Cf * Real.log bb := mul_le_mul_of_nonneg_right hcf hlb0
    have h2 : c * (Cf * Real.log bb) ≤ c * (f * Real.log k) := mul_le_mul_of_nonneg_left hlog hc.le
    nlinarith
  have hbbT : bb ≤ T ^ f := by
    have : Real.log bb ≤ Real.log (T ^ f) := by rw [Real.log_pow]; exact hlogbb
    exact (Real.log_le_log_iff (by linarith) (by positivity)).mp this
  have hf2 : 2 ≤ f := by omega
  have hr1 : ((r:ℝ) + 1) ≤ 2 ^ f := by
    have : r + 1 < 2 ^ f := lt_of_le_of_lt (by omega) Nat.lt_two_pow_self
    exact_mod_cast this.le
  have hCT : C ≤ T := by linarith
  have hTf : T ≤ T ^ (8 * f) := le_self_pow₀ hT1 (by omega)
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hCr : C * ((r:ℝ) + 1) ≤ T ^ (8 * f) * 2 ^ f :=
    mul_le_mul (le_trans hCT hTf) hr1 (by linarith) (by positivity)
  have hbb7 : (bb ^ 7)⁻¹ ≥ ((T ^ f) ^ 7)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hbbT 7)
  have hmain : C * ((r:ℝ) + 1) * (C / Th) ^ f ≤ (bb ^ 7)⁻¹ := by
    calc C * ((r:ℝ) + 1) * (C / Th) ^ f ≤ (T ^ (8 * f) * 2 ^ f) * ((2 * T ^ 15)⁻¹) ^ f :=
          mul_le_mul hCr huf (by positivity) (by positivity)
      _ = ((T ^ f) ^ 7)⁻¹ := by
          rw [inv_pow, mul_pow, ← pow_mul, ← pow_mul]; field_simp; ring
      _ ≤ (bb ^ 7)⁻¹ := hbb7
  refine ⟨?_, hmain⟩
  have h1 : (bb ^ 7)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hbb)
  have h2 : (r:ℝ) * (C / Th) ^ f ≤ C * ((r:ℝ) + 1) * (C / Th) ^ f := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith
  linarith

end Formalism.FourierDecayAlt.P
