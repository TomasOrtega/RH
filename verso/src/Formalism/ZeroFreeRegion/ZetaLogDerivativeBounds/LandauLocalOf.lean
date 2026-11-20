import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

open Complex Filter Topology Metric

noncomputable section

namespace Formalism.ZF

/- English proof (authored)
Differentiate the shifted power by the chain rule. For a positive exponent, multiply by the nonzero linear factor and divide by it to rewrite the lower power in the displayed form. For exponent zero both derivative expressions vanish.
-/
private theorem hasDerivAt_sub_pow_of_sub_ne_zero (a z : ℂ) (n : ℕ) (h : z - a ≠ 0) :
    HasDerivAt (fun w => (w - a) ^ n) ((z - a) ^ n * ((n : ℂ) / (z - a))) z := by
  have h1 : HasDerivAt (fun w : ℂ => w - a) 1 z := by
    simpa using (hasDerivAt_id z).sub_const a
  have h2 : HasDerivAt (fun w : ℂ => (w - a) ^ n) ((n : ℂ) * (z - a) ^ (n - 1) * 1) z :=
    (hasDerivAt_pow n (z - a)).comp z h1
  refine h2.congr_deriv ?_
  rcases n with _ | k
  · simp
  · rw [pow_succ, Nat.add_sub_cancel]
    have hinv : (z - a) * (z - a)⁻¹ = 1 := mul_inv_cancel₀ h
    linear_combination (-((z - a) ^ k * ((k + 1 : ℕ) : ℂ))) * hinv

/- English proof (authored)
Induct on the finite set of factors. The empty product has derivative zero. On adjoining one factor, its derivative is that factor times its reciprocal term. The product rule combines this term with the sum for the remaining factors, giving the derivative formula.
-/
private theorem hasDerivAt_prod_sub_pow (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ)
    (hz : ∀ ρ ∈ Z, z - ρ ≠ 0) :
    HasDerivAt (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ)
      ((∏ ρ ∈ Z, (z - ρ) ^ m ρ) * ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)) z := by
  classical
  revert hz
  induction Z using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.prod_empty, Finset.sum_empty, mul_zero]
    exact hasDerivAt_const z (1 : ℂ)
  | insert =>
    rename_i a s ha ih
    intro hz
    have hs : ∀ ρ ∈ s, z - ρ ≠ 0 := fun ρ hρ => hz ρ (Finset.mem_insert_of_mem hρ)
    have hza : z - a ≠ 0 := hz a (Finset.mem_insert_self a s)
    have hd := (hasDerivAt_sub_pow_of_sub_ne_zero a z (m a) hza).mul (ih hs)
    beta_reduce at hd
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    refine hd.congr_deriv ?_
    ring

/- English proof (authored)
The derivative of the product is the product times the sum of reciprocal terms. All the factors are nonzero at z, so division by their product cancels it, leaving precisely that sum.
-/
lemma landauLocal_logDeriv_prod (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ)
    (hz : ∀ ρ ∈ Z, z - ρ ≠ 0) :
    logDeriv (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) z = ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by
  rw [logDeriv_apply, (hasDerivAt_prod_sub_pow Z m z hz).deriv]
  have hP : (∏ ρ ∈ Z, (z - ρ) ^ m ρ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hz ρ hρ)
  exact (div_eq_iff hP).mpr (mul_comm _ _)

/- English proof (authored)
At power zero both sides are one. At each successor, multiply the preceding inequality by the base bounds, using nonnegativity, to preserve the order.
-/
private theorem pow_le_pow_left_of_nonneg_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) : a ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hab ha (le_trans (pow_nonneg ha k) ih)

/- English proof (authored)
The norm of a product is the product of norms, and a natural power’s norm is the same power of its norm. Applying both identities gives the formula.
-/
private theorem norm_prod_sub_pow (Z : Finset ℂ) (m : ℂ → ℕ) (w : ℂ) :
    ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ = ∏ ρ ∈ Z, ‖w - ρ‖ ^ m ρ := by
  simp only [norm_prod, norm_pow]

/- English proof (authored)
The factors P and H are nonzero. Divide the two numerator terms separately by PH, cancel their common factors, and subtract S. The remaining term is D/H.
-/
private theorem div_add_div_sub_eq_div (P S H D : ℂ) (hP : P ≠ 0) (hH : H ≠ 0) :
    (P * S * H + P * D) / (P * H) - S = D / H := by
  rw [sub_eq_iff_eq_add, div_eq_iff (mul_ne_zero hP hH)]
  have hHH : H⁻¹ * H = 1 := inv_mul_cancel₀ hH
  linear_combination (-(P * D)) * hHH

/- English proof (authored)
Use the given factorization to list the zeros in the disk of radius r/3. On the circle of radius r each removed linear factor has norm at least 2r/3, while at the center it has norm at most r/3. The growth hypothesis therefore bounds the holomorphic remainder on the circle by its center norm times M divided by two raised to the sum of the multiplicities. The maximum modulus principle extends this to the disk. Evaluate at the center and take logarithms to obtain the multiplicity bound. Apply the zero-free logarithmic derivative estimate to the remainder on the disk of radius r/3. At any point where f is nonzero, the product rule identifies the original derivative quotient minus the reciprocal zero terms with the derivative quotient of the remainder. Its bound on the half-sized disk is 72 log M divided by r.
-/
theorem localZeroExpansionOfFactorization : LandauLocalOf := by
  unfold LandauLocalOf LandauLocal
  intro hfac hlog f z₀ r M hr hM hf hf0 hbound
  classical
  have hr3 : 0 < r / 3 := by positivity
  obtain ⟨Z, m, h, hZ, hm, hh, hh0, hfeq⟩ := hfac f z₀ r (r / 3) hr3 (by linarith) hf hf0
  have hZball : ∀ ρ ∈ Z, ‖ρ - z₀‖ ≤ r / 3 := fun ρ hρ => by
    have := ((hZ ρ).1 hρ).1
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hZzero : ∀ ρ ∈ Z, f ρ = 0 := fun ρ hρ => ((hZ ρ).1 hρ).2
  have hz₀mem : z₀ ∈ Metric.closedBall z₀ r := Metric.mem_closedBall_self hr.le
  have hfz₀ := hfeq z₀ hz₀mem
  have hhz₀ : h z₀ ≠ 0 := by
    intro h0; apply hf0; rw [hfz₀, h0, mul_zero]
  have hPz₀le : ‖∏ ρ ∈ Z, (z₀ - ρ) ^ m ρ‖ ≤ (r / 3) ^ (∑ ρ ∈ Z, m ρ) := by
    rw [norm_prod_sub_pow, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun ρ _ => pow_nonneg (norm_nonneg _) _) ?_
    intro ρ hρ
    have h1 : ‖z₀ - ρ‖ ≤ r / 3 := by rw [norm_sub_rev]; exact hZball ρ hρ
    exact pow_le_pow_left_of_nonneg_le (norm_nonneg _) h1 _
  have hPw : ∀ w : ℂ, ‖w - z₀‖ = r →
      (2 * r / 3) ^ (∑ ρ ∈ Z, m ρ) ≤ ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ := by
    intro w hw
    rw [norm_prod_sub_pow, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun ρ _ => pow_nonneg (by linarith) _) ?_
    intro ρ hρ
    have h2 := hZball ρ hρ
    have h3 : ‖w - z₀‖ ≤ ‖w - ρ‖ + ‖ρ - z₀‖ := by
      have := norm_add_le (w - ρ) (ρ - z₀)
      rwa [sub_add_sub_cancel] at this
    have h1 : 2 * r / 3 ≤ ‖w - ρ‖ := by linarith
    exact pow_le_pow_left_of_nonneg_le (by linarith) h1 _
  have key_sphere : ∀ w : ℂ, ‖w - z₀‖ = r →
      (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖ ≤ M * ‖h z₀‖ := by
    intro w hw
    have hwmem : w ∈ Metric.closedBall z₀ r :=
      Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hw.le)
    have e1 := hbound w hwmem
    rw [hfeq w hwmem, hfz₀, norm_mul, norm_mul] at e1
    have e2 := hPw w hw
    have hq : 0 < (r / 3) ^ (∑ ρ ∈ Z, m ρ) := by positivity
    have e3 : (2 * r / 3) ^ (∑ ρ ∈ Z, m ρ) = (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * (r / 3) ^ (∑ ρ ∈ Z, m ρ) := by
      rw [mul_div_assoc, mul_pow]
    have e4 : (r / 3) ^ (∑ ρ ∈ Z, m ρ) * ((2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖)
        ≤ (r / 3) ^ (∑ ρ ∈ Z, m ρ) * (M * ‖h z₀‖) := by
      calc (r / 3) ^ (∑ ρ ∈ Z, m ρ) * ((2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖)
          = (2 * r / 3) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖ := by rw [e3]; ring
        _ ≤ ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ * ‖h w‖ := mul_le_mul_of_nonneg_right e2 (norm_nonneg _)
        _ ≤ M * (‖∏ ρ ∈ Z, (z₀ - ρ) ^ m ρ‖ * ‖h z₀‖) := e1
        _ ≤ M * ((r / 3) ^ (∑ ρ ∈ Z, m ρ) * ‖h z₀‖) := by
            refine mul_le_mul_of_nonneg_left ?_ (by linarith)
            exact mul_le_mul_of_nonneg_right hPz₀le (norm_nonneg _)
        _ = (r / 3) ^ (∑ ρ ∈ Z, m ρ) * (M * ‖h z₀‖) := by ring
    exact le_of_mul_le_mul_left e4 hq
  have hdc : DiffContOnCl ℂ h (Metric.ball z₀ r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball z₀ hr.ne']
    exact hh
  have hmax : ∀ z ∈ Metric.closedBall z₀ r,
      ‖h z‖ ≤ M * ‖h z₀‖ / (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) := by
    intro z hz
    have hz' : z ∈ closure (Metric.ball z₀ r) := by rwa [closure_ball z₀ hr.ne']
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc ?_ hz'
    intro w hw
    rw [frontier_ball z₀ hr.ne', mem_sphere_iff_norm] at hw
    rw [le_div_iff₀ (by positivity), mul_comm (‖h w‖)]
    exact key_sphere w hw
  have h2N : (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) ≤ M := by
    have := hmax z₀ hz₀mem
    have hpos : 0 < ‖h z₀‖ := norm_pos_iff.mpr hhz₀
    rw [le_div_iff₀ (by positivity), mul_comm M] at this
    exact le_of_mul_le_mul_left this hpos
  have hsum : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 := by
    rw [le_div_iff₀ (Real.log_pos one_lt_two), ← Real.log_pow]
    exact Real.log_le_log (by positivity) h2N
  have h2N1 : (1 : ℝ) ≤ (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) := by
    simpa using pow_le_pow_left_of_nonneg_le (a := 1) (b := 2) zero_le_one one_le_two (∑ ρ ∈ Z, m ρ)
  have hhb : ∀ z ∈ Metric.closedBall z₀ (r / 3), ‖h z‖ ≤ M * ‖h z₀‖ := by
    intro z hz
    have hz' : z ∈ Metric.closedBall z₀ r := Metric.closedBall_subset_closedBall (by linarith) hz
    have h1 := hmax z hz'
    have h2 : M * ‖h z₀‖ / (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) ≤ M * ‖h z₀‖ :=
      div_le_self (mul_nonneg (by linarith) (norm_nonneg _)) h2N1
    linarith
  have hlogb := hlog h z₀ (r / 3) M hr3 hM
    (hh.mono (Metric.closedBall_subset_closedBall (by linarith))) hh0 hhb
  refine ⟨Z, m, hZ, hm, hsum, ?_⟩
  intro z hz hfz
  have hzr : z ∈ Metric.ball z₀ r := by
    rw [Metric.mem_closedBall] at hz; rw [Metric.mem_ball]; linarith
  have hnhds : Metric.closedBall z₀ r ∈ 𝓝 z :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hzr) Metric.ball_subset_closedBall
  have hev : f =ᶠ[𝓝 z] fun w => (∏ ρ ∈ Z, (w - ρ) ^ m ρ) * h w :=
    Filter.mem_of_superset hnhds (fun w hw => hfeq w hw)
  have hfeqz := hfeq z (Metric.ball_subset_closedBall hzr)
  have hPz : (∏ ρ ∈ Z, (z - ρ) ^ m ρ) ≠ 0 := by
    intro h0; apply hfz; rw [hfeqz, h0, zero_mul]
  have hhz : h z ≠ 0 := by
    intro h0; apply hfz; rw [hfeqz, h0, mul_zero]
  have hzρ : ∀ ρ ∈ Z, z - ρ ≠ 0 := by
    intro ρ hρ h0; apply hfz; rw [sub_eq_zero.mp h0]; exact hZzero ρ hρ
  have hPd := hasDerivAt_prod_sub_pow Z m z hzρ
  have hhd : HasDerivAt h (deriv h z) z := (hh.differentiableAt hnhds).hasDerivAt
  have hd := (hPd.mul hhd).congr_of_eventuallyEq hev
  have hsplit : deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) = deriv h z / h z := by
    rw [hd.deriv, hfeqz]
    exact div_add_div_sub_eq_div _ _ _ _ hPz hhz
  rw [hsplit]
  have hz6 : z ∈ Metric.closedBall z₀ (r / 3 / 2) := by
    rw [Metric.mem_closedBall] at hz ⊢; linarith
  calc ‖deriv h z / h z‖ ≤ 24 * Real.log M / (r / 3) := hlogb z hz6
    _ = 72 * Real.log M / r := by rw [div_div_eq_mul_div]; ring

end Formalism.ZF
