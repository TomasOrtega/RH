import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.CoeffRescaleExpandOfNotDvd
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalMF
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFacSer
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmForm

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Unfold `prodSer`. Use `Finset.prod_induction _ (CoeffIn (Rm m)) (fun a b ha hb => ha.mul hb) ?_ (fun t ht => facSer_coeffIn hm ht)` and prove the remaining obligations. Introduce `n`. Rewrite using `[PowerSeries.coeff_one]`. Use `split_ifs`.

Conclude with `Subring.one_mem _`. Conclude with `Subring.zero_mem _`.
-/
theorem prodSer_coeffIn {m : ℕ} (hm : 0 < m) : CoeffIn (Rm m) (prodSer m) := by
  unfold prodSer
  refine Finset.prod_induction _ (CoeffIn (Rm m)) (fun a b ha hb => ha.mul hb) ?_
    (fun t ht => facSer_coeffIn hm ht)
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

/- English proof (translation)
Unfold `prodSer`. Use `Finset.prod_induction _ Conv (fun a b ha hb => ha.mul hb) ?_ (fun t ht => facSer_conv hm ht)` and prove the remaining obligations. Introduce `x _`. Use `(hasSum_single 0 fun n hn => ?_).summable` and prove the remaining obligations. Simplify using `[PowerSeries.coeff_one, hn]`.
-/
theorem prodSer_conv {m : ℕ} (hm : 0 < m) : Conv (prodSer m) := by
  unfold prodSer
  refine Finset.prod_induction _ Conv (fun a b ha hb => ha.mul hb) ?_
    (fun t ht => facSer_conv hm ht)
  intro x _
  refine (hasSum_single 0 fun n hn => ?_).summable
  simp [PowerSeries.coeff_one, hn]

/- English proof (translation)
Establish `hm' : (0 : ℝ) < m` using `by exact_mod_cast hm`. Establish `hx : ‖qm m τ‖ < 1`. Unfold `qm`. Rewrite using `[Complex.norm_exp]`. Establish `e : (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) / (m : ℂ)).re = -(2 * Real.pi * τ.im) / m`.

Rewrite using `[Complex.div_natCast_re]`. Simplify using the standard rewrite rules. Rewrite using `[e, ← Real.exp_zero]`. Conclude with `Real.exp_lt_exp.mpr (div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos, τ.im_pos]) hm')`. Establish `h1 : Conv (1 : PowerSeries ℂ)`.

Introduce `x _`. Use `(hasSum_single 0 fun n hn => ?_).summable` and prove the remaining obligations. Simplify using `[PowerSeries.coeff_one, hn]`. Establish `key : ∀ s ⊆ Tm m, Conv (∏ t ∈ s, facSer m t) ∧ ev (∏ t ∈ s, facSer m t) (qm m τ) = ∏ t ∈ s, fac t τ`. Introduce `s`.

Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Use `⟨by simpa using h1, ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.prod_empty]`. Unfold `ev`.

Rewrite using `[tsum_eq_single 0 fun n hn => by simp [PowerSeries.coeff_one, hn]]`. Simplify using the standard rewrite rules. Introduce `a s ha ih hs`. Establish `has : a ∈ Tm m` using `hs (Finset.mem_insert_self a s)`. Take `⟨c1, c2⟩` from `ih fun y hy => hs (Finset.mem_insert_of_mem hy)`.

Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha]`. Conclude with `⟨(facSer_conv hm has).mul c1, by`. Rewrite using `[ev_mul (facSer_conv hm has) c1 hx, facSer_ev hm has, c2]⟩`. Unfold `prodSer Gm`. Conclude with `(key _ subset_rfl).2`.
-/
theorem prodSer_ev {m : ℕ} (hm : 0 < m) (τ : ℍ) : ev (prodSer m) (qm m τ) = Gm m τ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hx : ‖qm m τ‖ < 1 := by
    unfold qm
    rw [Complex.norm_exp]
    have e : (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) / (m : ℂ)).re = -(2 * Real.pi * τ.im) / m := by
      rw [Complex.div_natCast_re]
      simp
    rw [e, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos, τ.im_pos]) hm')
  have h1 : Conv (1 : PowerSeries ℂ) := by
    intro x _
    refine (hasSum_single 0 fun n hn => ?_).summable
    simp [PowerSeries.coeff_one, hn]
  have key : ∀ s ⊆ Tm m, Conv (∏ t ∈ s, facSer m t) ∧
      ev (∏ t ∈ s, facSer m t) (qm m τ) = ∏ t ∈ s, fac t τ := by
    intro s
    classical
    refine Finset.induction_on s ?_ ?_
    · intro _
      refine ⟨by simpa using h1, ?_⟩
      simp only [Finset.prod_empty]
      unfold ev
      rw [tsum_eq_single 0 fun n hn => by simp [PowerSeries.coeff_one, hn]]
      simp
    · intro a s ha ih hs
      have has : a ∈ Tm m := hs (Finset.mem_insert_self a s)
      obtain ⟨c1, c2⟩ := ih fun y hy => hs (Finset.mem_insert_of_mem hy)
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact ⟨(facSer_conv hm has).mul c1, by
        rw [ev_mul (facSer_conv hm has) c1 hx, facSer_ev hm has, c2]⟩
  unfold prodSer Gm
  exact (key _ subset_rfl).2

/- English proof (translation)
Unfold `prodSer`. Use `LowUnit.prod _ _ fun t ht => facSer_low hm ht ?_` and prove the remaining obligations. Introduce `heq`. Apply `hsq` to reduce the goal to its premises. Unfold `Tm at ht`.

Rewrite `ht` using `[Finset.mem_image]`. Take `⟨x, hx, rfl⟩` from `ht`. Rewrite `hx` using `[Finset.mem_sigma, Nat.mem_divisors]`. Simplify using `only at heq`. Use `⟨x.1, ?_⟩` and prove the remaining obligations.

Establish `h2` using `Nat.div_mul_cancel hx.1.1`. Rewrite `h2` using `[← heq]`. Conclude with `h2.symm`.
-/
theorem prodSer_low {m : ℕ} (hm : 0 < m) (hsq : ¬ IsSquare m) : ∃ n0 u, LowUnit (Rm m) (prodSer m) n0 u := by
  unfold prodSer
  refine LowUnit.prod _ _ fun t ht => facSer_low hm ht ?_
  intro heq
  apply hsq
  unfold Tm at ht
  rw [Finset.mem_image] at ht
  obtain ⟨x, hx, rfl⟩ := ht
  rw [Finset.mem_sigma, Nat.mem_divisors] at hx
  dsimp only at heq
  refine ⟨x.1, ?_⟩
  have h2 := Nat.div_mul_cancel hx.1.1
  rw [← heq] at h2
  exact h2.symm

/- English proof (translation)
Establish `hm0 : m ≠ 0` using `hm.ne'`. Establish `hF` using `gmForm hm`. Use `eq_of_ev_eq (hF.conv.xp hm0) (prodSer_conv hm) ?_` and prove the remaining obligations. Introduce `x hx0 hx1`. Rewrite using `[ev_xp _ hm0]`.

Establish `hxne : x ≠ 0` using `norm_pos_iff.mp hx0`. Establish `hmR : (m : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr hm0`. Establish `hmC : (m : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hm0`. Establish `hmpos : (0 : ℝ) < m` using `by exact_mod_cast hm`. Establish `hlog : Real.log ‖x‖ < 0` using `Real.log_neg hx0 hx1`.

Set `w : ℂ` to `⟨(m : ℝ) * Complex.arg x / (2 * Real.pi), -((m : ℝ) * Real.log ‖x‖) / (2 * Real.pi)⟩`. Establish `him : 0 < w.im` using `by show 0 < -((m : ℝ) * Real.log ‖x‖) / (2 * Real.pi)`. Apply `div_pos _ (by positivity)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Set `τ : ℍ` to `⟨w, him⟩`.

Establish `hτ : (τ : ℂ) = w` using `rfl`. Establish `hlogx : 2 * (Real.pi : ℂ) * Complex.I * w / (m : ℂ) = Complex.log x`. Apply `Complex.ext` to reduce the goal to its premises. Rewrite using `[Complex.div_natCast_re, Complex.log_re]`. Simplify using `[w]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[Complex.div_natCast_im, Complex.log_im]`. Simplify using `[w]`. Clear the denominators using the available nonvanishing facts. Establish `hq : qm m τ = x`.

Unfold `qm`. Rewrite using `[hτ, hlogx, Complex.exp_log hxne]`. Establish `hq1 : qm 1 τ = x ^ m`. Rewrite using `[← hq]`. Unfold `qm`.

Rewrite using `[← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[← hq1, hF.ev_eq τ, ← prodSer_ev hm τ, hq]`.
-/
theorem gmQ_xp {m : ℕ} (hm : 0 < m) : xp m (qExpansion 1 (Gm m)) = prodSer m := by
  have hm0 : m ≠ 0 := hm.ne'
  have hF := gmForm hm
  refine eq_of_ev_eq (hF.conv.xp hm0) (prodSer_conv hm) ?_
  intro x hx0 hx1
  rw [ev_xp _ hm0]
  have hxne : x ≠ 0 := norm_pos_iff.mp hx0
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : Real.log ‖x‖ < 0 := Real.log_neg hx0 hx1

  let w : ℂ := ⟨(m : ℝ) * Complex.arg x / (2 * Real.pi), -((m : ℝ) * Real.log ‖x‖) / (2 * Real.pi)⟩
  have him : 0 < w.im := by
    show 0 < -((m : ℝ) * Real.log ‖x‖) / (2 * Real.pi)
    apply div_pos _ (by positivity)
    nlinarith
  let τ : ℍ := ⟨w, him⟩
  have hτ : (τ : ℂ) = w := rfl
  have hlogx : 2 * (Real.pi : ℂ) * Complex.I * w / (m : ℂ) = Complex.log x := by
    apply Complex.ext
    · rw [Complex.div_natCast_re, Complex.log_re]
      simp [w]
      field_simp
    · rw [Complex.div_natCast_im, Complex.log_im]
      simp [w]
      field_simp
  have hq : qm m τ = x := by
    unfold qm
    rw [hτ, hlogx, Complex.exp_log hxne]
  have hq1 : qm 1 τ = x ^ m := by
    rw [← hq]
    unfold qm
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [← hq1, hF.ev_eq τ, ← prodSer_ev hm τ, hq]

/- English proof (translation)
Introduce `n`. Establish `h` using `congrArg (PowerSeries.coeff (m * n)) (gmQ_xp hm)`. Simplify using `only [xp, PowerSeries.coeff_mk, dvd_mul_right, if_true, Nat.mul_div_cancel_left n hm] at h`. Rewrite using `[h]`. Conclude with `prodSer_coeffIn hm (m * n)`.
-/
theorem gmQ_coeffIn {m : ℕ} (hm : 0 < m) : CoeffIn (Rm m) (qExpansion 1 (Gm m)) := by
  intro n
  have h := congrArg (PowerSeries.coeff (m * n)) (gmQ_xp hm)
  simp only [xp, PowerSeries.coeff_mk, dvd_mul_right, if_true, Nat.mul_div_cancel_left n hm] at h
  rw [h]
  exact prodSer_coeffIn hm (m * n)

/- English proof (translation)
Take `⟨n0, u, hu1, hu2, hu3, hlow, hn0⟩` from `prodSer_low hm hsq`. Establish `hc : ∀ n, PowerSeries.coeff n (prodSer m) = if m ∣ n then PowerSeries.coeff (n / m) (qExpansion 1 (Gm m)) else 0`. Introduce `n`. Rewrite using `[← gmQ_xp hm]`. Simplify using `[xp]`.

Establish `hdvd : m ∣ n0`. Assume the negation of the conclusion as `h`. Rewrite `hn0` using `[hc, if_neg h]`. Conclude with `hu3 hn0.symm`. Take `⟨k, rfl⟩` from `hdvd`.

Use `⟨k, u, hu1, hu2, hu3, fun j hj => ?_, ?_⟩` and prove the remaining obligations. Establish `h2` using `hlow (m * j) (by nlinarith)`. Rewrite `h2` using `[hc, if_pos (dvd_mul_right m j), Nat.mul_div_cancel_left j hm]`. Conclude with `h2`. Rewrite `hn0` using `[hc, if_pos (dvd_mul_right m k), Nat.mul_div_cancel_left k hm]`.

Conclude with `hn0`.
-/
theorem gmQ_low {m : ℕ} (hm : 0 < m) (hsq : ¬ IsSquare m) :
    ∃ n0 u, LowUnit (Rm m) (qExpansion 1 (Gm m)) n0 u := by
  obtain ⟨n0, u, hu1, hu2, hu3, hlow, hn0⟩ := prodSer_low hm hsq
  have hc : ∀ n, PowerSeries.coeff n (prodSer m) =
      if m ∣ n then PowerSeries.coeff (n / m) (qExpansion 1 (Gm m)) else 0 := by
    intro n
    rw [← gmQ_xp hm]
    simp [xp]
  have hdvd : m ∣ n0 := by
    by_contra h
    rw [hc, if_neg h] at hn0
    exact hu3 hn0.symm
  obtain ⟨k, rfl⟩ := hdvd
  refine ⟨k, u, hu1, hu2, hu3, fun j hj => ?_, ?_⟩
  · have h2 := hlow (m * j) (by nlinarith)
    rw [hc, if_pos (dvd_mul_right m j), Nat.mul_div_cancel_left j hm] at h2
    exact h2
  · rw [hc, if_pos (dvd_mul_right m k), Nat.mul_div_cancel_left k hm] at hn0
    exact hn0

end ReciprocityTheory.ChartRestriction.L1
