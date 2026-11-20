import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AlgKlein

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Classical
open scoped ComplexConjugate Topology

namespace AlgP

section KleinPf

open Formalism.L2.Th1.F

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `[opU, herm]`.
-/
theorem translation_operator_zero (L : PeriodPair) (F : ℂ → ℂ) : opU L 0 F = F := by
  funext z
  simp [opU, herm]

/- English proof (translation)
The claim follows from `translation_operator_analytic L u (sgStarBasic L).1`.
-/
theorem sg_analytic (L : PeriodPair) (u : ℂ) : AnalyticOnNhd ℂ (opU L u (sgStar L)) Set.univ :=
  translation_operator_analytic L u (sgStarBasic L).1

/- English proof (translation)
The claim follows from `(th0Const L u).2 hu`.
-/
theorem sg_val_ne (L : PeriodPair) {u : ℂ} (hu : u ∉ L.lattice) : opU L u (sgStar L) 0 ≠ 0 :=
  (th0Const L u).2 hu

/- English proof (translation)
Unfold `semiChar`. Use `split_ifs`. Conclude with `⟨one_mem _, one_ne_zero⟩`. Conclude with `⟨neg_mem (one_mem _), by norm_num⟩`.
-/
theorem semiChar_mem (L : PeriodPair) (ω : ℂ) : semiChar L ω ∈ Formalism.MainNotions.TaylorLogMetric.Qbar ∧ semiChar L ω ≠ 0 := by
  unfold semiChar
  split_ifs
  · exact ⟨one_mem _, one_ne_zero⟩
  · exact ⟨neg_mem (one_mem _), by norm_num⟩

/- English proof (translation)
Establish `h` using `sgStarFixed L ω z hω`. Establish `hne` using `(semiChar_mem L ω).2`. Rewrite using `[← h, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]`.
-/
theorem sg_lat (L : PeriodPair) {ω : ℂ} (hω : ω ∈ L.lattice) (z : ℂ) :
    opU L ω (sgStar L) z = (semiChar L ω)⁻¹ * sgStar L z := by
  have h := sgStarFixed L ω z hω
  have hne := (semiChar_mem L ω).2
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/- English proof (translation)
Simplify using `only [altE, herm]`. Rewrite using `[show (N : ℂ) * x * conj y / (area L : ℂ) = ((N : ℝ) : ℂ) * (x * conj y / (area L : ℂ)) by push_cast; ring]`. Simplify using `[Complex.mul_im]`.
-/
theorem altE_nat_mul (L : PeriodPair) (N : ℕ) (x y : ℂ) : altE L ((N : ℂ) * x) y = (N : ℝ) * altE L x y := by
  simp only [altE, herm]
  rw [show (N : ℂ) * x * conj y / (area L : ℂ) = ((N : ℝ) : ℂ) * (x * conj y / (area L : ℂ)) by push_cast; ring]
  simp [Complex.mul_im]

/- English proof (translation)
Simplify using `only [altE, herm, map_mul, map_natCast]`. Rewrite using `[show x * ((N : ℂ) * conj y) / (area L : ℂ) = ((N : ℝ) : ℂ) * (x * conj y / (area L : ℂ)) by push_cast; ring]`. Simplify using `[Complex.mul_im]`.
-/
theorem altE_mul_nat (L : PeriodPair) (N : ℕ) (x y : ℂ) : altE L x ((N : ℂ) * y) = (N : ℝ) * altE L x y := by
  simp only [altE, herm, map_mul, map_natCast]
  rw [show x * ((N : ℂ) * conj y) / (area L : ℂ) = ((N : ℝ) : ℂ) * (x * conj y / (area L : ℂ)) by push_cast; ring]
  simp [Complex.mul_im]

/- English proof (translation)
Take `⟨k, hk⟩` from `h`. Establish `hk' : (N : ℂ) * (altE L x y : ℂ) = (k : ℂ)` using `by exact_mod_cast hk`. Use `rootOfUnity_mem_Qbar (k := 2 * N) (Nat.mul_pos two_pos hN) ?_` and prove the remaining obligations. Rewrite using `[← Complex.exp_nat_mul, Complex.exp_eq_one_iff]`. Use `⟨-k, ?_⟩` and prove the remaining obligations.

Use `push_cast`. Take the linear combination `(-2 * (Real.pi : ℂ) * Complex.I) * hk'`.
-/
theorem expAltE_mem (L : PeriodPair) (x y : ℂ) (N : ℕ) (hN : 0 < N) (h : ∃ k : ℤ, (N : ℝ) * altE L x y = k) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L x y : ℂ)) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  obtain ⟨k, hk⟩ := h
  have hk' : (N : ℂ) * (altE L x y : ℂ) = (k : ℂ) := by exact_mod_cast hk
  refine rootOfUnity_mem_Qbar (k := 2 * N) (Nat.mul_pos two_pos hN) ?_
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨-k, ?_⟩
  push_cast
  linear_combination (-2 * (Real.pi : ℂ) * Complex.I) * hk'

/- English proof (translation)
Take `⟨k, hk⟩` from `altEInt L _ _ hu hω`. Establish `he` using `expAltE_mem L u ω N hN ⟨k, by rw [← altE_nat_mul]; exact hk⟩`. Establish `hne` using `Complex.exp_ne_zero (-(Real.pi : ℂ) * Complex.I * (altE L u ω : ℂ))`. Take `⟨hψ, hψne⟩` from `semiChar_mem L ω`. Use `⟨(Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L u ω : ℂ)))⁻¹ * (semiChar L ω)⁻¹, mul_mem (inv_mem he) (inv_mem hψ), mul_ne_zero (inv_ne_zero hne) (inv_ne_zero hψne), fun z => ?_⟩` and prove the remaining obligations.

Establish `h` using `opUMul L u ω (sgStar L) z`. Establish `e : opU L u (opU L ω (sgStar L)) z = (semiChar L ω)⁻¹ * opU L u (sgStar L) z` using `by show opU L ω (sgStar L) (z + u) * _ = (semiChar L ω)⁻¹ * (sgStar L (z + u) * _)`. Rewrite using `[sg_lat L hω]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e]`.

Rewrite using `[← inv_mul_cancel_left₀ hne (opU L (u + ω) (sgStar L) z), ← h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sg_shift (L : PeriodPair) (u ω : ℂ) (N : ℕ) (hN : 0 < N) (hu : (N : ℂ) * u ∈ L.lattice)
    (hω : ω ∈ L.lattice) :
    ∃ c : ℂ, c ∈ Formalism.MainNotions.TaylorLogMetric.Qbar ∧ c ≠ 0 ∧ ∀ z, opU L (u + ω) (sgStar L) z = c * opU L u (sgStar L) z := by
  obtain ⟨k, hk⟩ := altEInt L _ _ hu hω
  have he := expAltE_mem L u ω N hN ⟨k, by rw [← altE_nat_mul]; exact hk⟩
  have hne := Complex.exp_ne_zero (-(Real.pi : ℂ) * Complex.I * (altE L u ω : ℂ))
  obtain ⟨hψ, hψne⟩ := semiChar_mem L ω
  refine ⟨(Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L u ω : ℂ)))⁻¹ * (semiChar L ω)⁻¹,
    mul_mem (inv_mem he) (inv_mem hψ), mul_ne_zero (inv_ne_zero hne) (inv_ne_zero hψne), fun z => ?_⟩
  have h := opUMul L u ω (sgStar L) z
  have e : opU L u (opU L ω (sgStar L)) z = (semiChar L ω)⁻¹ * opU L u (sgStar L) z := by
    show opU L ω (sgStar L) (z + u) * _ = (semiChar L ω)⁻¹ * (sgStar L (z + u) * _)
    rw [sg_lat L hω]
    ring
  rw [e] at h
  rw [← inv_mul_cancel_left₀ hne (opU L (u + ω) (sgStar L) z), ← h]
  ring

/- English proof (translation)
Simplify using `only [opU, herm, map_neg]`. Rewrite using `[show z + -u = -(-z + u) by ring, (sgStarBasic L).2.1 (-z + u)]`. Put the polynomial expressions in normal form.
-/
theorem sg_neg (L : PeriodPair) (u z : ℂ) : opU L (-u) (sgStar L) z = -opU L u (sgStar L) (-z) := by
  simp only [opU, herm, map_neg]
  rw [show z + -u = -(-z + u) by ring, (sgStarBasic L).2.1 (-z + u)]
  ring_nf

/- English proof (translation)
Rewrite using `[sg_neg, neg_zero]`.
-/
theorem sg_neg_val (L : PeriodPair) (u : ℂ) : opU L (-u) (sgStar L) 0 = -opU L u (sgStar L) 0 := by
  rw [sg_neg, neg_zero]

/- English proof (translation)
Establish `hf : opU L (-u) (sgStar L) = fun z => -opU L u (sgStar L) (-z)` using `funext (sg_neg L u)`. Establish `hd : HasDerivAt (opU L u (sgStar L)) (deriv (opU L u (sgStar L)) (-0)) (-0)` using `((sg_analytic L u) _ (Set.mem_univ _)).differentiableAt.hasDerivAt`. Establish `h2` using `(hd.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))).neg`. Rewrite using `[hf]`. Establish `e : (fun z => -opU L u (sgStar L) (-z)) = -(opU L u (sgStar L) ∘ Neg.neg)` using `rfl`.

Rewrite using `[e, h2.deriv]`. Simplify using the standard rewrite rules.
-/
theorem sg_neg_deriv (L : PeriodPair) (u : ℂ) :
    deriv (opU L (-u) (sgStar L)) 0 = deriv (opU L u (sgStar L)) 0 := by
  have hf : opU L (-u) (sgStar L) = fun z => -opU L u (sgStar L) (-z) := funext (sg_neg L u)
  have hd : HasDerivAt (opU L u (sgStar L)) (deriv (opU L u (sgStar L)) (-0)) (-0) :=
    ((sg_analytic L u) _ (Set.mem_univ _)).differentiableAt.hasDerivAt
  have h2 := (hd.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))).neg
  rw [hf]
  have e : (fun z => -opU L u (sgStar L) (-z)) = -(opU L u (sgStar L) ∘ Neg.neg) := rfl
  rw [e, h2.deriv]
  simp

/- English proof (translation)
Establish `h1` using `PDeriv.eventually_notMem L hP`. Establish `h2 : Filter.Tendsto (fun z : ℂ => z + P) (𝓝 0) (𝓝 P)` using `(continuous_add_const P).tendsto' 0 _ (by simp)`. Conclude with `h2.eventually h1`.
-/
theorem ev_add_notMem (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) : ∀ᶠ z in 𝓝 (0 : ℂ), z + P ∉ L.lattice := by
  have h1 := PDeriv.eventually_notMem L hP
  have h2 : Filter.Tendsto (fun z : ℂ => z + P) (𝓝 0) (𝓝 P) := (continuous_add_const P).tendsto' 0 _ (by simp)
  exact h2.eventually h1

/- English proof (translation)
The claim follows from `analyticAt_of_eventually ((ev_add_notMem L hP).mono fun z hz => ((PDeriv.hasDerivAt_P L hz).comp_add_const z P).differentiableAt)`.
-/
theorem wp_analytic (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) :
    AnalyticAt ℂ (fun z => L.weierstrassP (z + P)) 0 :=
  analyticAt_of_eventually ((ev_add_notMem L hP).mono fun z hz =>
    ((PDeriv.hasDerivAt_P L hz).comp_add_const z P).differentiableAt)

/- English proof (translation)
Establish `hA : ∀ u, AnalyticAt ℂ (opU L u (sgStar L)) 0` using `fun u => sg_analytic L u 0 (Set.mem_univ _)`. Establish `hw` using `wp_analytic L hP`. Establish `e1` using `Taylor.taylor0_mul (hA (P + Q)) (hA (P - Q))`. Establish `e2` using `Taylor.taylor0_mul (hA P) (hA P)`. Establish `a3 : AnalyticAt ℂ (fun z => (-1 : ℂ) * L.weierstrassP (z + P)) 0` using `analyticAt_const.mul hw`.

Establish `e3 : taylor0 (fun z => (-1 : ℂ) * L.weierstrassP (z + P)) = PowerSeries.C (-1 : ℂ) * taylor0 (fun z => L.weierstrassP (z + P))`. Rewrite using `[Taylor.taylor0_mul (f := fun _ => (-1 : ℂ)) (g := fun z => L.weierstrassP (z + P)) analyticAt_const hw, Taylor.taylor0_const]`. Establish `a4 : AnalyticAt ℂ (fun z => L.weierstrassP Q + (-1 : ℂ) * L.weierstrassP (z + P)) 0` using `analyticAt_const.add a3`. Establish `e4 : taylor0 (fun z => L.weierstrassP Q + (-1 : ℂ) * L.weierstrassP (z + P)) = PowerSeries.C (L.weierstrassP Q) + PowerSeries.C (-1 : ℂ) * taylor0 (fun z => L.weierstrassP (z + P))`. Rewrite using `[Taylor.taylor0_add (f := fun _ => L.weierstrassP Q) (g := fun z => (-1 : ℂ) * L.weierstrassP (z + P)) analyticAt_const a3, Taylor.taylor0_const, e3]`.

Establish `a2 : AnalyticAt ℂ (fun z => opU L P (sgStar L) z * opU L P (sgStar L) z) 0` using `(hA P).mul (hA P)`. Establish `a5 : AnalyticAt ℂ (fun z => (L.weierstrassP Q + (-1 : ℂ) * L.weierstrassP (z + P)) * (opU L P (sgStar L) z * opU L P (sgStar L) z)) 0` using `a4.mul a2`. Establish `e5 : taylor0 (fun z => (L.weierstrassP Q + (-1 : ℂ) * L.weierstrassP (z + P)) * (opU L P (sgStar L) z * opU L P (sgStar L) z)) = (PowerSeries.C (L.weierstrassP Q) + PowerSeries.C (-1 : ℂ) * taylor0 (fun z => L.weierstrassP (z + P))) * (taylor0 (opU L P (sgStar L)) * taylor0 (opU …`. Rewrite using `[Taylor.taylor0_mul (f := fun z => L.weierstrassP Q + (-1 : ℂ) * L.weierstrassP (z + P)) (g := fun z => opU L P (sgStar L) z * opU L P (sgStar L) z) a4 a2, e4, e2]`. Establish `e6 : taylor0 (fun z => opU L Q (sgStar L) 0 ^ 2 * ((L.weierstrassP Q + (-1 : ℂ) * L.weierstrassP (z + P)) * (opU L P (sgStar L) z * opU L P (sgStar L) z))) = PowerSeries.C (opU L Q (sgStar L) 0 ^ 2) * ((PowerSeries.C (L.weierstrassP Q) + PowerSeries.C (-1 : ℂ) * taylor0 (fun z => …`.

Rewrite using `[Taylor.taylor0_mul (f := fun _ => opU L Q (sgStar L) 0 ^ 2) (g := fun z => (L.weierstrassP Q + (-1 : ℂ) * L.weierstrassP (z + P)) * (opU L P (sgStar L) z * opU L P (sgStar L) z)) analyticAt_const a5, Taylor.taylor0_const, e5]`. Rewrite using `[← e1, ← e6]`. Use `Taylor.taylor0_congr ((ev_add_notMem L hP).mono fun z hz => ?_)` and prove the remaining obligations. Establish `h` using `translateProduct L P Q z hQ hz`. Take the linear combination `h`.
-/
theorem tp_series (L : PeriodPair) (P Q : ℂ) (hQ : Q ∉ L.lattice) (hP : P ∉ L.lattice) :
    taylor0 (opU L (P + Q) (sgStar L)) * taylor0 (opU L (P - Q) (sgStar L)) =
      PowerSeries.C (opU L Q (sgStar L) 0 ^ 2) * ((PowerSeries.C (L.weierstrassP Q) +
        PowerSeries.C (-1 : ℂ) * taylor0 (fun z => L.weierstrassP (z + P))) *
          (taylor0 (opU L P (sgStar L)) * taylor0 (opU L P (sgStar L)))) := by
  have hA : ∀ u, AnalyticAt ℂ (opU L u (sgStar L)) 0 := fun u => sg_analytic L u 0 (Set.mem_univ _)
  have hw := wp_analytic L hP
  have e1 := Taylor.taylor0_mul (hA (P + Q)) (hA (P - Q))
  have e2 := Taylor.taylor0_mul (hA P) (hA P)
  have a3 : AnalyticAt ℂ (fun z => (-1 : ℂ) * L.weierstrassP (z + P)) 0 := analyticAt_const.mul hw
  have e3 : taylor0 (fun z => (-1 : ℂ) * L.weierstrassP (z + P)) =
      PowerSeries.C (-1 : ℂ) * taylor0 (fun z => L.weierstrassP (z + P)) := by
    rw [Taylor.taylor0_mul (f := fun _ => (-1 : ℂ)) (g := fun z => L.weierstrassP (z + P)) analyticAt_const hw,
      Taylor.taylor0_const]
  have a4 : AnalyticAt ℂ (fun z => L.weierstrassP Q + (-1 : ℂ) * L.weierstrassP (z + P)) 0 := analyticAt_const.add a3
  have e4 : taylor0 (fun z => L.weierstrassP Q + (-1 : ℂ) * L.weierstrassP (z + P)) =
      PowerSeries.C (L.weierstrassP Q) + PowerSeries.C (-1 : ℂ) * taylor0 (fun z => L.weierstrassP (z + P)) := by
    rw [Taylor.taylor0_add (f := fun _ => L.weierstrassP Q) (g := fun z => (-1 : ℂ) * L.weierstrassP (z + P))
      analyticAt_const a3, Taylor.taylor0_const, e3]
  have a2 : AnalyticAt ℂ (fun z => opU L P (sgStar L) z * opU L P (sgStar L) z) 0 := (hA P).mul (hA P)
  have a5 : AnalyticAt ℂ (fun z => (L.weierstrassP Q + (-1 : ℂ) * L.weierstrassP (z + P)) *
      (opU L P (sgStar L) z * opU L P (sgStar L) z)) 0 := a4.mul a2
  have e5 : taylor0 (fun z => (L.weierstrassP Q + (-1 : ℂ) * L.weierstrassP (z + P)) *
      (opU L P (sgStar L) z * opU L P (sgStar L) z)) =
      (PowerSeries.C (L.weierstrassP Q) + PowerSeries.C (-1 : ℂ) * taylor0 (fun z => L.weierstrassP (z + P))) *
        (taylor0 (opU L P (sgStar L)) * taylor0 (opU L P (sgStar L))) := by
    rw [Taylor.taylor0_mul (f := fun z => L.weierstrassP Q + (-1 : ℂ) * L.weierstrassP (z + P))
      (g := fun z => opU L P (sgStar L) z * opU L P (sgStar L) z) a4 a2, e4, e2]
  have e6 : taylor0 (fun z => opU L Q (sgStar L) 0 ^ 2 * ((L.weierstrassP Q + (-1 : ℂ) * L.weierstrassP (z + P)) *
      (opU L P (sgStar L) z * opU L P (sgStar L) z))) =
      PowerSeries.C (opU L Q (sgStar L) 0 ^ 2) * ((PowerSeries.C (L.weierstrassP Q) +
        PowerSeries.C (-1 : ℂ) * taylor0 (fun z => L.weierstrassP (z + P))) *
          (taylor0 (opU L P (sgStar L)) * taylor0 (opU L P (sgStar L)))) := by
    rw [Taylor.taylor0_mul (f := fun _ => opU L Q (sgStar L) 0 ^ 2)
      (g := fun z => (L.weierstrassP Q + (-1 : ℂ) * L.weierstrassP (z + P)) *
        (opU L P (sgStar L) z * opU L P (sgStar L) z)) analyticAt_const a5, Taylor.taylor0_const, e5]
  rw [← e1, ← e6]
  refine Taylor.taylor0_congr ((ev_add_notMem L hP).mono fun z hz => ?_)
  have h := translateProduct L P Q z hQ hz
  linear_combination h

/- English proof (translation)
Apply the tactic sequence `refine ⟨?_, ?_, ?_⟩ <;>`. Simplify using `[PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]`.
-/
theorem coeff_mul_low_degrees (f g : PowerSeries ℂ) :
    PowerSeries.coeff 0 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 0 g ∧
    PowerSeries.coeff 1 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 1 g +
      PowerSeries.coeff 1 f * PowerSeries.coeff 0 g ∧
    PowerSeries.coeff 2 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 2 g +
      PowerSeries.coeff 1 f * PowerSeries.coeff 1 g + PowerSeries.coeff 2 f * PowerSeries.coeff 0 g := by
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]

/- English proof (translation)
Apply the tactic sequence `refine ⟨?_, ?_, ?_⟩ <;> simp [PowerSeries.coeff_C]`.
-/
theorem coeff_const_add_low_degrees (c : ℂ) (f : PowerSeries ℂ) :
    PowerSeries.coeff 0 (PowerSeries.C c + f) = c + PowerSeries.coeff 0 f ∧
    PowerSeries.coeff 1 (PowerSeries.C c + f) = PowerSeries.coeff 1 f ∧
    PowerSeries.coeff 2 (PowerSeries.C c + f) = PowerSeries.coeff 2 f := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [PowerSeries.coeff_C]

/- English proof (translation)
Establish `hev` using `ev_add_notMem L hP`. Establish `hW : ∀ z, z + P ∉ L.lattice → HasDerivAt (fun z => L.weierstrassP (z + P)) (L.derivWeierstrassP (z + P)) z` using `fun z hz => (PDeriv.hasDerivAt_P L hz).comp_add_const z P`. Establish `hP0 : (0 : ℂ) + P ∉ L.lattice` using `by rwa [zero_add]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[coeff0_taylor0, zero_add]`.

Rewrite using `[coeff1_taylor0, (hW 0 hP0).deriv, zero_add]`. Rewrite using `[Taylor.coeff_taylor0, iteratedDeriv_succ, iteratedDeriv_one]`. Establish `hd : deriv (fun z => L.weierstrassP (z + P)) =ᶠ[𝓝 (0 : ℂ)] fun z => L.derivWeierstrassP (z + P)` using `hev.mono fun z hz => (hW z hz).deriv`. Rewrite using `[Filter.EventuallyEq.deriv_eq hd, ((pSecond L (0 + P) hP0).comp_add_const 0 P).deriv, zero_add]`. Evaluate the numerical expressions.
-/
theorem wp_coeffs (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) :
    PowerSeries.coeff 0 (taylor0 (fun z => L.weierstrassP (z + P))) = L.weierstrassP P ∧
    PowerSeries.coeff 1 (taylor0 (fun z => L.weierstrassP (z + P))) = L.derivWeierstrassP P ∧
    PowerSeries.coeff 2 (taylor0 (fun z => L.weierstrassP (z + P))) =
      (6 * L.weierstrassP P ^ 2 - L.g₂ / 2) / 2 := by
  have hev := ev_add_notMem L hP
  have hW : ∀ z, z + P ∉ L.lattice → HasDerivAt (fun z => L.weierstrassP (z + P)) (L.derivWeierstrassP (z + P)) z :=
    fun z hz => (PDeriv.hasDerivAt_P L hz).comp_add_const z P
  have hP0 : (0 : ℂ) + P ∉ L.lattice := by rwa [zero_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [coeff0_taylor0, zero_add]
  · rw [coeff1_taylor0, (hW 0 hP0).deriv, zero_add]
  · rw [Taylor.coeff_taylor0, iteratedDeriv_succ, iteratedDeriv_one]
    have hd : deriv (fun z => L.weierstrassP (z + P)) =ᶠ[𝓝 (0 : ℂ)] fun z => L.derivWeierstrassP (z + P) :=
      hev.mono fun z hz => (hW z hz).deriv
    rw [Filter.EventuallyEq.deriv_eq hd, ((pSecond L (0 + P) hP0).comp_add_const 0 P).deriv, zero_add]
    norm_num

/- English proof (translation)
Establish `hsd` using `sgStarBasic L`. Establish `hsA : AnalyticAt ℂ (sgStar L) 0` using `hsd.1.analyticAt 0`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[coeff0_taylor0]`. Conclude with `(hsd.2.2.1 0).2 (zero_mem _)`.

Rewrite using `[coeff1_taylor0]`. Conclude with `hsd.2.2.2.1`. Establish `h1` using `taylorDeriv.2.1 (sgStar L) (-1) hsA`. Establish `e : (fun z => sgStar L ((-1) * z)) = fun z => (-1 : ℂ) * sgStar L z`. Use function extensionality and compare the values at `z`.

Rewrite using `[neg_one_mul, hsd.2.1, neg_one_mul]`. Rewrite `h1` using `[e, Taylor.taylor0_mul (f := fun _ => (-1 : ℂ)) (g := sgStar L) analyticAt_const hsA, Taylor.taylor0_const]`. Establish `h2` using `congrArg (PowerSeries.coeff 2) h1`. Rewrite `h2` using `[PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale]`. Take the linear combination `(-1 / 2 : ℂ) * h2`.
-/
theorem sg_coeffs (L : PeriodPair) :
    PowerSeries.coeff 0 (taylor0 (sgStar L)) = 0 ∧ PowerSeries.coeff 1 (taylor0 (sgStar L)) = 1 ∧
    PowerSeries.coeff 2 (taylor0 (sgStar L)) = 0 := by
  have hsd := sgStarBasic L
  have hsA : AnalyticAt ℂ (sgStar L) 0 := hsd.1.analyticAt 0
  refine ⟨?_, ?_, ?_⟩
  · rw [coeff0_taylor0]
    exact (hsd.2.2.1 0).2 (zero_mem _)
  · rw [coeff1_taylor0]
    exact hsd.2.2.2.1
  · have h1 := taylorDeriv.2.1 (sgStar L) (-1) hsA
    have e : (fun z => sgStar L ((-1) * z)) = fun z => (-1 : ℂ) * sgStar L z := by
      funext z
      rw [neg_one_mul, hsd.2.1, neg_one_mul]
    rw [e, Taylor.taylor0_mul (f := fun _ => (-1 : ℂ)) (g := sgStar L) analyticAt_const hsA,
      Taylor.taylor0_const] at h1
    have h2 := congrArg (PowerSeries.coeff 2) h1
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale] at h2
    linear_combination (-1 / 2 : ℂ) * h2

/- English proof (translation)
Establish `hP0 : (0 : ℂ) + P ∉ L.lattice` using `by rwa [zero_add]`. Rewrite using `[((PDeriv.hasDerivAt_P L hP0).comp_add_const 0 P).deriv, zero_add]`.
-/
theorem wp_deriv0 (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) :
    deriv (fun z => L.weierstrassP (z + P)) 0 = L.derivWeierstrassP P := by
  have hP0 : (0 : ℂ) + P ∉ L.lattice := by rwa [zero_add]
  rw [((PDeriv.hasDerivAt_P L hP0).comp_add_const 0 P).deriv, zero_add]

/- English proof (translation)
Establish `e0` using `congrArg (PowerSeries.coeff 0) h`. Establish `e1` using `congrArg (PowerSeries.coeff 1) h`. Establish `e2` using `congrArg (PowerSeries.coeff 2) h`. Take `⟨a0, a1, a2⟩` from `coeff_mul_low_degrees A B`. Take `⟨x0, x1, x2⟩` from `coeff_mul_low_degrees (PowerSeries.C p + PowerSeries.C (-1 : ℂ) * W) (G * G)`.

Take `⟨c0, c1, c2⟩` from `coeff_const_add_low_degrees p (PowerSeries.C (-1 : ℂ) * W)`. Take `⟨g0, g1, g2⟩` from `coeff_mul_low_degrees G G`. Rewrite `e0`, `e1`, `e2` using `[PowerSeries.coeff_C_mul]`. Rewrite `e0` using `[a0, x0, c0, g0, PowerSeries.coeff_C_mul]`. Rewrite `e1` using `[a1, x1, c0, c1, g0, g1, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]`.

Rewrite `e2` using `[a2, x2, c0, c1, c2, g0, g1, g2, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Take the linear combination `e0`. Take the linear combination `e1`. Take the linear combination `e2`.
-/
theorem series_rel (A B W G : PowerSeries ℂ) (c p : ℂ)
    (h : A * B = PowerSeries.C c * ((PowerSeries.C p + PowerSeries.C (-1 : ℂ) * W) * (G * G))) :
    PowerSeries.coeff 0 A * PowerSeries.coeff 0 B =
      c * ((p - PowerSeries.coeff 0 W) * (PowerSeries.coeff 0 G * PowerSeries.coeff 0 G)) ∧
    PowerSeries.coeff 0 A * PowerSeries.coeff 1 B + PowerSeries.coeff 1 A * PowerSeries.coeff 0 B =
      c * ((p - PowerSeries.coeff 0 W) * (2 * PowerSeries.coeff 0 G * PowerSeries.coeff 1 G) -
        PowerSeries.coeff 1 W * (PowerSeries.coeff 0 G * PowerSeries.coeff 0 G)) ∧
    PowerSeries.coeff 0 A * PowerSeries.coeff 2 B + PowerSeries.coeff 1 A * PowerSeries.coeff 1 B +
        PowerSeries.coeff 2 A * PowerSeries.coeff 0 B =
      c * ((p - PowerSeries.coeff 0 W) * (2 * PowerSeries.coeff 0 G * PowerSeries.coeff 2 G +
          PowerSeries.coeff 1 G * PowerSeries.coeff 1 G) -
        PowerSeries.coeff 1 W * (2 * PowerSeries.coeff 0 G * PowerSeries.coeff 1 G) -
        PowerSeries.coeff 2 W * (PowerSeries.coeff 0 G * PowerSeries.coeff 0 G)) := by
  have e0 := congrArg (PowerSeries.coeff 0) h
  have e1 := congrArg (PowerSeries.coeff 1) h
  have e2 := congrArg (PowerSeries.coeff 2) h
  obtain ⟨a0, a1, a2⟩ := coeff_mul_low_degrees A B
  obtain ⟨x0, x1, x2⟩ := coeff_mul_low_degrees (PowerSeries.C p + PowerSeries.C (-1 : ℂ) * W) (G * G)
  obtain ⟨c0, c1, c2⟩ := coeff_const_add_low_degrees p (PowerSeries.C (-1 : ℂ) * W)
  obtain ⟨g0, g1, g2⟩ := coeff_mul_low_degrees G G
  rw [PowerSeries.coeff_C_mul] at e0 e1 e2
  rw [a0, x0, c0, g0, PowerSeries.coeff_C_mul] at e0
  rw [a1, x1, c0, c1, g0, g1, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at e1
  rw [a2, x2, c0, c1, c2, g0, g1, g2, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at e2
  refine ⟨?_, ?_, ?_⟩
  · linear_combination e0
  · linear_combination e1
  · linear_combination e2

/- English proof (translation)
Take `⟨e0, e1, -⟩` from `series_rel _ _ _ _ _ _ (tp_series L P Q hQ hP)`. Take `⟨w0, w1, -⟩` from `wp_coeffs L hP`. Establish `hwd` using `wp_deriv0 L hP`. Simplify using `only [w0, w1, coeff0_taylor0, coeff1_taylor0, hwd, zero_add] at e0 e1`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Take the linear combination `e0`. Take the linear combination `e1`.
-/
theorem tp_rel (L : PeriodPair) (P Q : ℂ) (hQ : Q ∉ L.lattice) (hP : P ∉ L.lattice) :
    opU L (P + Q) (sgStar L) 0 * opU L (P - Q) (sgStar L) 0 =
      opU L Q (sgStar L) 0 ^ 2 * ((L.weierstrassP Q - L.weierstrassP P) * opU L P (sgStar L) 0 ^ 2) ∧
    deriv (opU L (P + Q) (sgStar L)) 0 * opU L (P - Q) (sgStar L) 0 +
      opU L (P + Q) (sgStar L) 0 * deriv (opU L (P - Q) (sgStar L)) 0 =
      opU L Q (sgStar L) 0 ^ 2 * ((L.weierstrassP Q - L.weierstrassP P) *
        (2 * opU L P (sgStar L) 0 * deriv (opU L P (sgStar L)) 0) -
          L.derivWeierstrassP P * opU L P (sgStar L) 0 ^ 2) := by
  obtain ⟨e0, e1, -⟩ := series_rel _ _ _ _ _ _ (tp_series L P Q hQ hP)
  obtain ⟨w0, w1, -⟩ := wp_coeffs L hP
  have hwd := wp_deriv0 L hP
  simp only [w0, w1, coeff0_taylor0, coeff1_taylor0, hwd, zero_add] at e0 e1
  refine ⟨?_, ?_⟩
  · linear_combination e0
  · linear_combination e1

/- English proof (translation)
Establish `h` using `tp_series L Q Q hQ hQ`. Rewrite `h` using `[sub_self, translation_operator_zero]`. Take `⟨-, e1, e2⟩` from `series_rel _ _ _ _ _ _ h`. Take `⟨w0, w1, w2⟩` from `wp_coeffs L hQ`. Take `⟨s0, s1, s2⟩` from `sg_coeffs L`.

Establish `hwd` using `wp_deriv0 L hQ`. Simplify using `only [w0, w1, w2, s0, s1, s2, coeff0_taylor0, coeff1_taylor0, hwd, zero_add] at e1 e2`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take the linear combination `e1`. Take the linear combination `e2`.
-/
theorem dbl_rel (L : PeriodPair) (Q : ℂ) (hQ : Q ∉ L.lattice) :
    opU L (Q + Q) (sgStar L) 0 = -L.derivWeierstrassP Q * opU L Q (sgStar L) 0 ^ 4 ∧
    deriv (opU L (Q + Q) (sgStar L)) 0 = opU L Q (sgStar L) 0 ^ 2 *
      (-L.derivWeierstrassP Q * (2 * opU L Q (sgStar L) 0 * deriv (opU L Q (sgStar L)) 0) -
        (6 * L.weierstrassP Q ^ 2 - L.g₂ / 2) / 2 * opU L Q (sgStar L) 0 ^ 2) := by
  have h := tp_series L Q Q hQ hQ
  rw [sub_self, translation_operator_zero] at h
  obtain ⟨-, e1, e2⟩ := series_rel _ _ _ _ _ _ h
  obtain ⟨w0, w1, w2⟩ := wp_coeffs L hQ
  obtain ⟨s0, s1, s2⟩ := sg_coeffs L
  have hwd := wp_deriv0 L hQ
  simp only [w0, w1, w2, s0, s1, s2, coeff0_taylor0, coeff1_taylor0, hwd, zero_add] at e1 e2
  refine ⟨?_, ?_⟩
  · linear_combination e1
  · linear_combination e2

/- English proof (translation)
Establish `h` using `tp_rel L (((m + 2 : ℕ) : ℂ) * Q) Q hQ hP`. Establish `e1 : ((m + 2 : ℕ) : ℂ) * Q + Q = ((m + 3 : ℕ) : ℂ) * Q` using `by push_cast; ring`. Establish `e2 : ((m + 2 : ℕ) : ℂ) * Q - Q = ((m + 1 : ℕ) : ℂ) * Q` using `by push_cast; ring`. Rewrite `h` using `[e1, e2]`. Conclude with `h`.
-/
theorem step_rel (L : PeriodPair) (Q : ℂ) (m : ℕ) (hQ : Q ∉ L.lattice) (hP : ((m + 2 : ℕ) : ℂ) * Q ∉ L.lattice) :
    opU L (((m + 3 : ℕ) : ℂ) * Q) (sgStar L) 0 * opU L (((m + 1 : ℕ) : ℂ) * Q) (sgStar L) 0 =
      opU L Q (sgStar L) 0 ^ 2 * ((L.weierstrassP Q - L.weierstrassP (((m + 2 : ℕ) : ℂ) * Q)) *
        opU L (((m + 2 : ℕ) : ℂ) * Q) (sgStar L) 0 ^ 2) ∧
    deriv (opU L (((m + 3 : ℕ) : ℂ) * Q) (sgStar L)) 0 * opU L (((m + 1 : ℕ) : ℂ) * Q) (sgStar L) 0 +
      opU L (((m + 3 : ℕ) : ℂ) * Q) (sgStar L) 0 * deriv (opU L (((m + 1 : ℕ) : ℂ) * Q) (sgStar L)) 0 =
      opU L Q (sgStar L) 0 ^ 2 * ((L.weierstrassP Q - L.weierstrassP (((m + 2 : ℕ) : ℂ) * Q)) *
        (2 * opU L (((m + 2 : ℕ) : ℂ) * Q) (sgStar L) 0 * deriv (opU L (((m + 2 : ℕ) : ℂ) * Q) (sgStar L)) 0) -
          L.derivWeierstrassP (((m + 2 : ℕ) : ℂ) * Q) * opU L (((m + 2 : ℕ) : ℂ) * Q) (sgStar L) 0 ^ 2) := by
  have h := tp_rel L (((m + 2 : ℕ) : ℂ) * Q) Q hQ hP
  have e1 : ((m + 2 : ℕ) : ℂ) * Q + Q = ((m + 3 : ℕ) : ℂ) * Q := by push_cast; ring
  have e2 : ((m + 2 : ℕ) : ℂ) * Q - Q = ((m + 1 : ℕ) : ℂ) * Q := by push_cast; ring
  rw [e1, e2] at h
  exact h

/- English proof (translation)
Establish `hQ : Q ∉ L.lattice` using `by simpa using hmin 1 one_pos (by omega)`. Establish `hx : opU L Q (sgStar L) 0 ≠ 0` using `sg_val_ne L hQ`. Establish `hKne : ∀ j : ℕ, 0 < j → j < N → opU L ((j : ℂ) * Q) (sgStar L) 0 ≠ 0` using `fun j h0 h1 => sg_val_ne L (hmin j h0 h1)`. Establish `hPT : ∀ j : ℕ, 0 < j → j < N → L.weierstrassP ((j : ℂ) * Q) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar ∧ L.derivWeierstrassP ((j : ℂ) * Q) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar`. Introduce `j h0 h1`.

Use `pTorsAlg_of L hg2 hg3 _ ⟨N, by omega, ?_⟩ (hmin j h0 h1)` and prove the remaining obligations. Rewrite using `[show (N : ℂ) * ((j : ℂ) * Q) = (j : ℂ) * ((N : ℂ) * Q) by ring, ← nsmul_eq_mul]`. Conclude with `nsmul_mem hNQ j`. Establish `hPQ` using `hPT 1 one_pos (by omega)`. Simplify using `only [Nat.cast_one, one_mul] at hPQ`.

Establish `S1 : ∃ a ∈ Formalism.MainNotions.TaylorLogMetric.Qbar, a ≠ 0 ∧ opU L (((1 : ℕ) : ℂ) * Q) (sgStar L) 0 = a * opU L Q (sgStar L) 0 ^ (1 ^ 2) ∧ ∃ b ∈ Formalism.MainNotions.TaylorLogMetric.Qbar, deriv (opU L (((1 : ℕ) : ℂ) * Q) (sgStar L)) 0 = opU L (((1 : ℕ) : ℂ) * Q) (sgStar L) 0 * …`. Use `⟨1, one_mem _, one_ne_zero, by simp, 0, zero_mem _, ?_⟩` and prove the remaining obligations. Simplify using `only [Nat.cast_one, one_mul, add_zero]`. Clear the denominators using the available nonvanishing facts. Establish `S2 : ∃ a ∈ Formalism.MainNotions.TaylorLogMetric.Qbar, a ≠ 0 ∧ opU L (((2 : ℕ) : ℂ) * Q) (sgStar L) 0 = a * opU L Q (sgStar L) 0 ^ (2 ^ 2) ∧ ∃ b ∈ Formalism.MainNotions.TaylorLogMetric.Qbar, deriv (opU L (((2 : ℕ) : ℂ) * Q) (sgStar L)) 0 = opU L (((2 : ℕ) : ℂ) * Q) (sgStar L) 0 * …`.

Take `⟨d1, d2⟩` from `dbl_rel L Q hQ`. Establish `e : ((2 : ℕ) : ℂ) * Q = Q + Q` using `by push_cast; ring`. Establish `hK2` using `hKne 2 two_pos (by omega)`. Rewrite `hK2`, the goal using `[e]`. Establish `hp' : L.derivWeierstrassP Q ≠ 0`.

Introduce `h0`. Rewrite `hK2` using `[d1, h0]`. Simplify using `at hK2`. Use `⟨-L.derivWeierstrassP Q, neg_mem hPQ.2, neg_ne_zero.2 hp', by rw [d1]; ring, ((6 * L.weierstrassP Q ^ 2 - L.g₂ / 2) / 2) / L.derivWeierstrassP Q, ?_, ?_⟩` and prove the remaining obligations. Establish `h6 : (6 : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar`.

Use `natCast_mem Formalism.MainNotions.TaylorLogMetric.Qbar 6` as an intermediate fact. Simplify using `using this`. Establish `h2' : (2 : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar`. Use `natCast_mem Formalism.MainNotions.TaylorLogMetric.Qbar 2` as an intermediate fact. Simplify using `using this`.

Conclude with `div_mem (div_mem (sub_mem (mul_mem h6 (pow_mem hPQ.1 2)) (div_mem hg2 h2')) h2') hPQ.2`. Rewrite using `[d2, d1]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero`. Introduce `_ j hj`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hj`. Break down `hj with rfl | rfl` into its components or cases.

Conclude with `S1`. Conclude with `S2`. Consider the case `succ m ih`. Introduce `hm j hj`. Establish `ih'` using `ih (by omega)`.

Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hj`. Break down `hj with rfl | rfl` into its components or cases. Conclude with `ih' (m + 2) (by simp)`. Use `show ∃ a ∈ Formalism.MainNotions.TaylorLogMetric.Qbar, a ≠ 0 ∧ opU L (((m + 3 : ℕ) : ℂ) * Q) (sgStar L) 0 = a * opU L Q (sgStar L) 0 ^ ((m + 3) ^ 2) ∧ ∃ b ∈ Formalism.MainNotions.TaylorLogMetric.Qbar, deriv (opU L (((m + 3 : ℕ) : ℂ) * Q) (sgStar L)) 0 = opU L (((m + 3 : ℕ) : ℂ) * …`. Take `⟨a1, ha1, ha1ne, hK1, b1, hb1, hD1⟩` from `ih' (m + 1) (by simp)`.

Take `⟨a2, ha2, ha2ne, hK2, b2, hb2, hD2⟩` from `ih' (m + 2) (by simp)`. Take `⟨c0, c1⟩` from `step_rel L Q m hQ (hmin (m + 2) (by omega) (by omega))`. Establish `hK3ne` using `hKne (m + 3) (by omega) (by omega)`. Establish `hK1ne` using `hKne (m + 1) (by omega) (by omega)`. Take `⟨hpm, hqm⟩` from `hPT (m + 2) (by omega) (by omega)`.

Use `set x := opU L Q (sgStar L) 0 with hxdef`. Use `set y := deriv (opU L Q (sgStar L)) 0 with hydef`. Use `set K1 := opU L (((m + 1 : ℕ) : ℂ) * Q) (sgStar L) 0 with hK1def`. Use `set K2 := opU L (((m + 2 : ℕ) : ℂ) * Q) (sgStar L) 0 with hK2def`. Use `set K3 := opU L (((m + 3 : ℕ) : ℂ) * Q) (sgStar L) 0 with hK3def`.

Use `set D1 := deriv (opU L (((m + 1 : ℕ) : ℂ) * Q) (sgStar L)) 0 with hD1def`. Use `set D2 := deriv (opU L (((m + 2 : ℕ) : ℂ) * Q) (sgStar L)) 0 with hD2def`. Use `set D3 := deriv (opU L (((m + 3 : ℕ) : ℂ) * Q) (sgStar L)) 0 with hD3def`. Use `set p := L.weierstrassP Q - L.weierstrassP (((m + 2 : ℕ) : ℂ) * Q) with hpdef`. Use `set q := L.derivWeierstrassP (((m + 2 : ℕ) : ℂ) * Q) with hqdef`.

Establish `hp : p ≠ 0`. Introduce `h0`. Apply `mul_ne_zero hK3ne hK1ne` to reduce the goal to its premises. Rewrite using `[c0, h0]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2' : (2 : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar`. Use `natCast_mem Formalism.MainNotions.TaylorLogMetric.Qbar 2` as an intermediate fact. Simplify using `using this`. Establish `hpQ : p ∈ Formalism.MainNotions.TaylorLogMetric.Qbar` using `sub_mem hPQ.1 hpm`. Use `⟨p * a2 ^ 2 * a1⁻¹, mul_mem (mul_mem hpQ (pow_mem ha2 2)) (inv_mem ha1), mul_ne_zero (mul_ne_zero hp (pow_ne_zero 2 ha2ne)) (inv_ne_zero ha1ne), ?_, 2 * b2 - b1 - q * p⁻¹, sub_mem (sub_mem (mul_mem h2' hb2) hb1) (mul_mem hqm (inv_mem hpQ)), ?_⟩` and prove the remaining obligations.

Apply `mul_right_cancel₀ hK1ne` to reduce the goal to its premises. Establish `hpow : x ^ ((m + 3) ^ 2) * x ^ ((m + 1) ^ 2) = x ^ 2 * (x ^ ((m + 2) ^ 2)) ^ 2`. Rewrite using `[← pow_mul, ← pow_add, ← pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hinv : a1⁻¹ * a1 = 1` using `inv_mul_cancel₀ ha1ne`. Rewrite using `[c0, hK2]`. Use `conv_rhs => rw [hK1]`. Take the linear combination `(-(p * a2 ^ 2)) * hpow - p * a2 ^ 2 * x ^ ((m + 3) ^ 2) * x ^ ((m + 1) ^ 2) * hinv`. Apply `mul_right_cancel₀ hK1ne` to reduce the goal to its premises.

Rewrite `c1` using `[hD1, hD2]`. Establish `hinvp : p⁻¹ * p = 1` using `inv_mul_cancel₀ hp`. Move the coercions through the operations in `at c1 ⊢`. Take the linear combination `c1 + (-2 * (((m : ℂ) + 2) * (y / x) + b2) + q * p⁻¹) * c0 + x ^ 2 * q * K2 ^ 2 * hinvp`.
-/
theorem kv_rec (L : PeriodPair) (hg2 : L.g₂ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) (hg3 : L.g₃ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) (Q : ℂ) (N : ℕ)
    (hN3 : 3 ≤ N) (hNQ : (N : ℂ) * Q ∈ L.lattice) (hmin : ∀ m : ℕ, 0 < m → m < N → (m : ℂ) * Q ∉ L.lattice) :
    ∀ m : ℕ, m + 3 ≤ N → ∀ j ∈ ({m + 1, m + 2} : Finset ℕ),
      ∃ a ∈ Formalism.MainNotions.TaylorLogMetric.Qbar, a ≠ 0 ∧
        opU L ((j : ℂ) * Q) (sgStar L) 0 = a * opU L Q (sgStar L) 0 ^ (j ^ 2) ∧
        ∃ b ∈ Formalism.MainNotions.TaylorLogMetric.Qbar, deriv (opU L ((j : ℂ) * Q) (sgStar L)) 0 = opU L ((j : ℂ) * Q) (sgStar L) 0 *
          ((j : ℂ) * (deriv (opU L Q (sgStar L)) 0 / opU L Q (sgStar L) 0) + b) := by
  have hQ : Q ∉ L.lattice := by simpa using hmin 1 one_pos (by omega)
  have hx : opU L Q (sgStar L) 0 ≠ 0 := sg_val_ne L hQ
  have hKne : ∀ j : ℕ, 0 < j → j < N → opU L ((j : ℂ) * Q) (sgStar L) 0 ≠ 0 := fun j h0 h1 =>
    sg_val_ne L (hmin j h0 h1)
  have hPT : ∀ j : ℕ, 0 < j → j < N →
      L.weierstrassP ((j : ℂ) * Q) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar ∧ L.derivWeierstrassP ((j : ℂ) * Q) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    intro j h0 h1
    refine pTorsAlg_of L hg2 hg3 _ ⟨N, by omega, ?_⟩ (hmin j h0 h1)
    rw [show (N : ℂ) * ((j : ℂ) * Q) = (j : ℂ) * ((N : ℂ) * Q) by ring, ← nsmul_eq_mul]
    exact nsmul_mem hNQ j
  have hPQ := hPT 1 one_pos (by omega)
  simp only [Nat.cast_one, one_mul] at hPQ

  have S1 : ∃ a ∈ Formalism.MainNotions.TaylorLogMetric.Qbar, a ≠ 0 ∧
      opU L (((1 : ℕ) : ℂ) * Q) (sgStar L) 0 = a * opU L Q (sgStar L) 0 ^ (1 ^ 2) ∧
      ∃ b ∈ Formalism.MainNotions.TaylorLogMetric.Qbar, deriv (opU L (((1 : ℕ) : ℂ) * Q) (sgStar L)) 0 = opU L (((1 : ℕ) : ℂ) * Q) (sgStar L) 0 *
        (((1 : ℕ) : ℂ) * (deriv (opU L Q (sgStar L)) 0 / opU L Q (sgStar L) 0) + b) := by
    refine ⟨1, one_mem _, one_ne_zero, by simp, 0, zero_mem _, ?_⟩
    simp only [Nat.cast_one, one_mul, add_zero]
    field_simp

  have S2 : ∃ a ∈ Formalism.MainNotions.TaylorLogMetric.Qbar, a ≠ 0 ∧
      opU L (((2 : ℕ) : ℂ) * Q) (sgStar L) 0 = a * opU L Q (sgStar L) 0 ^ (2 ^ 2) ∧
      ∃ b ∈ Formalism.MainNotions.TaylorLogMetric.Qbar, deriv (opU L (((2 : ℕ) : ℂ) * Q) (sgStar L)) 0 = opU L (((2 : ℕ) : ℂ) * Q) (sgStar L) 0 *
        (((2 : ℕ) : ℂ) * (deriv (opU L Q (sgStar L)) 0 / opU L Q (sgStar L) 0) + b) := by
    obtain ⟨d1, d2⟩ := dbl_rel L Q hQ
    have e : ((2 : ℕ) : ℂ) * Q = Q + Q := by push_cast; ring
    have hK2 := hKne 2 two_pos (by omega)
    rw [e] at hK2 ⊢
    have hp' : L.derivWeierstrassP Q ≠ 0 := by
      intro h0
      rw [d1, h0] at hK2
      simp at hK2
    refine ⟨-L.derivWeierstrassP Q, neg_mem hPQ.2, neg_ne_zero.2 hp', by rw [d1]; ring,
      ((6 * L.weierstrassP Q ^ 2 - L.g₂ / 2) / 2) / L.derivWeierstrassP Q, ?_, ?_⟩
    · have h6 : (6 : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
        have := natCast_mem Formalism.MainNotions.TaylorLogMetric.Qbar 6
        simpa using this
      have h2' : (2 : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
        have := natCast_mem Formalism.MainNotions.TaylorLogMetric.Qbar 2
        simpa using this
      exact div_mem (div_mem (sub_mem (mul_mem h6 (pow_mem hPQ.1 2)) (div_mem hg2 h2')) h2') hPQ.2
    · rw [d2, d1]
      field_simp
      ring
  intro m
  induction m with
  | zero =>
    intro _ j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact S1
    · exact S2
  | succ m ih =>
    intro hm j hj
    have ih' := ih (by omega)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact ih' (m + 2) (by simp)
    · show ∃ a ∈ Formalism.MainNotions.TaylorLogMetric.Qbar, a ≠ 0 ∧
        opU L (((m + 3 : ℕ) : ℂ) * Q) (sgStar L) 0 = a * opU L Q (sgStar L) 0 ^ ((m + 3) ^ 2) ∧
        ∃ b ∈ Formalism.MainNotions.TaylorLogMetric.Qbar, deriv (opU L (((m + 3 : ℕ) : ℂ) * Q) (sgStar L)) 0 =
          opU L (((m + 3 : ℕ) : ℂ) * Q) (sgStar L) 0 *
            (((m + 3 : ℕ) : ℂ) * (deriv (opU L Q (sgStar L)) 0 / opU L Q (sgStar L) 0) + b)
      obtain ⟨a1, ha1, ha1ne, hK1, b1, hb1, hD1⟩ := ih' (m + 1) (by simp)
      obtain ⟨a2, ha2, ha2ne, hK2, b2, hb2, hD2⟩ := ih' (m + 2) (by simp)
      obtain ⟨c0, c1⟩ := step_rel L Q m hQ (hmin (m + 2) (by omega) (by omega))
      have hK3ne := hKne (m + 3) (by omega) (by omega)
      have hK1ne := hKne (m + 1) (by omega) (by omega)
      obtain ⟨hpm, hqm⟩ := hPT (m + 2) (by omega) (by omega)
      set x := opU L Q (sgStar L) 0 with hxdef
      set y := deriv (opU L Q (sgStar L)) 0 with hydef
      set K1 := opU L (((m + 1 : ℕ) : ℂ) * Q) (sgStar L) 0 with hK1def
      set K2 := opU L (((m + 2 : ℕ) : ℂ) * Q) (sgStar L) 0 with hK2def
      set K3 := opU L (((m + 3 : ℕ) : ℂ) * Q) (sgStar L) 0 with hK3def
      set D1 := deriv (opU L (((m + 1 : ℕ) : ℂ) * Q) (sgStar L)) 0 with hD1def
      set D2 := deriv (opU L (((m + 2 : ℕ) : ℂ) * Q) (sgStar L)) 0 with hD2def
      set D3 := deriv (opU L (((m + 3 : ℕ) : ℂ) * Q) (sgStar L)) 0 with hD3def
      set p := L.weierstrassP Q - L.weierstrassP (((m + 2 : ℕ) : ℂ) * Q) with hpdef
      set q := L.derivWeierstrassP (((m + 2 : ℕ) : ℂ) * Q) with hqdef
      have hp : p ≠ 0 := by
        intro h0
        apply mul_ne_zero hK3ne hK1ne
        rw [c0, h0]
        ring
      have h2' : (2 : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
        have := natCast_mem Formalism.MainNotions.TaylorLogMetric.Qbar 2
        simpa using this
      have hpQ : p ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := sub_mem hPQ.1 hpm
      refine ⟨p * a2 ^ 2 * a1⁻¹, mul_mem (mul_mem hpQ (pow_mem ha2 2)) (inv_mem ha1),
        mul_ne_zero (mul_ne_zero hp (pow_ne_zero 2 ha2ne)) (inv_ne_zero ha1ne), ?_, 2 * b2 - b1 - q * p⁻¹,
        sub_mem (sub_mem (mul_mem h2' hb2) hb1) (mul_mem hqm (inv_mem hpQ)), ?_⟩
      · apply mul_right_cancel₀ hK1ne
        have hpow : x ^ ((m + 3) ^ 2) * x ^ ((m + 1) ^ 2) = x ^ 2 * (x ^ ((m + 2) ^ 2)) ^ 2 := by
          rw [← pow_mul, ← pow_add, ← pow_add]
          congr 1
          ring
        have hinv : a1⁻¹ * a1 = 1 := inv_mul_cancel₀ ha1ne
        rw [c0, hK2]
        conv_rhs => rw [hK1]
        linear_combination (-(p * a2 ^ 2)) * hpow - p * a2 ^ 2 * x ^ ((m + 3) ^ 2) * x ^ ((m + 1) ^ 2) * hinv
      · apply mul_right_cancel₀ hK1ne
        rw [hD1, hD2] at c1
        have hinvp : p⁻¹ * p = 1 := inv_mul_cancel₀ hp
        push_cast at c1 ⊢
        linear_combination c1 + (-2 * (((m : ℂ) + 2) * (y / x) + b2) + q * p⁻¹) * c0 + x ^ 2 * q * K2 ^ 2 * hinvp

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, N = n + 3` from `⟨N - 3, by omega⟩`. Establish `hQ : Q ∉ L.lattice` using `by simpa using hmin 1 one_pos (by omega)`. Establish `hx` using `sg_val_ne L hQ`. Take `⟨a, ha, hane, hK, b, hb, hD⟩` from `kv_rec L hg2 hg3 Q (n + 3) hN3 hNQ hmin n le_rfl (n + 2) (by simp)`. Establish `hNneg : ((n + 3 : ℕ) : ℂ) * (-Q) ∈ L.lattice`.

Rewrite using `[mul_neg]`. Conclude with `neg_mem hNQ`. Take `⟨c, hc, hcne, hsh⟩` from `sg_shift L (-Q) (((n + 3 : ℕ) : ℂ) * Q) (n + 3) (by omega) hNneg hNQ`. Establish `e : -Q + ((n + 3 : ℕ) : ℂ) * Q = ((n + 2 : ℕ) : ℂ) * Q` using `by push_cast; ring`. Rewrite `hsh` using `[e]`.

Establish `hKv : opU L (((n + 2 : ℕ) : ℂ) * Q) (sgStar L) 0 = -c * opU L Q (sgStar L) 0`. Rewrite using `[hsh, sg_neg_val]`. Expand and normalize the polynomial expressions, which then agree. Establish `hDv : deriv (opU L (((n + 2 : ℕ) : ℂ) * Q) (sgStar L)) 0 = c * deriv (opU L Q (sgStar L)) 0`. Establish `hf : opU L (((n + 2 : ℕ) : ℂ) * Q) (sgStar L) = fun z => c * opU L (-Q) (sgStar L) z` using `funext hsh`.

Rewrite using `[hf, deriv_const_mul _ ((sg_analytic L (-Q)) 0 (Set.mem_univ _)).differentiableAt, sg_neg_deriv]`. Rewrite `hK` using `[hKv]`. Rewrite `hD` using `[hDv, hKv]`. Use `set x := opU L Q (sgStar L) 0 with hxdef`. Use `set y := deriv (opU L Q (sgStar L)) 0 with hydef`.

Establish `e2 : (n + 2) ^ 2 = (n ^ 2 + 4 * n + 3) + 1` using `by ring`. Rewrite `hK` using `[e2, pow_succ]`. Establish `hxe : x ^ (n ^ 2 + 4 * n + 3) * a = -c`. Apply `mul_right_cancel₀ hx` to reduce the goal to its premises. Take the linear combination `(-1 : ℂ) * hK`.

Establish `hxe' : x ^ (n ^ 2 + 4 * n + 3) = -c / a` using `eq_div_of_mul_eq hane hxe`. Establish `hxQ : x ∈ Formalism.MainNotions.TaylorLogMetric.Qbar`. Use `mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := n ^ 2 + 4 * n + 3) (by positivity) ?_)` and prove the remaining obligations. Rewrite using `[hxe']`. Conclude with `mem_algebraicClosure_iff.1 (div_mem (neg_mem hc) ha)`.

Use `⟨hxQ, ?_⟩` and prove the remaining obligations. Establish `hxinv : x * x⁻¹ = 1` using `mul_inv_cancel₀ hx`. Move the coercions through the operations in `at hD`. Establish `h1 : c * (y * ((n : ℂ) + 3) + x * b) = 0`. Take the linear combination `hD - c * ((n : ℂ) + 2) * y * hxinv`.

Establish `h2 : y * ((n : ℂ) + 3) + x * b = 0` using `(mul_eq_zero.1 h1).resolve_left hcne`. Establish `h3 : (n : ℂ) + 3 ≠ 0`. Establish `: ((n + 3 : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast (by omega : n + 3 ≠ 0)`. Move the coercions through the operations in `at this`. Conclude with `this`.

Establish `hy : y = -(x * b) / ((n : ℂ) + 3)` using `eq_div_of_mul_eq h3 (by linear_combination h2)`. Rewrite using `[hy]`. Establish `h3Q : (n : ℂ) + 3 ∈ Formalism.MainNotions.TaylorLogMetric.Qbar`. Use `natCast_mem Formalism.MainNotions.TaylorLogMetric.Qbar (n + 3)` as an intermediate fact. Move the coercions through the operations in `at this`.

Conclude with `this`. Conclude with `div_mem (neg_mem (mul_mem hxQ hb)) h3Q`.
-/
theorem kv_main (L : PeriodPair) (hg2 : L.g₂ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) (hg3 : L.g₃ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) (Q : ℂ) (N : ℕ)
    (hN3 : 3 ≤ N) (hNQ : (N : ℂ) * Q ∈ L.lattice) (hmin : ∀ m : ℕ, 0 < m → m < N → (m : ℂ) * Q ∉ L.lattice) :
    opU L Q (sgStar L) 0 ∈ Formalism.MainNotions.TaylorLogMetric.Qbar ∧ deriv (opU L Q (sgStar L)) 0 ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 3 := ⟨N - 3, by omega⟩
  have hQ : Q ∉ L.lattice := by simpa using hmin 1 one_pos (by omega)
  have hx := sg_val_ne L hQ
  obtain ⟨a, ha, hane, hK, b, hb, hD⟩ := kv_rec L hg2 hg3 Q (n + 3) hN3 hNQ hmin n le_rfl (n + 2) (by simp)
  have hNneg : ((n + 3 : ℕ) : ℂ) * (-Q) ∈ L.lattice := by
    rw [mul_neg]
    exact neg_mem hNQ
  obtain ⟨c, hc, hcne, hsh⟩ := sg_shift L (-Q) (((n + 3 : ℕ) : ℂ) * Q) (n + 3) (by omega) hNneg hNQ
  have e : -Q + ((n + 3 : ℕ) : ℂ) * Q = ((n + 2 : ℕ) : ℂ) * Q := by push_cast; ring
  rw [e] at hsh
  have hKv : opU L (((n + 2 : ℕ) : ℂ) * Q) (sgStar L) 0 = -c * opU L Q (sgStar L) 0 := by
    rw [hsh, sg_neg_val]
    ring
  have hDv : deriv (opU L (((n + 2 : ℕ) : ℂ) * Q) (sgStar L)) 0 = c * deriv (opU L Q (sgStar L)) 0 := by
    have hf : opU L (((n + 2 : ℕ) : ℂ) * Q) (sgStar L) = fun z => c * opU L (-Q) (sgStar L) z := funext hsh
    rw [hf, deriv_const_mul _ ((sg_analytic L (-Q)) 0 (Set.mem_univ _)).differentiableAt, sg_neg_deriv]
  rw [hKv] at hK
  rw [hDv, hKv] at hD
  set x := opU L Q (sgStar L) 0 with hxdef
  set y := deriv (opU L Q (sgStar L)) 0 with hydef
  have e2 : (n + 2) ^ 2 = (n ^ 2 + 4 * n + 3) + 1 := by ring
  rw [e2, pow_succ] at hK
  have hxe : x ^ (n ^ 2 + 4 * n + 3) * a = -c := by
    apply mul_right_cancel₀ hx
    linear_combination (-1 : ℂ) * hK
  have hxe' : x ^ (n ^ 2 + 4 * n + 3) = -c / a := eq_div_of_mul_eq hane hxe
  have hxQ : x ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := n ^ 2 + 4 * n + 3) (by positivity) ?_)
    rw [hxe']
    exact mem_algebraicClosure_iff.1 (div_mem (neg_mem hc) ha)
  refine ⟨hxQ, ?_⟩
  have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  push_cast at hD
  have h1 : c * (y * ((n : ℂ) + 3) + x * b) = 0 := by
    linear_combination hD - c * ((n : ℂ) + 2) * y * hxinv
  have h2 : y * ((n : ℂ) + 3) + x * b = 0 := (mul_eq_zero.1 h1).resolve_left hcne
  have h3 : (n : ℂ) + 3 ≠ 0 := by
    have : ((n + 3 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 3 ≠ 0)
    push_cast at this
    exact this
  have hy : y = -(x * b) / ((n : ℂ) + 3) := eq_div_of_mul_eq h3 (by linear_combination h2)
  rw [hy]
  have h3Q : (n : ℂ) + 3 ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    have := natCast_mem Formalism.MainNotions.TaylorLogMetric.Qbar (n + 3)
    push_cast at this
    exact this
  exact div_mem (neg_mem (mul_mem hxQ hb)) h3Q

/- English proof (translation)
Establish `hspec` using `Nat.find_spec hu`. Establish `hmin : ∀ m : ℕ, 0 < m → m < Nat.find hu → (m : ℂ) * u ∉ L.lattice` using `fun m h0 hlt hm => Nat.find_min hu hlt ⟨h0, hm⟩`. Distinguish the cases in `h3 : 3 ≤ Nat.find hu`. Conclude with `kv_main L hg2 hg3 u _ h3 hspec.2 hmin`. Establish `hne1 : Nat.find hu ≠ 1`.

Introduce `h`. Use `hspec.2` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `hu' (by simpa using this)`. Establish `h2 : Nat.find hu = 2`.

Use `hspec.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h2u : (2 : ℂ) * u ∈ L.lattice`. Use `hspec.2` as an intermediate fact. Rewrite `this` using `[h2]`.

Conclude with `this` after adjusting the coercions. Use `set Q' := u / 2 with hQ'def`. Establish `eu : Q' + Q' = u` using `by rw [hQ'def]; ring`. Establish `hQ'4 : ((4 : ℕ) : ℂ) * Q' ∈ L.lattice`. Rewrite using `[show ((4 : ℕ) : ℂ) * Q' = 2 * u by rw [hQ'def]; push_cast; ring]`.

Conclude with `h2u`. Establish `hmin' : ∀ m : ℕ, 0 < m → m < 4 → (m : ℂ) * Q' ∉ L.lattice`. Introduce `m h0 h4 hm`. Use `interval_cases m`. Apply `hu'` to reduce the goal to its premises.

Establish `hm' : Q' ∈ L.lattice` using `by simpa using hm`. Rewrite using `[← eu]`. Conclude with `add_mem hm' hm'`. Apply `hu'` to reduce the goal to its premises. Rewrite using `[show u = ((2 : ℕ) : ℂ) * Q' by rw [hQ'def]; push_cast; ring]`.

Conclude with `hm`. Apply `hu'` to reduce the goal to its premises. Establish `hm' : Q' ∈ L.lattice`. Rewrite using `[show Q' = 2 * u - ((3 : ℕ) : ℂ) * Q' by rw [hQ'def]; push_cast; ring]`. Conclude with `sub_mem h2u hm`.

Rewrite using `[← eu]`. Conclude with `add_mem hm' hm'`. Take `⟨hkQ, -⟩` from `kv_main L hg2 hg3 Q' 4 (by norm_num) hQ'4 hmin'`. Establish `hQ' : Q' ∉ L.lattice` using `by simpa using hmin' 1 one_pos (by norm_num)`. Take `⟨d1, -⟩` from `dbl_rel L Q' hQ'`.

Rewrite `d1` using `[eu]`. Establish `hp'` using `(pTorsAlg_of L hg2 hg3 Q' ⟨4, by norm_num, hQ'4⟩ hQ').2`. Use `⟨by rw [d1]; exact mul_mem (neg_mem hp') (pow_mem hkQ 4), ?_⟩` and prove the remaining obligations. Establish `h2u' : ((2 : ℕ) : ℂ) * u ∈ L.lattice` using `by exact_mod_cast h2u`. Take `⟨c, hc, hcne, hsh⟩` from `sg_shift L u (-(2 * u)) 2 two_pos h2u' (neg_mem h2u)`.

Rewrite `hsh` using `[show u + -(2 * u) = -u by ring]`. Establish `hk` using `sg_val_ne L hu'`. Establish `hv : -opU L u (sgStar L) 0 = c * opU L u (sgStar L) 0` using `by rw [← sg_neg_val, hsh]`. Establish `hcm : c = -1` using `mul_right_cancel₀ hk (by linear_combination -hv)`. Establish `hf : opU L (-u) (sgStar L) = fun z => c * opU L u (sgStar L) z` using `funext hsh`.

Establish `hd1 : deriv (opU L (-u) (sgStar L)) 0 = c * deriv (opU L u (sgStar L)) 0`. Rewrite using `[hf, deriv_const_mul _ ((sg_analytic L u) 0 (Set.mem_univ _)).differentiableAt]`. Rewrite `hd1` using `[sg_neg_deriv, hcm]`. Establish `h0 : deriv (opU L u (sgStar L)) 0 = 0` using `by linear_combination hd1 / 2`. Rewrite using `[h0]`.

Conclude with `zero_mem _`.
-/
theorem kv (L : PeriodPair) (hg2 : L.g₂ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) (hg3 : L.g₃ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) (u : ℂ)
    (hu : ∃ N : ℕ, 0 < N ∧ (N : ℂ) * u ∈ L.lattice) (hu' : u ∉ L.lattice) :
    opU L u (sgStar L) 0 ∈ Formalism.MainNotions.TaylorLogMetric.Qbar ∧ deriv (opU L u (sgStar L)) 0 ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  have hspec := Nat.find_spec hu
  have hmin : ∀ m : ℕ, 0 < m → m < Nat.find hu → (m : ℂ) * u ∉ L.lattice := fun m h0 hlt hm =>
    Nat.find_min hu hlt ⟨h0, hm⟩
  by_cases h3 : 3 ≤ Nat.find hu
  · exact kv_main L hg2 hg3 u _ h3 hspec.2 hmin
  have hne1 : Nat.find hu ≠ 1 := by
    intro h
    have := hspec.2
    rw [h] at this
    exact hu' (by simpa using this)
  have h2 : Nat.find hu = 2 := by
    have := hspec.1
    omega
  have h2u : (2 : ℂ) * u ∈ L.lattice := by
    have := hspec.2
    rw [h2] at this
    exact_mod_cast this
  set Q' := u / 2 with hQ'def
  have eu : Q' + Q' = u := by rw [hQ'def]; ring
  have hQ'4 : ((4 : ℕ) : ℂ) * Q' ∈ L.lattice := by
    rw [show ((4 : ℕ) : ℂ) * Q' = 2 * u by rw [hQ'def]; push_cast; ring]
    exact h2u
  have hmin' : ∀ m : ℕ, 0 < m → m < 4 → (m : ℂ) * Q' ∉ L.lattice := by
    intro m h0 h4 hm
    interval_cases m
    · apply hu'
      have hm' : Q' ∈ L.lattice := by simpa using hm
      rw [← eu]
      exact add_mem hm' hm'
    · apply hu'
      rw [show u = ((2 : ℕ) : ℂ) * Q' by rw [hQ'def]; push_cast; ring]
      exact hm
    · apply hu'
      have hm' : Q' ∈ L.lattice := by
        rw [show Q' = 2 * u - ((3 : ℕ) : ℂ) * Q' by rw [hQ'def]; push_cast; ring]
        exact sub_mem h2u hm
      rw [← eu]
      exact add_mem hm' hm'
  obtain ⟨hkQ, -⟩ := kv_main L hg2 hg3 Q' 4 (by norm_num) hQ'4 hmin'
  have hQ' : Q' ∉ L.lattice := by simpa using hmin' 1 one_pos (by norm_num)
  obtain ⟨d1, -⟩ := dbl_rel L Q' hQ'
  rw [eu] at d1
  have hp' := (pTorsAlg_of L hg2 hg3 Q' ⟨4, by norm_num, hQ'4⟩ hQ').2
  refine ⟨by rw [d1]; exact mul_mem (neg_mem hp') (pow_mem hkQ 4), ?_⟩
  have h2u' : ((2 : ℕ) : ℂ) * u ∈ L.lattice := by exact_mod_cast h2u
  obtain ⟨c, hc, hcne, hsh⟩ := sg_shift L u (-(2 * u)) 2 two_pos h2u' (neg_mem h2u)
  rw [show u + -(2 * u) = -u by ring] at hsh
  have hk := sg_val_ne L hu'
  have hv : -opU L u (sgStar L) 0 = c * opU L u (sgStar L) 0 := by rw [← sg_neg_val, hsh]
  have hcm : c = -1 := mul_right_cancel₀ hk (by linear_combination -hv)
  have hf : opU L (-u) (sgStar L) = fun z => c * opU L u (sgStar L) z := funext hsh
  have hd1 : deriv (opU L (-u) (sgStar L)) 0 = c * deriv (opU L u (sgStar L)) 0 := by
    rw [hf, deriv_const_mul _ ((sg_analytic L u) 0 (Set.mem_univ _)).differentiableAt]
  rw [sg_neg_deriv, hcm] at hd1
  have h0 : deriv (opU L u (sgStar L)) 0 = 0 := by linear_combination hd1 / 2
  rw [h0]
  exact zero_mem _

/- English proof (translation)
Introduce and unpack `s ⟨N, hN, hNs⟩`. Establish `ht2 : ((2 : ℕ) : ℂ) * (ω₀ / 2) ∈ L.lattice`. Rewrite using `[show ((2 : ℕ) : ℂ) * (ω₀ / 2) = ω₀ by push_cast; ring]`. Conclude with `hω`. Establish `hkt` using `(kv L hg2 hg3 (ω₀ / 2) ⟨2, two_pos, ht2⟩ hh).1`.

Establish `hkt0` using `sg_val_ne L hh`. Take `⟨k, hk⟩` from `altEInt L _ _ hNs hω`. Establish `hph : Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L s (ω₀ / 2) : ℂ)) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar`. Use `expAltE_mem L s (ω₀ / 2) (2 * N) (by omega) ⟨k, ?_⟩` and prove the remaining obligations. Establish `e1 : ω₀ = ((2 : ℕ) : ℂ) * (ω₀ / 2)` using `by push_cast; ring`.

Rewrite `hk` using `[e1, altE_nat_mul, altE_mul_nat]`. Rewrite using `[← hk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `htor : ∃ M : ℕ, 0 < M ∧ (M : ℂ) * (s + ω₀ / 2) ∈ L.lattice`.

Use `⟨2 * N, by omega, ?_⟩` and prove the remaining obligations. Establish `e : ((2 * N : ℕ) : ℂ) * (s + ω₀ / 2) = (N : ℂ) * s + (N : ℂ) * s + N • ω₀`. Rewrite using `[nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `add_mem (add_mem hNs hNs) (nsmul_mem hω N)`. Establish `hform : opU L s (th0 L (ω₀ / 2)) = fun z => (Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L s (ω₀ / 2) : ℂ)) / opU L (ω₀ / 2) (sgStar L) 0) * opU L (s + ω₀ / 2) (sgStar L) z`. Use function extensionality and compare the values at `z`. Rewrite using `[opUTh0 L (ω₀ / 2) s z]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hcQ : Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L s (ω₀ / 2) : ℂ)) / opU L (ω₀ / 2) (sgStar L) 0 ∈ Formalism.MainNotions.TaylorLogMetric.Qbar` using `div_mem hph hkt`. Establish `hsd` using `sgStarBasic L`. Rewrite using `[hform, deriv_const_mul _ ((sg_analytic L _) 0 (Set.mem_univ _)).differentiableAt]`. Distinguish the cases in `hu : s + ω₀ / 2 ∈ L.lattice`.

Establish `hG : opU L (s + ω₀ / 2) (sgStar L) = fun z => (semiChar L (s + ω₀ / 2))⁻¹ * sgStar L z`. Use function extensionality and compare the values at `(sg_lat L hu)`. Establish `hψ` using `(semiChar_mem L (s + ω₀ / 2)).1`. Use `⟨mul_mem hcQ ?_, mul_mem hcQ ?_⟩` and prove the remaining obligations. Rewrite using `[hG]`.

Simplify using `only`. Rewrite using `[(hsd.2.2.1 0).2 (zero_mem _), mul_zero]`. Conclude with `zero_mem _`. Rewrite using `[hG, deriv_const_mul _ (hsd.1 0), hsd.2.2.2.1, mul_one]`. Conclude with `inv_mem hψ`.

Take `⟨h0, h1⟩` from `kv L hg2 hg3 _ htor hu`. Conclude with `⟨mul_mem hcQ h0, mul_mem hcQ h1⟩`.
-/
theorem kleinAlg_of (L : PeriodPair) (ω₀ : ℂ) (hω : ω₀ ∈ L.lattice) (hh : ω₀ / 2 ∉ L.lattice)
    (hg2 : L.g₂ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) (hg3 : L.g₃ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) : KleinAlg L ω₀ := by
  rintro s ⟨N, hN, hNs⟩
  have ht2 : ((2 : ℕ) : ℂ) * (ω₀ / 2) ∈ L.lattice := by
    rw [show ((2 : ℕ) : ℂ) * (ω₀ / 2) = ω₀ by push_cast; ring]
    exact hω
  have hkt := (kv L hg2 hg3 (ω₀ / 2) ⟨2, two_pos, ht2⟩ hh).1
  have hkt0 := sg_val_ne L hh
  obtain ⟨k, hk⟩ := altEInt L _ _ hNs hω
  have hph : Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L s (ω₀ / 2) : ℂ)) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    refine expAltE_mem L s (ω₀ / 2) (2 * N) (by omega) ⟨k, ?_⟩
    have e1 : ω₀ = ((2 : ℕ) : ℂ) * (ω₀ / 2) := by push_cast; ring
    rw [e1, altE_nat_mul, altE_mul_nat] at hk
    rw [← hk]
    push_cast
    ring
  have htor : ∃ M : ℕ, 0 < M ∧ (M : ℂ) * (s + ω₀ / 2) ∈ L.lattice := by
    refine ⟨2 * N, by omega, ?_⟩
    have e : ((2 * N : ℕ) : ℂ) * (s + ω₀ / 2) = (N : ℂ) * s + (N : ℂ) * s + N • ω₀ := by
      rw [nsmul_eq_mul]
      push_cast
      ring
    rw [e]
    exact add_mem (add_mem hNs hNs) (nsmul_mem hω N)
  have hform : opU L s (th0 L (ω₀ / 2)) = fun z =>
      (Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L s (ω₀ / 2) : ℂ)) / opU L (ω₀ / 2) (sgStar L) 0) *
        opU L (s + ω₀ / 2) (sgStar L) z := by
    funext z
    rw [opUTh0 L (ω₀ / 2) s z]
    ring
  have hcQ : Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L s (ω₀ / 2) : ℂ)) / opU L (ω₀ / 2) (sgStar L) 0
      ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := div_mem hph hkt
  have hsd := sgStarBasic L
  rw [hform, deriv_const_mul _ ((sg_analytic L _) 0 (Set.mem_univ _)).differentiableAt]
  by_cases hu : s + ω₀ / 2 ∈ L.lattice
  · have hG : opU L (s + ω₀ / 2) (sgStar L) = fun z => (semiChar L (s + ω₀ / 2))⁻¹ * sgStar L z :=
      funext (sg_lat L hu)
    have hψ := (semiChar_mem L (s + ω₀ / 2)).1
    refine ⟨mul_mem hcQ ?_, mul_mem hcQ ?_⟩
    · rw [hG]
      simp only
      rw [(hsd.2.2.1 0).2 (zero_mem _), mul_zero]
      exact zero_mem _
    · rw [hG, deriv_const_mul _ (hsd.1 0), hsd.2.2.2.1, mul_one]
      exact inv_mem hψ
  · obtain ⟨h0, h1⟩ := kv L hg2 hg3 _ htor hu
    exact ⟨mul_mem hcQ h0, mul_mem hcQ h1⟩

end KleinPf

section KleinAllPf

/- English proof (translation)
Introduce `D cc δ B hcc hδ`. Establish `sd : B.StdOK` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ`. Take `⟨h2, h3⟩` from `Sigma.invAlg' D cc δ hcc hδ B.L B.lat`. Conclude with `kleinAlg_of B.L B.ω₀ sd.per sd.half h2 h3`.
-/
theorem klein_forms_algebraic : KleinAll := by
  intro D cc δ B hcc hδ
  have sd : B.StdOK := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ
  obtain ⟨h2, h3⟩ := Sigma.invAlg' D cc δ hcc hδ B.L B.lat
  exact kleinAlg_of B.L B.ω₀ sd.per sd.half h2 h3

/- English proof (translation)
The claim follows from `kerTransAll_of_kleinAll klein_forms_algebraic`.
-/
theorem kernel_torsion_translates_algebraic : KerTransAll := kerTransAll_of_kleinAll klein_forms_algebraic

/- English proof (translation)
The claim follows from `algFact_of_kerTrans kernel_torsion_translates_algebraic`.
-/
theorem algebraic_fact_kernels : AlgFact := algFact_of_kerTrans kernel_torsion_translates_algebraic

/- English proof (translation)
The claim follows from `algZero_of_trans kernel_torsion_translates_algebraic`.
-/
theorem zero_value_algebraic : AlgZero := algZero_of_trans kernel_torsion_translates_algebraic

/- English proof (translation)
The claim follows from `zeroAlg_of_kerTrans kernel_torsion_translates_algebraic`.
-/
theorem vanishing_algebraic : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestB.ZeroAlg := zeroAlg_of_kerTrans kernel_torsion_translates_algebraic

end KleinAllPf

end AlgP

end Formalism.L2.KerInert
