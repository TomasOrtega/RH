import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterHypothesisAllPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterLargeAllPointsStatement
import Formalism.PieriBlockIdeals.PieriColumnMinors.LargeParameterEstimates
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie

namespace GlobalTheory.ExpTie

open Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.LargeParameterEstimates

/- English proof (translation)
Establish `ht4 : (4 : ℝ) ≤ P.t`. Use `hH.t_ge; have : 4 ≤ P.t := by omega` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hA1 : 1 ≤ A` using `by linarith [hR.t_le]`. Establish `hx` using `hB.x_ge`.

Establish `hL` using `hB.L_ge`. Establish `hA7 : A ^ 7 ≤ P.b`. Establish `h3` using `hB.b3`. Establish `hx2 : (1 : ℝ) ≤ P.x ^ 2` using `one_le_pow₀ (by linarith)`. Establish `hL3 : (1 : ℝ) ≤ P.L ^ 3` using `one_le_pow₀ (by linarith)`.

Establish `hA70 : 0 ≤ A ^ 7` using `by positivity`. Establish `: A ^ 7 ≤ 40 * A ^ 7 * P.x ^ 2 * P.L ^ 3`. Establish `h1 : (1 : ℝ) ≤ 40 * P.x ^ 2 * P.L ^ 3` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `this.trans h3`.

Establish `hA4 : A ^ 4 ≤ P.b ^ ((4 : ℝ) / 7)`. Establish `e : (A ^ 7) ^ ((4 : ℝ) / 7) = A ^ 4`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]`. Evaluate the numerical expressions. Rewrite using `[← e]`.

Conclude with `Real.rpow_le_rpow (by positivity) hA7 (by norm_num)`. Use `Formalism.CohomologicalDescent.LargeParameterEstimates.large_bound_of_constraints P X' A hH hR hB h45 ?_` and prove the remaining obligations. Establish `hc : 0 ≤ 4 * P.x ^ 2 * P.L ^ 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem large_of_rows_pow {P : Par} {X' A : ℝ} (hH : P.Hyp) (hR : Rows P X' A) (hB : Big P.L P.x X' A)
    (h45 : P.b ^ ((4 : ℝ) / 5) ≤ P.w'' / P.S)
    (hpow : 4 * P.x ^ 2 * P.L ^ 2 * P.b ^ ((4 : ℝ) / 7) < P.b ^ ((4 : ℝ) / 5)) : P.Large := by
  have ht4 : (4 : ℝ) ≤ P.t := by
    have := hH.t_ge; have : 4 ≤ P.t := by omega
    exact_mod_cast this
  have hA1 : 1 ≤ A := by linarith [hR.t_le]
  have hx := hB.x_ge
  have hL := hB.L_ge
  have hA7 : A ^ 7 ≤ P.b := by
    have h3 := hB.b3
    have hx2 : (1 : ℝ) ≤ P.x ^ 2 := one_le_pow₀ (by linarith)
    have hL3 : (1 : ℝ) ≤ P.L ^ 3 := one_le_pow₀ (by linarith)
    have hA70 : 0 ≤ A ^ 7 := by positivity
    have : A ^ 7 ≤ 40 * A ^ 7 * P.x ^ 2 * P.L ^ 3 := by
      have h1 : (1 : ℝ) ≤ 40 * P.x ^ 2 * P.L ^ 3 := by nlinarith
      nlinarith
    exact this.trans h3
  have hA4 : A ^ 4 ≤ P.b ^ ((4 : ℝ) / 7) := by
    have e : (A ^ 7) ^ ((4 : ℝ) / 7) = A ^ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    rw [← e]
    exact Real.rpow_le_rpow (by positivity) hA7 (by norm_num)
  refine Formalism.CohomologicalDescent.LargeParameterEstimates.large_bound_of_constraints P X' A hH hR hB h45 ?_
  have hc : 0 ≤ 4 * P.x ^ 2 * P.L ^ 2 := by positivity
  calc 4 * A ^ 4 * P.x ^ 2 * P.L ^ 2 = (4 * P.x ^ 2 * P.L ^ 2) * A ^ 4 := by ring
    _ ≤ (4 * P.x ^ 2 * P.L ^ 2) * P.b ^ ((4 : ℝ) / 7) := mul_le_mul_of_nonneg_left hA4 hc
    _ = 4 * P.x ^ 2 * P.L ^ 2 * P.b ^ ((4 : ℝ) / 7) := by ring
    _ < P.b ^ ((4 : ℝ) / 5) := hpow

/- English proof (translation)
Establish `hΔ0 : 0 ≤ Δ`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Use the polynomial consequences of the given equalities and inequalities. Establish `hrhs : x * Real.exp (x ^ e) / Real.exp (x ^ (e / 3)) / (x * n) = Real.exp (x ^ e - x ^ (e / 3)) / n`.

Rewrite using `[Real.exp_sub]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hrhs, le_div_iff₀ hS, ← Real.exp_mul, le_div_iff₀ hn]`. Establish `hkn : k * n ≤ x ^ (a1 + a2)`. Rewrite using `[Real.rpow_add hx]; exact mul_le_mul hkx hnx hn.le (by positivity)`.

Establish `h1 : k * (4 * Δ) * n ≤ Real.exp (1 / 10 * x ^ e) * Real.exp (x ^ (e / 4) / 2)`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul (by linarith) hΔ hΔ0 (by positivity)` to reduce the goal to its premises. Use `_ ≤ Real.exp (1 / 10 * x ^ e) * Real.exp (x ^ (e / 4) / 2) := mul_le_mul_of_nonneg_right E1 (by positivity)`. Rewrite `h1` using `[← Real.exp_add]`.

Establish `h2 : Real.exp (1 / 10 * x ^ e + x ^ (e / 4) / 2) ≤ Real.exp (x ^ e * (1 / 5) - x ^ (e / 3))` using `Real.exp_le_exp.2 (by linarith)`. Establish `h3` using `mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos (x ^ e * ((4 : ℝ) / 5))).le`. Rewrite `h3` using `[← Real.exp_add]`. Establish `e4 : x ^ e * ((4 : ℝ) / 5) + (x ^ e * (1 / 5) - x ^ (e / 3)) = x ^ e - x ^ (e / 3)` using `by ring`. Rewrite `h3` using `[e4]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem w_over_S_real {x e k n Δ a1 a2 : ℝ} (hx : 0 < x) (hk : 0 ≤ k) (hn : 0 < n) (hS : 0 < k * (4 * Δ))
    (hkx : k ≤ x ^ a1) (hnx : n ≤ x ^ a2) (hΔ : Δ ≤ Real.exp (x ^ (e / 4) / 2))
    (E1 : 4 * x ^ (a1 + a2) ≤ Real.exp (1 / 10 * x ^ e)) (E2 : 20 * x ^ (e / 3) ≤ x ^ e)
    (E3 : 10 * x ^ (e / 4) ≤ x ^ e) :
    Real.exp (x ^ e) ^ ((4 : ℝ) / 5) ≤ x * Real.exp (x ^ e) / Real.exp (x ^ (e / 3)) / (x * n) / (k * (4 * Δ)) := by
  have hΔ0 : 0 ≤ Δ := by
    by_contra h; push_neg at h; nlinarith
  have hrhs : x * Real.exp (x ^ e) / Real.exp (x ^ (e / 3)) / (x * n) = Real.exp (x ^ e - x ^ (e / 3)) / n := by
    rw [Real.exp_sub]; field_simp
  rw [hrhs, le_div_iff₀ hS, ← Real.exp_mul, le_div_iff₀ hn]
  have hkn : k * n ≤ x ^ (a1 + a2) := by
    rw [Real.rpow_add hx]; exact mul_le_mul hkx hnx hn.le (by positivity)
  have h1 : k * (4 * Δ) * n ≤ Real.exp (1 / 10 * x ^ e) * Real.exp (x ^ (e / 4) / 2) := by
    calc k * (4 * Δ) * n = (4 * (k * n)) * Δ := by ring
      _ ≤ (4 * x ^ (a1 + a2)) * Real.exp (x ^ (e / 4) / 2) := by
          apply mul_le_mul (by linarith) hΔ hΔ0 (by positivity)
      _ ≤ Real.exp (1 / 10 * x ^ e) * Real.exp (x ^ (e / 4) / 2) :=
          mul_le_mul_of_nonneg_right E1 (by positivity)
  rw [← Real.exp_add] at h1
  have h2 : Real.exp (1 / 10 * x ^ e + x ^ (e / 4) / 2) ≤ Real.exp (x ^ e * (1 / 5) - x ^ (e / 3)) :=
    Real.exp_le_exp.2 (by linarith)
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos (x ^ e * ((4 : ℝ) / 5))).le
  rw [← Real.exp_add] at h3
  have e4 : x ^ e * ((4 : ℝ) / 5) + (x ^ e * (1 / 5) - x ^ (e / 3)) = x ^ e - x ^ (e / 3) := by ring
  rw [e4] at h3
  calc Real.exp (x ^ e * ((4 : ℝ) / 5)) * (k * (4 * Δ)) * n
      = Real.exp (x ^ e * ((4 : ℝ) / 5)) * (k * (4 * Δ) * n) := by ring
    _ ≤ _ := h3

/- English proof (translation)
Rewrite using `[← Real.exp_mul, ← Real.exp_mul]`. Establish `e1 : x ^ (2 + 2 * e) = x ^ 2 * (x ^ e) ^ 2`. Rewrite using `[Real.rpow_add hx, Real.rpow_two, mul_comm 2 e, Real.rpow_mul hx.le, Real.rpow_two]`. Rewrite `E` using `[e1]`. Establish `hp : 0 < x ^ 2 * (x ^ e) ^ 2` using `by have := Real.rpow_pos_of_pos hx e; positivity`.

Establish `h1 : 4 * x ^ 2 * (x ^ e) ^ 2 < Real.exp (8 / 35 * x ^ e)` using `by linarith`. Establish `h2` using `mul_lt_mul_of_pos_right h1 (Real.exp_pos (x ^ e * ((4 : ℝ) / 7)))`. Rewrite `h2` using `[← Real.exp_add]`. Establish `e2 : 8 / 35 * x ^ e + x ^ e * ((4 : ℝ) / 7) = x ^ e * ((4 : ℝ) / 5)` using `by ring`. Rewrite `h2` using `[e2]`. Then use the resulting hypothesis.
-/
theorem pow_real {x e : ℝ} (hx : 0 < x) (E : 5 * x ^ (2 + 2 * e) ≤ Real.exp (8 / 35 * x ^ e)) :
    4 * x ^ 2 * (x ^ e) ^ 2 * Real.exp (x ^ e) ^ ((4 : ℝ) / 7) < Real.exp (x ^ e) ^ ((4 : ℝ) / 5) := by
  rw [← Real.exp_mul, ← Real.exp_mul]
  have e1 : x ^ (2 + 2 * e) = x ^ 2 * (x ^ e) ^ 2 := by
    rw [Real.rpow_add hx, Real.rpow_two, mul_comm 2 e, Real.rpow_mul hx.le, Real.rpow_two]
  rw [e1] at E
  have hp : 0 < x ^ 2 * (x ^ e) ^ 2 := by have := Real.rpow_pos_of_pos hx e; positivity
  have h1 : 4 * x ^ 2 * (x ^ e) ^ 2 < Real.exp (8 / 35 * x ^ e) := by linarith
  have h2 := mul_lt_mul_of_pos_right h1 (Real.exp_pos (x ^ e * ((4 : ℝ) / 7)))
  rw [← Real.exp_add] at h2
  have e2 : 8 / 35 * x ^ e + x ^ e * ((4 : ℝ) / 7) = x ^ e * ((4 : ℝ) / 5) := by ring
  rwa [e2] at h2

end GlobalTheory.ExpTie

namespace GlobalTheory.ExpTie

open Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.LargeParameterEstimates

/- English proof (translation)
Establish `E1` using `Formalism.CohomologicalDescent.LargeParameterEstimates.eventually_power_le_exp_mul_power 4 ((9 / 2 + 10 * eps + eps / 100) + (2 + 8 * eps + eps / 100)) (1 / 10) eps (by norm_num) he`. Establish `E4` using `Formalism.CohomologicalDescent.LargeParameterEstimates.eventually_power_le_exp_mul_power 5 (2 + 2 * eps) (8 / 35) eps (by norm_num) he`. Establish `E2 : ∀ᶠ x : ℝ in Filter.atTop, 20 ≤ x ^ (2 * eps / 3)` using `(tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _`. Establish `E3 : ∀ᶠ x : ℝ in Filter.atTop, 10 ≤ x ^ (3 * eps / 4)` using `(tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _`. Establish `E : ∀ᶠ x : ℝ in Filter.atTop, 0 < x ∧ 4 * x ^ ((9 / 2 + 10 * eps + eps / 100) + (2 + 8 * eps + eps / 100)) ≤ Real.exp (1 / 10 * x ^ eps) ∧ 20 * x ^ (eps / 3) ≤ x ^ eps ∧ 10 * x ^ (eps / 4) ≤ x ^ eps ∧ 5 * x ^ (2 + 2 * eps) ≤ Real.exp (8 / 35 * x ^ eps)` using `by filter_upwards [E1, E2, E3, E4, Filter.eventually_gt_atTop 0] with x e1 e2 e3 e4 hx`.

Use `⟨hx, e1, ?_, ?_, e4⟩` and prove the remaining obligations. Establish `s : x ^ eps = x ^ (eps / 3) * x ^ (2 * eps / 3)`. Rewrite using `[← Real.rpow_add hx]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Use `Real.rpow_pos_of_pos hx (eps / 3)` as an intermediate fact. Rewrite using `[s]`. Use the polynomial consequences of the given equalities and inequalities. Establish `s : x ^ eps = x ^ (eps / 4) * x ^ (3 * eps / 4)`. Rewrite using `[← Real.rpow_add hx]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `Real.rpow_pos_of_pos hx (eps / 4)` as an intermediate fact. Rewrite using `[s]`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `Filter.eventually_atTop.1 E`.
-/
theorem ev_large (eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
    0 < x ∧
    4 * x ^ ((9 / 2 + 10 * eps + eps / 100) + (2 + 8 * eps + eps / 100)) ≤ Real.exp (1 / 10 * x ^ eps) ∧
    20 * x ^ (eps / 3) ≤ x ^ eps ∧ 10 * x ^ (eps / 4) ≤ x ^ eps ∧
    5 * x ^ (2 + 2 * eps) ≤ Real.exp (8 / 35 * x ^ eps) := by
  have E1 := Formalism.CohomologicalDescent.LargeParameterEstimates.eventually_power_le_exp_mul_power 4 ((9 / 2 + 10 * eps + eps / 100) + (2 + 8 * eps + eps / 100)) (1 / 10) eps
    (by norm_num) he
  have E4 := Formalism.CohomologicalDescent.LargeParameterEstimates.eventually_power_le_exp_mul_power 5 (2 + 2 * eps) (8 / 35) eps (by norm_num) he
  have E2 : ∀ᶠ x : ℝ in Filter.atTop, 20 ≤ x ^ (2 * eps / 3) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have E3 : ∀ᶠ x : ℝ in Filter.atTop, 10 ≤ x ^ (3 * eps / 4) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have E : ∀ᶠ x : ℝ in Filter.atTop, 0 < x ∧
      4 * x ^ ((9 / 2 + 10 * eps + eps / 100) + (2 + 8 * eps + eps / 100)) ≤ Real.exp (1 / 10 * x ^ eps) ∧
      20 * x ^ (eps / 3) ≤ x ^ eps ∧ 10 * x ^ (eps / 4) ≤ x ^ eps ∧
      5 * x ^ (2 + 2 * eps) ≤ Real.exp (8 / 35 * x ^ eps) := by
    filter_upwards [E1, E2, E3, E4, Filter.eventually_gt_atTop 0] with x e1 e2 e3 e4 hx
    refine ⟨hx, e1, ?_, ?_, e4⟩
    · have s : x ^ eps = x ^ (eps / 3) * x ^ (2 * eps / 3) := by
        rw [← Real.rpow_add hx]; congr 1; ring
      have := Real.rpow_pos_of_pos hx (eps / 3)
      rw [s]; nlinarith
    · have s : x ^ eps = x ^ (eps / 4) * x ^ (3 * eps / 4) := by
        rw [← Real.rpow_add hx]; congr 1; ring
      have := Real.rpow_pos_of_pos hx (eps / 4)
      rw [s]; nlinarith
  exact Filter.eventually_atTop.1 E

/- English proof (translation)
Use `⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩` and prove the remaining obligations. Take `⟨x0, hx0⟩` from `ev_large eps he`. Use `⟨x0, fun x hx hle i p _ _ j => ?_⟩` and prove the remaining obligations. Take `⟨hxp, E1, E2, E3, E4⟩` from `hx0 x hle`. Establish `hxx : (Fm.L x i).sc.x = x` using `Fm.L_x x i hx`.

Establish `hee : (Fm.L x i).sc.eps = eps` using `Fm.L_eps x i`. Establish `hsz` using `Fm.sizes x hx i`. Establish `hN : SizeN (Fm.L x i)` using `hsz.1`. Establish `hK : SizeK (Fm.L x i)` using `hsz.2.2.1`. Establish `hD` using `(Fm.params x hx i).logDel`.

Establish `hS` using `(Fm.L x i).Sc_pos`. Rewrite `hS` using `[(Fm.L x i).Sc_eq]`. Unfold `SizeN szTh at hN`. Unfold `SizeK szTh at hK`. Rewrite `hN`, `hK`, `hD` using `[hxx, hee]`.

Prove the components needed by the constructor for the conclusion. Use `show Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) ^ ((4 : ℝ) / 5) ≤ (Fm.L x i).sc.x * Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) / Real.exp ((Fm.L x i).sc.x ^ ((Fm.L x i).sc.eps / 3)) / ((Fm.L x i).sc.x * ((Fm.D x i).R.n : ℝ)) / (Fm.L x i).Sc`. Rewrite using `[(Fm.L x i).Sc_eq, hxx, hee]`. Establish `hk : (0 : ℝ) ≤ (Fm.D x i).R.k` using `Nat.cast_nonneg _`. Establish `hn : (0 : ℝ) < (Fm.D x i).R.n` using `lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hN.1`.

Establish `hΔ : ((Fm.D x i).s.Del : ℝ) ≤ Real.exp (x ^ (eps / 4) / 2)`. Establish `h4 : 0 < 4 * ((Fm.D x i).s.Del : ℝ)` using `pos_of_mul_pos_right hS hk`. Conclude with `(Real.log_le_iff_le_exp (by linarith)).1 hD`. Conclude with `w_over_S_real hxp hk hn hS hK.2 hN.2 hΔ E1 E2 E3`. Use `show 4 * (Fm.L x i).sc.x ^ 2 * ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) ^ 2 * Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) ^ ((4 : ℝ) / 7) < Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) ^ ((4 : ℝ) / 5)`.

Rewrite using `[hxx, hee]`. Conclude with `pow_real hxp E4`.
-/
theorem parOf_further : AtPts fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m,
    (parOf (Fm.L x i) j).b ^ ((4 : ℝ) / 5) ≤ (parOf (Fm.L x i) j).w'' / (parOf (Fm.L x i) j).S ∧
    4 * (parOf (Fm.L x i) j).x ^ 2 * (parOf (Fm.L x i) j).L ^ 2 * (parOf (Fm.L x i) j).b ^ ((4 : ℝ) / 7) <
      (parOf (Fm.L x i) j).b ^ ((4 : ℝ) / 5) := by
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := ev_large eps he
  refine ⟨x0, fun x hx hle i p _ _ j => ?_⟩
  obtain ⟨hxp, E1, E2, E3, E4⟩ := hx0 x hle
  have hxx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hee : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hsz := Fm.sizes x hx i
  have hN : SizeN (Fm.L x i) := hsz.1
  have hK : SizeK (Fm.L x i) := hsz.2.2.1
  have hD := (Fm.params x hx i).logDel
  have hS := (Fm.L x i).Sc_pos
  rw [(Fm.L x i).Sc_eq] at hS
  unfold SizeN szTh at hN
  unfold SizeK szTh at hK
  rw [hxx, hee] at hN hK hD
  constructor
  · show Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) ^ ((4 : ℝ) / 5) ≤
      (Fm.L x i).sc.x * Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) /
        Real.exp ((Fm.L x i).sc.x ^ ((Fm.L x i).sc.eps / 3)) / ((Fm.L x i).sc.x * ((Fm.D x i).R.n : ℝ)) / (Fm.L x i).Sc
    rw [(Fm.L x i).Sc_eq, hxx, hee]
    have hk : (0 : ℝ) ≤ (Fm.D x i).R.k := Nat.cast_nonneg _
    have hn : (0 : ℝ) < (Fm.D x i).R.n := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hN.1
    have hΔ : ((Fm.D x i).s.Del : ℝ) ≤ Real.exp (x ^ (eps / 4) / 2) := by
      have h4 : 0 < 4 * ((Fm.D x i).s.Del : ℝ) := pos_of_mul_pos_right hS hk
      exact (Real.log_le_iff_le_exp (by linarith)).1 hD
    exact w_over_S_real hxp hk hn hS hK.2 hN.2 hΔ E1 E2 E3
  · show 4 * (Fm.L x i).sc.x ^ 2 * ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) ^ 2 *
        Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) ^ ((4 : ℝ) / 7) <
      Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) ^ ((4 : ℝ) / 5)
    rw [hxx, hee]
    exact pow_real hxp E4

/- English proof (translation)
The claim follows from `atPts_imp (atPts_and (atPts_and parOf_hyp GlobalTheory.T.parameter_large_all_points) parOf_further) fun _ _ _ _ _ H j => by obtain ⟨⟨hH, hR⟩, hE⟩ := H obtain ⟨X', A, hR', hB⟩ := hR j exact large_of_rows_pow (hH j) hR' hB (hE j).1 (hE j).2`.
-/
theorem parOf_large : AtPts fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, (parOf (Fm.L x i) j).Large :=
  atPts_imp (atPts_and (atPts_and parOf_hyp GlobalTheory.T.parameter_large_all_points) parOf_further) fun _ _ _ _ _ H j => by
    obtain ⟨⟨hH, hR⟩, hE⟩ := H
    obtain ⟨X', A, hR', hB⟩ := hR j
    exact large_of_rows_pow (hH j) hR' hB (hE j).1 (hE j).2

end GlobalTheory.ExpTie
