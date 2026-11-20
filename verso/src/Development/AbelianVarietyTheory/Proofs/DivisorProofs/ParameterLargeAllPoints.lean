import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp
import Formalism.PieriBlockIdeals.PieriColumnMinors.LargeParameterEstimates

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn
  GlobalTheory.ExpTie

namespace GlobalTheory.ExpTie

/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Establish `hx1 : 1 ≤ x` using `by linarith`. Establish `hX : 0 < L.sc.X'` using `Real.exp_pos _`. Establish `hk2 : (2 : ℝ) ≤ D.R.k`. Establish `h1` using `D.R.f_le_k`.

Establish `h2 : 0 < D.R.ord` using `Formalism.HC.Frame.ord_pos _`. Conclude with `(show 2 ≤ D.R.k by omega)` after adjusting the coercions. Establish `hm2 : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast D.R.two_le_m`. Establish `hn1 : (1 : ℝ) ≤ D.R.n`. Establish `: 1 ≤ D.R.n` using `Formalism.HC.Frame.ord_pos _`.

Conclude with `this` after adjusting the coercions. Establish `ht0 : (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`. Establish `heta` using `L.etaSz_pos`. Establish `hSc` using `L.Sc_pos`. Establish `hw : L.sc.X' * L.sc.w'' D.R.n = L.sc.b / D.R.n`.

Unfold `Scale.w'' Scale.b' Scale.a`. Rewrite using `[hx]`. Clear the denominators using the available nonvanishing facts. Establish `hw0 : 0 ≤ L.sc.w'' D.R.n`. Unfold `Scale.w'' Scale.b' Scale.a Scale.b`.

Rewrite using `[hx]`. Check the signs of the components of the expression. Establish `hb0 : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hbn : L.sc.b / D.R.n ≤ L.sc.b` using `div_le_self hb0.le hn1`. Establish `hkS` using `P5.kS_le`.

Establish `hmt` using `P5.mteta`. Establish `hS_le : L.Sc ≤ L.sc.w'' D.R.n / 2`. Establish `: 2 * L.Sc ≤ (D.R.k : ℝ) * L.Sc` using `mul_le_mul_of_nonneg_right hk2 hSc.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `heta_le : L.etaSz ≤ L.sc.w'' D.R.n / 2`.

Establish `h1 : (2 : ℝ) ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1)` using `by nlinarith`. Establish `: 2 * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz` using `mul_le_mul_of_nonneg_right h1 heta.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `htw` using `L.t_win`. Rewrite `htw` using `[hx]`.

Establish `hkt : D.R.k + D.R.m + 4 ≤ D.R.t` using `by have := D.R.rank_add_five_le; omega`. Establish `hkt' : (D.R.k : ℝ) + D.R.m + 4 ≤ D.R.t` using `by exact_mod_cast hkt`. Establish `hCt : x ^ L.Ct ≤ x ^ C` using `Real.rpow_le_rpow_of_exponent_le hx1 hC0`. Use `⟨⟨?_, ?_, ?_, ?_, ?_, rfl, D.R.f_le_k, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show L.sc.a / L.sc.X' = L.sc.x * Real.exp L.sc.L / L.sc.X'`.

Both sides reduce to the same expression. Use `show L.sc.X' * (L.Sc + L.etaSz) ≤ Real.exp L.sc.L`. Establish `: L.sc.X' * (L.Sc + L.etaSz) ≤ L.sc.X' * L.sc.w'' D.R.n` using `mul_le_mul_of_nonneg_left (by linarith) hX.le`. Establish `hb : Real.exp L.sc.L = L.sc.b` using `rfl`. Rewrite using `[hb]`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hkS`. Use `show 1 ≤ L.Sc`. Rewrite using `[L.Sc_eq]`. Establish `hD` using `P5.Del_ge.2.2.2`.

Establish `hN : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ)`. Establish `: 1 ≤ D.R.N D.R.m` using `by unfold Ranks.N; have := D.R.m_add_three_le_k; omega`. Conclude with `this` after adjusting the coercions. Establish `hm10 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10` using `one_le_pow₀ (by linarith)`. Establish `h1 : (1 : ℝ) ≤ (D.s.Del : ℝ)` using `by nlinarith`.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `D.R.two_le_m`. Conclude with `htw.2.trans hCt`. Use `show (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ x ^ C * L.sc.x`. Rewrite using `[hx]`.

Establish `hT` using `htw.2`. Establish `ht1` using `htw.1`. Establish `hN3 : (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ 3 * (x ^ L.Ct) ^ 2`. Establish `h3 : (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ 3 * (D.R.t : ℝ) ^ 2` using `by nlinarith`. Establish `h4 : (D.R.t : ℝ) ^ 2 ≤ (x ^ L.Ct) ^ 2` using `pow_le_pow_left₀ ht0 hT 2`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsq : (x ^ L.Ct) ^ 2 * x ≤ x ^ C`. Rewrite using `[sq, ← Real.rpow_add hx0]`. Combine the equalities or inequalities in the displayed calculation. Establish `hpos : 0 ≤ (x ^ L.Ct) ^ 2` using `sq_nonneg _`.

Use the polynomial consequences of the given equalities and inequalities. Use `show Formalism.CohomologicalDescent.LargeParameterEstimates.Big (L.sc.x ^ L.sc.eps) L.sc.x (Real.exp (L.sc.x ^ (L.sc.eps / 3))) (x ^ C)`. Rewrite using `[hx, heps]`. Conclude with `hB`.
-/
theorem rows_big_of_largeParameter {D : D7} (L : SizeData₂ D) (P5 : ParameterChoice' D L) (j : Fin D.R.m) (eps C x : ℝ)
    (hx : L.sc.x = x) (heps : L.sc.eps = eps) (hC : 2 * L.Ct + 1 ≤ C) (hC0 : L.Ct ≤ C) (hx2 : 2 ≤ x)
    (hB : Formalism.CohomologicalDescent.LargeParameterEstimates.Big (x ^ eps) x (Real.exp (x ^ (eps / 3))) (x ^ C)) :
    Formalism.CohomologicalDescent.LargeParameterEstimates.Rows (parOf L j) L.sc.X' (x ^ C) ∧
      Formalism.CohomologicalDescent.LargeParameterEstimates.Big (parOf L j).L (parOf L j).x L.sc.X' (x ^ C) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hX : 0 < L.sc.X' := Real.exp_pos _
  have hk2 : (2 : ℝ) ≤ D.R.k := by
    have h1 := D.R.f_le_k
    have h2 : 0 < D.R.ord := Formalism.HC.Frame.ord_pos _
    exact_mod_cast (show 2 ≤ D.R.k by omega)
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
    exact_mod_cast this
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have heta := L.etaSz_pos
  have hSc := L.Sc_pos

  have hw : L.sc.X' * L.sc.w'' D.R.n = L.sc.b / D.R.n := by
    unfold Scale.w'' Scale.b' Scale.a
    rw [hx]
    field_simp
  have hw0 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w'' Scale.b' Scale.a Scale.b
    rw [hx]
    positivity
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hbn : L.sc.b / D.R.n ≤ L.sc.b := div_le_self hb0.le hn1
  have hkS := P5.kS_le
  have hmt := P5.mteta
  have hS_le : L.Sc ≤ L.sc.w'' D.R.n / 2 := by
    have : 2 * L.Sc ≤ (D.R.k : ℝ) * L.Sc := mul_le_mul_of_nonneg_right hk2 hSc.le
    linarith
  have heta_le : L.etaSz ≤ L.sc.w'' D.R.n / 2 := by
    have h1 : (2 : ℝ) ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) := by nlinarith
    have : 2 * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := mul_le_mul_of_nonneg_right h1 heta.le
    linarith

  have htw := L.t_win
  rw [hx] at htw
  have hkt : D.R.k + D.R.m + 4 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
  have hkt' : (D.R.k : ℝ) + D.R.m + 4 ≤ D.R.t := by exact_mod_cast hkt
  have hCt : x ^ L.Ct ≤ x ^ C := Real.rpow_le_rpow_of_exponent_le hx1 hC0
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, rfl, D.R.f_le_k, ?_, ?_⟩, ?_⟩
  ·
    show L.sc.a / L.sc.X' = L.sc.x * Real.exp L.sc.L / L.sc.X'
    rfl
  · show L.sc.X' * (L.Sc + L.etaSz) ≤ Real.exp L.sc.L
    have : L.sc.X' * (L.Sc + L.etaSz) ≤ L.sc.X' * L.sc.w'' D.R.n :=
      mul_le_mul_of_nonneg_left (by linarith) hX.le
    have hb : Real.exp L.sc.L = L.sc.b := rfl
    rw [hb]
    linarith
  · exact hkS
  · show 1 ≤ L.Sc
    rw [L.Sc_eq]
    have hD := P5.Del_ge.2.2.2
    have hN : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
      have : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; have := D.R.m_add_three_le_k; omega
      exact_mod_cast this
    have hm10 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ (by linarith)
    have h1 : (1 : ℝ) ≤ (D.s.Del : ℝ) := by nlinarith
    nlinarith
  · exact D.R.two_le_m
  · exact htw.2.trans hCt
  ·
    show (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ x ^ C * L.sc.x
    rw [hx]
    have hT := htw.2
    have ht1 := htw.1
    have hN3 : (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ 3 * (x ^ L.Ct) ^ 2 := by
      have h3 : (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ 3 * (D.R.t : ℝ) ^ 2 := by nlinarith
      have h4 : (D.R.t : ℝ) ^ 2 ≤ (x ^ L.Ct) ^ 2 := pow_le_pow_left₀ ht0 hT 2
      linarith
    have hsq : (x ^ L.Ct) ^ 2 * x ≤ x ^ C := by
      rw [sq, ← Real.rpow_add hx0]
      calc x ^ (L.Ct + L.Ct) * x = x ^ (L.Ct + L.Ct + 1) := by rw [Real.rpow_add hx0 (L.Ct + L.Ct) 1, Real.rpow_one]
        _ ≤ x ^ C := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hpos : 0 ≤ (x ^ L.Ct) ^ 2 := sq_nonneg _
    nlinarith
  · show Formalism.CohomologicalDescent.LargeParameterEstimates.Big (L.sc.x ^ L.sc.eps) L.sc.x (Real.exp (L.sc.x ^ (L.sc.eps / 3))) (x ^ C)
    rw [hx, heps]
    exact hB

/- English proof (translation)
Use `⟨1, one_pos, fun eps heps _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩` and prove the remaining obligations. Take `⟨x0, hx0⟩` from `Formalism.CohomologicalDescent.LargeParameterEstimates.eventually_large_parameter_bound eps (2 * |Fm.Ct| + 2) heps`. Use `⟨max x0 2, fun x hx hle i _ _ _ j => ?_⟩` and prove the remaining obligations. Establish `hCt` using `Fm.Ct_eq x i`. Use `⟨(Fm.L x i).sc.X', x ^ (2 * |Fm.Ct| + 2), rows_big_of_largeParameter (Fm.L x i) (Fm.params x hx i) j eps _ x (Fm.L_x x i hx) (Fm.L_eps x i) ?_ ?_ ((le_max_right _ _).trans hle) (hx0 x ((le_max_left _ _).trans hle))⟩` and prove the remaining obligations.

Rewrite using `[hCt]`. Combine the linear relations using `[le_abs_self Fm.Ct]`. Rewrite using `[hCt]`. Combine the linear relations using `[le_abs_self Fm.Ct, abs_nonneg Fm.Ct]`.
-/
theorem rows_big : GlobalTheory.BigOn.AtPts fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, ∃ X' A : ℝ,
    Formalism.CohomologicalDescent.LargeParameterEstimates.Rows (GlobalTheory.ExpTie.parOf (Fm.L x i) j) X' A ∧
      Formalism.CohomologicalDescent.LargeParameterEstimates.Big (GlobalTheory.ExpTie.parOf (Fm.L x i) j).L (GlobalTheory.ExpTie.parOf (Fm.L x i) j).x X' A := by
  refine ⟨1, one_pos, fun eps heps _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := Formalism.CohomologicalDescent.LargeParameterEstimates.eventually_large_parameter_bound eps (2 * |Fm.Ct| + 2) heps
  refine ⟨max x0 2, fun x hx hle i _ _ _ j => ?_⟩
  have hCt := Fm.Ct_eq x i
  refine ⟨(Fm.L x i).sc.X', x ^ (2 * |Fm.Ct| + 2),
    rows_big_of_largeParameter (Fm.L x i) (Fm.params x hx i) j eps _ x (Fm.L_x x i hx) (Fm.L_eps x i) ?_ ?_
      ((le_max_right _ _).trans hle) (hx0 x ((le_max_left _ _).trans hle))⟩
  · rw [hCt]
    linarith [le_abs_self Fm.Ct]
  · rw [hCt]
    linarith [le_abs_self Fm.Ct, abs_nonneg Fm.Ct]

end GlobalTheory.ExpTie

end
