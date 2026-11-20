import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

variable {D : Formalism.BasicNotions.D7}

/- English proof (translation)
Establish `hk` using `D.R.m_add_three_le_k`. Establish `hm2` using `D.R.two_le_m`. Establish `hw : ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ L.Sc + (GlobalTheory.ExpTie.Lift.wts L j).c τ`. Establish `hU` using `U_last L j τ`. Establish `h0` using `hv.1 0 (by omega)`.

Establish `hcv` using `(L.cloud_v τ ⟨0, by omega⟩).2`. Establish `hwd : (GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ = (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ 0` using `by show (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ 0 - (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ ((Vc D j).rank - 1) = _`. Rewrite using `[hU, sub_zero]`. Rewrite using `[hwd]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hc` using `c_le L j τ hv`. Establish `hnt : (D.eTau τ : D.R.GG) ∉ D.host.thickPlaces`. Introduce `h`. Apply `hT` to reduce the goal to its premises. Simplify using `only [wts, Finset.mem_filter, Finset.mem_univ, true_and]`.

Conclude with `h`. Establish `he : (GlobalTheory.ExpTie.Lift.wts L j).e τ = wj D ((j : ℕ) + 1) τ` using `rfl`. Distinguish the cases in `htop : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces`. Use `left`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht1, ht2⟩ : ∃ t ∈ D.host.TT, D.R.tau1 t = (D.eTau τ : D.R.GG) := by`.

Unfold `Host.topPlaces at htop`. Simplify using `using htop`. Establish `x1` using `L.sc.one_lt_alt`. Establish `x0 : 0 < L.sc.x` using `by linarith`. Establish `hb0 : 0 < L.sc.b'`.

Establish `hX : 0 < L.sc.X'` using `by unfold Scale.X'; positivity`. Establish `hb : 0 < L.sc.b` using `by unfold Scale.b; positivity`. Unfold `Scale.b' Scale.a`. Check the signs of the components of the expression. Establish `hk0 : (0 : ℝ) < D.R.k` using `by exact_mod_cast (by omega : 0 < D.R.k)`.

Establish `hLa : 0 < L.LaG`. Establish `h1` using `P5.S_le`. Establish `h2` using `L.Sc_pos`. Assume the negation of the conclusion as `hn`. Use `push_neg at hn`.

Establish `: L.LaG * L.sc.b' / D.R.k ≤ 0` using `div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hn hb0.le) hk0.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbT : ((L.bT ⟨t, ht1⟩ : ℝ)) ≤ L.sc.b' * (1 + 1 / L.sc.x ^ 2)`. Establish `h1` using `P5.bT_le ⟨t, ht1⟩`. Establish `h2` using `P5.rho_le`.

Establish `h4 : 0 ≤ P5.Crho * Real.log L.sc.x * L.LaG / D.R.k`. Use `P5.Crho_pos` as an intermediate fact. Use `Real.log_nonneg x1.le` as an intermediate fact. Check the signs of the components of the expression. Establish `hx2 : L.sc.x ^ (-2 : ℝ) = 1 / L.sc.x ^ 2`.

Rewrite using `[Real.rpow_neg x0.le, one_div]`. Use `norm_cast`. Unfold `LevelStarExponents.rhoP at h2`. Rewrite `h2` using `[hx2]`. Establish `hq : 0 ≤ 1 / L.sc.x ^ 2` using `by positivity`.

Establish `h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / L.sc.x ^ 2`. Establish `: 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k = (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b'` using `by ring`. Establish `h6` using `mul_le_mul_of_nonneg_right h5 hb0.le`.

Use the polynomial consequences of the given equalities and inequalities. Establish `a` using `L.bT_ge ⟨t, ht1⟩`. Establish `wj1` using `L.win_top ((j : ℕ) + 1) (by omega) (by omega) τ ⟨t, ht1⟩ ht2.symm`. Establish `wjm` using `L.win_top D.R.m (by omega) le_rfl τ ⟨t, ht1⟩ ht2.symm`. Use `⟨⟨(L.bT ⟨t, ht1⟩ : ℝ), a, hbT, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[he]`. Conclude with `wj1.1`. Rewrite using `[he]`. Conclude with `wj1.2`. Use `show _ ≤ L.Sc + L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) + L.etaSz + ((D.R.t : ℝ) - 1) / 2`.

Establish `: L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) = L.sc.b' * (1 + 1 / L.sc.x ^ 2) + L.sc.b' / L.sc.x` using `by ring`. Combine the linear relations using `[wjm.2]`. Use `right`. Establish `hthin : D.host.IsThin (D.eTau τ : D.R.GG)` using `⟨(D.eTau τ).2, htop, hnt⟩`. Establish `wj1` using `L.win_thin ((j : ℕ) + 1) (by omega) (by omega) τ hthin`.

Establish `wjm` using `L.win_thin D.R.m (by omega) le_rfl τ hthin`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[he]`. Conclude with `wj1.1`. Rewrite using `[he]`.

Conclude with `wj1.2`. Use `show _ ≤ L.Sc + L.sc.w'' D.R.n + L.etaSz + ((D.R.t : ℝ) - 1) / 2`. Combine the linear relations using `[wjm.2]`.
-/
theorem other_of_not_thick (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau)
    (hv : GlobalTheory.ExpTie.Lift.ValsAt L j τ) (hT : τ ∉ (GlobalTheory.ExpTie.Lift.wts L j).T2) :
    ((GlobalTheory.ExpTie.parOf L j).Top ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).S + (GlobalTheory.ExpTie.parOf L j).b' * (1 + 1 / (GlobalTheory.ExpTie.parOf L j).x + 1 / (GlobalTheory.ExpTie.parOf L j).x ^ 2) + (GlobalTheory.ExpTie.parOf L j).η + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2) ∨ ((GlobalTheory.ExpTie.parOf L j).Thin ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).S + (GlobalTheory.ExpTie.parOf L j).w'' + (GlobalTheory.ExpTie.parOf L j).η + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2) := by
  classical
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m

  have hw : ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ L.Sc + (GlobalTheory.ExpTie.Lift.wts L j).c τ := by
    have hU := U_last L j τ
    have h0 := hv.1 0 (by omega)
    have hcv := (L.cloud_v τ ⟨0, by omega⟩).2
    have hwd : (GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ = (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ 0 := by
      show (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ 0 - (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ ((Vc D j).rank - 1) = _
      rw [hU, sub_zero]
    rw [hwd]
    linarith
  have hc := c_le L j τ hv
  have hnt : (D.eTau τ : D.R.GG) ∉ D.host.thickPlaces := by
    intro h
    apply hT
    simp only [wts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  have he : (GlobalTheory.ExpTie.Lift.wts L j).e τ = wj D ((j : ℕ) + 1) τ := rfl
  by_cases htop : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · left
    obtain ⟨t, ht1, ht2⟩ : ∃ t ∈ D.host.TT, D.R.tau1 t = (D.eTau τ : D.R.GG) := by
      unfold Host.topPlaces at htop
      simpa using htop
    have x1 := L.sc.one_lt_alt
    have x0 : 0 < L.sc.x := by linarith
    have hb0 : 0 < L.sc.b' := by
      have hX : 0 < L.sc.X' := by unfold Scale.X'; positivity
      have hb : 0 < L.sc.b := by unfold Scale.b; positivity
      unfold Scale.b' Scale.a
      positivity
    have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
    have hLa : 0 < L.LaG := by
      have h1 := P5.S_le
      have h2 := L.Sc_pos
      by_contra hn
      push_neg at hn
      have : L.LaG * L.sc.b' / D.R.k ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hn hb0.le) hk0.le
      linarith
    have hbT : ((L.bT ⟨t, ht1⟩ : ℝ)) ≤ L.sc.b' * (1 + 1 / L.sc.x ^ 2) := by
      have h1 := P5.bT_le ⟨t, ht1⟩
      have h2 := P5.rho_le
      have h4 : 0 ≤ P5.Crho * Real.log L.sc.x * L.LaG / D.R.k := by
        have := P5.Crho_pos; have := Real.log_nonneg x1.le; positivity
      have hx2 : L.sc.x ^ (-2 : ℝ) = 1 / L.sc.x ^ 2 := by
        rw [Real.rpow_neg x0.le, one_div]; norm_cast
      unfold LevelStarExponents.rhoP at h2
      rw [hx2] at h2
      have hq : 0 ≤ 1 / L.sc.x ^ 2 := by positivity
      have h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / L.sc.x ^ 2 := by
        have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
        linarith
      have : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
        (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
      have h6 := mul_le_mul_of_nonneg_right h5 hb0.le
      nlinarith
    have a := L.bT_ge ⟨t, ht1⟩
    have wj1 := L.win_top ((j : ℕ) + 1) (by omega) (by omega) τ ⟨t, ht1⟩ ht2.symm
    have wjm := L.win_top D.R.m (by omega) le_rfl τ ⟨t, ht1⟩ ht2.symm
    refine ⟨⟨(L.bT ⟨t, ht1⟩ : ℝ), a, hbT, ?_, ?_⟩, ?_⟩
    · rw [he]; exact wj1.1
    · rw [he]; exact wj1.2
    · show _ ≤ L.Sc + L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) + L.etaSz + ((D.R.t : ℝ) - 1) / 2
      have : L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) = L.sc.b' * (1 + 1 / L.sc.x ^ 2) + L.sc.b' / L.sc.x := by ring
      linarith [wjm.2]
  · right
    have hthin : D.host.IsThin (D.eTau τ : D.R.GG) := ⟨(D.eTau τ).2, htop, hnt⟩
    have wj1 := L.win_thin ((j : ℕ) + 1) (by omega) (by omega) τ hthin
    have wjm := L.win_thin D.R.m (by omega) le_rfl τ hthin
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [he]; exact wj1.1
    · rw [he]; exact wj1.2
    · show _ ≤ L.Sc + L.sc.w'' D.R.n + L.etaSz + ((D.R.t : ℝ) - 1) / 2
      linarith [wjm.2]

end GlobalTheory.ExpTie.Lift
