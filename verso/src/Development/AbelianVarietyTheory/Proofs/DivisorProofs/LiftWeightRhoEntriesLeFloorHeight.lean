import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

/- English proof (translation)
Introduce `D L P5 j τ hL hv a ha`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hm2` using `D.R.two_le_m`. Establish `ht1 : (1 : ℝ) ≤ D.R.t` using `L.t_win.1`. Establish `hk1 : (1 : ℝ) ≤ D.R.k` using `by exact_mod_cast (by omega : 1 ≤ D.R.k)`.

Establish `hS` using `L.Sc_pos`. Establish `hη` using `L.etaSz_pos`. Establish `x1` using `L.sc.one_lt_alt`. Establish `x0 : 0 < L.sc.x` using `by linarith`. Establish `hb0 : 0 < L.sc.b'`.

Unfold `Scale.b' Scale.a Scale.X' Scale.b`. Conclude with `div_pos (mul_pos x0 (Real.exp_pos _)) (Real.exp_pos _)`. Establish `hn : (1 : ℝ) ≤ D.R.n` using `by unfold Ranks.n; exact_mod_cast (Nat.succ_le_of_lt (Formalism.HC.Frame.ord_pos _) : 1 ≤ _)`. Establish `hU0` using `U_nonneg L j τ 0 (by have := rank_eq j; omega)`. Establish `hUa` using `liftWeightCombinatorialData_U_le_U_zero L j τ a ha`.

Establish `hv0` using `hv.1 0 (by omega)`. Establish `hcl` using `L.cloud_v τ ⟨0, by omega⟩`. Establish `hc` using `c_le L j τ hv`. Establish `ePb : (parOf L j).b = L.sc.b` using `rfl`. Establish `eh : (parOf L j).h = L.sc.b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1` using `rfl`.

Establish `hbb'` using `hL.bb'`. Establish `htop` using `hL.top_le`. Simplify using `only [parOf] at hbb' htop`. Express the relevant statement in the definitionally equal form `12 * (D.R.k : ℝ) * (D.R.t : ℝ) * L.sc.b' < L.sc.b at hbb'`. Establish `hm1 : 1 ≤ D.R.m` using `by omega`.

Establish `key : wj D D.R.m τ ≤ L.sc.b + L.etaSz + 1 ∨ wj D D.R.m τ ≤ L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) + L.etaSz`. Distinguish the cases in `h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht1, ht2⟩ : ∃ t ∈ D.host.TT, D.R.tau1 t = (D.eTau τ : D.R.GG) := by`. Unfold `Host.topPlaces at h1`. Simplify using `using h1`.

Establish `hw` using `(L.win_top D.R.m hm1 le_rfl τ ⟨t, ht1⟩ ht2.symm).2`. Establish `hbt` using `P5.bT_le ⟨t, ht1⟩`. Establish `hr` using `P5.rho_le`. Unfold `LevelStarExponents.rhoP at hr`. Establish `hLa : 0 < L.LaG`.

Establish `h` using `P5.S_le`. Assume the negation of the conclusion as `hc'`. Use `push_neg at hc'`. Establish `: L.LaG * L.sc.b' / D.R.k ≤ 0` using `div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc' hb0.le) (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hNs : 0 ≤ LevelStarExponents.Nstar L`. Unfold `LevelStarExponents.Nstar Scale.delta1`. Check the signs of the components of the expression. Establish `hx2 : L.sc.x ^ (-2 : ℝ) = 1 / L.sc.x ^ 2`. Rewrite using `[Real.rpow_neg x0.le, one_div]`.

Use `norm_cast`. Establish `h4 : 0 ≤ P5.Crho * Real.log L.sc.x * L.LaG / D.R.k`. Use `P5.Crho_pos` as an intermediate fact. Use `Real.log_nonneg x1.le` as an intermediate fact. Check the signs of the components of the expression.

Establish `h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / L.sc.x ^ 2`. Establish `h6 : 0 ≤ LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k` using `by positivity`. Establish `: 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k)` using `by ring`. Rewrite `hr` using `[hx2]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h7 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k = (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b'` using `by ring`. Establish `h8 : (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' ≤ 1 / L.sc.x ^ 2 * L.sc.b'` using `mul_le_mul_of_nonneg_right h5 hb0.le`. Use `right`. Establish `: L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) = L.sc.b' + L.sc.b' / L.sc.x + 1 / L.sc.x ^ 2 * L.sc.b'` using `by ring`. Rewrite using `[this]`.

Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces`. Conclude with `Or.inl (L.win_thick D.R.m hm1 le_rfl τ h2).2`. Establish `hw` using `(L.win_thin D.R.m hm1 le_rfl τ ⟨(D.eTau τ).2, h1, h2⟩).2 right`. Establish `hw1 : L.sc.w'' D.R.n ≤ L.sc.b'`.

Unfold `Scale.w''`. Rewrite using `[div_le_iff₀ (by positivity)]`. Establish `hxn : 1 ≤ L.sc.x * (D.R.n : ℝ)` using `by nlinarith`. Use `mul_le_mul_of_nonneg_left hxn hb0.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hpos : 0 ≤ L.sc.b' * (1 / L.sc.x + 1 / L.sc.x ^ 2)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hU0h : ((wts L j).U (parOf L j) τ 0 : ℝ) ≤ (parOf L j).h`. Rewrite using `[eh]`. Break down `key with h | h` into its components or cases.

Use the polynomial consequences of the given equalities and inequalities. Establish `h2b : 2 * L.sc.b' < L.sc.b`. Establish `: 2 * L.sc.b' ≤ 12 * (D.R.k : ℝ) * (D.R.t : ℝ) * L.sc.b'`. Establish `: (1 : ℝ) ≤ (D.R.k : ℝ) * (D.R.t : ℝ)` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfl : ((wts L j).U (parOf L j) τ 0).toNat ≤ Formalism.CohomologicalDescent.ShortWeightBounds.h0 (parOf L j)`. Unfold `Formalism.CohomologicalDescent.ShortWeightBounds.h0`. Apply `Nat.le_floor` to reduce the goal to its premises.

Establish `: (((wts L j).U (parOf L j) τ 0).toNat : ℝ) = ((wts L j).U (parOf L j) τ 0 : ℝ)`. Conclude with `Int.toNat_of_nonneg hU0` after adjusting the coercions. Rewrite using `[this]`. Conclude with `hU0h`. Use linear arithmetic over natural numbers and integers.
-/
theorem wts_U_le_h0_of_large : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau), (GlobalTheory.ExpTie.parOf L j).Large → GlobalTheory.ExpTie.Lift.ValsAt L j τ → ∀ a, a < (GlobalTheory.ExpTie.parOf L j).Nr → (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (Formalism.CohomologicalDescent.ShortWeightBounds.h0 (GlobalTheory.ExpTie.parOf L j) : ℤ) := by
  intro D L P5 j τ hL hv a ha
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have ht1 : (1 : ℝ) ≤ D.R.t := L.t_win.1
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hS := L.Sc_pos
  have hη := L.etaSz_pos
  have x1 := L.sc.one_lt_alt
  have x0 : 0 < L.sc.x := by linarith
  have hb0 : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X' Scale.b
    exact div_pos (mul_pos x0 (Real.exp_pos _)) (Real.exp_pos _)
  have hn : (1 : ℝ) ≤ D.R.n := by unfold Ranks.n; exact_mod_cast (Nat.succ_le_of_lt (Formalism.HC.Frame.ord_pos _) : 1 ≤ _)
  have hU0 := U_nonneg L j τ 0 (by have := rank_eq j; omega)
  have hUa := liftWeightCombinatorialData_U_le_U_zero L j τ a ha
  have hv0 := hv.1 0 (by omega)
  have hcl := L.cloud_v τ ⟨0, by omega⟩
  have hc := c_le L j τ hv

  have ePb : (parOf L j).b = L.sc.b := rfl
  have eh : (parOf L j).h = L.sc.b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1 := rfl
  have hbb' := hL.bb'
  have htop := hL.top_le
  simp only [parOf] at hbb' htop
  change 12 * (D.R.k : ℝ) * (D.R.t : ℝ) * L.sc.b' < L.sc.b at hbb'

  have hm1 : 1 ≤ D.R.m := by omega
  have key : wj D D.R.m τ ≤ L.sc.b + L.etaSz + 1 ∨
      wj D D.R.m τ ≤ L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) + L.etaSz := by
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      obtain ⟨t, ht1, ht2⟩ : ∃ t ∈ D.host.TT, D.R.tau1 t = (D.eTau τ : D.R.GG) := by
        unfold Host.topPlaces at h1
        simpa using h1
      have hw := (L.win_top D.R.m hm1 le_rfl τ ⟨t, ht1⟩ ht2.symm).2
      have hbt := P5.bT_le ⟨t, ht1⟩
      have hr := P5.rho_le
      unfold LevelStarExponents.rhoP at hr
      have hLa : 0 < L.LaG := by
        have h := P5.S_le
        by_contra hc'
        push_neg at hc'
        have : L.LaG * L.sc.b' / D.R.k ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc' hb0.le) (by positivity)
        linarith
      have hNs : 0 ≤ LevelStarExponents.Nstar L := by
        unfold LevelStarExponents.Nstar Scale.delta1; positivity
      have hx2 : L.sc.x ^ (-2 : ℝ) = 1 / L.sc.x ^ 2 := by
        rw [Real.rpow_neg x0.le, one_div]; norm_cast
      have h4 : 0 ≤ P5.Crho * Real.log L.sc.x * L.LaG / D.R.k := by
        have := P5.Crho_pos; have := Real.log_nonneg x1.le; positivity
      have h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / L.sc.x ^ 2 := by
        have h6 : 0 ≤ LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k := by positivity
        have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
        rw [hx2] at hr
        linarith
      have h7 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
          (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
      have h8 : (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' ≤ 1 / L.sc.x ^ 2 * L.sc.b' :=
        mul_le_mul_of_nonneg_right h5 hb0.le
      right
      have : L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) = L.sc.b' + L.sc.b' / L.sc.x + 1 / L.sc.x ^ 2 * L.sc.b' := by ring
      rw [this]
      linarith
    · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · exact Or.inl (L.win_thick D.R.m hm1 le_rfl τ h2).2
      · have hw := (L.win_thin D.R.m hm1 le_rfl τ ⟨(D.eTau τ).2, h1, h2⟩).2
        right
        have hw1 : L.sc.w'' D.R.n ≤ L.sc.b' := by
          unfold Scale.w''
          rw [div_le_iff₀ (by positivity)]
          have hxn : 1 ≤ L.sc.x * (D.R.n : ℝ) := by nlinarith
          have := mul_le_mul_of_nonneg_left hxn hb0.le
          linarith
        have hpos : 0 ≤ L.sc.b' * (1 / L.sc.x + 1 / L.sc.x ^ 2) := by positivity
        nlinarith
  have hU0h : ((wts L j).U (parOf L j) τ 0 : ℝ) ≤ (parOf L j).h := by
    rw [eh]
    rcases key with h | h
    · nlinarith
    · have h2b : 2 * L.sc.b' < L.sc.b := by
        have : 2 * L.sc.b' ≤ 12 * (D.R.k : ℝ) * (D.R.t : ℝ) * L.sc.b' := by
          have : (1 : ℝ) ≤ (D.R.k : ℝ) * (D.R.t : ℝ) := by nlinarith
          nlinarith
        linarith
      linarith
  have hfl : ((wts L j).U (parOf L j) τ 0).toNat ≤ Formalism.CohomologicalDescent.ShortWeightBounds.h0 (parOf L j) := by
    unfold Formalism.CohomologicalDescent.ShortWeightBounds.h0
    apply Nat.le_floor
    have : (((wts L j).U (parOf L j) τ 0).toNat : ℝ) = ((wts L j).U (parOf L j) τ 0 : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hU0
    rw [this]; exact hU0h
  omega

end GlobalTheory.ExpTie.Lift
