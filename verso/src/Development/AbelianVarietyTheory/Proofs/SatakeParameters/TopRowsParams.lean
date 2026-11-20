import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.TopRows

/- English proof (translation)
Take `⟨hz1, hz2⟩` from `hz`. Establish `hk : 0 < D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `hτ : (D.eTau (tauPl D z) : D.R.GG) = D.R.tau1 (⟨z.2, hz2⟩ : D.host.TT)`. Unfold `tauPl`. Rewrite using `[Equiv.apply_symm_apply]`.

Simplify using `[plGG, hz1]`. Take `⟨hu1, huk⟩` from `L.top_u (tauPl D z) ⟨z.2, hz2⟩ hk hτ`. Take `⟨-, hw⟩` from `L.win_top (j + 1) (by omega) (by omega) (tauPl D z) ⟨z.2, hz2⟩ hτ`. Establish `ha : aL L z.2 = L.aT ⟨z.2, hz2⟩` using `by unfold aL; rw [dif_pos hz2]`. Establish `hb : bL L z.2 = L.bT ⟨z.2, hz2⟩` using `by unfold bL; rw [dif_pos hz2]`.

Establish `hwe : wPl D (j + 1) z = (((D.hcW u (tauPl D z)).e ⟨j, hj⟩ : ℚ) : ℝ)`. Unfold `wPl wj`. Rewrite using `[dif_pos (by simpa using hj), D.hcW_e]`. Both sides reduce to the same expression. Establish `hkc : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1`.

Rewrite using `[Nat.cast_sub (by omega)]; simp`. Establish `e1 : DV.nuRow D u (j + 1) (tauPl D z) 0 = (aL L z.2 : ℝ) + (wPl D (j + 1) z - kaJ D (j + 1))`. Rewrite using `[RowWeightLemmas.nuRow_head D u j hj _ 0 hk, D.hcW_first u _ hk, ha, hwe]`. Unfold `kaJ Ranks.N`. Use `push_cast`.

Rewrite using `[hu1]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : DV.nuRow D u (j + 1) (tauPl D z) (D.R.k - 1) = (wPl D (j + 1) z - kaJ D (j + 1)) - (bL L z.2 : ℝ)`. Rewrite using `[RowWeightLemmas.nuRow_head D u j hj _ (D.R.k - 1) (by omega), D.hcW_last u _ hk, hb, hwe]`. Unfold `kaJ Ranks.N`.

Use `push_cast`. Rewrite using `[huk, hkc]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨e1, e2, (RowWeightLemmas.nuRow_pos D u j hj _ _ (by unfold Ranks.N; omega)).le, ?_⟩` and prove the remaining obligations. Establish `hka : 0 ≤ kaJ D (j + 1)`.

Unfold `kaJ`. Use `push_cast`. Establish `: (0 : ℝ) ≤ (2 * ((j : ℝ) + 1) - 1)` using `by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith`. Check the signs of the components of the expression. Rewrite using `[e2, hb]`.

Express the relevant statement in the definitionally equal form `wPl D (j + 1) z ≤ _ at hw`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nuRow_tauPl_of_isTopPl {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m)
    (z : Bool × HH D) (hz : IsTopPl D z) :
    DV.nuRow D u (j + 1) (tauPl D z) 0 = (aL L z.2 : ℝ) + (wPl D (j + 1) z - kaJ D (j + 1)) ∧
    DV.nuRow D u (j + 1) (tauPl D z) (D.R.k - 1) = (wPl D (j + 1) z - kaJ D (j + 1)) - (bL L z.2 : ℝ) ∧
    0 ≤ DV.nuRow D u (j + 1) (tauPl D z) (D.R.k - 1) ∧
    DV.nuRow D u (j + 1) (tauPl D z) (D.R.k - 1) ≤ L.sc.b' / L.sc.x + L.etaSz := by
  obtain ⟨hz1, hz2⟩ := hz
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  have hτ : (D.eTau (tauPl D z) : D.R.GG) = D.R.tau1 (⟨z.2, hz2⟩ : D.host.TT) := by
    unfold tauPl
    rw [Equiv.apply_symm_apply]
    simp [plGG, hz1]
  obtain ⟨hu1, huk⟩ := L.top_u (tauPl D z) ⟨z.2, hz2⟩ hk hτ
  obtain ⟨-, hw⟩ := L.win_top (j + 1) (by omega) (by omega) (tauPl D z) ⟨z.2, hz2⟩ hτ
  have ha : aL L z.2 = L.aT ⟨z.2, hz2⟩ := by unfold aL; rw [dif_pos hz2]
  have hb : bL L z.2 = L.bT ⟨z.2, hz2⟩ := by unfold bL; rw [dif_pos hz2]
  have hwe : wPl D (j + 1) z = (((D.hcW u (tauPl D z)).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold wPl wj
    rw [dif_pos (by simpa using hj), D.hcW_e]
    rfl
  have hkc : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have e1 : DV.nuRow D u (j + 1) (tauPl D z) 0 = (aL L z.2 : ℝ) + (wPl D (j + 1) z - kaJ D (j + 1)) := by
    rw [RowWeightLemmas.nuRow_head D u j hj _ 0 hk, D.hcW_first u _ hk, ha, hwe]
    unfold kaJ Ranks.N
    push_cast
    rw [hu1]
    ring
  have e2 : DV.nuRow D u (j + 1) (tauPl D z) (D.R.k - 1) =
      (wPl D (j + 1) z - kaJ D (j + 1)) - (bL L z.2 : ℝ) := by
    rw [RowWeightLemmas.nuRow_head D u j hj _ (D.R.k - 1) (by omega), D.hcW_last u _ hk, hb, hwe]
    unfold kaJ Ranks.N
    push_cast
    rw [huk, hkc]
    ring
  refine ⟨e1, e2, (RowWeightLemmas.nuRow_pos D u j hj _ _ (by unfold Ranks.N; omega)).le, ?_⟩
  have hka : 0 ≤ kaJ D (j + 1) := by
    unfold kaJ
    push_cast
    have : (0 : ℝ) ≤ (2 * ((j : ℝ) + 1) - 1) := by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
    positivity
  rw [e2, hb]
  change wPl D (j + 1) z ≤ _ at hw
  linarith

/- English proof (translation)
Establish `hx : 0 < L.sc.x` using `lt_trans one_pos L.sc.one_lt_alt`. Establish `hb : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hb' : 0 < L.sc.b'` using `div_pos (mul_pos hx hb) (Real.exp_pos _)`. Establish `hn1 : (1 : ℝ) ≤ D.R.n`. Establish `: 1 ≤ D.R.n` using `D.R.ord_pos`.

Conclude with `this` after adjusting the coercions. Establish `hm : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast D.R.two_le_m`. Establish `ht : (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`. Establish `h1 : L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz` using `le_mul_of_one_le_left L.etaSz_pos.le (by nlinarith)`. Establish `h2 : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x`.

Unfold `Scale.w''`. Conclude with `div_le_div_of_nonneg_left hb'.le hx (le_mul_of_one_le_right hx.le hn1)`. Conclude with `h1.trans (P.mteta.trans h2)`.
-/
theorem eta_le {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : L.etaSz ≤ L.sc.b' / L.sc.x := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hx hb) (Real.exp_pos _)
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have h1 : L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz :=
    le_mul_of_one_le_left L.etaSz_pos.le (by nlinarith)
  have h2 : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := by
    unfold Scale.w''
    exact div_le_div_of_nonneg_left hb'.le hx (le_mul_of_one_le_right hx.le hn1)
  exact h1.trans (P.mteta.trans h2)

/- English proof (translation)
Introduce `eps Fm`. Use `⟨0, fun x _ hx1 i u j hj z hz => ?_⟩` and prove the remaining obligations. Establish `h4` using `eta_le (Fm.params x hx1 i)`. Take `⟨e1, e2, e3, e4⟩` from `nuRow_tauPl_of_isTopPl (Fm.L x i) u j hj z hz`. Use `⟨e1, e2, e3, e4.trans ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_div_assoc]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem top_rows : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) 0 = (aL (Fm.L x i) z.2 : ℝ) + (wPl (Fm.D x i) (j + 1) z - kaJ (Fm.D x i) (j + 1)) ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) ((Fm.D x i).R.k - 1) = (wPl (Fm.D x i) (j + 1) z - kaJ (Fm.D x i) (j + 1)) - (bL (Fm.L x i) z.2 : ℝ) ∧ 0 ≤ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) ((Fm.D x i).R.k - 1) ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) ((Fm.D x i).R.k - 1) ≤ 2 * (Fm.L x i).sc.b' / (Fm.L x i).sc.x := by
  intro eps Fm
  refine ⟨0, fun x _ hx1 i u j hj z hz => ?_⟩
  have h4 := eta_le (Fm.params x hx1 i)
  obtain ⟨e1, e2, e3, e4⟩ := nuRow_tauPl_of_isTopPl (Fm.L x i) u j hj z hz
  refine ⟨e1, e2, e3, e4.trans ?_⟩
  rw [mul_div_assoc]
  linarith

end GlobalTheory.TopRows
