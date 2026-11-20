import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.ElevenLe
import Formalism.LocalRingCardinality.ColumnWeightSpreadOffTop
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NuRowZeroLeThreeMul
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

noncomputable section

namespace GlobalTheory.AtG.KernelSizes

variable {D : D7} {L : SizeData₂ D}

/- English proof (translation)
Establish `hA1 : 1 ≤ A` using `by linarith`. Distinguish the cases in `h : N ≤ A ^ 5`. Establish `hA7 : 1 ≤ A ^ 7` using `one_le_pow₀ hA1`. Establish `e1 : 6 * A ^ 2 * N ≤ 6 * A ^ 7`. Use `mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 6 * A ^ 2)` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation. Establish `e2 : A ^ 8 = A * A ^ 7` using `by ring`. Establish `e3 : 10 * A ^ 7 ≤ A * A ^ 7` using `mul_le_mul_of_nonneg_right hA (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `push_neg at h`.

Establish `hA25 : A ^ 2 ≤ A ^ 5` using `pow_le_pow_right₀ hA1 (by norm_num)`. Establish `hAN : A ^ 2 < N` using `lt_of_le_of_lt hA25 h`. Establish `e1 : 6 * A ^ 2 * N < 6 * N * N` using `by nlinarith`. Establish `hN14 : 8 ≤ N ^ 14`. Establish `: (2 : ℝ) ^ 14 ≤ N ^ 14` using `pow_le_pow_left₀ (by norm_num) hN 14`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e2 : N ^ 16 = N ^ 2 * N ^ 14` using `by ring`. Establish `e3 : N ^ 2 * 8 ≤ N ^ 2 * N ^ 14` using `mul_le_mul_of_nonneg_left hN14 (by positivity)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem key_ineq (A N Y : ℝ) (hA : 10 ≤ A) (hN : 2 ≤ N) (h1 : A ^ 8 ≤ Y) (h2 : N ^ 16 ≤ Y) :
    6 * A ^ 2 * N + 2 < Y := by
  have hA1 : 1 ≤ A := by linarith
  by_cases h : N ≤ A ^ 5
  · have hA7 : 1 ≤ A ^ 7 := one_le_pow₀ hA1
    have e1 : 6 * A ^ 2 * N ≤ 6 * A ^ 7 := by
      have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 6 * A ^ 2)
      calc 6 * A ^ 2 * N ≤ 6 * A ^ 2 * A ^ 5 := this
        _ = 6 * A ^ 7 := by ring
    have e2 : A ^ 8 = A * A ^ 7 := by ring
    have e3 : 10 * A ^ 7 ≤ A * A ^ 7 := mul_le_mul_of_nonneg_right hA (by positivity)
    linarith
  · push_neg at h
    have hA25 : A ^ 2 ≤ A ^ 5 := pow_le_pow_right₀ hA1 (by norm_num)
    have hAN : A ^ 2 < N := lt_of_le_of_lt hA25 h
    have e1 : 6 * A ^ 2 * N < 6 * N * N := by nlinarith
    have hN14 : 8 ≤ N ^ 14 := by
      have : (2 : ℝ) ^ 14 ≤ N ^ 14 := pow_le_pow_left₀ (by norm_num) hN 14
      linarith
    have e2 : N ^ 16 = N ^ 2 * N ^ 14 := by ring
    have e3 : N ^ 2 * 8 ≤ N ^ 2 * N ^ 14 := mul_le_mul_of_nonneg_left hN14 (by positivity)
    nlinarith

/- English proof (translation)
Take `⟨Y, h1, h2, -, h4⟩` from `P.g_Y`. Establish `hx0 : (0 : ℝ) < L.sc.x` using `by linarith [L.sc.one_lt_alt]`. Establish `hq : (0 : ℝ) < D.host.q` using `lt_trans (Real.rpow_pos_of_pos hx0 _) P.qd_pow.1`. Establish `hd : (0 : ℝ) < D.host.d` using `lt_trans (Real.rpow_pos_of_pos hx0 _) P.qd_pow.2`. Establish `hq1 : (1 : ℝ) ≤ D.host.q`.

Establish `: 0 < D.host.q` using `by exact_mod_cast hq`. Conclude with `this` after adjusting the coercions. Establish `hd1 : (1 : ℝ) ≤ D.host.d`. Establish `: 0 < D.host.d` using `by exact_mod_cast hd`. Conclude with `this` after adjusting the coercions.

Establish `hQ1 : (1 : ℝ) ≤ D.host.QS` using `by exact_mod_cast D.host.QS_pos`. Establish `hc : (1 : ℝ) ≤ (LevelStarExponents.condE D : ℝ)`. Unfold `LevelStarExponents.condE`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation.

Establish `hcC : 1 ≤ (LevelStarExponents.condE D : ℝ) ^ P.CY` using `Real.one_le_rpow hc P.CY_pos.le`. Establish `hY0 : 0 ≤ Y` using `le_trans (by positivity) h1`. Establish `hN4 : (D.R.N D.R.m : ℝ) ^ 4 ≤ Y ^ ((1 : ℝ) / 4)`. Establish `hN : 0 ≤ (D.R.N D.R.m : ℝ) ^ 4` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Use `⟨Y, h1, ?_, fun i => (h4 i).1⟩` and prove the remaining obligations. Establish `h5 : ((D.R.N D.R.m : ℝ) ^ 4) ^ 4 ≤ (Y ^ ((1 : ℝ) / 4)) ^ 4` using `pow_le_pow_left₀ (by positivity) hN4 4`. Establish `h6 : (Y ^ ((1 : ℝ) / 4)) ^ 4 = Y`. Rewrite using `[← Real.rpow_natCast (Y ^ ((1 : ℝ) / 4)), ← Real.rpow_mul hY0]`. Evaluate the numerical expressions.

Rewrite `h5` using `[h6]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_Y (P : ParameterChoice' D L) :
    ∃ Y : ℝ, ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ Y ∧ (D.R.N D.R.m : ℝ) ^ 16 ≤ Y ∧ ∀ i, Y ≤ (D.host.g i : ℝ) := by
  obtain ⟨Y, h1, h2, -, h4⟩ := P.g_Y
  have hx0 : (0 : ℝ) < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hq : (0 : ℝ) < D.host.q := lt_trans (Real.rpow_pos_of_pos hx0 _) P.qd_pow.1
  have hd : (0 : ℝ) < D.host.d := lt_trans (Real.rpow_pos_of_pos hx0 _) P.qd_pow.2
  have hq1 : (1 : ℝ) ≤ D.host.q := by
    have : 0 < D.host.q := by exact_mod_cast hq
    exact_mod_cast this
  have hd1 : (1 : ℝ) ≤ D.host.d := by
    have : 0 < D.host.d := by exact_mod_cast hd
    exact_mod_cast this
  have hQ1 : (1 : ℝ) ≤ D.host.QS := by exact_mod_cast D.host.QS_pos
  have hc : (1 : ℝ) ≤ (LevelStarExponents.condE D : ℝ) := by
    unfold LevelStarExponents.condE
    push_cast
    calc (1 : ℝ) ≤ 1 * 1 * 1 := by norm_num
      _ ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by gcongr
  have hcC : 1 ≤ (LevelStarExponents.condE D : ℝ) ^ P.CY := Real.one_le_rpow hc P.CY_pos.le
  have hY0 : 0 ≤ Y := le_trans (by positivity) h1
  have hN4 : (D.R.N D.R.m : ℝ) ^ 4 ≤ Y ^ ((1 : ℝ) / 4) := by
    have hN : 0 ≤ (D.R.N D.R.m : ℝ) ^ 4 := by positivity
    nlinarith
  refine ⟨Y, h1, ?_, fun i => (h4 i).1⟩
  have h5 : ((D.R.N D.R.m : ℝ) ^ 4) ^ 4 ≤ (Y ^ ((1 : ℝ) / 4)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hN4 4
  have h6 : (Y ^ ((1 : ℝ) / 4)) ^ 4 = Y := by
    rw [← Real.rpow_natCast (Y ^ ((1 : ℝ) / 4)), ← Real.rpow_mul hY0]
    norm_num
  rw [h6] at h5
  calc (D.R.N D.R.m : ℝ) ^ 16 = ((D.R.N D.R.m : ℝ) ^ 4) ^ 4 := by ring
    _ ≤ Y := h5

/- English proof (translation)
Unfold `LiftErrorLocal.lifts at hj`. Take `⟨j1, j2⟩` from `Finset.mem_Icc.1 hj`. Take `⟨i, rfl⟩ : ∃ i, j = i + 1` from `⟨j - 1, by omega⟩`. Establish `hi : i < D.R.m` using `by omega`. Establish `hb : ∀ t, (L.bT t : ℝ) ≤ 2 * L.sc.b'` using `fun t => by`.

Use `P.bT_le' t` as an intermediate fact. Use `GlobalTheory.CoreHt.RowsRange.b'_pos L` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT : GlobalTheory.CoreHt.ThickUp L` using `fun j h1 h2 τ hc => (L.win_thick j h1 h2 τ hc).2`. Establish `ha : 0 ≤ L.sc.a`.

Unfold `Scale.a`. Use `GlobalTheory.CoreHt.RowsRange.one_le_b L` as an intermediate fact. Use `L.sc.one_lt_alt` as an intermediate fact. Check the signs of the components of the expression. Establish `hrow : ∀ r ∈ Finset.range (D.R.N (i + 1 - 1)), DV.nuRow D u (i + 1) τ r ≤ 3 * L.sc.a`.

Introduce `r hr`. Rewrite `hr` using `[Finset.mem_range, Nat.add_sub_cancel]`. Conclude with `(RowWeightLemmas.nuRow_anti' D u i hi τ r 0 (Nat.zero_le _) hr).trans (GlobalTheory.CoreHt.RowsRange.nuRow_zero_le_three_mul L P hb hT u i hi τ)`. Unfold `nuAbs`. Establish `hs` using `Finset.sum_le_card_nsmul _ _ _ hrow`.

Rewrite `hs` using `[Finset.card_range, nsmul_eq_mul, Nat.add_sub_cancel]`. Establish `hNi : (D.R.N i : ℝ) ≤ D.R.N D.R.m`. Establish `: D.R.N i ≤ D.R.N D.R.m`. Unfold `Ranks.N`. Use `Nat.mul_le_mul_right (D.R.t + 1) hi.le` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions. Rewrite using `[Nat.add_sub_cancel]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem nuAbs_le (P : ParameterChoice' D L) (u : D.what₂.Word) (j : ℕ) (hj : j ∈ LiftErrorLocal.lifts D) (τ : D.what₂.Tau) :
    nuAbs D u j τ ≤ (D.R.N D.R.m : ℝ) * (3 * L.sc.a) := by
  unfold LiftErrorLocal.lifts at hj
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < D.R.m := by omega
  have hb : ∀ t, (L.bT t : ℝ) ≤ 2 * L.sc.b' := fun t => by
    have := P.bT_le' t
    have := GlobalTheory.CoreHt.RowsRange.b'_pos L
    linarith
  have hT : GlobalTheory.CoreHt.ThickUp L := fun j h1 h2 τ hc => (L.win_thick j h1 h2 τ hc).2
  have ha : 0 ≤ L.sc.a := by
    unfold Scale.a
    have := GlobalTheory.CoreHt.RowsRange.one_le_b L
    have := L.sc.one_lt_alt
    positivity
  have hrow : ∀ r ∈ Finset.range (D.R.N (i + 1 - 1)), DV.nuRow D u (i + 1) τ r ≤ 3 * L.sc.a := by
    intro r hr
    rw [Finset.mem_range, Nat.add_sub_cancel] at hr
    exact (RowWeightLemmas.nuRow_anti' D u i hi τ r 0 (Nat.zero_le _) hr).trans
      (GlobalTheory.CoreHt.RowsRange.nuRow_zero_le_three_mul L P hb hT u i hi τ)
  unfold nuAbs
  have hs := Finset.sum_le_card_nsmul _ _ _ hrow
  rw [Finset.card_range, nsmul_eq_mul, Nat.add_sub_cancel] at hs
  have hNi : (D.R.N i : ℝ) ≤ D.R.N D.R.m := by
    have : D.R.N i ≤ D.R.N D.R.m := by
      unfold Ranks.N
      have := Nat.mul_le_mul_right (D.R.t + 1) hi.le
      omega
    exact_mod_cast this
  rw [Nat.add_sub_cancel]
  calc _ ≤ (D.R.N i : ℝ) * (3 * L.sc.a) := hs
    _ ≤ _ := mul_le_mul_of_nonneg_right hNi (by positivity)

/- English proof (translation)
Unfold `LiftErrorLocal.Dpi`. Establish `hs` using `Finset.sum_le_card_nsmul (Finset.univ : Finset D.what₂.Tau) (fun τ => nuAbs D u j τ) _ (fun τ _ => nuAbs_le P u j hj τ)`. Rewrite `hs` using `[Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]`. Conclude with `hs`.
-/
theorem Dpi_le (P : ParameterChoice' D L) (u : D.what₂.Word) (j : ℕ) (hj : j ∈ LiftErrorLocal.lifts D) :
    LiftErrorLocal.Dpi D u j ≤ (D.R.f : ℝ) * ((D.R.N D.R.m : ℝ) * (3 * L.sc.a)) := by
  unfold LiftErrorLocal.Dpi
  have hs := Finset.sum_le_card_nsmul (Finset.univ : Finset D.what₂.Tau) (fun τ => nuAbs D u j τ) _
    (fun τ _ => nuAbs_le P u j hj τ)
  rw [Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at hs
  exact hs

/- English proof (translation)
Introduce `eps _ _`. Use `⟨0, fun D L P hS _ _ i => ?_⟩` and prove the remaining obligations. Take `⟨Y, hY1, hY2, hY3⟩` from `exists_Y P`. Establish `hx1` using `L.sc.one_lt_alt`. Establish `hk5 : (5 : ℝ) ≤ D.R.k` using `P.five_le_k`.

Establish `hb2 : 2 ≤ L.sc.b`. Establish `h1` using `GlobalTheory.CoreHt.RowsRange.one_le_scL L`. Establish `h2` using `Real.add_one_le_exp L.sc.L`. Unfold `Scale.b`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hfk : (D.R.f : ℝ) ≤ D.R.k`. Establish `: D.R.f ≤ D.R.k` using `D.R.f_le_k`. Conclude with `this` after adjusting the coercions. Establish `hf0 : (0 : ℝ) ≤ D.R.f` using `Nat.cast_nonneg _`. Establish `hNk : (D.R.k : ℝ) ≤ D.R.N D.R.m`.

Establish `: D.R.k ≤ D.R.N D.R.m` using `by unfold Ranks.N; omega`. Conclude with `this` after adjusting the coercions. Establish `hxk : L.sc.x ≤ D.R.k`. Establish `hK` using `hS.2.2.1.1`. Establish `he : (1 : ℝ) ≤ 9 / 2 + 10 * L.sc.eps - szTh L`.

Unfold `szTh`. Combine the linear relations using `[L.sc.eps_pos, L.sc.eps_lt]`. Use `Real.rpow_le_rpow_of_exponent_le hx1.le he` as an intermediate fact. Rewrite `this` using `[Real.rpow_one]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hak : L.sc.a ≤ D.R.k * L.sc.b`. Unfold `Scale.a`. Conclude with `mul_le_mul_of_nonneg_right hxk (by linarith)`. Use `set A : ℝ := (D.R.k : ℝ) * L.sc.b with hA`. Use `set N : ℝ := (D.R.N D.R.m : ℝ) with hN`.

Establish `hA10 : 10 ≤ A` using `by rw [hA]; nlinarith`. Establish `hN2 : 2 ≤ N` using `by linarith`. Establish `hkey` using `key_ineq A N Y hA10 hN2 hY1 hY2`. Establish `hkA : (D.R.k : ℝ) ^ 2 * L.sc.b ≤ A ^ 2`. Rewrite using `[hA]`.

Establish `: (D.R.k : ℝ) ^ 2 * L.sc.b * 1 ≤ (D.R.k : ℝ) ^ 2 * L.sc.b * L.sc.b` using `mul_le_mul_of_nonneg_left (by linarith) (by positivity)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hD : ∀ u : D.what₂.Word, ∀ j ∈ LiftErrorLocal.lifts D, LiftErrorLocal.Dpi D u j ≤ 3 * A ^ 2 * N`. Introduce `u j hj`. Establish `h1` using `Dpi_le P u j hj`.

Establish `hN0 : 0 ≤ N` using `by linarith`. Establish `h2 : (D.R.f : ℝ) * (N * (3 * L.sc.a)) ≤ (D.R.k : ℝ) * (N * (3 * (D.R.k * L.sc.b)))`. Apply `mul_le_mul hfk _ (by have := GlobalTheory.CoreHt.RowsRange.one_le_b L; unfold Scale.a; positivity) (by linarith)` to reduce the goal to its premises. Conclude with `mul_le_mul_of_nonneg_left (by linarith) hN0`. Establish `h3 : (D.R.k : ℝ) * (N * (3 * (D.R.k * L.sc.b))) = 3 * ((D.R.k : ℝ) ^ 2 * L.sc.b) * N` using `by ring`.

Establish `h4 : 3 * ((D.R.k : ℝ) ^ 2 * L.sc.b) * N ≤ 3 * A ^ 2 * N`. Use `mul_le_mul_of_nonneg_left hkA (by norm_num : (0 : ℝ) ≤ 3)` as an intermediate fact. Conclude with `mul_le_mul_of_nonneg_right this hN0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hg` using `hY3 i`.

Establish `hA2 : 1 ≤ A ^ 2` using `by nlinarith`. Use `⟨?_, fun u j hj => ?_⟩` and prove the remaining obligations. Establish `h1 : (2 * D.R.f * D.R.N D.R.m + 1 : ℝ) < D.host.g i`. Establish `: (2 : ℝ) * D.R.f * N ≤ 2 * (3 * A ^ 2 * N)`. Establish `: (D.R.f : ℝ) ≤ 3 * A ^ 2` using `by nlinarith`.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h1` after adjusting the coercions. Establish `h` using `hD u j hj`. Prove the components needed by the constructor for the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sizeAt_of_params : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L →
    Formalism.MainNotions.SizesAt L → L.sc.eps = eps → x0 ≤ L.sc.x → ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i := by
  intro eps _ _
  refine ⟨0, fun D L P hS _ _ i => ?_⟩
  obtain ⟨Y, hY1, hY2, hY3⟩ := exists_Y P
  have hx1 := L.sc.one_lt_alt
  have hk5 : (5 : ℝ) ≤ D.R.k := P.five_le_k
  have hb2 : 2 ≤ L.sc.b := by
    have h1 := GlobalTheory.CoreHt.RowsRange.one_le_scL L
    have h2 := Real.add_one_le_exp L.sc.L
    unfold Scale.b
    linarith
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by
    have : D.R.f ≤ D.R.k := D.R.f_le_k
    exact_mod_cast this
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hNk : (D.R.k : ℝ) ≤ D.R.N D.R.m := by
    have : D.R.k ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    exact_mod_cast this

  have hxk : L.sc.x ≤ D.R.k := by
    have hK := hS.2.2.1.1
    have he : (1 : ℝ) ≤ 9 / 2 + 10 * L.sc.eps - szTh L := by
      unfold szTh
      linarith [L.sc.eps_pos, L.sc.eps_lt]
    have := Real.rpow_le_rpow_of_exponent_le hx1.le he
    rw [Real.rpow_one] at this
    linarith
  have hak : L.sc.a ≤ D.R.k * L.sc.b := by
    unfold Scale.a
    exact mul_le_mul_of_nonneg_right hxk (by linarith)
  set A : ℝ := (D.R.k : ℝ) * L.sc.b with hA
  set N : ℝ := (D.R.N D.R.m : ℝ) with hN
  have hA10 : 10 ≤ A := by rw [hA]; nlinarith
  have hN2 : 2 ≤ N := by linarith
  have hkey := key_ineq A N Y hA10 hN2 hY1 hY2
  have hkA : (D.R.k : ℝ) ^ 2 * L.sc.b ≤ A ^ 2 := by
    rw [hA]
    have : (D.R.k : ℝ) ^ 2 * L.sc.b * 1 ≤ (D.R.k : ℝ) ^ 2 * L.sc.b * L.sc.b :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith

  have hD : ∀ u : D.what₂.Word, ∀ j ∈ LiftErrorLocal.lifts D, LiftErrorLocal.Dpi D u j ≤ 3 * A ^ 2 * N := by
    intro u j hj
    have h1 := Dpi_le P u j hj
    have hN0 : 0 ≤ N := by linarith
    have h2 : (D.R.f : ℝ) * (N * (3 * L.sc.a)) ≤ (D.R.k : ℝ) * (N * (3 * (D.R.k * L.sc.b))) := by
      apply mul_le_mul hfk _ (by have := GlobalTheory.CoreHt.RowsRange.one_le_b L; unfold Scale.a; positivity) (by linarith)
      exact mul_le_mul_of_nonneg_left (by linarith) hN0
    have h3 : (D.R.k : ℝ) * (N * (3 * (D.R.k * L.sc.b))) = 3 * ((D.R.k : ℝ) ^ 2 * L.sc.b) * N := by ring
    have h4 : 3 * ((D.R.k : ℝ) ^ 2 * L.sc.b) * N ≤ 3 * A ^ 2 * N := by
      have := mul_le_mul_of_nonneg_left hkA (by norm_num : (0 : ℝ) ≤ 3)
      exact mul_le_mul_of_nonneg_right this hN0
    linarith
  have hg := hY3 i
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  refine ⟨?_, fun u j hj => ?_⟩
  · have h1 : (2 * D.R.f * D.R.N D.R.m + 1 : ℝ) < D.host.g i := by
      have : (2 : ℝ) * D.R.f * N ≤ 2 * (3 * A ^ 2 * N) := by
        have : (D.R.f : ℝ) ≤ 3 * A ^ 2 := by nlinarith
        nlinarith
      linarith
    exact_mod_cast h1
  · have h := hD u j hj
    constructor
    · linarith
    · nlinarith

end GlobalTheory.AtG.KernelSizes
