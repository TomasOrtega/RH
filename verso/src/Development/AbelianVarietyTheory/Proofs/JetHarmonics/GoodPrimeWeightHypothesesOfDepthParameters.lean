import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceWeightRowGapMulBoundsSizeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightRestDegreeAfterGapsBoundsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FirstRowsBoundAndSizesBoundsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

namespace GlobalTheory.GoodDepth

/- English proof (translation)
Introduce `D L Pm Tp hK T hP hC h5 hx hkb hlog j hj`. Take `⟨hfirst, hw⟩` from `GlobalTheory.T.firstRows_bound_and_sizes_bounds D L Pm Tp hK j hj hx hkb`. Take `⟨hr0, hr1⟩` from `GlobalTheory.T.weight_rest_degree_after_gaps_bounds D L Pm Tp hK T hP j hj`. Establish `hgap` using `fun z => GlobalTheory.T.realPlaceWeightRowGap_mul_bounds_size D L Pm Tp hK j hj z (hw z).1`. Establish `hj1 : 1 ≤ j` using `hj.1`.

Establish `hj2 : j ≤ D.R.m` using `hj.2`. Establish `hm2` using `D.R.two_le_m`. Establish `hmk` using `D.R.m_add_three_le_k`. Establish `hn : 0 < D.R.n` using `by unfold Ranks.n; positivity`. Establish `hf : 1 ≤ D.R.f` using `by unfold Ranks.f; omega`.

Establish `hr : 2 ≤ D.R.r` using `by unfold Ranks.r; omega`. Establish `hDp : 1 ≤ Tp.Dp`. Rewrite using `[Tp.Dp_eq]`. Conclude with `Nat.mul_pos hf (Nat.choose_pos hr)`. Establish `h40` using `Tp.TO_40`.

Establish `hTpos : (0 : ℝ) < Tp.TO` using `by exact_mod_cast TO_pos Tp`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hw'' : 0 < L.sc.w'' D.R.n`. Unfold `Scale.w'' Scale.b' Scale.a Scale.b Scale.X'`. Establish `: (0 : ℝ) < D.R.n` using `by exact_mod_cast hn`.

Check the signs of the components of the expression. Establish `hm0 : (0 : ℝ) < D.R.m` using `by exact_mod_cast (by omega : 0 < D.R.m)`. Establish `hwj : ∀ z, (numOf D L).w j z = wj D j (plOf D z)`. Introduce `z`. Establish `h1 : j - 1 < D.R.m` using `by omega`.

Establish `h2 : 1 ≤ j ∧ j ≤ (numOf D L).R.m` using `⟨hj1, hj2⟩`. Unfold `NumDatum.w NumDatum.eQ wj`. Rewrite using `[dif_pos h1, dif_pos h2]`. Both sides reduce to the same expression. Use `⟨⟨((Tp.Dp : ℝ) + 4) / Tp.TO, ?_, fun z => lt_of_lt_of_le hw'' (hw z).1, fun z => (hgap z).1, fun z => (hgap z).2, ⟨by positivity, ?_⟩, ?_, hr0, hr1⟩, fun τ _ => hfirst τ, ?_, ?_, hlog, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `TO_pos Tp` after adjusting the coercions. Rewrite using `[div_le_one hTpos]`. Conclude with `(by omega : Tp.Dp + 4 ≤ Tp.TO)` after adjusting the coercions. Use `show ((D.R.k : ℝ) - 1) * (((Tp.Dp : ℝ) + 4) / Tp.TO) ≤ 5 * D.R.m`. Establish `h` using `Tp.TO_Dk`.

Rewrite `h` using `[div_le_iff₀ hm0]`. Rewrite using `[← mul_div_assoc, div_le_iff₀ hTpos]`. Establish `hD : (1 : ℝ) ≤ Tp.Dp` using `by exact_mod_cast hDp`. Establish `hk : (1 : ℝ) ≤ D.R.k` using `by exact_mod_cast (by omega : 1 ≤ D.R.k)`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 hD) (sub_nonneg.2 hk)]`.

Use `le_trans ?_ Tp.nW_win.1 show 10 * (D.R.r : ℝ) * (D.R.f + (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m) ≤ _` and prove the remaining obligations. Unfold `LevelStarExponents.nW`. Establish `hk : (0 : ℝ) ≤ (D.R.k : ℝ) - 1`. Establish `: (1 : ℝ) ≤ D.R.k` using `by exact_mod_cast (by omega : 1 ≤ D.R.k)`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `gcongr`. Use `le_trans h5 ?_` and prove the remaining obligations. Unfold `Scale.L`. Use `L.sc.eps_pos` as an intermediate fact. Use `L.sc.ez_le` as an intermediate fact.

Conclude with `Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (by linarith)`. Introduce `p hp hin`. Assume the negation of the conclusion as `h`. Establish `hin' : D.host.cls p = PrimeClass.inertClass ∨ D.host.cls p = PrimeClass.signal` using `hin`. Establish `hne2 : p ≠ 2`.

Introduce and unpack `rfl`. Establish `e : D.host.cls 2 = PrimeClass.ram2` using `primeClass_two D.host.toHostRaw`. Rewrite `hin'` using `[e]`. Simplify using `at hin'`. Establish `hp3 : p = 3`.

Establish `h5 : p < 5` using `not_le.1 h`. Establish `h2` using `hp.two_le`. Use `interval_cases p`. Conclude with `absurd rfl hne2`. Both sides reduce to the same expression.

Conclude with `absurd hp (by norm_num)`. Establish `hp4 : p ≤ D.host.splitBound`. Rewrite using `[hp3]`. Conclude with `le_trans (Nat.le_floor (by exact_mod_cast h5)) L.split_tie`. Establish `hjac` using `D.host.split_small p hp hne2 hp4`.

Break down `hin' with e | e` into its components or cases. Conclude with `((primeClass_eq_inert_iff D.host.toHostRaw).1 e).2.2.2.1 hjac`. Conclude with `((primeClass_eq_signal_iff D.host.toHostRaw).1 e).2.2.2.1 hjac`. Introduce `z z'`. Rewrite using `[hwj, hwj]`.

Conclude with `Pm.X''_ratio j j _ _ hj1 hj2 hj1 hj2`.
-/
theorem goodPage_run : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), T.Q.Pins → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → Real.log D.R.k ≤ L.sc.L → ∀ j : ℕ, InR D j →
  GoodPage (numOf D L) j (T.Q.Dw j) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) Tp.nWn Tp.TO 100 L.sc.b L.sc.L := by
  intro D L Pm Tp hK T hP hC h5 hx hkb hlog j hj
  obtain ⟨hfirst, hw⟩ := GlobalTheory.T.firstRows_bound_and_sizes_bounds D L Pm Tp hK j hj hx hkb
  obtain ⟨hr0, hr1⟩ := GlobalTheory.T.weight_rest_degree_after_gaps_bounds D L Pm Tp hK T hP j hj
  have hgap := fun z => GlobalTheory.T.realPlaceWeightRowGap_mul_bounds_size D L Pm Tp hK j hj z (hw z).1
  have hj1 : 1 ≤ j := hj.1
  have hj2 : j ≤ D.R.m := hj.2
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hn : 0 < D.R.n := by unfold Ranks.n; positivity
  have hf : 1 ≤ D.R.f := by unfold Ranks.f; omega
  have hr : 2 ≤ D.R.r := by unfold Ranks.r; omega
  have hDp : 1 ≤ Tp.Dp := by
    rw [Tp.Dp_eq]
    exact Nat.mul_pos hf (Nat.choose_pos hr)
  have h40 := Tp.TO_40
  have hTpos : (0 : ℝ) < Tp.TO := by exact_mod_cast TO_pos Tp
  have hx0 : 0 < L.sc.x := by linarith
  have hw'' : 0 < L.sc.w'' D.R.n := by
    unfold Scale.w'' Scale.b' Scale.a Scale.b Scale.X'
    have : (0 : ℝ) < D.R.n := by exact_mod_cast hn
    positivity
  have hm0 : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have hwj : ∀ z, (numOf D L).w j z = wj D j (plOf D z) := by
    intro z
    have h1 : j - 1 < D.R.m := by omega
    have h2 : 1 ≤ j ∧ j ≤ (numOf D L).R.m := ⟨hj1, hj2⟩
    unfold NumDatum.w NumDatum.eQ wj
    rw [dif_pos h1, dif_pos h2]
    rfl
  refine ⟨⟨((Tp.Dp : ℝ) + 4) / Tp.TO, ?_, fun z => lt_of_lt_of_le hw'' (hw z).1, fun z => (hgap z).1,
    fun z => (hgap z).2, ⟨by positivity, ?_⟩, ?_, hr0, hr1⟩, fun τ _ => hfirst τ, ?_, ?_, hlog, ?_, ?_⟩
  · exact_mod_cast TO_pos Tp
  · rw [div_le_one hTpos]
    exact_mod_cast (by omega : Tp.Dp + 4 ≤ Tp.TO)
  · show ((D.R.k : ℝ) - 1) * (((Tp.Dp : ℝ) + 4) / Tp.TO) ≤ 5 * D.R.m
    have h := Tp.TO_Dk
    rw [div_le_iff₀ hm0] at h
    rw [← mul_div_assoc, div_le_iff₀ hTpos]
    have hD : (1 : ℝ) ≤ Tp.Dp := by exact_mod_cast hDp
    have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
    nlinarith [mul_nonneg (sub_nonneg.2 hD) (sub_nonneg.2 hk)]
  · refine le_trans ?_ Tp.nW_win.1
    show 10 * (D.R.r : ℝ) * (D.R.f + (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m) ≤ _
    unfold LevelStarExponents.nW
    have hk : (0 : ℝ) ≤ (D.R.k : ℝ) - 1 := by
      have : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
      linarith
    gcongr
  · refine le_trans h5 ?_
    unfold Scale.L
    have := L.sc.eps_pos
    have := L.sc.ez_le
    exact Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (by linarith)
  · intro p hp hin
    by_contra h
    have hin' : D.host.cls p = PrimeClass.inertClass ∨
        D.host.cls p = PrimeClass.signal := hin
    have hne2 : p ≠ 2 := by
      rintro rfl
      have e : D.host.cls 2 = PrimeClass.ram2 := primeClass_two D.host.toHostRaw
      rw [e] at hin'
      simp at hin'
    have hp3 : p = 3 := by
      have h5 : p < 5 := not_le.1 h
      have h2 := hp.two_le
      interval_cases p
      · exact absurd rfl hne2
      · rfl
      · exact absurd hp (by norm_num)
    have hp4 : p ≤ D.host.splitBound := by
      rw [hp3]
      exact le_trans (Nat.le_floor (by exact_mod_cast h5)) L.split_tie
    have hjac := D.host.split_small p hp hne2 hp4
    rcases hin' with e | e
    · exact ((primeClass_eq_inert_iff D.host.toHostRaw).1 e).2.2.2.1 hjac
    · exact ((primeClass_eq_signal_iff D.host.toHostRaw).1 e).2.2.2.1 hjac
  · intro z z'
    rw [hwj, hwj]
    exact Pm.X''_ratio j j _ _ hj1 hj2 hj1 hj2

end GlobalTheory.GoodDepth
