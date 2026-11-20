import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

/- English proof (translation)
Introduce `V F _ _ _ _ Y hY p hp q w hw K hKY hK`. Take `⟨C, hC⟩` from `(hK.image (continuous_id.sub continuous_const : Continuous fun x : V => x - p)).isBounded.exists_norm_le`. Use `set K' : Set V := (fun z : ℝ × V => p + z.1 • (z.2 - p)) '' (Set.Icc (0 : ℝ) 1 ×ˢ K)`. Establish `hK'c : IsCompact K'` using `(isCompact_Icc.prod hK).image (by fun_prop)`. Establish `hK'Y : K' ⊆ Y`.

Introduce and unpack `_ ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩`. Conclude with `hY.add_smul_sub_mem hp (hKY hx) ht`. Establish `hwK` using `hw K' hK'Y hK'c`. Rewrite `hwK`, the goal using `[Metric.tendstoUniformlyOn_iff]`. Introduce `ε hε`.

Establish `hR : 0 < |C| + 1` using `by positivity`. Use `filter_upwards [hwK (ε / 2 / (|C| + 1)) (by positivity)] with k hk x hx`. Simplify using `only [Pi.zero_apply, dist_zero_left] at hk ⊢`. Establish `hxp : ‖x - p‖ ≤ |C| + 1`. Establish `h0` using `hC (x - p) ⟨x, hx, rfl⟩`.

Combine the linear relations using `[le_abs_self C]`. Establish `hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖t ^ q • (w k (p + t • (x - p))).curryLeft (x - p)‖ ≤ ε / 2 / (|C| + 1) * (|C| + 1)`. Introduce `t ht`. Rewrite `ht` using `[Set.uIoc_of_le zero_le_one]`. Establish `hy : p + t • (x - p) ∈ K'` using `⟨(t, x), ⟨⟨ht.1.le, ht.2⟩, hx⟩, rfl⟩`.

Establish `h1` using `hk _ hy`. Rewrite using `[norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos ht.1]`. Establish `h2 : t ^ q ≤ 1` using `pow_le_one₀ ht.1.le ht.2`. Establish `h3 : ‖(w k (p + t • (x - p))).curryLeft (x - p)‖ ≤ ‖w k (p + t • (x - p))‖ * ‖x - p‖`. Use `(ContinuousLinearMap.le_opNorm _ _).trans_eq ?_` and prove the remaining obligations.

Rewrite using `[ContinuousAlternatingMap.norm_curryLeft]`. Establish `h4 : ‖w k (p + t • (x - p))‖ * ‖x - p‖ ≤ ε / 2 / (|C| + 1) * (|C| + 1)` using `mul_le_mul h1.le hxp (norm_nonneg _) (by positivity)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[one_mul]`. Conclude with `h3.trans h4`.

Establish `hint` using `intervalIntegral.norm_integral_le_of_norm_le_const hbound`. Establish `e : ε / 2 / (|C| + 1) * (|C| + 1) = ε / 2` using `by field_simp`. Rewrite `hint` using `[e]`. Simplify using `only [sub_zero, abs_one, mul_one] at hint`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Cj.H.coneLim :
    UpperTheory.V.Cj.H.ConeLim := by
  intro V F _ _ _ _ Y hY p hp q w hw K hKY hK
  obtain ⟨C, hC⟩ := (hK.image (continuous_id.sub continuous_const :
    Continuous fun x : V => x - p)).isBounded.exists_norm_le
  set K' : Set V := (fun z : ℝ × V => p + z.1 • (z.2 - p)) '' (Set.Icc (0 : ℝ) 1 ×ˢ K)
  have hK'c : IsCompact K' := (isCompact_Icc.prod hK).image (by fun_prop)
  have hK'Y : K' ⊆ Y := by
    rintro _ ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    exact hY.add_smul_sub_mem hp (hKY hx) ht
  have hwK := hw K' hK'Y hK'c
  rw [Metric.tendstoUniformlyOn_iff] at hwK ⊢
  intro ε hε
  have hR : 0 < |C| + 1 := by positivity
  filter_upwards [hwK (ε / 2 / (|C| + 1)) (by positivity)] with k hk x hx
  simp only [Pi.zero_apply, dist_zero_left] at hk ⊢
  have hxp : ‖x - p‖ ≤ |C| + 1 := by
    have h0 := hC (x - p) ⟨x, hx, rfl⟩
    linarith [le_abs_self C]
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖t ^ q • (w k (p + t • (x - p))).curryLeft (x - p)‖ ≤ ε / 2 / (|C| + 1) * (|C| + 1) := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hy : p + t • (x - p) ∈ K' := ⟨(t, x), ⟨⟨ht.1.le, ht.2⟩, hx⟩, rfl⟩
    have h1 := hk _ hy
    rw [norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos ht.1]
    have h2 : t ^ q ≤ 1 := pow_le_one₀ ht.1.le ht.2
    have h3 : ‖(w k (p + t • (x - p))).curryLeft (x - p)‖
        ≤ ‖w k (p + t • (x - p))‖ * ‖x - p‖ := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans_eq ?_
      rw [ContinuousAlternatingMap.norm_curryLeft]
    have h4 : ‖w k (p + t • (x - p))‖ * ‖x - p‖ ≤ ε / 2 / (|C| + 1) * (|C| + 1) :=
      mul_le_mul h1.le hxp (norm_nonneg _) (by positivity)
    calc t ^ q * ‖(w k (p + t • (x - p))).curryLeft (x - p)‖
        ≤ 1 * ‖(w k (p + t • (x - p))).curryLeft (x - p)‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ ε / 2 / (|C| + 1) * (|C| + 1) := by
          rw [one_mul]
          exact h3.trans h4
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have e : ε / 2 / (|C| + 1) * (|C| + 1) = ε / 2 := by field_simp
  rw [e] at hint
  simp only [sub_zero, abs_one, mul_one] at hint
  calc ‖UpperTheory.V.Cj.H.coneOp p (w k) x‖
      = ‖∫ t in (0 : ℝ)..1, t ^ q • (w k (p + t • (x - p))).curryLeft (x - p)‖ := rfl
    _ ≤ ε / 2 := hint
    _ < ε := by linarith
