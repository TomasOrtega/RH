import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyBallSubset

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.ProductChartAll

open scoped ENNReal in

/- English proof (translation)
Establish `hout : K⁻¹ • ν.toOuterMeasure ≤ OuterMeasure.pi fun i => (μ i).toOuterMeasure`. Use `OuterMeasure.le_pi.2 fun s _ => ?_` and prove the remaining obligations. Establish `hsub : Set.pi Set.univ s ⊆ Set.pi Set.univ fun i => toMeasurable (μ i) (s i)` using `Set.pi_mono fun i _ => subset_toMeasurable (μ i) (s i)`. Establish `hbox` using `h (fun i => toMeasurable (μ i) (s i)) fun i => measurableSet_toMeasurable _ _`. Simplify using `only [measure_toMeasurable] at hbox`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ENNReal.inv_mul_cancel h0 h1, one_mul]`. Both sides reduce to the same expression. Use `Measure.le_iff.2 fun A hA => ?_` and prove the remaining obligations. Establish `hA'` using `hout A`.

Rewrite using `[Measure.smul_apply, smul_eq_mul, Measure.pi_def, toMeasure_apply _ _ hA]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ENNReal.mul_inv_cancel h0 h1, one_mul]`. Use `_ ≤ K * OuterMeasure.pi (fun i => (μ i).toOuterMeasure) A := by gcongr`. Conclude with `hA'`.
-/
theorem le_smul_pi {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
    (ν : Measure (∀ i, α i)) (μ : ∀ i, Measure (α i)) {K : ℝ≥0∞} (h0 : K ≠ 0) (h1 : K ≠ ⊤)
    (h : ∀ s : ∀ i, Set (α i), (∀ i, MeasurableSet (s i)) →
      ν (Set.pi Set.univ s) ≤ K * ∏ i, μ i (s i)) :
    ν ≤ K • Measure.pi μ := by

  have hout : K⁻¹ • ν.toOuterMeasure ≤ OuterMeasure.pi fun i => (μ i).toOuterMeasure := by
    refine OuterMeasure.le_pi.2 fun s _ => ?_
    have hsub : Set.pi Set.univ s ⊆ Set.pi Set.univ fun i => toMeasurable (μ i) (s i) :=
      Set.pi_mono fun i _ => subset_toMeasurable (μ i) (s i)
    have hbox := h (fun i => toMeasurable (μ i) (s i)) fun i => measurableSet_toMeasurable _ _
    simp only [measure_toMeasurable] at hbox
    calc (K⁻¹ • ν.toOuterMeasure) (Set.pi Set.univ s)
        = K⁻¹ * ν (Set.pi Set.univ s) := rfl
      _ ≤ K⁻¹ * ν (Set.pi Set.univ fun i => toMeasurable (μ i) (s i)) := by
          gcongr
      _ ≤ K⁻¹ * (K * ∏ i, μ i (s i)) := by gcongr
      _ = ∏ i, (μ i).toOuterMeasure (s i) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel h0 h1, one_mul]
          rfl
  refine Measure.le_iff.2 fun A hA => ?_
  have hA' := hout A
  rw [Measure.smul_apply, smul_eq_mul, Measure.pi_def, toMeasure_apply _ _ hA]
  calc ν A = K * (K⁻¹ * ν A) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel h0 h1, one_mul]
    _ ≤ K * OuterMeasure.pi (fun i => (μ i).toOuterMeasure) A := by
        gcongr
        exact hA'

/- English proof (translation)
Establish `hq` using `Real.abs_exp_sub_one_sub_id_le (x := x) (by rw [abs_of_nonneg h0]; exact h1)`. Establish `hsq : x ^ 2 ≤ x` using `by nlinarith`. Use `(abs_le.mp hq).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exp_sub_one_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x - 1 ≤ 2 * x := by
  have hq := Real.abs_exp_sub_one_sub_id_le (x := x) (by rw [abs_of_nonneg h0]; exact h1)
  have hsq : x ^ 2 ≤ x := by nlinarith
  have := (abs_le.mp hq).2
  linarith

open scoped Matrix.Norms.Frobenius in

/- English proof (translation)
Set `T` to `Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)`. Establish `hTc : Continuous (T : Matrix (Fin n) (Fin n) ℂ → _)` using `LinearMap.continuous_of_finiteDimensional T.toAlgEquiv.toLinearEquiv.toLinearMap`. Establish `hEn : ∀ i, ‖T (E i)‖ ≤ 1`. Introduce `i`. Establish `hF : ‖E i‖ = 1`.

Establish `h2 : ‖E i‖ ^ 2 = 1`. Rewrite using `[← GlobalTheory.ProductChart.ip_self, GlobalTheory.ProductChart.ip_apply, hE i i, if_pos rfl]`. Use polynomial arithmetic with `[norm_nonneg (E i)]`. Use `ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_` and prove the remaining obligations. Establish `hv : T (E i) v = WithLp.toLp 2 (E i *ᵥ WithLp.ofLp v)` using `rfl`.

Rewrite using `[hv, ← Matrix.frobenius_norm_replicateCol (ι := Unit), Matrix.replicateCol_mulVec, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `himg : ∀ (u : UJ ε) (x : Fin (n ^ 2) → ℝ), uMat u = (List.ofFn fun i => NormedSpace.exp ((x i : ℂ) • E i)).prod → T (uMat u) = (List.ofFn fun i => NormedSpace.exp ((ContinuousLinearMap.proj i : (Fin (n ^ 2) → ℝ) →L[ℝ] ℝ) x • T (E i))).prod`. Introduce `u x hu`. Rewrite using `[hu, map_list_prod, List.map_ofFn]`.

Use `congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))` and prove the remaining obligations. Simplify using `only [Function.comp_apply, ContinuousLinearMap.proj_apply]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨-, B, hB, hBn, -, -, -⟩` from `GlobalTheory.ProductChart.exists_deriv_prod hs t' (n ^ 2) (fun i => T (E i)) (fun i => ContinuousLinearMap.proj i) hEn ht'`. Take `⟨-, -, -, -, hPn, -, -⟩` from `GlobalTheory.ProductChart.exists_deriv_prod hs t (n ^ 2) (fun i => T (E i)) (fun i => ContinuousLinearMap.proj i) hEn ht`.

Rewrite `hB` using `[← himg a' t' ha']`. Rewrite `hPn` using `[← himg a t ha]`. Establish `hmul : uMat (a * a'⁻¹) = uMat a * uMat a'⁻¹` using `rfl`. Establish `hr : uMat a' * uMat a'⁻¹ = 1` using `by first`. Consider the case `exact Units.mul_inv (a' : (Matrix (Fin n) (Fin n) ℂ)ˣ)`.

Consider the case `simp [uMat]`. Establish `hinv : T (uMat a'⁻¹) = B`. Combine the equalities or inequalities in the displayed calculation. Establish `hprod : T (uMat (a * a'⁻¹)) = T (uMat a) * B` using `by rw [hmul, map_mul, hinv]`. Establish `hclose` using `GlobalTheory.ProductChart.norm_mul_sub_one_le hPn hBn`.

Rewrite `hclose` using `[← hprod, ← Real.exp_add]`. Establish `hnorm : ‖T (uMat (a * a'⁻¹))‖ ≤ 2`. Establish `h1 : ‖(1 : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ ≤ 1` using `ContinuousLinearMap.norm_id_le`. Establish `h3 : ‖T (uMat (a * a'⁻¹))‖ ≤ ‖T (uMat (a * a'⁻¹)) - 1‖ + ‖(1 : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖`. Simplify using `using norm_add_le (T (uMat (a * a'⁻¹)) - 1) 1`.

Establish `h4 : ((n ^ 2 : ℕ) : ℝ) * s + ((n ^ 2 : ℕ) : ℝ) * s = 2 * n ^ 2 * s` using `by push_cast; ring`. Rewrite `hclose` using `[h4]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd : dOp (uMat (a * a'⁻¹)) = Real.log ‖T (uMat (a * a'⁻¹))‖`. Unfold `dOp`.

Both sides reduce to the same expression. Rewrite using `[hd]`. Break down `(norm_nonneg (T (uMat (a * a'⁻¹)))).eq_or_lt with h0 | h0` into its components or cases. Rewrite using `[← h0, Real.log_zero]`. Conclude with `Real.log_nonneg one_le_two`.

Conclude with `Real.log_le_log h0 hnorm`.
-/
theorem dOp_chart_le {n : ℕ} {ε : Fin n → Bool} {s : ℝ} {E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ}
    (hE : ∀ i j, ((E i * (E j)ᴴ).trace).re = if i = j then 1 else 0) (hs : 0 ≤ s)
    (hn : Real.exp (2 * n ^ 2 * s) ≤ 2) (a a' : UJ ε) (t t' : Fin (n ^ 2) → ℝ)
    (ht : ∀ i, |t i| ≤ s) (ht' : ∀ i, |t' i| ≤ s)
    (ha : uMat a = (List.ofFn fun i => NormedSpace.exp ((t i : ℂ) • E i)).prod)
    (ha' : uMat a' = (List.ofFn fun i => NormedSpace.exp ((t' i : ℂ) • E i)).prod) :
    dOp (uMat (a * a'⁻¹)) ≤ Real.log 2 := by
  classical

  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hTc : Continuous (T : Matrix (Fin n) (Fin n) ℂ → _) :=
    LinearMap.continuous_of_finiteDimensional T.toAlgEquiv.toLinearEquiv.toLinearMap

  have hEn : ∀ i, ‖T (E i)‖ ≤ 1 := by
    intro i
    have hF : ‖E i‖ = 1 := by
      have h2 : ‖E i‖ ^ 2 = 1 := by
        rw [← GlobalTheory.ProductChart.ip_self, GlobalTheory.ProductChart.ip_apply, hE i i, if_pos rfl]
      nlinarith [norm_nonneg (E i)]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    have hv : T (E i) v = WithLp.toLp 2 (E i *ᵥ WithLp.ofLp v) := rfl
    rw [hv, ← Matrix.frobenius_norm_replicateCol (ι := Unit), Matrix.replicateCol_mulVec, one_mul]
    calc ‖E i * Matrix.replicateCol Unit (WithLp.ofLp v)‖
        ≤ ‖E i‖ * ‖Matrix.replicateCol Unit (WithLp.ofLp v)‖ := Matrix.frobenius_norm_mul _ _
      _ = ‖v‖ := by rw [hF, one_mul, Matrix.frobenius_norm_replicateCol]

  have himg : ∀ (u : UJ ε) (x : Fin (n ^ 2) → ℝ),
      uMat u = (List.ofFn fun i => NormedSpace.exp ((x i : ℂ) • E i)).prod →
      T (uMat u) = (List.ofFn fun i => NormedSpace.exp
        ((ContinuousLinearMap.proj i : (Fin (n ^ 2) → ℝ) →L[ℝ] ℝ) x • T (E i))).prod := by
    intro u x hu
    rw [hu, map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    simp only [Function.comp_apply, ContinuousLinearMap.proj_apply]
    calc T (NormedSpace.exp ((x i : ℂ) • E i)) = NormedSpace.exp (T ((x i : ℂ) • E i)) :=
          NormedSpace.map_exp T hTc _
      _ = NormedSpace.exp (x i • T (E i)) := by rw [map_smul, Complex.coe_smul]
  obtain ⟨-, B, hB, hBn, -, -, -⟩ := GlobalTheory.ProductChart.exists_deriv_prod hs t' (n ^ 2) (fun i => T (E i))
    (fun i => ContinuousLinearMap.proj i) hEn ht'
  obtain ⟨-, -, -, -, hPn, -, -⟩ := GlobalTheory.ProductChart.exists_deriv_prod hs t (n ^ 2) (fun i => T (E i))
    (fun i => ContinuousLinearMap.proj i) hEn ht
  rw [← himg a' t' ha'] at hB
  rw [← himg a t ha] at hPn

  have hmul : uMat (a * a'⁻¹) = uMat a * uMat a'⁻¹ := rfl
  have hr : uMat a' * uMat a'⁻¹ = 1 := by
    first
      | exact Units.mul_inv (a' : (Matrix (Fin n) (Fin n) ℂ)ˣ)
      | simp [uMat]
  have hinv : T (uMat a'⁻¹) = B := by
    calc T (uMat a'⁻¹) = (B * T (uMat a')) * T (uMat a'⁻¹) := by rw [hB, one_mul]
      _ = B * T (uMat a' * uMat a'⁻¹) := by rw [map_mul, mul_assoc]
      _ = B := by rw [hr, map_one, mul_one]
  have hprod : T (uMat (a * a'⁻¹)) = T (uMat a) * B := by rw [hmul, map_mul, hinv]
  have hclose := GlobalTheory.ProductChart.norm_mul_sub_one_le hPn hBn
  rw [← hprod, ← Real.exp_add] at hclose
  have hnorm : ‖T (uMat (a * a'⁻¹))‖ ≤ 2 := by
    have h1 : ‖(1 : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    have h3 : ‖T (uMat (a * a'⁻¹))‖ ≤
        ‖T (uMat (a * a'⁻¹)) - 1‖ + ‖(1 : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ := by
      simpa using norm_add_le (T (uMat (a * a'⁻¹)) - 1) 1
    have h4 : ((n ^ 2 : ℕ) : ℝ) * s + ((n ^ 2 : ℕ) : ℝ) * s = 2 * n ^ 2 * s := by push_cast; ring
    rw [h4] at hclose
    linarith
  have hd : dOp (uMat (a * a'⁻¹)) = Real.log ‖T (uMat (a * a'⁻¹))‖ := by
    unfold dOp
    rfl
  rw [hd]
  rcases (norm_nonneg (T (uMat (a * a'⁻¹)))).eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]
    exact Real.log_nonneg one_le_two
  · exact Real.log_le_log h0 hnorm

/- English proof (translation)
Introduce `I c s E Θ hc hG hE hs h12 h8 hΘ`. Establish `hn0 : (0 : ℝ) ≤ I.n` using `Nat.cast_nonneg _`. Establish `hnum : (I.n : ℝ) * (Real.exp (3 * (I.n : ℝ) ^ 2 * s) - 1) ≤ 1 / 2 ∧ Real.exp (2 * (I.n : ℝ) ^ 2 * s) ≤ 2 ∧ Real.exp (2 * (I.n : ℝ) ^ 3 * (Real.exp (2 * (I.n : ℝ) ^ 2 * s) - 1)) ≤ Real.exp 1`. Break down `Nat.eq_zero_or_pos I.n with h | h` into its components or cases. Simplify using `only [h, Nat.cast_zero]`.

Evaluate the numerical expressions. Establish `hm : (1 : ℝ) ≤ I.n` using `by exact_mod_cast h`. Establish `hsq : (I.n : ℝ) ^ 2 * s ≤ (I.n : ℝ) ^ 3 * s`. Establish `: (I.n : ℝ) ^ 2 ≤ (I.n : ℝ) ^ 3` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hsq5 : (I.n : ℝ) ^ 5 * s = (I.n : ℝ) ^ 3 * ((I.n : ℝ) ^ 2 * s)` using `by ring`. Establish `h3 : 3 * (I.n : ℝ) ^ 2 * s ≤ 1` using `by nlinarith`. Establish `h2 : 2 * (I.n : ℝ) ^ 2 * s ≤ 1` using `by nlinarith`. Establish `hp : 0 ≤ (I.n : ℝ) ^ 2 * s` using `by positivity`. Establish `e3` using `exp_sub_one_le (by positivity) h3`.

Establish `e2` using `exp_sub_one_le (by positivity) h2`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: (I.n : ℝ) * (Real.exp (3 * (I.n : ℝ) ^ 2 * s) - 1) ≤ (I.n : ℝ) * (2 * (3 * (I.n : ℝ) ^ 2 * s))` using `mul_le_mul_of_nonneg_left e3 hn0`. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.

Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Establish `hn3 : 0 ≤ 2 * (I.n : ℝ) ^ 3` using `by positivity`. Use `mul_le_mul_of_nonneg_left e2 hn3` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Take `⟨hchart, hexp2, hK1⟩` from `hnum`.

Set `C : Set (Fin (I.n ^ 2) → ℝ)` to `Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) s`. Set `Θv : ∀ v, (Fin (I.n ^ 2) → ℝ) → UJ (I.ε v)` to `fun v x => Θ (fun _ => x) v`. Establish `hΘv : ∀ v x, uMat (Θv v x) = (List.ofFn fun i => NormedSpace.exp ((x i : ℂ) • E v i)).prod` using `fun v x => hΘ (fun _ => x) v`. Establish `hΘeq : ∀ t, Θ t = fun v => Θv v (t v)`. Introduce `t`.

Use function extensionality and compare the values at `v`. Conclude with `GlobalTheory.GaugeConst.uMat_injective (I.ε v) ((hΘ t v).trans (hΘv v (t v)).symm)`. Establish `hcont : ∀ v, Continuous (Θv v)`. Introduce `v`. Establish `hE' : Continuous fun y : EuclideanSpace ℝ (Fin (I.n ^ 2)) => Θv v (WithLp.ofLp y)`.

Use `GlobalTheory.ProductChart.continuous_chart (E := E v) _ fun y => ?_` and prove the remaining obligations. Rewrite using `[hΘv]`. Simplify using `only [Complex.coe_smul]`. Conclude with `hE'.comp (PiLp.continuous_toLp _ _)`. Establish `hmeas : ∀ v, Measurable (Θv v)` using `fun v => (hcont v).measurable`.

Establish `hCc : IsCompact C` using `isCompact_univ_pi fun _ => isCompact_Icc`. Set `Sv : ∀ v, Set (UJ (I.ε v))` to `fun v => Θv v '' C`. Establish `hSv : ∀ v, MeasurableSet (Sv v)` using `fun v => ((hCc.image (hcont v)).isClosed).measurableSet`. Use `⟨Set.pi Set.univ Sv, MeasurableSet.univ_pi hSv, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha a' ha' v`.

Take `⟨x, hx, hxa⟩` from `ha v (Set.mem_univ v)`. Take `⟨x', hx', hxa'⟩` from `ha' v (Set.mem_univ v)`. Establish `hb : ∀ y ∈ C, ∀ i, |y i| ≤ s` using `fun y hy i => by`. Establish `hyi` using `hy i (Set.mem_univ i)`. Rewrite using `[abs_of_nonneg hyi.1]`.

Conclude with `hyi.2`. Establish `e1 : uMat (a v) = (List.ofFn fun i => NormedSpace.exp ((x i : ℂ) • E v i)).prod`. Rewrite using `[← hxa]`. Conclude with `hΘv v x`. Establish `e2 : uMat (a' v) = (List.ofFn fun i => NormedSpace.exp ((x' i : ℂ) • E v i)).prod`.

Rewrite using `[← hxa']`. Conclude with `hΘv v x'`. Conclude with `dOp_chart_le (hE v) hs.le hexp2 (a v) (a' v) x x' (hb x hx) (hb x' hx') e1 e2`. Introduce `Φ hΦ set Kc := Real.exp (2 * (I.n : ℝ) ^ 3 * (Real.exp (2 * (I.n : ℝ) ^ 2 * s) - 1)) with hKc`. Establish `hone : ∀ v (Ψ : UJ (I.ε v) → ENNReal), Measurable Ψ → ∫⁻ t in C, Ψ (Θv v t) ≤ ENNReal.ofReal (Kc * c v) * ∫⁻ y in Sv v, Ψ y ∂(muG (I.ε v))` using `fun v => GlobalTheory.ProductChart.lintegral_chart_le I.n (I.ε v) (c v) s (E v) (Θv v) (hc v) (hG v) (hE v) hs hchart (hΘv v)`.

Use `haveI : IsFiniteMeasure ((volume : Measure (Fin (I.n ^ 2) → ℝ)).restrict C) := isFiniteMeasure_restrict.2 hCc.measure_lt_top.ne`. Set `ν : ∀ v, Measure (UJ (I.ε v))` to `fun v => ((volume : Measure (Fin (I.n ^ 2) → ℝ)).restrict C).map (Θv v)`. Set `μS : ∀ v, Measure (UJ (I.ε v))` to `fun v => (muG (I.ε v)).restrict (Sv v)`. Establish `hfac : ∀ v (A : Set (UJ (I.ε v))), MeasurableSet A → ν v A ≤ ENNReal.ofReal (Kc * c v) * μS v A`. Introduce `v A hA`.

Establish `hind : Measurable (A.indicator (1 : UJ (I.ε v) → ENNReal))` using `measurable_one.indicator hA`. Combine the equalities or inequalities in the displayed calculation. Use `set K : ENNReal := ∏ v, ENNReal.ofReal (Kc * c v) with hK`. Establish `hbox : ∀ A : ∀ v, Set (UJ (I.ε v)), (∀ v, MeasurableSet (A v)) → Measure.pi ν (Set.pi Set.univ A) ≤ K * ∏ v, μS v (A v)`. Introduce `A hA`.

Rewrite using `[Measure.pi_pi, hK, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_le_prod' fun v _ => hfac v (A v) (hA v)`. Establish `hle : Measure.pi ν ≤ K • Measure.pi μS`. Distinguish the cases in `hK0 : K = 0`. Establish `h0 : Measure.pi ν = 0`.

Rewrite using `[← Measure.measure_univ_eq_zero, ← Set.pi_univ]`. Use `hbox (fun _ => Set.univ) fun _ => MeasurableSet.univ` as an intermediate fact. Rewrite `this` using `[hK0, zero_mul]`. Conclude with `le_antisymm this zero_le`. Rewrite using `[h0]`.

Conclude with `Measure.zero_le _`. Conclude with `le_smul_pi (Measure.pi ν) μS hK0 (ENNReal.prod_ne_top fun v _ => ENNReal.ofReal_ne_top) hbox`. Establish `hKle : K ≤ ENNReal.ofReal (Real.exp I.f * ∏ v, c v)`. Distinguish the cases in `hc0 : ∀ v, 0 ≤ c v`. Establish `hKc0 : 0 ≤ Kc` using `(Real.exp_pos _).le`.

Rewrite using `[hK, ← ENNReal.ofReal_prod_of_nonneg fun v _ => mul_nonneg hKc0 (hc0 v)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]`. Apply `mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun v _ => hc0 v)` to reduce the goal to its premises. Establish `hcard : Fintype.card (InfinitePlace I.F) ≤ I.f`.

Establish `h1` using `NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := I.F)`. Establish `h2` using `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (K := I.F)`. Establish `h3 : I.f = Module.finrank ℚ I.F` using `by unfold AutInst.f; rfl`. Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation.

Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Rewrite using `[mul_one]`. Conclude with `hcard` after adjusting the coercions. Use `push_neg at hc0`. Take `⟨v, hv⟩` from `hc0`.

Establish `: ENNReal.ofReal (Kc * c v) = 0` using `ENNReal.ofReal_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hv.le)`. Rewrite using `[hK, Finset.prod_eq_zero (Finset.mem_univ v) this]`. Conclude with `zero_le`. Establish `hvol : (volume : Measure (InfinitePlace I.F → Fin (I.n ^ 2) → ℝ)).restrict (Set.pi Set.univ fun _ => C) = Measure.pi fun _ => (volume : Measure (Fin (I.n ^ 2) → ℝ)).restrict C`. Rewrite using `[show (volume : Measure (InfinitePlace I.F → Fin (I.n ^ 2) → ℝ)) = Measure.pi fun _ => (volume : Measure (Fin (I.n ^ 2) → ℝ)) from rfl, Measure.restrict_pi_pi]`.

Establish `hmapm : Measurable fun t : InfinitePlace I.F → Fin (I.n ^ 2) → ℝ => fun v => Θv v (t v)` using `measurable_pi_lambda _ fun v => (hmeas v).comp (measurable_pi_apply v)`. Establish `hmap : (Measure.pi fun _ => (volume : Measure (Fin (I.n ^ 2) → ℝ)).restrict C).map (fun t v => Θv v (t v)) = Measure.pi ν` using `Measure.pi_map_pi fun v => (hmeas v).aemeasurable`. Establish `hmu : (muInf I).restrict (Set.pi Set.univ Sv) = Measure.pi μS`. Rewrite using `[show muInf I = Measure.pi fun v => muG (I.ε v) from rfl, Measure.restrict_pi_pi]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hset : (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) s) = Set.pi Set.univ fun _ : InfinitePlace I.F => C` using `rfl`. Rewrite using `[hset, hvol]`. Conclude with `lintegral_congr fun t => by rw [hΘeq t]`. Use `_ = ∫⁻ y, Φ y ∂(Measure.pi ν) := by rw [← hmap, lintegral_map hΦ hmapm]`. Use `_ ≤ ∫⁻ y, Φ y ∂(K • Measure.pi μS) := lintegral_mono' hle le_rfl`.

Use `_ = K * ∫⁻ y in Set.pi Set.univ Sv, Φ y ∂(muInf I) := by`. Rewrite using `[lintegral_smul_measure, hmu, smul_eq_mul]`. Use `_ ≤ ENNReal.ofReal (Real.exp I.f * ∏ v, c v) * ∫⁻ y in Set.pi Set.univ Sv, Φ y ∂(muInf I) := by gcongr`.
-/
theorem lintegral_chart_all_le : ∀ (I : AutInst) (c : InfinitePlace I.F → ℝ) (s : ℝ) (E : InfinitePlace I.F → Fin (I.n ^ 2) → Matrix (Fin I.n) (Fin I.n) ℂ) (Θ : (InfinitePlace I.F → Fin (I.n ^ 2) → ℝ) → I.Ginf), (∀ v, IsGauge (I.ε v) (c v)) → (∀ v i, inG (I.ε v) (E v i)) → (∀ v i j, ((E v i * (E v j)ᴴ).trace).re = if i = j then 1 else 0) → 0 < s → 12 * (I.n : ℝ) ^ 3 * s ≤ 1 → 8 * (I.n : ℝ) ^ 5 * s ≤ 1 → (∀ t v, uMat (Θ t v) = (List.ofFn fun i => NormedSpace.exp ((t v i : ℂ) • E v i)).prod) → ∃ S : Set I.Ginf, MeasurableSet S ∧ (∀ a ∈ S, ∀ a' ∈ S, ∀ v, dOp (uMat ((a * a'⁻¹) v)) ≤ Real.log 2) ∧ ∀ Φ : I.Ginf → ENNReal, Measurable Φ → ∫⁻ t in Set.pi Set.univ (fun _ => Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) s), Φ (Θ t) ≤ ENNReal.ofReal (Real.exp I.f * ∏ v, c v) * ∫⁻ y in S, Φ y ∂(muInf I) := by
  intro I c s E Θ hc hG hE hs h12 h8 hΘ
  classical

  have hn0 : (0 : ℝ) ≤ I.n := Nat.cast_nonneg _
  have hnum : (I.n : ℝ) * (Real.exp (3 * (I.n : ℝ) ^ 2 * s) - 1) ≤ 1 / 2 ∧
      Real.exp (2 * (I.n : ℝ) ^ 2 * s) ≤ 2 ∧
      Real.exp (2 * (I.n : ℝ) ^ 3 * (Real.exp (2 * (I.n : ℝ) ^ 2 * s) - 1)) ≤ Real.exp 1 := by
    rcases Nat.eq_zero_or_pos I.n with h | h
    · simp only [h, Nat.cast_zero]
      norm_num
    · have hm : (1 : ℝ) ≤ I.n := by exact_mod_cast h
      have hsq : (I.n : ℝ) ^ 2 * s ≤ (I.n : ℝ) ^ 3 * s := by
        have : (I.n : ℝ) ^ 2 ≤ (I.n : ℝ) ^ 3 := by nlinarith
        nlinarith
      have hsq5 : (I.n : ℝ) ^ 5 * s = (I.n : ℝ) ^ 3 * ((I.n : ℝ) ^ 2 * s) := by ring
      have h3 : 3 * (I.n : ℝ) ^ 2 * s ≤ 1 := by nlinarith
      have h2 : 2 * (I.n : ℝ) ^ 2 * s ≤ 1 := by nlinarith
      have hp : 0 ≤ (I.n : ℝ) ^ 2 * s := by positivity
      have e3 := exp_sub_one_le (by positivity) h3
      have e2 := exp_sub_one_le (by positivity) h2
      refine ⟨?_, ?_, ?_⟩
      · have : (I.n : ℝ) * (Real.exp (3 * (I.n : ℝ) ^ 2 * s) - 1) ≤ (I.n : ℝ) * (2 * (3 * (I.n : ℝ) ^ 2 * s)) :=
          mul_le_mul_of_nonneg_left e3 hn0
        nlinarith
      · nlinarith
      · apply Real.exp_le_exp.2
        have hn3 : 0 ≤ 2 * (I.n : ℝ) ^ 3 := by positivity
        have := mul_le_mul_of_nonneg_left e2 hn3
        nlinarith
  obtain ⟨hchart, hexp2, hK1⟩ := hnum

  let C : Set (Fin (I.n ^ 2) → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) s
  let Θv : ∀ v, (Fin (I.n ^ 2) → ℝ) → UJ (I.ε v) := fun v x => Θ (fun _ => x) v
  have hΘv : ∀ v x, uMat (Θv v x) = (List.ofFn fun i => NormedSpace.exp ((x i : ℂ) • E v i)).prod :=
    fun v x => hΘ (fun _ => x) v
  have hΘeq : ∀ t, Θ t = fun v => Θv v (t v) := by
    intro t
    funext v
    exact GlobalTheory.GaugeConst.uMat_injective (I.ε v) ((hΘ t v).trans (hΘv v (t v)).symm)
  have hcont : ∀ v, Continuous (Θv v) := by
    intro v
    have hE' : Continuous fun y : EuclideanSpace ℝ (Fin (I.n ^ 2)) => Θv v (WithLp.ofLp y) := by
      refine GlobalTheory.ProductChart.continuous_chart (E := E v) _ fun y => ?_
      rw [hΘv]
      simp only [Complex.coe_smul]
    exact hE'.comp (PiLp.continuous_toLp _ _)
  have hmeas : ∀ v, Measurable (Θv v) := fun v => (hcont v).measurable
  have hCc : IsCompact C := isCompact_univ_pi fun _ => isCompact_Icc
  let Sv : ∀ v, Set (UJ (I.ε v)) := fun v => Θv v '' C
  have hSv : ∀ v, MeasurableSet (Sv v) := fun v => ((hCc.image (hcont v)).isClosed).measurableSet
  refine ⟨Set.pi Set.univ Sv, MeasurableSet.univ_pi hSv, ?_, ?_⟩
  ·
    intro a ha a' ha' v
    obtain ⟨x, hx, hxa⟩ := ha v (Set.mem_univ v)
    obtain ⟨x', hx', hxa'⟩ := ha' v (Set.mem_univ v)
    have hb : ∀ y ∈ C, ∀ i, |y i| ≤ s := fun y hy i => by
      have hyi := hy i (Set.mem_univ i)
      rw [abs_of_nonneg hyi.1]
      exact hyi.2
    have e1 : uMat (a v) = (List.ofFn fun i => NormedSpace.exp ((x i : ℂ) • E v i)).prod := by
      rw [← hxa]
      exact hΘv v x
    have e2 : uMat (a' v) = (List.ofFn fun i => NormedSpace.exp ((x' i : ℂ) • E v i)).prod := by
      rw [← hxa']
      exact hΘv v x'
    exact dOp_chart_le (hE v) hs.le hexp2 (a v) (a' v) x x' (hb x hx) (hb x' hx') e1 e2
  · intro Φ hΦ

    set Kc := Real.exp (2 * (I.n : ℝ) ^ 3 * (Real.exp (2 * (I.n : ℝ) ^ 2 * s) - 1)) with hKc
    have hone : ∀ v (Ψ : UJ (I.ε v) → ENNReal), Measurable Ψ →
        ∫⁻ t in C, Ψ (Θv v t) ≤ ENNReal.ofReal (Kc * c v) * ∫⁻ y in Sv v, Ψ y ∂(muG (I.ε v)) :=
      fun v => GlobalTheory.ProductChart.lintegral_chart_le I.n (I.ε v) (c v) s (E v) (Θv v) (hc v) (hG v) (hE v)
        hs hchart (hΘv v)
    haveI : IsFiniteMeasure ((volume : Measure (Fin (I.n ^ 2) → ℝ)).restrict C) :=
      isFiniteMeasure_restrict.2 hCc.measure_lt_top.ne
    let ν : ∀ v, Measure (UJ (I.ε v)) := fun v => ((volume : Measure (Fin (I.n ^ 2) → ℝ)).restrict C).map (Θv v)
    let μS : ∀ v, Measure (UJ (I.ε v)) := fun v => (muG (I.ε v)).restrict (Sv v)
    have hfac : ∀ v (A : Set (UJ (I.ε v))), MeasurableSet A → ν v A ≤ ENNReal.ofReal (Kc * c v) * μS v A := by
      intro v A hA
      have hind : Measurable (A.indicator (1 : UJ (I.ε v) → ENNReal)) := measurable_one.indicator hA
      calc ν v A = ∫⁻ y, A.indicator 1 y ∂(ν v) := (lintegral_indicator_one hA).symm
        _ = ∫⁻ t in C, A.indicator 1 (Θv v t) := lintegral_map hind (hmeas v)
        _ ≤ ENNReal.ofReal (Kc * c v) * ∫⁻ y in Sv v, A.indicator 1 y ∂(muG (I.ε v)) := hone v _ hind
        _ = ENNReal.ofReal (Kc * c v) * μS v A := by rw [lintegral_indicator_one hA]
    set K : ENNReal := ∏ v, ENNReal.ofReal (Kc * c v) with hK
    have hbox : ∀ A : ∀ v, Set (UJ (I.ε v)), (∀ v, MeasurableSet (A v)) →
        Measure.pi ν (Set.pi Set.univ A) ≤ K * ∏ v, μS v (A v) := by
      intro A hA
      rw [Measure.pi_pi, hK, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod' fun v _ => hfac v (A v) (hA v)
    have hle : Measure.pi ν ≤ K • Measure.pi μS := by
      by_cases hK0 : K = 0
      · have h0 : Measure.pi ν = 0 := by
          rw [← Measure.measure_univ_eq_zero, ← Set.pi_univ]
          have := hbox (fun _ => Set.univ) fun _ => MeasurableSet.univ
          rw [hK0, zero_mul] at this
          exact le_antisymm this zero_le
        rw [h0]
        exact Measure.zero_le _
      · exact le_smul_pi (Measure.pi ν) μS hK0
          (ENNReal.prod_ne_top fun v _ => ENNReal.ofReal_ne_top) hbox

    have hKle : K ≤ ENNReal.ofReal (Real.exp I.f * ∏ v, c v) := by
      by_cases hc0 : ∀ v, 0 ≤ c v
      · have hKc0 : 0 ≤ Kc := (Real.exp_pos _).le
        rw [hK, ← ENNReal.ofReal_prod_of_nonneg fun v _ => mul_nonneg hKc0 (hc0 v)]
        apply ENNReal.ofReal_le_ofReal
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun v _ => hc0 v)
        have hcard : Fintype.card (InfinitePlace I.F) ≤ I.f := by
          have h1 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := I.F)
          have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (K := I.F)
          have h3 : I.f = Module.finrank ℚ I.F := by unfold AutInst.f; rfl
          omega
        calc Kc ^ Fintype.card (InfinitePlace I.F) ≤ Real.exp 1 ^ Fintype.card (InfinitePlace I.F) :=
              pow_le_pow_left₀ hKc0 hK1 _
          _ = Real.exp (Fintype.card (InfinitePlace I.F) * 1) := (Real.exp_nat_mul _ _).symm
          _ ≤ Real.exp I.f := by
              apply Real.exp_le_exp.2
              rw [mul_one]
              exact_mod_cast hcard
      · push_neg at hc0
        obtain ⟨v, hv⟩ := hc0
        have : ENNReal.ofReal (Kc * c v) = 0 :=
          ENNReal.ofReal_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hv.le)
        rw [hK, Finset.prod_eq_zero (Finset.mem_univ v) this]
        exact zero_le

    have hvol : (volume : Measure (InfinitePlace I.F → Fin (I.n ^ 2) → ℝ)).restrict
        (Set.pi Set.univ fun _ => C) = Measure.pi fun _ => (volume : Measure (Fin (I.n ^ 2) → ℝ)).restrict C := by
      rw [show (volume : Measure (InfinitePlace I.F → Fin (I.n ^ 2) → ℝ)) =
        Measure.pi fun _ => (volume : Measure (Fin (I.n ^ 2) → ℝ)) from rfl, Measure.restrict_pi_pi]
    have hmapm : Measurable fun t : InfinitePlace I.F → Fin (I.n ^ 2) → ℝ => fun v => Θv v (t v) :=
      measurable_pi_lambda _ fun v => (hmeas v).comp (measurable_pi_apply v)
    have hmap : (Measure.pi fun _ => (volume : Measure (Fin (I.n ^ 2) → ℝ)).restrict C).map
        (fun t v => Θv v (t v)) = Measure.pi ν :=
      Measure.pi_map_pi fun v => (hmeas v).aemeasurable
    have hmu : (muInf I).restrict (Set.pi Set.univ Sv) = Measure.pi μS := by
      rw [show muInf I = Measure.pi fun v => muG (I.ε v) from rfl, Measure.restrict_pi_pi]
    calc ∫⁻ t in Set.pi Set.univ (fun _ => Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) s), Φ (Θ t)
        = ∫⁻ t, Φ (fun v => Θv v (t v)) ∂(Measure.pi fun _ =>
            (volume : Measure (Fin (I.n ^ 2) → ℝ)).restrict C) := by
          have hset : (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) s) =
              Set.pi Set.univ fun _ : InfinitePlace I.F => C := rfl
          rw [hset, hvol]
          exact lintegral_congr fun t => by rw [hΘeq t]
      _ = ∫⁻ y, Φ y ∂(Measure.pi ν) := by rw [← hmap, lintegral_map hΦ hmapm]
      _ ≤ ∫⁻ y, Φ y ∂(K • Measure.pi μS) := lintegral_mono' hle le_rfl
      _ = K * ∫⁻ y in Set.pi Set.univ Sv, Φ y ∂(muInf I) := by
          rw [lintegral_smul_measure, hmu, smul_eq_mul]
      _ ≤ ENNReal.ofReal (Real.exp I.f * ∏ v, c v) * ∫⁻ y in Set.pi Set.univ Sv, Φ y ∂(muInf I) := by
          gcongr

end GlobalTheory.ProductChartAll
