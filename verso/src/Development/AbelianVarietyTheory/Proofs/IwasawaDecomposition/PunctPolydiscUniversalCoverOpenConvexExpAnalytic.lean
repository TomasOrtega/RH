import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Introduce `n a`. Establish `hEq : GlobalTheory.ShFam.Hor.logDom n a = ⋂ k : Fin n, (fun s : Fin n → ℂ => s k) ⁻¹' (if (k : ℕ) < a then {z : ℂ | z.re < 0} else Metric.ball (0 : ℂ) 1)`. Use extensionality with `s`. Simplify using `only [GlobalTheory.ShFam.Hor.logDom, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]`. Use `forall_congr' fun k => ?_` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> simp [Metric.mem_ball, dist_zero_right]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hEq]`. Use `isOpen_iInter_of_finite fun k => ?_` and prove the remaining obligations. Use `IsOpen.preimage (continuous_apply k) ?_` and prove the remaining obligations.

Use `split_ifs`. Conclude with `isOpen_lt Complex.continuous_re continuous_const`. Conclude with `Metric.isOpen_ball`. Rewrite using `[hEq]`. Use `convex_iInter fun k => ?_` and prove the remaining obligations.

Establish `hc : Convex ℝ (if (k : ℕ) < a then {z : ℂ | z.re < 0} else Metric.ball (0 : ℂ) 1)` using `by split_ifs`. Conclude with `convex_halfSpace_lt (f := Complex.re) Complex.reLm.isLinear 0`. Conclude with `convex_ball 0 1`. Conclude with `hc.linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k)`. Introduce `s`.

Rewrite using `[analyticAt_pi_iff]`. Introduce `k`. Use `show AnalyticAt ℂ (fun s : Fin n → ℂ => if (k : ℕ) < a then Complex.exp (s k) else s k) s`. Establish `hp : AnalyticAt ℂ (fun s : Fin n → ℂ => s k) s` using `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) k).analyticAt s`. Use `split_ifs`.

Conclude with `analyticAt_cexp.comp hp`. Conclude with `hp`. Introduce `s hs`. Rewrite using `[Metric.mem_ball, dist_zero_right, pi_norm_lt_iff one_pos]`. Introduce `k`.

Establish `hk` using `hs k`. Simplify using `only [GlobalTheory.ShFam.Hor.logExp]`. Use `split_ifs at hk ⊢ with h`. Rewrite using `[Complex.norm_exp]`. Conclude with `Real.exp_lt_one_iff.mpr hk`.

Conclude with `hk`.
-/
theorem GlobalTheory.logDom_chart_props : ∀ (n a : ℕ), IsOpen (GlobalTheory.ShFam.Hor.logDom n a) ∧ Convex ℝ (GlobalTheory.ShFam.Hor.logDom n a) ∧ (∀ s, AnalyticAt ℂ (GlobalTheory.ShFam.Hor.logExp a : (Fin n → ℂ) → Fin n → ℂ) s) ∧ Set.MapsTo (GlobalTheory.ShFam.Hor.logExp a) (GlobalTheory.ShFam.Hor.logDom n a) (Metric.ball (0 : Fin n → ℂ) 1) := by
  intro n a
  have hEq : GlobalTheory.ShFam.Hor.logDom n a = ⋂ k : Fin n, (fun s : Fin n → ℂ => s k) ⁻¹' (if (k : ℕ) < a then {z : ℂ | z.re < 0} else Metric.ball (0 : ℂ) 1) := by
    ext s
    simp only [GlobalTheory.ShFam.Hor.logDom, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    refine forall_congr' fun k => ?_
    split_ifs <;> simp [Metric.mem_ball, dist_zero_right]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hEq]
    refine isOpen_iInter_of_finite fun k => ?_
    refine IsOpen.preimage (continuous_apply k) ?_
    split_ifs
    · exact isOpen_lt Complex.continuous_re continuous_const
    · exact Metric.isOpen_ball
  · rw [hEq]
    refine convex_iInter fun k => ?_
    have hc : Convex ℝ (if (k : ℕ) < a then {z : ℂ | z.re < 0} else Metric.ball (0 : ℂ) 1) := by
      split_ifs
      · exact convex_halfSpace_lt (f := Complex.re) Complex.reLm.isLinear 0
      · exact convex_ball 0 1
    exact hc.linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k)
  · intro s
    rw [analyticAt_pi_iff]
    intro k
    show AnalyticAt ℂ (fun s : Fin n → ℂ => if (k : ℕ) < a then Complex.exp (s k) else s k) s
    have hp : AnalyticAt ℂ (fun s : Fin n → ℂ => s k) s :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) k).analyticAt s
    split_ifs
    · exact analyticAt_cexp.comp hp
    · exact hp
  · intro s hs
    rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff one_pos]
    intro k
    have hk := hs k
    simp only [GlobalTheory.ShFam.Hor.logExp]
    split_ifs at hk ⊢ with h
    · rw [Complex.norm_exp]
      exact Real.exp_lt_one_iff.mpr hk
    · exact hk
