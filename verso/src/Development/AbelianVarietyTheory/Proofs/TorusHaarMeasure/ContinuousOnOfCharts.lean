import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

namespace GlobalTheory.KronMetric

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use `h 1 X.Γ.one_mem x hx b hb` as an intermediate fact. Rewrite `this` using `[FundSetPf.lact_one]`. Then use the resulting hypothesis.
-/
theorem inv_rmul {r : ℕ} {X : Data E r} {ψ : Frame X.Ψ r → ℝ} (h : IsInvFn X ψ) {x b : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) : ψ (rmul x b) = ψ x := by
  have := h 1 X.Γ.one_mem x hx b hb
  rwa [FundSetPf.lact_one] at this

/- English proof (translation)
Use `h γ hγ x hx _ (ExtFPf.oneF_mem X)` as an intermediate fact. Rewrite `this` using `[ExtFPf.rmul_oneF]`. Then use the resulting hypothesis.
-/
theorem inv_lact {r : ℕ} {X : Data E r} {ψ : Frame X.Ψ r → ℝ} (h : IsInvFn X ψ) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : ψ (lact γ x) = ψ x := by
  have := h γ hγ x hx _ (ExtFPf.oneF_mem X)
  rwa [ExtFPf.rmul_oneF] at this

/- English proof (translation)
Introduce `x hx`. Take `⟨x1, ho, b, hb, hxe⟩` from `ortho_holds r X x hx`. Take `⟨D⟩` from `ExtFPf.luData_of lu_holds X x1 ho`. Establish `h0 : (0 : V (nd X)) ∈ OmF X x1` using `by show cpt X x1 0 ∈ X.dom`. Rewrite using `[IW.cpt_zero]`.

Conclude with `IW.orth_mem_dom X x1 ho`. Establish `hΔ : D.Δ x ≠ 0`. Use `(D.uniq 0 h0 b hb).1` as an intermediate fact. Rewrite `this` using `[IW.cpt_zero, ← hxe]`. Then use the resulting hypothesis. Establish `hc : ContinuousOn (fun y => ψ (cpt X x1 (D.zOf y))) (ExtFPf.cell D)` using `(hs x1 ho).comp D.hz.continuousOn fun y hy => (D.split y hy.1 hy.2).1`.

Establish `hc' : ContinuousOn ψ (ExtFPf.cell D)`. Use `hc.congr fun y hy => ?_` and prove the remaining obligations. Take `⟨h1, h2, h3⟩` from `D.split y hy.1 hy.2`. Use `show ψ y = ψ (cpt X x1 (D.zOf y))`. Use `conv_lhs => rw [h3]`.

Conclude with `inv_rmul h h1 h2`. Conclude with `(hc'.continuousAt ((ExtFPf.isOpen_cell D).mem_nhds ⟨hx, hΔ⟩)).continuousWithinAt`.
-/
theorem continuousOn_of_charts {r : ℕ} {X : Data E r} {ψ : Frame X.Ψ r → ℝ} (h : IsInvFn X ψ)
    (hs : ∀ x0, IsOrth X x0 → ContinuousOn (fun z => ψ (cpt X x0 z)) (OmF X x0)) :
    ContinuousOn ψ X.dom := by
  intro x hx
  obtain ⟨x1, ho, b, hb, hxe⟩ := ortho_holds r X x hx
  obtain ⟨D⟩ := ExtFPf.luData_of lu_holds X x1 ho
  have h0 : (0 : V (nd X)) ∈ OmF X x1 := by
    show cpt X x1 0 ∈ X.dom
    rw [IW.cpt_zero]
    exact IW.orth_mem_dom X x1 ho
  have hΔ : D.Δ x ≠ 0 := by
    have := (D.uniq 0 h0 b hb).1
    rwa [IW.cpt_zero, ← hxe] at this
  have hc : ContinuousOn (fun y => ψ (cpt X x1 (D.zOf y))) (ExtFPf.cell D) :=
    (hs x1 ho).comp D.hz.continuousOn fun y hy => (D.split y hy.1 hy.2).1
  have hc' : ContinuousOn ψ (ExtFPf.cell D) := by
    refine hc.congr fun y hy => ?_
    obtain ⟨h1, h2, h3⟩ := D.split y hy.1 hy.2
    show ψ y = ψ (cpt X x1 (D.zOf y))
    conv_lhs => rw [h3]
    exact inv_rmul h h1 h2
  exact (hc'.continuousAt ((ExtFPf.isOpen_cell D).mem_nhds ⟨hx, hΔ⟩)).continuousWithinAt

/- English proof (translation)
Establish `hn` using `FlowCoefficientBounds.nfac_pos X hx la`. Unfold `phla`. Rewrite using `[neg_mul, neg_neg, show 2 * Real.log (X.nfac la x) = Real.log (X.nfac la x ^ 2) by`. Rewrite using `[Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]`.
-/
theorem exp_neg_phla {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Real.exp (-phla X la x) = X.nfac la x ^ 2 := by
  have hn := FlowCoefficientBounds.nfac_pos X hx la
  unfold phla
  rw [neg_mul, neg_neg, show 2 * Real.log (X.nfac la x) = Real.log (X.nfac la x ^ 2) by
    rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]

/- English proof (translation)
Rewrite using `[neg_add, Real.exp_add, exp_neg_phla X la hx]`.
-/
theorem exp_neg_add {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    Real.exp (-(phla X la x + ψ x)) = X.nfac la x ^ 2 * Real.exp (-ψ x) := by
  rw [neg_add, Real.exp_add, exp_neg_phla X la hx]

/- English proof (translation)
Introduce and unpack `⟨hR, hL, -⟩ r X la ψ hinv hs ⟨C, hC⟩`. Establish `hψc : ContinuousOn ψ X.dom` using `continuousOn_of_charts hinv fun x0 h => (hs x0 h).continuousOn`. Use `⟨hψc, ⟨?_, ?_, ?_⟩, Real.exp (-C), Real.exp_pos _, ?_⟩` and prove the remaining obligations. Establish `hc : ContinuousOn (fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) X.dom`. Use `ENNReal.continuous_ofReal.comp_continuousOn ?_` and prove the remaining obligations.

Use `(((ExtFPf.nfac_contOn X la).pow 2).mul (Real.continuous_exp.comp_continuousOn hψc.neg)).congr fun x hx => ?_` and prove the remaining obligations. Conclude with `exp_neg_add X la ψ hx`. Rewrite using `[← Set.piecewise_eq_indicator]`. Conclude with `hc.measurable_piecewise continuousOn_const (FourierCoefficientDomain.isOpen_dom X).measurableSet`. Introduce `x hx b hb`.

Establish `hxb` using `OntoS.dom_rmul X hx hb`. Establish `hpos : 0 < ‖bchar la b‖` using `norm_pos_iff.2 (OntoE.bchar_ne X la hb)`. Rewrite using `[Set.indicator_of_mem hxb, Set.indicator_of_mem hx, exp_neg_add X la ψ hxb, exp_neg_add X la ψ hx, hR r X la x hx b hb, inv_rmul hinv hx hb, ← ENNReal.ofReal_div_of_pos (by positivity)]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Introduce `γ hγ x hx`. Establish `hγx` using `OntoS.dom_lact X hγ hx`. Rewrite using `[Set.indicator_of_mem hγx, Set.indicator_of_mem hx, exp_neg_add X la ψ hγx, exp_neg_add X la ψ hx, hL r X la γ hγ x hx, inv_lact hinv hγ hx]`. Introduce `x hx`. Rewrite using `[Set.indicator_of_mem hx, ← Real.exp_add]`.

Use `ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)` and prove the remaining obligations. Combine the linear relations using `[hC x hx]`.
-/
theorem kronMetric :
    (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), ∀ ψ : Frame X.Ψ r → ℝ, IsInvFn X ψ → (∀ x0, IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0)) → (∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) → ContinuousOn ψ X.dom ∧ IsMetricW X la (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) ∧ WLower X la (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x))))) := by
  rintro ⟨hR, hL, -⟩ r X la ψ hinv hs ⟨C, hC⟩
  classical
  have hψc : ContinuousOn ψ X.dom := continuousOn_of_charts hinv fun x0 h => (hs x0 h).continuousOn
  refine ⟨hψc, ⟨?_, ?_, ?_⟩, Real.exp (-C), Real.exp_pos _, ?_⟩
  · have hc : ContinuousOn (fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) X.dom := by
      refine ENNReal.continuous_ofReal.comp_continuousOn ?_
      refine (((ExtFPf.nfac_contOn X la).pow 2).mul
        (Real.continuous_exp.comp_continuousOn hψc.neg)).congr fun x hx => ?_
      exact exp_neg_add X la ψ hx
    rw [← Set.piecewise_eq_indicator]
    exact hc.measurable_piecewise continuousOn_const (FourierCoefficientDomain.isOpen_dom X).measurableSet
  · intro x hx b hb
    have hxb := OntoS.dom_rmul X hx hb
    have hpos : 0 < ‖bchar la b‖ := norm_pos_iff.2 (OntoE.bchar_ne X la hb)
    rw [Set.indicator_of_mem hxb, Set.indicator_of_mem hx, exp_neg_add X la ψ hxb,
      exp_neg_add X la ψ hx, hR r X la x hx b hb, inv_rmul hinv hx hb,
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  · intro γ hγ x hx
    have hγx := OntoS.dom_lact X hγ hx
    rw [Set.indicator_of_mem hγx, Set.indicator_of_mem hx, exp_neg_add X la ψ hγx,
      exp_neg_add X la ψ hx, hL r X la γ hγ x hx, inv_lact hinv hγ hx]
  · intro x hx
    rw [Set.indicator_of_mem hx, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    linarith [hC x hx]

end GlobalTheory.KronMetric
