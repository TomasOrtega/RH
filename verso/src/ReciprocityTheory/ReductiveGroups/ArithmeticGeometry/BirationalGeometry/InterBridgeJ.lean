import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set

def LogAbsLocIntStatement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (f : (Fin D → ℂ) → ℂ), IsOpen U → AnalyticOnNhd ℂ f U →
    LocallyIntegrableOn (fun z => Real.log ‖f z‖) U volume

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on`. Simplify using `using analyticAt_const`. Name the introduced variables `p q hp hq`. Establish `h` using `hp.add hq`. Simplify using `only [map_add]`.

Conclude with `h`. Name the introduced variables `p i hp`. Establish `h` using `hp.mul (hγ i)`. Simplify using `only [map_mul, MvPolynomial.eval_X]`. Conclude with `h`.
-/
theorem analyticAt_eval_poly {D : ℕ} {σ : Type*} (p : MvPolynomial σ ℂ)
    {γ : (Fin D → ℂ) → σ → ℂ} {u : Fin D → ℂ} (hγ : ∀ i, AnalyticAt ℂ (fun v => γ v i) u) :
    AnalyticAt ℂ (fun v => eval (γ v) p) u := by
  induction p using MvPolynomial.induction_on
  · simpa using analyticAt_const
  · rename_i p q hp hq
    have h := hp.add hq
    simp only [map_add]
    exact h
  · rename_i p i hp
    have h := hp.mul (hγ i)
    simp only [map_mul, MvPolynomial.eval_X]
    exact h

/- English proof (translation)
The claim follows from `|Real.log (a / b)| ≤ |Real.log a| + |Real.log b| := by rcases ha.eq_or_lt with h | h · subst h simp · rw [Real.log_div h.ne' hb.ne', abs_le] constructor <;> linarith [le_abs_self (Real.log a), neg_abs_le (Real.log a), le_abs_self (Real.log b), neg_abs_le (Real.log b)]`.
-/
theorem abs_log_div_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    |Real.log (a / b)| ≤ |Real.log a| + |Real.log b| := by
  rcases ha.eq_or_lt with h | h
  · subst h
    simp
  · rw [Real.log_div h.ne' hb.ne', abs_le]
    constructor <;> linarith [le_abs_self (Real.log a), neg_abs_le (Real.log a),
      le_abs_self (Real.log b), neg_abs_le (Real.log b)]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

/- English proof (translation)
Take `⟨a, hAa, hsa, -⟩` from `hs`. Establish `hpot : ∀ i, IsPotential R.A (potOf R (L i))` using `fun i => isPotential_potOf R (hL i)`. Introduce `j Kc hKt hKc`. Establish `hdens` using `locDensCont R.A (fun i => potOf R (L i)) hpot j`. Establish `hloc : LocallyIntegrableOn (fun y => logNorm A s (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y))) (R.A.chart j).target volume`.

Introduce `y0 hy0`. Set `x0` to `(R.A.chart j).symm y0`. Set `V` to `(R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0`. Establish `hVo : IsOpen V` using `(R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)`. Establish `hy0V : y0 ∈ V` using `⟨hy0, R.mem_U x0⟩`.

Set `γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ` to `fun v => R.lift x0 ((R.A.chart j).symm v)`. Set `F : (Fin e → ℂ) → ℂ` to `fun v => eval (γ v) (map (Int.castRingHom ℂ) s)`. Set `H : (Fin e → ℂ) → ℝ` to `fun v => A.h (γ v)`. Establish `hγa : ∀ y ∈ V, ∀ p, AnalyticAt ℂ (fun v => γ v p) y` using `fun y hy p => R.holo x0 p j y hy`. Establish `hFan : AnalyticOnNhd ℂ F V` using `fun y hy => analyticAt_eval_poly _ (hγa y hy)`.

Establish `hγc : ContinuousOn γ V` using `continuousOn_pi.mpr (fun p => (R.holo x0 p j).continuousOn)`. Establish `hnz : ∀ y ∈ V, ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0` using `fun y hy => (R.mem x0 _ hy.2).1`. Establish `hHpos : ∀ y ∈ V, 0 < H y` using `fun y hy => A.pos _ (hnz y hy)`. Establish `hHc : ContinuousOn H V` using `hA.continuousOn.comp hγc (fun y hy => hnz y hy)`. Establish `hlogH : ContinuousOn (fun y => Real.log (H y)) V` using `hHc.log (fun y hy => (hHpos y hy).ne')`.

Establish `hlogF : LocallyIntegrableOn (fun y => Real.log ‖F y‖) V volume` using `hLA e V F hVo hFan`. Establish `hinv : ∀ y ∈ V, logNorm A s (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)) = Real.log (‖F y‖ / H y)`. Introduce `y hy`. Take `⟨c, hc, hcz⟩` from `R.compat ((R.A.chart j).symm y) x0 ((R.A.chart j).symm y) ⟨R.mem_U _, hy.2⟩`. Rewrite using `[hcz]`.

Establish `h1` using `logNorm_bsmul A hAa hsa hc (R.lift x0 ((R.A.chart j).symm y))`. Conclude with `h1`. Take `⟨δ, hδ, hball⟩` from `Metric.isOpen_iff.mp hVo y0 hy0V`. Establish `hBV : Metric.closedBall y0 (δ / 2) ⊆ V` using `(Metric.closedBall_subset_ball (by linarith)).trans hball`. Establish `hBc : IsCompact (Metric.closedBall y0 (δ / 2))` using `isCompact_closedBall y0 (δ / 2)`.

Establish `hBm : MeasurableSet (Metric.closedBall y0 (δ / 2))` using `Metric.isClosed_closedBall.measurableSet`. Use `⟨Metric.closedBall y0 (δ / 2), mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds y0 (by linarith)), ?_⟩` and prove the remaining obligations. Establish `hmeas : AEStronglyMeasurable (fun y => Real.log (‖F y‖ / H y)) (volume.restrict (Metric.closedBall y0 (δ / 2)))`. Establish `hF' : AEMeasurable (fun y => ‖F y‖) (volume.restrict (Metric.closedBall y0 (δ / 2)))` using `((hFan.continuousOn.mono hBV).aestronglyMeasurable hBm).norm.aemeasurable`. Establish `hH' : AEMeasurable H (volume.restrict (Metric.closedBall y0 (δ / 2)))` using `((hHc.mono hBV).aestronglyMeasurable hBm).aemeasurable`.

Conclude with `(Real.measurable_log.comp_aemeasurable (hF'.div hH')).aestronglyMeasurable`. Establish `hint : IntegrableOn (fun y => Real.log (‖F y‖ / H y)) (Metric.closedBall y0 (δ / 2)) volume`. Establish `hb : Integrable (fun y => |Real.log ‖F y‖| + |Real.log (H y)|) (volume.restrict (Metric.closedBall y0 (δ / 2)))` using `(Integrable.abs (hlogF.integrableOn_compact_subset hBV hBc)).add (Integrable.abs ((hlogH.mono hBV).integrableOn_compact hBc))`. Use `hb.mono' hmeas ?_` and prove the remaining obligations. Use `(ae_restrict_iff' hBm).mpr (Filter.Eventually.of_forall (fun y hy => ?_))` and prove the remaining obligations.

Rewrite using `[Real.norm_eq_abs]`. Conclude with `abs_log_div_le (norm_nonneg _) (hHpos y (hBV hy))`. Conclude with `hint.congr_fun (fun y hy => (hinv y (hBV hy)).symm) hBm`. Conclude with `(hloc.integrableOn_compact_subset hKt hKc).mul_continuousOn (hdens.mono hKt) hKc`.
-/
theorem brIntegrable_of (hLA : LogAbsLocIntStatement) (R : AnLogRes P J e)
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    MIntegrable R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) := by
  classical
  obtain ⟨a, hAa, hsa, -⟩ := hs
  have hpot : ∀ i, IsPotential R.A (potOf R (L i)) := fun i => isPotential_potOf R (hL i)
  intro j Kc hKt hKc
  have hdens := locDensCont R.A (fun i => potOf R (L i)) hpot j
  have hloc : LocallyIntegrableOn
      (fun y => logNorm A s (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)))
      (R.A.chart j).target volume := by
    intro y0 hy0
    let x0 := (R.A.chart j).symm y0
    let V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0
    have hVo : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
    have hy0V : y0 ∈ V := ⟨hy0, R.mem_U x0⟩
    let γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun v => R.lift x0 ((R.A.chart j).symm v)
    let F : (Fin e → ℂ) → ℂ := fun v => eval (γ v) (map (Int.castRingHom ℂ) s)
    let H : (Fin e → ℂ) → ℝ := fun v => A.h (γ v)
    have hγa : ∀ y ∈ V, ∀ p, AnalyticAt ℂ (fun v => γ v p) y := fun y hy p => R.holo x0 p j y hy
    have hFan : AnalyticOnNhd ℂ F V := fun y hy => analyticAt_eval_poly _ (hγa y hy)
    have hγc : ContinuousOn γ V := continuousOn_pi.mpr (fun p => (R.holo x0 p j).continuousOn)
    have hnz : ∀ y ∈ V, ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := fun y hy => (R.mem x0 _ hy.2).1
    have hHpos : ∀ y ∈ V, 0 < H y := fun y hy => A.pos _ (hnz y hy)
    have hHc : ContinuousOn H V := hA.continuousOn.comp hγc (fun y hy => hnz y hy)
    have hlogH : ContinuousOn (fun y => Real.log (H y)) V := hHc.log (fun y hy => (hHpos y hy).ne')
    have hlogF : LocallyIntegrableOn (fun y => Real.log ‖F y‖) V volume := hLA e V F hVo hFan
    have hinv : ∀ y ∈ V, logNorm A s (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)) =
        Real.log (‖F y‖ / H y) := by
      intro y hy
      obtain ⟨c, hc, hcz⟩ := R.compat ((R.A.chart j).symm y) x0 ((R.A.chart j).symm y)
        ⟨R.mem_U _, hy.2⟩
      rw [hcz]
      have h1 := logNorm_bsmul A hAa hsa hc (R.lift x0 ((R.A.chart j).symm y))
      exact h1
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hVo y0 hy0V
    have hBV : Metric.closedBall y0 (δ / 2) ⊆ V :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    have hBc : IsCompact (Metric.closedBall y0 (δ / 2)) := isCompact_closedBall y0 (δ / 2)
    have hBm : MeasurableSet (Metric.closedBall y0 (δ / 2)) :=
      Metric.isClosed_closedBall.measurableSet
    refine ⟨Metric.closedBall y0 (δ / 2),
      mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds y0 (by linarith)), ?_⟩
    have hmeas : AEStronglyMeasurable (fun y => Real.log (‖F y‖ / H y))
        (volume.restrict (Metric.closedBall y0 (δ / 2))) := by
      have hF' : AEMeasurable (fun y => ‖F y‖) (volume.restrict (Metric.closedBall y0 (δ / 2))) :=
        ((hFan.continuousOn.mono hBV).aestronglyMeasurable hBm).norm.aemeasurable
      have hH' : AEMeasurable H (volume.restrict (Metric.closedBall y0 (δ / 2))) :=
        ((hHc.mono hBV).aestronglyMeasurable hBm).aemeasurable
      exact (Real.measurable_log.comp_aemeasurable (hF'.div hH')).aestronglyMeasurable
    have hint : IntegrableOn (fun y => Real.log (‖F y‖ / H y)) (Metric.closedBall y0 (δ / 2))
        volume := by
      have hb : Integrable (fun y => |Real.log ‖F y‖| + |Real.log (H y)|)
          (volume.restrict (Metric.closedBall y0 (δ / 2))) :=
        (Integrable.abs (hlogF.integrableOn_compact_subset hBV hBc)).add
          (Integrable.abs ((hlogH.mono hBV).integrableOn_compact hBc))
      refine hb.mono' hmeas ?_
      refine (ae_restrict_iff' hBm).mpr (Filter.Eventually.of_forall (fun y hy => ?_))
      rw [Real.norm_eq_abs]
      exact abs_log_div_le (norm_nonneg _) (hHpos y (hBV hy))
    exact hint.congr_fun (fun y hy => (hinv y (hBV hy)).symm) hBm
  exact (hloc.integrableOn_compact_subset hKt hKc).mul_continuousOn (hdens.mono hKt) hKc

end ReciprocityTheory.ChartRestriction.G.Geo
