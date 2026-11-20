import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FzSliceContDiffOn

noncomputable section

open MeasureTheory Matrix Filter Topology Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Establish `hU` using `(fzHol n m 0).2.2`. Introduce `y hy`. Establish `h1 : AnalyticAt ℂ (fun p : ℂ × M2 n => fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) p (1, 0)) (0, y)` using `(ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ), (0 : M2 n))).analyticAt _ |>.comp (hU.fderiv (0, y) ⟨Set.mem_univ _, hy⟩)`. Establish `hl : AnalyticAt ℂ (fun w : M2 n => ((0 : ℂ), w)) y` using `analyticAt_const.prod analyticAt_id`. Establish `h2` using `h1.comp hl`.

Use `h2.congr ?_` and prove the remaining obligations. Use `filter_upwards [isOpen_domZ.mem_nhds hy] with w hw`. Conclude with `(Fd_eq m hw).symm`.
-/
theorem Fd_analytic (m : ℕ) : AnalyticOnNhd ℂ (Fd (n := n) m) (DomZ n) := by
  have hU := (fzHol n m 0).2.2
  intro y hy
  have h1 : AnalyticAt ℂ (fun p : ℂ × M2 n => fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) p (1, 0)) (0, y) :=
    (ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ), (0 : M2 n))).analyticAt _ |>.comp (hU.fderiv (0, y) ⟨Set.mem_univ _, hy⟩)
  have hl : AnalyticAt ℂ (fun w : M2 n => ((0 : ℂ), w)) y := analyticAt_const.prod analyticAt_id
  have h2 := h1.comp hl
  refine h2.congr ?_
  filter_upwards [isOpen_domZ.mem_nhds hy] with w hw
  exact (Fd_eq m hw).symm

/- English proof (translation)
Introduce `n m`. Use `⟨(Fd_analytic m).contDiffOn_of_completeSpace, ?_⟩` and prove the remaining obligations. Introduce `Kg _ _ _ _ _ _ μ _ ι hι hK ρ ψ a b x hρ hψ hψs ha hb hx`. Establish `hιG : ∀ k, InG (ι k)` using `fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1`. Use `set y : Kg × (Fin n → Fin n → ℝ) → M2 n := fun p => x * ι p.1 * a * nU (herm p.2) * b with hydef`.

Establish `hherm : Continuous (herm (n` using `n)) := by unfold herm; fun_prop`. Establish `hnU : Continuous fun t : Fin n → Fin n → ℝ => nU (herm t)`. Unfold `nU`. Conclude with `Continuous.matrix_fromBlocks continuous_const hherm continuous_const continuous_const`. Establish `hy : Continuous y` using `(((continuous_const.mul (hι.comp continuous_fst)).mul continuous_const).mul (hnU.comp continuous_snd)).mul continuous_const`.

Establish `hyD : ∀ p, y p ∈ DomZ n` using `fun p => gset_sub_domZ (inG_mul (inG_mul (inG_mul (inG_mul hx (hιG p.1)) ha) (inG_nU_herm p.2)) hb)`. Use `set U : ℂ × M2 n → ℂ := fun q => fz m 0 q.1 q.2 with hUdef`. Establish `hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ DomZ n)` using `fz_contDiffOn m`. Establish `hO : IsOpen (Set.univ ×ˢ DomZ n : Set (ℂ × M2 n))` using `isOpen_univ.prod isOpen_domZ`. Use `set U' : ℂ × M2 n → ℂ := fun q => fderiv ℂ U q (1, 0) with hU'def`.

Establish `hU' : ContinuousOn U' (Set.univ ×ˢ DomZ n)` using `((hU.fderiv_of_isOpen (m := ∞) hO (by simp)).clm_apply contDiffOn_const).continuousOn`. Use `set F : ℂ → Kg × (Fin n → Fin n → ℝ) → ℂ := fun z p => ρ p.1 * (U (z, y p) * ψ p.2) with hFdef`. Use `set F' : ℂ → Kg × (Fin n → Fin n → ℝ) → ℂ := fun z p => ρ p.1 * (U' (z, y p) * ψ p.2) with hF'def`. Use `set S : Set (Kg × (Fin n → Fin n → ℝ)) := Set.univ ×ˢ tsupport ψ with hSdef`. Establish `hS : IsCompact S` using `isCompact_univ.prod hψs`.

Establish `hzero : ∀ p, p ∉ S → ψ p.2 = 0` using `fun p hp => image_eq_zero_of_notMem_tsupport (fun h => hp ⟨Set.mem_univ _, h⟩)`. Establish `hFc : ∀ z, Continuous (F z)` using `fun z => (hρ.comp continuous_fst).mul ((hU.continuousOn.comp_continuous (continuous_const.prodMk hy) (fun p => ⟨Set.mem_univ _, hyD p⟩)).mul (hψ.comp continuous_snd))`. Establish `hF'c : Continuous fun q : ℂ × (Kg × (Fin n → Fin n → ℝ)) => F' q.1 q.2` using `(hρ.comp (continuous_fst.comp continuous_snd)).mul ((hU'.comp_continuous (continuous_fst.prodMk (hy.comp continuous_snd)) (fun q => ⟨Set.mem_univ _, hyD q.2⟩)).mul (hψ.comp (continuous_snd.comp continuous_snd)))`. Establish `hsupp : ∀ (G : Kg × (Fin n → Fin n → ℝ) → ℂ), Continuous G → (∀ p, p ∉ S → G p = 0) → Integrable G (μ.prod volume)`. Introduce `G hG h0`.

Use `hG.integrable_of_hasCompactSupport (IsCompact.of_isClosed_subset hS (isClosed_tsupport G) ?_)` and prove the remaining obligations. Use `closure_minimal (fun p hp => ?_) (isClosed_univ.prod (isClosed_tsupport ψ))` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hp (h0 p h)`. Establish `hFi : ∀ z, Integrable (F z) (μ.prod volume)` using `fun z => hsupp _ (hFc z) (fun p hp => by simp [hFdef, hzero p hp])`.

Take `⟨C, hC⟩` from `(isCompact_closedBall (0 : ℂ) 1 |>.prod hS).exists_bound_of_continuousOn hF'c.continuousOn`. Establish `hbound_int : Integrable (S.indicator fun _ => C) (μ.prod volume)` using `(integrable_indicator_iff (isClosed_univ.prod (isClosed_tsupport ψ)).measurableSet).2 (integrableOn_const hS.measure_lt_top.ne)`. Establish `hderiv` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.prod volume) (F := F) (F' := F') (x₀ := (0 : ℂ)) (s := Metric.ball 0 1) (bound := S.indicator fun _ => C) (Metric.ball_mem_nhds 0 one_pos) (Filter.Eventually.of_forall fun z => (hFc z).aestronglyMeasurable) (hFi 0) ((hF'c.c …`. Distinguish the cases in `hp : p ∈ S`. Rewrite using `[Set.indicator_of_mem hp]`.

Conclude with `hC (z, p) ⟨Metric.ball_subset_closedBall hz, hp⟩`. Rewrite using `[Set.indicator_of_notMem hp]`. Simplify using `[hF'def, hzero p hp])`. Use `hbound_int`. Use the proof step `(Filter.Eventually.of_forall fun p z _ => by`.

Establish `hd : DifferentiableAt ℂ U (z, y p)` using `(hU.contDiffAt (hO.mem_nhds ⟨Set.mem_univ _, hyD p⟩)).differentiableAt (by simp)`. Establish `hl : HasDerivAt (fun z' : ℂ => (z', y p)) ((1 : ℂ), (0 : M2 n)) z` using `(hasDerivAt_id z).prodMk (hasDerivAt_const z (y p))`. Establish `h1` using `hd.hasFDerivAt.comp_hasDerivAt z hl`. Conclude with `(h1.mul_const (ψ p.2)).const_mul (ρ p.1))`. Establish `hT : ∀ (G : M2 n → ℂ), (Integrable (fun p : Kg × (Fin n → Fin n → ℝ) => ρ p.1 * (G (y p) * ψ p.2)) (μ.prod volume)) → tOp μ ι ρ ψ a b G x = ∫ p, ρ p.1 * (G (y p) * ψ p.2) ∂(μ.prod volume)`.

Introduce `G hG`. Rewrite using `[integral_prod _ hG]`. Unfold `tOp`. Use `integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Simplify using `only [hydef]`.

Conclude with `(integral_const_mul _ _).symm`. Establish `e1 : (fun z => tOp μ ι ρ ψ a b (fz m 0 z) x) = fun z => ∫ p, F z p ∂(μ.prod volume)`. Use function extensionality and compare the values at `z`. Conclude with `hT (fz m 0 z) (hFi z)`. Establish `e2 : ∫ p, F' 0 p ∂(μ.prod volume) = tOp μ ι ρ ψ a b (Fd m) x`.

Establish `hF'0 : F' 0 = fun p => ρ p.1 * (Fd m (y p) * ψ p.2)`. Use function extensionality and compare the values at `p`. Simplify using `only [hF'def, hU'def, Fd_eq m (hyD p)]`. Both sides reduce to the same expression. Rewrite using `[hF'0, hT (Fd m) (hF'0 ▸ hderiv.1)]`.

Rewrite using `[e1, hderiv.2.deriv, e2]`.
-/
theorem fdProps : FdProps := by
  intro n m
  refine ⟨(Fd_analytic m).contDiffOn_of_completeSpace, ?_⟩
  intro Kg _ _ _ _ _ _ μ _ ι hι hK ρ ψ a b x hρ hψ hψs ha hb hx
  have hιG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  set y : Kg × (Fin n → Fin n → ℝ) → M2 n := fun p => x * ι p.1 * a * nU (herm p.2) * b with hydef
  have hherm : Continuous (herm (n := n)) := by unfold herm; fun_prop
  have hnU : Continuous fun t : Fin n → Fin n → ℝ => nU (herm t) := by
    unfold nU; exact Continuous.matrix_fromBlocks continuous_const hherm continuous_const continuous_const
  have hy : Continuous y :=
    (((continuous_const.mul (hι.comp continuous_fst)).mul continuous_const).mul (hnU.comp continuous_snd)).mul
      continuous_const
  have hyD : ∀ p, y p ∈ DomZ n := fun p =>
    gset_sub_domZ (inG_mul (inG_mul (inG_mul (inG_mul hx (hιG p.1)) ha) (inG_nU_herm p.2)) hb)
  set U : ℂ × M2 n → ℂ := fun q => fz m 0 q.1 q.2 with hUdef
  have hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ DomZ n) := fz_contDiffOn m
  have hO : IsOpen (Set.univ ×ˢ DomZ n : Set (ℂ × M2 n)) := isOpen_univ.prod isOpen_domZ
  set U' : ℂ × M2 n → ℂ := fun q => fderiv ℂ U q (1, 0) with hU'def
  have hU' : ContinuousOn U' (Set.univ ×ˢ DomZ n) :=
    ((hU.fderiv_of_isOpen (m := ∞) hO (by simp)).clm_apply contDiffOn_const).continuousOn
  set F : ℂ → Kg × (Fin n → Fin n → ℝ) → ℂ := fun z p => ρ p.1 * (U (z, y p) * ψ p.2) with hFdef
  set F' : ℂ → Kg × (Fin n → Fin n → ℝ) → ℂ := fun z p => ρ p.1 * (U' (z, y p) * ψ p.2) with hF'def
  set S : Set (Kg × (Fin n → Fin n → ℝ)) := Set.univ ×ˢ tsupport ψ with hSdef
  have hS : IsCompact S := isCompact_univ.prod hψs
  have hzero : ∀ p, p ∉ S → ψ p.2 = 0 := fun p hp =>
    image_eq_zero_of_notMem_tsupport (fun h => hp ⟨Set.mem_univ _, h⟩)
  have hFc : ∀ z, Continuous (F z) := fun z =>
    (hρ.comp continuous_fst).mul ((hU.continuousOn.comp_continuous (continuous_const.prodMk hy)
      (fun p => ⟨Set.mem_univ _, hyD p⟩)).mul (hψ.comp continuous_snd))
  have hF'c : Continuous fun q : ℂ × (Kg × (Fin n → Fin n → ℝ)) => F' q.1 q.2 :=
    (hρ.comp (continuous_fst.comp continuous_snd)).mul ((hU'.comp_continuous (continuous_fst.prodMk
      (hy.comp continuous_snd)) (fun q => ⟨Set.mem_univ _, hyD q.2⟩)).mul (hψ.comp (continuous_snd.comp continuous_snd)))
  have hsupp : ∀ (G : Kg × (Fin n → Fin n → ℝ) → ℂ), Continuous G → (∀ p, p ∉ S → G p = 0) →
      Integrable G (μ.prod volume) := by
    intro G hG h0
    refine hG.integrable_of_hasCompactSupport (IsCompact.of_isClosed_subset hS (isClosed_tsupport G) ?_)
    refine closure_minimal (fun p hp => ?_) (isClosed_univ.prod (isClosed_tsupport ψ))
    by_contra h; exact hp (h0 p h)
  have hFi : ∀ z, Integrable (F z) (μ.prod volume) := fun z =>
    hsupp _ (hFc z) (fun p hp => by simp [hFdef, hzero p hp])
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1 |>.prod hS).exists_bound_of_continuousOn hF'c.continuousOn
  have hbound_int : Integrable (S.indicator fun _ => C) (μ.prod volume) :=
    (integrable_indicator_iff (isClosed_univ.prod (isClosed_tsupport ψ)).measurableSet).2 (integrableOn_const hS.measure_lt_top.ne)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.prod volume) (F := F) (F' := F')
    (x₀ := (0 : ℂ)) (s := Metric.ball 0 1) (bound := S.indicator fun _ => C) (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun z => (hFc z).aestronglyMeasurable) (hFi 0)
    ((hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p z hz => by
      by_cases hp : p ∈ S
      · rw [Set.indicator_of_mem hp]
        exact hC (z, p) ⟨Metric.ball_subset_closedBall hz, hp⟩
      · rw [Set.indicator_of_notMem hp]
        simp [hF'def, hzero p hp])
    hbound_int
    (Filter.Eventually.of_forall fun p z _ => by
      have hd : DifferentiableAt ℂ U (z, y p) :=
        (hU.contDiffAt (hO.mem_nhds ⟨Set.mem_univ _, hyD p⟩)).differentiableAt (by simp)
      have hl : HasDerivAt (fun z' : ℂ => (z', y p)) ((1 : ℂ), (0 : M2 n)) z :=
        (hasDerivAt_id z).prodMk (hasDerivAt_const z (y p))
      have h1 := hd.hasFDerivAt.comp_hasDerivAt z hl
      exact (h1.mul_const (ψ p.2)).const_mul (ρ p.1))
  have hT : ∀ (G : M2 n → ℂ), (Integrable (fun p : Kg × (Fin n → Fin n → ℝ) => ρ p.1 * (G (y p) * ψ p.2))
      (μ.prod volume)) → tOp μ ι ρ ψ a b G x = ∫ p, ρ p.1 * (G (y p) * ψ p.2) ∂(μ.prod volume) := by
    intro G hG
    rw [integral_prod _ hG]
    unfold tOp
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hydef]
    exact (integral_const_mul _ _).symm
  have e1 : (fun z => tOp μ ι ρ ψ a b (fz m 0 z) x) = fun z => ∫ p, F z p ∂(μ.prod volume) := by
    funext z; exact hT (fz m 0 z) (hFi z)
  have e2 : ∫ p, F' 0 p ∂(μ.prod volume) = tOp μ ι ρ ψ a b (Fd m) x := by
    have hF'0 : F' 0 = fun p => ρ p.1 * (Fd m (y p) * ψ p.2) := by
      funext p; simp only [hF'def, hU'def, Fd_eq m (hyD p)]; rfl
    rw [hF'0, hT (Fd m) (hF'0 ▸ hderiv.1)]
  rw [e1, hderiv.2.deriv, e2]

end PositivityTheory.Rg.Sw.HSt
