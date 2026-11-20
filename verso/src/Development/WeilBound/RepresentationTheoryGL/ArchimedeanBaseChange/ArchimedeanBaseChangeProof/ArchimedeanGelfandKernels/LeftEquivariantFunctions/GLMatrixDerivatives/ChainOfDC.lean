import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfGam

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.DCc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Introduce `x hx`. Establish `hev : f =ᶠ[𝓝 x] f'` using `Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h`. Simplify using `only [DC, Rd, hev.fderiv_eq, h hx]`.
-/
theorem dc_congr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V))
    (Fr : Mat n → (V →L[ℂ] V)) {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) :
    Set.EqOn (DC ε Fr f) (DC ε Fr f') U := by
  intro x hx
  have hev : f =ᶠ[𝓝 x] f' := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h
  simp only [DC, Rd, hev.fderiv_eq, h hx]

/- English proof (translation)
Establish `hs : IsOpen ((Set.univ : Set ℝ) ×ˢ GLs n)` using `isOpen_univ.prod (isOpen_GLs n)`. Establish `hc : ContinuousOn (fderiv ℝ (Function.uncurry u)) (Set.univ ×ˢ GLs n)` using `hu.continuousOn_fderiv_of_isOpen hs (by simp)`. Establish `key : ∀ t, fderiv ℝ (u t) x = (fderiv ℝ (Function.uncurry u) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Mat n))`. Introduce `t`. Establish `hd : DifferentiableAt ℝ (Function.uncurry u) (t, x)` using `(hu.differentiableOn (by simp)).differentiableAt (hs.mem_nhds ⟨Set.mem_univ _, hx⟩)`.

Conclude with `(hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv`. Establish `hline : Continuous fun t : ℝ => ((t, x) : ℝ × Mat n)` using `continuous_id.prodMk continuous_const`. Prove the components needed by the constructor for the conclusion. Conclude with `hu.continuousOn.comp_continuous hline (fun t => ⟨Set.mem_univ _, hx⟩)`. Simplify using `only [Rd, key, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]`.

Conclude with `(hc.comp_continuous hline (fun t => ⟨Set.mem_univ _, hx⟩)).clm_apply continuous_const`.
-/
theorem cont_partial {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (u : ℝ → Mat n → V)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ GLs n)) (x : Mat n) (hx : x ∈ GLs n) (X : Mat n) :
    Continuous (fun t => u t x) ∧ Continuous (fun t => Rd X (u t) x) := by
  have hs : IsOpen ((Set.univ : Set ℝ) ×ˢ GLs n) := isOpen_univ.prod (isOpen_GLs n)
  have hc : ContinuousOn (fderiv ℝ (Function.uncurry u)) (Set.univ ×ˢ GLs n) :=
    hu.continuousOn_fderiv_of_isOpen hs (by simp)
  have key : ∀ t, fderiv ℝ (u t) x =
      (fderiv ℝ (Function.uncurry u) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Mat n)) := by
    intro t
    have hd : DifferentiableAt ℝ (Function.uncurry u) (t, x) :=
      (hu.differentiableOn (by simp)).differentiableAt (hs.mem_nhds ⟨Set.mem_univ _, hx⟩)
    exact (hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv
  have hline : Continuous fun t : ℝ => ((t, x) : ℝ × Mat n) := continuous_id.prodMk continuous_const
  constructor
  · exact hu.continuousOn.comp_continuous hline (fun t => ⟨Set.mem_univ _, hx⟩)
  · simp only [Rd, key, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    exact (hc.comp_continuous hline (fun t => ⟨Set.mem_univ _, hx⟩)).clm_apply continuous_const

/- English proof (translation)
Use `HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) T) ?_` and prove the remaining obligations. Introduce `t ht`. Simplify using `only [Complex.ofReal_eq_zero]`. Conclude with `hgb.2.2 t (by simpa [Real.norm_eq_abs, not_le] using ht)`.
-/
theorem bump_cpt (g : ℝ → ℝ) (T : ℝ) (hgb : IsBump g T) : HasCompactSupport fun t => (g t : ℂ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) T) ?_
  intro t ht
  simp only [Complex.ofReal_eq_zero]
  exact hgb.2.2 t (by simpa [Real.norm_eq_abs, not_le] using ht)

/- English proof (translation)
Use `((Complex.continuous_ofReal.comp hgb.1.continuous).smul hφ).integrable_of_hasCompactSupport ?_` and prove the remaining obligations. Conclude with `(bump_cpt g T hgb).smul_right`.
-/
theorem int_bump {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (g : ℝ → ℝ) (T : ℝ) (hgb : IsBump g T)
    (φ : ℝ → V) (hφ : Continuous φ) : Integrable fun t => (g t : ℂ) • φ t := by
  refine ((Complex.continuous_ofReal.comp hgb.1.continuous).smul hφ).integrable_of_hasCompactSupport ?_
  exact (bump_cpt g T hgb).smul_right

/- English proof (translation)
Establish `hc` using `fun X => cont_partial u hu x hx X`. Establish `ia : ∀ X, Integrable (fun t => (g t : ℂ) • Rd X (u t) x)` using `fun X => int_bump g T hgb _ (hc X).2`. Establish `ib : Integrable (fun t => (g t : ℂ) • u t x)` using `int_bump g T hgb _ (hc 0).1`. Establish `iab : ∀ p : Fin n × Fin n, Integrable (fun t => (g t : ℂ) • Rd (hb p) (u t) x + (fderiv ℝ Fr 1 (hb p)) ((g t : ℂ) • u t x))` using `fun p => (ia _).add ((fderiv ℝ Fr 1 (hb p)).integrable_comp ib)`. Establish `hpt : ∀ t, (g t : ℂ) • DC ε Fr (u t) x = ∑ p : Fin n × Fin n, ε (hb p) ((g t : ℂ) • Rd (hb p) (u t) x + (fderiv ℝ Fr 1 (hb p)) ((g t : ℂ) • u t x))`.

Introduce `t`. Simplify using `only [DC, Finset.smul_sum, map_add, map_smul, smul_add]`. Rewrite using `[integral_congr_ae (Filter.Eventually.of_forall hpt)]`. Rewrite using `[integral_finset_sum _ (fun p _ => (ε (hb p)).integrable_comp (iab p))]`. Simplify using `only [DC, hRd _ x hx]`.

Use `Finset.sum_congr rfl (fun p _ => ?_)` and prove the remaining obligations. Rewrite using `[(ε (hb p)).integral_comp_comm (iab p), integral_add (ia _) ((fderiv ℝ Fr 1 (hb p)).integrable_comp ib), (fderiv ℝ Fr 1 (hb p)).integral_comp_comm ib]`.
-/
theorem param_dc {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V))
    (Fr : Mat n → (V →L[ℂ] V)) (u : ℝ → Mat n → V)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ GLs n)) (g : ℝ → ℝ) (T : ℝ) (hgb : IsBump g T)
    (hRd : ∀ X, ∀ x ∈ GLs n, Rd X (fun x' => ∫ t, (g t : ℂ) • u t x') x = ∫ t, (g t : ℂ) • Rd X (u t) x)
    (x : Mat n) (hx : x ∈ GLs n) :
    ∫ t, (g t : ℂ) • DC ε Fr (u t) x = DC ε Fr (fun x' => ∫ t, (g t : ℂ) • u t x') x := by
  have hc := fun X => cont_partial u hu x hx X
  have ia : ∀ X, Integrable (fun t => (g t : ℂ) • Rd X (u t) x) := fun X => int_bump g T hgb _ (hc X).2
  have ib : Integrable (fun t => (g t : ℂ) • u t x) := int_bump g T hgb _ (hc 0).1
  have iab : ∀ p : Fin n × Fin n, Integrable (fun t => (g t : ℂ) • Rd (hb p) (u t) x +
      (fderiv ℝ Fr 1 (hb p)) ((g t : ℂ) • u t x)) :=
    fun p => (ia _).add ((fderiv ℝ Fr 1 (hb p)).integrable_comp ib)
  have hpt : ∀ t, (g t : ℂ) • DC ε Fr (u t) x = ∑ p : Fin n × Fin n, ε (hb p)
      ((g t : ℂ) • Rd (hb p) (u t) x + (fderiv ℝ Fr 1 (hb p)) ((g t : ℂ) • u t x)) := by
    intro t
    simp only [DC, Finset.smul_sum, map_add, map_smul, smul_add]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finset_sum _ (fun p _ => (ε (hb p)).integrable_comp (iab p))]
  simp only [DC, hRd _ x hx]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [(ε (hb p)).integral_comp_comm (iab p),
    integral_add (ia _) ((fderiv ℝ Fr 1 (hb p)).integrable_comp ib),
    (fderiv ℝ Fr 1 (hb p)).integral_comp_comm ib]

end PositivityTheory.RgBcC.LfSt.ChainPf.DCc
