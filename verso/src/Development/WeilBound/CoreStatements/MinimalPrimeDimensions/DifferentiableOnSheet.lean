import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.IntegralBallPow
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.EvaluationGenEqZero
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxE

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open MeasureTheory Set Filter Topology Matrix GlobalTheory.ChartGlue
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GroundTheory.Heights₂.Heights (HermNorm coneBall)
open scoped ENNReal ContDiff

namespace ChowFormHeightComparison₂.CF.C

variable {R : Type} [CommRing R] {m e : ℕ}

def euc (h : HermNorm m) (x : Fin m → ℂ) : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)

/- English proof (translation)
Rewrite using `[Matrix.det_transpose]`. Conclude with `h.isUnit_det`.
-/
theorem isUnit_det_transpose (h : HermNorm m) : IsUnit (h.matᵀ).det := by
  rw [Matrix.det_transpose]; exact h.isUnit_det

/- English proof (translation)
Express the relevant statement in the definitionally equal form `h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_transpose h), Matrix.one_mulVec]`.
-/
theorem pointOf_euc (h : HermNorm m) (x : Fin m → ℂ) : h.pointOf (euc h x) = x := by
  change h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_transpose h), Matrix.one_mulVec]

/- English proof (translation)
Establish `hu` using `isUnit_det_transpose h`. Simplify using `only [HermNorm.pointOf, euc]`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]`.
-/
theorem euc_pointOf (h : HermNorm m) (y : EuclideanSpace ℂ (Fin m)) : euc h (h.pointOf y) = y := by
  have hu := isUnit_det_transpose h
  simp only [HermNorm.pointOf, euc]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/- English proof (translation)
Simplify using `only [euc, Matrix.mulVec_smul]`. Both sides reduce to the same expression.
-/
theorem euc_smul (h : HermNorm m) (c : ℂ) (x : Fin m → ℂ) : euc h (c • x) = c • euc h x := by
  simp only [euc, Matrix.mulVec_smul]
  rfl

/- English proof (translation)
The claim follows from `Function.LeftInverse.injective (pointOf_euc h)`.
-/
theorem euc_injective (h : HermNorm m) : Function.Injective (euc h) :=
  Function.LeftInverse.injective (pointOf_euc h)

/- English proof (translation)
The claim follows from `EuclideanSpace.norm_eq _`.
-/
theorem norm_euc (h : HermNorm m) (x : Fin m → ℂ) : ‖euc h x‖ = h.dualNorm x := EuclideanSpace.norm_eq _

/- English proof (translation)
Unfold `euc`. Use `fun_prop`.
-/
theorem continuous_euc (h : HermNorm m) : Continuous (euc h) := by
  unfold euc
  fun_prop

variable {Z : Scheme.{0}} {B : LB Z} {p : Z ⟶ Sp R} {s : Fin m → B.Sec} {σ : R →+* ℂ}

variable (s) in

def sheet (h : HermNorm m) (c : AlgChart p σ e) (i : B.ι) (x : Fin e → ℂ) : Fin m → ℂ :=
  (h.matᵀ)⁻¹ *ᵥ loc p s σ i (c.e.symm (WithLp.toLp 2 x))

variable {h : HermNorm m} {φ : Weight p σ B}

/- English proof (translation)
Conclude with `(c.e.isOpen_inter_preimage_symm (isOpen_ptsIn _)).preimage (PiLp.continuous_toLp 2 _)`.
-/
theorem isOpen_dom (c : AlgChart p σ e) (i : B.ι) :
    IsOpen ((WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i))) := by
  exact (c.e.isOpen_inter_preimage_symm (isOpen_ptsIn _)).preimage (PiLp.continuous_toLp 2 _)

/- English proof (translation)
Establish `hL : Differentiable ℂ (WithLp.toLp 2 : (Fin e → ℂ) → V e)` using `(PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin e => ℂ)).symm.differentiable`. Establish `hg : ∀ k, DifferentiableOn ℂ (fun x : Fin e → ℂ => loc p s σ i (c.e.symm (WithLp.toLp 2 x)) k) ((WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i)))`. Introduce `k`. Conclude with `(c.holo (B.U i) ((s k).f i)).comp hL.differentiableOn (fun x hx => hx)`. Rewrite using `[differentiableOn_pi]`.

Introduce `j`. Simplify using `only [sheet, Matrix.mulVec, dotProduct]`. Conclude with `DifferentiableOn.fun_sum fun k _ => (hg k).const_mul _`.
-/
theorem differentiableOn_sheet (c : AlgChart p σ e) (i : B.ι) : DifferentiableOn ℂ (sheet s h c i)
    ((WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i))) := by
  have hL : Differentiable ℂ (WithLp.toLp 2 : (Fin e → ℂ) → V e) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin e => ℂ)).symm.differentiable
  have hg : ∀ k, DifferentiableOn ℂ (fun x : Fin e → ℂ => loc p s σ i (c.e.symm (WithLp.toLp 2 x)) k)
      ((WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i))) := by
    intro k
    exact (c.holo (B.U i) ((s k).f i)).comp hL.differentiableOn (fun x hx => hx)
  rw [differentiableOn_pi]
  intro j
  simp only [sheet, Matrix.mulVec, dotProduct]
  exact DifferentiableOn.fun_sum fun k _ => (hg k).const_mul _

/- English proof (translation)
Simplify using `only [sheet, euc, WithLp.toLp_ofLp, c.e.left_inv hy]`.
-/
theorem toLp_sheet (c : AlgChart p σ e) (i : B.ι) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    WithLp.toLp 2 (sheet s h c i (c.e y).ofLp) = euc h (loc p s σ i y) := by
  simp only [sheet, euc, WithLp.toLp_ofLp, c.e.left_inv hy]

/- English proof (translation)
Introduce `h0`. Apply `loc_ne_zero hE hi` to reduce the goal to its premises. Establish `h1` using `congrArg (WithLp.toLp 2) h0`. Rewrite `h1` using `[toLp_sheet c i hy]`. Apply `euc_injective h` to reduce the goal to its premises.

Rewrite using `[h1]`. Simplify using `[euc]`.
-/
theorem sheet_ne_zero (hE : Emb p s) (c : AlgChart p σ e) {i : B.ι} {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hi : y ∈ ptsIn p σ (B.U i)) : sheet s h c i (c.e y).ofLp ≠ 0 := by
  intro h0
  apply loc_ne_zero hE hi
  have h1 := congrArg (WithLp.toLp 2) h0
  rw [toLp_sheet c i hy] at h1
  apply euc_injective h
  rw [h1]
  simp [euc]

/- English proof (translation)
Establish `hO` using `c.e.isOpen_inter_preimage_symm (isOpen_ptsIn (B.U i))`. Establish `hmem : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i)`. Use `⟨c.e.map_source hy, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.mem_preimage, c.e.left_inv hy]`. Conclude with `hi`.

Rewrite using `[c.chernDens_eq hφ hy hi]`. Unfold `AlgChart.hess`. Apply `dens_eq` to reduce the goal to its premises. Establish `hmem' : (c.e y).ofLp ∈ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i))`. Rewrite using `[Set.mem_preimage, WithLp.toLp_ofLp]`.

Conclude with `hmem`. Use `filter_upwards [(isOpen_dom c i).mem_nhds hmem'] with x hx`. Conclude with `(differentiableOn_sheet (s := s) (h := h) c i).differentiableAt ((isOpen_dom c i).mem_nhds hx)`. Conclude with `sheet_ne_zero hE c hy hi`. Use `filter_upwards [hO.mem_nhds hmem] with v hv`.

Rewrite using `[hF i _ hv.2, ← norm_euc h]`. Simplify using `only [sheet, WithLp.toLp_ofLp]`. Both sides reduce to the same expression.
-/
theorem chernDens_eq_fsDens (hE : Emb p s) (hφ : φ.IsCInf) (hF : IsFS φ s h) (c : AlgChart p σ e) {i : B.ι}
    {y : CxPts p σ} (hy : y ∈ c.e.source) (hi : y ∈ ptsIn p σ (B.U i)) :
    c.chernDens φ y = fsDens (sheet s h c i) (c.e y).ofLp := by
  have hO := c.e.isOpen_inter_preimage_symm (isOpen_ptsIn (B.U i))
  have hmem : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i) := by
    refine ⟨c.e.map_source hy, ?_⟩
    rw [Set.mem_preimage, c.e.left_inv hy]
    exact hi
  rw [c.chernDens_eq hφ hy hi]
  unfold AlgChart.hess
  apply dens_eq
  · have hmem' : (c.e y).ofLp ∈ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹'
        (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i)) := by
      rw [Set.mem_preimage, WithLp.toLp_ofLp]
      exact hmem
    filter_upwards [(isOpen_dom c i).mem_nhds hmem'] with x hx
    exact (differentiableOn_sheet (s := s) (h := h) c i).differentiableAt ((isOpen_dom c i).mem_nhds hx)
  · exact sheet_ne_zero hE c hy hi
  · filter_upwards [hO.mem_nhds hmem] with v hv
    rw [hF i _ hv.2, ← norm_euc h]
    simp only [sheet, WithLp.toLp_ofLp]
    rfl

/- English proof (translation)
Establish `hc : ∀ c : AlgChart p σ e, chartMeas c.e (fun y => ENNReal.ofReal (((-1 : ℤˣ) : ℤ) * c.chernDens φ y)) = 0`. Introduce `c`. Unfold `chartMeas`. Establish `h0 : (volume.restrict c.e.target).withDensity ((fun y => ENNReal.ofReal (((-1 : ℤˣ) : ℤ) * c.chernDens φ y)) ∘ c.e.symm) = 0`. Rewrite using `[withDensity_congr_ae (g := 0), withDensity_zero]`.

Use `filter_upwards [ae_restrict_mem c.e.open_target.measurableSet] with v hv`. Establish `hs` using `c.e.map_target hv`. Simplify using `only [Function.comp_apply, Pi.zero_apply]`. Rewrite using `[chernDens_eq_fsDens hE hφ hF c hs (mem_pick hE.isLB _)]`. Apply `ENNReal.ofReal_eq_zero.2` to reduce the goal to its premises.

Use `fsDens_nonneg (sheet s h c (pick hE.isLB (c.e.symm v))) (c.e (c.e.symm v)).ofLp` as an intermediate fact. Simplify using `only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[h0, Measure.map_zero]`. Unfold `Weight.chernPart glueMeas`.

Conclude with `le_antisymm (iSup_le fun c => (hc c).le) (Measure.zero_le _)`.
-/
theorem chernPart_neg (hE : Emb p s) (hφ : φ.IsCInf) (hF : IsFS φ s h) : φ.chernPart e (-1) = 0 := by
  have hc : ∀ c : AlgChart p σ e,
      chartMeas c.e (fun y => ENNReal.ofReal (((-1 : ℤˣ) : ℤ) * c.chernDens φ y)) = 0 := by
    intro c
    unfold chartMeas
    have h0 : (volume.restrict c.e.target).withDensity
        ((fun y => ENNReal.ofReal (((-1 : ℤˣ) : ℤ) * c.chernDens φ y)) ∘ c.e.symm) = 0 := by
      rw [withDensity_congr_ae (g := 0), withDensity_zero]
      filter_upwards [ae_restrict_mem c.e.open_target.measurableSet] with v hv
      have hs := c.e.map_target hv
      simp only [Function.comp_apply, Pi.zero_apply]
      rw [chernDens_eq_fsDens hE hφ hF c hs (mem_pick hE.isLB _)]
      apply ENNReal.ofReal_eq_zero.2
      have := fsDens_nonneg (sheet s h c (pick hE.isLB (c.e.symm v))) (c.e (c.e.symm v)).ofLp
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
      linarith
    rw [h0, Measure.map_zero]
  unfold Weight.chernPart glueMeas
  exact le_antisymm (iSup_le fun c => (hc c).le) (Measure.zero_le _)

/- English proof (translation)
Establish `hs : MeasurableSet (ptsIn p σ U)` using `(isOpen_ptsIn U).measurableSet`. Establish `he : ev p σ U f = (ptsIn p σ U).piecewise (ev p σ U f) 0`. Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : y ∈ ptsIn p σ U`. Simplify using `[Set.piecewise, hy]`.

Simplify using `[Set.piecewise, hy, ev_of_notMem hy]`. Rewrite using `[he]`. Conclude with `(continuousOn_ev f).measurable_piecewise continuousOn_const hs`.
-/
theorem measurable_ev (U : Z.Opens) (f : Γ(Z, U)) : Measurable (ev p σ U f) := by
  classical
  have hs : MeasurableSet (ptsIn p σ U) := (isOpen_ptsIn U).measurableSet
  have he : ev p σ U f = (ptsIn p σ U).piecewise (ev p σ U f) 0 := by
    funext y
    by_cases hy : y ∈ ptsIn p σ U
    · simp [Set.piecewise, hy]
    · simp [Set.piecewise, hy, ev_of_notMem hy]
  rw [he]
  exact (continuousOn_ev f).measurable_piecewise continuousOn_const hs

variable [SecondCountableTopology (CxPts p σ)]

/- English proof (translation)
Take `⟨T, hT, hTU⟩` from `TopologicalSpace.isOpen_iUnion_countable (fun i : B.ι => ptsIn p σ (B.U i)) (fun i => isOpen_ptsIn _)`. Establish `hcov : ∀ y : CxPts p σ, ∃ i ∈ T, y ∈ ptsIn p σ (B.U i)`. Introduce `y`. Establish `hy : y ∈ ⋃ i ∈ T, ptsIn p σ (B.U i)`. Rewrite using `[hTU]`.

Conclude with `mem_iUnion.2 ⟨_, mem_pick hB y⟩`. Simplify using `using hy`. Establish `hloc : ∀ i, Measurable fun y => F (euc h (loc p s σ i y))`. Introduce `i`. Use `hm.comp ((continuous_euc h).measurable.comp ?_)` and prove the remaining obligations.

Conclude with `measurable_pi_lambda _ fun k => measurable_ev (B.U i) ((s k).f i)`. Establish `heq : ∀ i, ∀ y ∈ ptsIn p σ (B.U i), F (euc h (coords p σ hB s y)) = F (euc h (loc p s σ i y))`. Introduce `i y hy`. Take `⟨c, hc, hcl⟩` from `loc_eq_smul (s := s) (mem_pick hB y) hy`. Establish `hco : coords p σ hB s y = loc p s σ (pick hB y) y` using `rfl`.

Rewrite using `[hco, hcl, euc_smul, hF c hc]`. Introduce `t ht`. Establish `hpre : (fun y => F (euc h (coords p σ hB s y))) ⁻¹' t = ⋃ i ∈ T, ptsIn p σ (B.U i) ∩ (fun y => F (euc h (loc p s σ i y))) ⁻¹' t`. Use extensionality with `y`. Simplify using `only [mem_preimage, mem_iUnion, mem_inter_iff, exists_prop]`.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Take `⟨i, hi, hyi⟩` from `hcov y`. Conclude with `⟨i, hi, hyi, by rw [← heq i y hyi]; exact hy⟩`. Introduce and unpack `⟨i, hi, hyi, hy⟩`.

Rewrite using `[heq i y hyi]`. Conclude with `hy`. Rewrite using `[hpre]`. Conclude with `MeasurableSet.biUnion hT fun i _ => (isOpen_ptsIn _).measurableSet.inter (hloc i ht)`.
-/
theorem measurable_coords {β : Type} [MeasurableSpace β] (hB : B.IsLB) {F : EuclideanSpace ℂ (Fin m) → β}
    (hm : Measurable F) (hF : ∀ t : ℂ, t ≠ 0 → ∀ x, F (t • x) = F x) :
    Measurable fun y => F (euc h (coords p σ hB s y)) := by
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i : B.ι => ptsIn p σ (B.U i)) (fun i => isOpen_ptsIn _)
  have hcov : ∀ y : CxPts p σ, ∃ i ∈ T, y ∈ ptsIn p σ (B.U i) := by
    intro y
    have hy : y ∈ ⋃ i ∈ T, ptsIn p σ (B.U i) := by
      rw [hTU]
      exact mem_iUnion.2 ⟨_, mem_pick hB y⟩
    simpa using hy
  have hloc : ∀ i, Measurable fun y => F (euc h (loc p s σ i y)) := by
    intro i
    refine hm.comp ((continuous_euc h).measurable.comp ?_)
    exact measurable_pi_lambda _ fun k => measurable_ev (B.U i) ((s k).f i)
  have heq : ∀ i, ∀ y ∈ ptsIn p σ (B.U i),
      F (euc h (coords p σ hB s y)) = F (euc h (loc p s σ i y)) := by
    intro i y hy
    obtain ⟨c, hc, hcl⟩ := loc_eq_smul (s := s) (mem_pick hB y) hy
    have hco : coords p σ hB s y = loc p s σ (pick hB y) y := rfl
    rw [hco, hcl, euc_smul, hF c hc]
  intro t ht
  have hpre : (fun y => F (euc h (coords p σ hB s y))) ⁻¹' t =
      ⋃ i ∈ T, ptsIn p σ (B.U i) ∩ (fun y => F (euc h (loc p s σ i y))) ⁻¹' t := by
    ext y
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · intro hy
      obtain ⟨i, hi, hyi⟩ := hcov y
      exact ⟨i, hi, hyi, by rw [← heq i y hyi]; exact hy⟩
    · rintro ⟨i, hi, hyi, hy⟩
      rw [heq i y hyi]
      exact hy
  rw [hpre]
  exact MeasurableSet.biUnion hT fun i _ => (isOpen_ptsIn _).measurableSet.inter (hloc i ht)

/- English proof (translation)
Establish `h1 : AEMeasurable v (volume.restrict D)` using `hv.aemeasurable hD`. Establish `h2 : Measurable fun x => fun j : Fin e => fderiv ℂ v x (Pi.single j 1)` using `measurable_pi_lambda _ fun j => measurable_fderiv_apply_const ℂ v _`. Establish `hpair : AEMeasurable (fun x => (v x, fun j : Fin e => fderiv ℂ v x (Pi.single j 1))) (volume.restrict D)` using `h1.prodMk h2.aemeasurable`. Establish `hcons : Continuous fun q : (Fin n → ℂ) × (Fin e → Fin n → ℂ) => (Fin.cons q.1 q.2 : Fin (e + 1) → Fin n → ℂ)` using `Continuous.finCons (A := fun _ => Fin n → ℂ) continuous_fst continuous_snd`. Establish `hw : ∀ a : Fin (e + 1), Continuous fun q : (Fin n → ℂ) × (Fin e → Fin n → ℂ) => (Fin.cons q.1 q.2 : Fin (e + 1) → Fin n → ℂ) a` using `fun a => (continuous_apply a).comp hcons`.

Establish `hM : Continuous fun q : (Fin n → ℂ) × (Fin e → Fin n → ℂ) => (Matrix.of fun a b : Fin (e + 1) => ∑ i : Fin n, star ((Fin.cons q.1 q.2 : Fin (e + 1) → Fin n → ℂ) a i) * (Fin.cons q.1 q.2 : Fin (e + 1) → Fin n → ℂ) b i).det.re`. Use `Complex.continuous_re.comp (Continuous.matrix_det ?_)` and prove the remaining obligations. Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply]`. Conclude with `continuous_finset_sum _ fun i _ => ((continuous_apply i).comp (hw a)).star.mul ((continuous_apply i).comp (hw b))`.

Establish `hψ : Measurable fun q : (Fin n → ℂ) × (Fin e → Fin n → ℂ) => ENNReal.ofReal ((e.factorial : ℝ) / Real.pi ^ e * (Matrix.of fun a b : Fin (e + 1) => ∑ i : Fin n, star ((Fin.cons q.1 q.2 : Fin (e + 1) → Fin n → ℂ) a i) * (Fin.cons q.1 q.2 : Fin (e + 1) → Fin n → ℂ) b i).det.re / ‖Wi …` using `ENNReal.measurable_ofReal.comp ((measurable_const.mul hM.measurable).div (((continuous_norm.comp ((PiLp.continuous_toLp 2 _).comp continuous_fst)).pow _).measurable))`. Use `(hψ.comp_aemeasurable hpair).congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply, fsDens, GroundTheory.Heights₂.Heights.gramVol]`.
-/
private theorem aemeasurable_ofReal_fsDens {e n : ℕ} {v : (Fin e → ℂ) → Fin n → ℂ} {D : Set (Fin e → ℂ)}
    (hv : ContinuousOn v D) (hD : MeasurableSet D) :
    AEMeasurable (fun x => ENNReal.ofReal (fsDens v x)) (volume.restrict D) := by
  have h1 : AEMeasurable v (volume.restrict D) := hv.aemeasurable hD
  have h2 : Measurable fun x => fun j : Fin e => fderiv ℂ v x (Pi.single j 1) :=
    measurable_pi_lambda _ fun j => measurable_fderiv_apply_const ℂ v _
  have hpair : AEMeasurable (fun x => (v x, fun j : Fin e => fderiv ℂ v x (Pi.single j 1)))
      (volume.restrict D) := h1.prodMk h2.aemeasurable
  have hcons : Continuous fun q : (Fin n → ℂ) × (Fin e → Fin n → ℂ) =>
      (Fin.cons q.1 q.2 : Fin (e + 1) → Fin n → ℂ) :=
    Continuous.finCons (A := fun _ => Fin n → ℂ) continuous_fst continuous_snd
  have hw : ∀ a : Fin (e + 1), Continuous fun q : (Fin n → ℂ) × (Fin e → Fin n → ℂ) =>
      (Fin.cons q.1 q.2 : Fin (e + 1) → Fin n → ℂ) a := fun a =>
    (continuous_apply a).comp hcons
  have hM : Continuous fun q : (Fin n → ℂ) × (Fin e → Fin n → ℂ) =>
      (Matrix.of fun a b : Fin (e + 1) => ∑ i : Fin n,
        star ((Fin.cons q.1 q.2 : Fin (e + 1) → Fin n → ℂ) a i) *
          (Fin.cons q.1 q.2 : Fin (e + 1) → Fin n → ℂ) b i).det.re := by
    refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.of_apply]
    exact continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp (hw a)).star.mul ((continuous_apply i).comp (hw b))
  have hψ : Measurable fun q : (Fin n → ℂ) × (Fin e → Fin n → ℂ) =>
      ENNReal.ofReal ((e.factorial : ℝ) / Real.pi ^ e *
        (Matrix.of fun a b : Fin (e + 1) => ∑ i : Fin n,
          star ((Fin.cons q.1 q.2 : Fin (e + 1) → Fin n → ℂ) a i) *
            (Fin.cons q.1 q.2 : Fin (e + 1) → Fin n → ℂ) b i).det.re /
        ‖WithLp.toLp 2 q.1‖ ^ (2 * (e + 1))) :=
    ENNReal.measurable_ofReal.comp ((measurable_const.mul hM.measurable).div
      (((continuous_norm.comp ((PiLp.continuous_toLp 2 _).comp continuous_fst)).pow _).measurable))
  refine (hψ.comp_aemeasurable hpair).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, fsDens, GroundTheory.Heights₂.Heights.gramVol]

/- English proof (translation)
Use `set ρ : AlgChart p σ e → CxPts p σ → ℝ≥0∞ := fun c' y => ENNReal.ofReal (((((1 : ℤˣ) : ℤ) : ℝ)) * c'.chernDens φ y) with hρ`. Establish `hglue : ∀ S, MeasurableSet S → S ⊆ c.e.source → φ.chernPart e 1 S = chartMeas c.e (ρ c) S`. Introduce `S hS hSs`. Use `glueMeas_apply (fun c' : AlgChart p σ e => c'.e) ρ (fun a b => a.holo_trans b) ?_ c hS hSs` and prove the remaining obligations. Introduce `a b y ha hb`.

Simplify using `only [hρ, Units.val_one, Int.cast_one, one_mul]`. Rewrite using `[a.chernDens_trans b hφ ha hb, ENNReal.ofReal_mul (sq_nonneg _)]`. Use `set D := (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' (c.e '' A) with hDdef`. Use `set g : (Fin e → ℂ) → CxPts p σ := fun x => c.e.symm (WithLp.toLp 2 x) with hgdef`. Use `set dens : (Fin e → ℂ) → ℝ≥0∞ := fun x => ENNReal.ofReal (fsDens (sheet s h c i) x) with hdensdef`.

Establish `hAi : MeasurableSet (c.e '' A)` using `measurableSet_image c.e hA hAc`. Establish `hD : MeasurableSet D` using `hAi.preimage (PiLp.continuous_toLp 2 _).measurable`. Establish `hpt : ∀ x ∈ D, ∃ a ∈ A, c.e a = WithLp.toLp 2 x ∧ g x = a`. Introduce `x hx`. Take `⟨a, ha, hax⟩` from `hx`.

Conclude with `⟨a, ha, hax, by simp only [hgdef]; rw [← hax, c.e.left_inv (hAc ha)]⟩`. Establish `hDT : D ⊆ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i))`. Introduce `x hx`. Take `⟨a, ha, hax, hga⟩` from `hpt x hx`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hax]`. Conclude with `c.e.map_source (hAc ha)`. Use `show g x ∈ ptsIn p σ (B.U i)`. Rewrite using `[hga]`. Conclude with `hc (hAc ha)`.

Establish `hgc : ContinuousOn g D` using `c.e.continuousOn_symm.comp (PiLp.continuous_toLp 2 _).continuousOn (fun x hx => (hDT hx).1)`. Establish `hg : AEMeasurable g ((volume.restrict D).withDensity dens)` using `(hgc.aemeasurable hD).mono_ac (withDensity_absolutelyContinuous _ _)`. Establish `hdens : AEMeasurable dens (volume.restrict D)` using `aemeasurable_ofReal_fsDens ((differentiableOn_sheet (s := s) (h := h) c i).continuousOn.mono hDT) hD`. Establish `hval : ∀ x ∈ D, ρ c (c.e.symm (WithLp.toLp 2 x)) = dens x`. Introduce `x hx`.

Take `⟨a, ha, hax, hga⟩` from `hpt x hx`. Establish `hga' : c.e.symm (WithLp.toLp 2 x) = a` using `hga`. Simplify using `only [hρ, hdensdef, Units.val_one, Int.cast_one, one_mul]`. Rewrite using `[hga', chernDens_eq_fsDens hE hφ hF c (hAc ha) (hc (hAc ha)), hax, WithLp.ofLp_toLp]`. Establish `hmeas : (φ.chernPart e 1).restrict A = Measure.map g ((volume.restrict D).withDensity dens)`.

Use extensionality with `S hS`. Rewrite using `[Measure.restrict_apply hS, Measure.map_apply_of_aemeasurable hg hS, withDensity_apply', Measure.restrict_restrict' hD]`. Establish `hSA : S ∩ A ⊆ c.e.source` using `inter_subset_right.trans hAc`. Establish `hset : g ⁻¹' S ∩ D = (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' (c.e '' (S ∩ A))`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxS, hxD⟩`. Take `⟨a, ha, hax, hga⟩` from `hpt x hxD`. Use `⟨a, ⟨?_, ha⟩, hax⟩` and prove the remaining obligations. Rewrite using `[← hga]`.

Conclude with `hxS`. Introduce and unpack `⟨a, ⟨haS, ha⟩, hax⟩`. Establish `hxD : x ∈ D` using `⟨a, ha, hax⟩`. Take `⟨a', ha', hax', hga'⟩` from `hpt x hxD`. Use `⟨?_, hxD⟩` and prove the remaining obligations.

Use `show g x ∈ S`. Establish `: a' = a` using `c.e.injOn (hAc ha') (hAc ha) (hax'.trans hax.symm)`. Rewrite using `[hga', this]`. Conclude with `haS`. Rewrite using `[hset, hglue (S ∩ A) (hS.inter hA) hSA, chartMeas_apply_of_subset _ _ (hS.inter hA) hSA, ← (GroundTheory.Heights₂.Heights.ConeMapAreaFormula.measurePreserving_toLp e).setLIntegral_comp_preimage_emb (MeasurableEquiv.toLp 2 (Fin e → ℂ)).measurableEmbedding]`.

Use `setLIntegral_congr_fun ((measurableSet_image c.e (hS.inter hA) hSA).preimage (PiLp.continuous_toLp 2 _).measurable) fun x hx => ?_` and prove the remaining obligations. Establish `hxD : x ∈ D`. Take `⟨a, ⟨_, ha⟩, hax⟩` from `hx`. Conclude with `⟨a, ha, hax⟩`. Conclude with `hval x hxD`.

Rewrite using `[hmeas, lintegral_map' hΦ.aemeasurable hg]`. Establish `hmul` using `lintegral_withDensity_eq_lintegral_mul₀ hdens (hΦ.comp_aemeasurable (hgc.aemeasurable hD))`. Conclude with `hmul.trans (lintegral_congr fun x => mul_comm _ _)`.
-/
theorem lintegral_chart (hE : Emb p s) (hφ : φ.IsCInf) (hF : IsFS φ s h) (c : AlgChart p σ e) {i : B.ι}
    (hc : c.e.source ⊆ ptsIn p σ (B.U i)) {A : Set (CxPts p σ)} (hA : MeasurableSet A) (hAc : A ⊆ c.e.source)
    {Φ : CxPts p σ → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ y in A, Φ y ∂φ.chernPart e 1 = ∫⁻ x in (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' (c.e '' A),
      Φ (c.e.symm (WithLp.toLp 2 x)) * ENNReal.ofReal (fsDens (sheet s h c i) x) := by
  set ρ : AlgChart p σ e → CxPts p σ → ℝ≥0∞ :=
    fun c' y => ENNReal.ofReal (((((1 : ℤˣ) : ℤ) : ℝ)) * c'.chernDens φ y) with hρ
  have hglue : ∀ S, MeasurableSet S → S ⊆ c.e.source → φ.chernPart e 1 S = chartMeas c.e (ρ c) S := by
    intro S hS hSs
    refine glueMeas_apply (fun c' : AlgChart p σ e => c'.e) ρ (fun a b => a.holo_trans b) ?_ c hS hSs
    intro a b y ha hb
    simp only [hρ, Units.val_one, Int.cast_one, one_mul]
    rw [a.chernDens_trans b hφ ha hb, ENNReal.ofReal_mul (sq_nonneg _)]
  set D := (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' (c.e '' A) with hDdef
  set g : (Fin e → ℂ) → CxPts p σ := fun x => c.e.symm (WithLp.toLp 2 x) with hgdef
  set dens : (Fin e → ℂ) → ℝ≥0∞ := fun x => ENNReal.ofReal (fsDens (sheet s h c i) x) with hdensdef
  have hAi : MeasurableSet (c.e '' A) := measurableSet_image c.e hA hAc
  have hD : MeasurableSet D := hAi.preimage (PiLp.continuous_toLp 2 _).measurable
  have hpt : ∀ x ∈ D, ∃ a ∈ A, c.e a = WithLp.toLp 2 x ∧ g x = a := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hx
    exact ⟨a, ha, hax, by simp only [hgdef]; rw [← hax, c.e.left_inv (hAc ha)]⟩
  have hDT : D ⊆ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹'
      (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i)) := by
    intro x hx
    obtain ⟨a, ha, hax, hga⟩ := hpt x hx
    refine ⟨?_, ?_⟩
    · rw [← hax]
      exact c.e.map_source (hAc ha)
    · show g x ∈ ptsIn p σ (B.U i)
      rw [hga]
      exact hc (hAc ha)
  have hgc : ContinuousOn g D :=
    c.e.continuousOn_symm.comp (PiLp.continuous_toLp 2 _).continuousOn (fun x hx => (hDT hx).1)
  have hg : AEMeasurable g ((volume.restrict D).withDensity dens) :=
    (hgc.aemeasurable hD).mono_ac (withDensity_absolutelyContinuous _ _)
  have hdens : AEMeasurable dens (volume.restrict D) :=
    aemeasurable_ofReal_fsDens ((differentiableOn_sheet (s := s) (h := h) c i).continuousOn.mono hDT) hD
  have hval : ∀ x ∈ D, ρ c (c.e.symm (WithLp.toLp 2 x)) = dens x := by
    intro x hx
    obtain ⟨a, ha, hax, hga⟩ := hpt x hx
    have hga' : c.e.symm (WithLp.toLp 2 x) = a := hga
    simp only [hρ, hdensdef, Units.val_one, Int.cast_one, one_mul]
    rw [hga', chernDens_eq_fsDens hE hφ hF c (hAc ha) (hc (hAc ha)), hax, WithLp.ofLp_toLp]
  have hmeas : (φ.chernPart e 1).restrict A = Measure.map g ((volume.restrict D).withDensity dens) := by
    ext S hS
    rw [Measure.restrict_apply hS, Measure.map_apply_of_aemeasurable hg hS, withDensity_apply',
      Measure.restrict_restrict' hD]
    have hSA : S ∩ A ⊆ c.e.source := inter_subset_right.trans hAc
    have hset : g ⁻¹' S ∩ D = (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' (c.e '' (S ∩ A)) := by
      ext x
      constructor
      · rintro ⟨hxS, hxD⟩
        obtain ⟨a, ha, hax, hga⟩ := hpt x hxD
        refine ⟨a, ⟨?_, ha⟩, hax⟩
        rw [← hga]
        exact hxS
      · rintro ⟨a, ⟨haS, ha⟩, hax⟩
        have hxD : x ∈ D := ⟨a, ha, hax⟩
        obtain ⟨a', ha', hax', hga'⟩ := hpt x hxD
        refine ⟨?_, hxD⟩
        show g x ∈ S
        have : a' = a := c.e.injOn (hAc ha') (hAc ha) (hax'.trans hax.symm)
        rw [hga', this]
        exact haS
    rw [hset, hglue (S ∩ A) (hS.inter hA) hSA, chartMeas_apply_of_subset _ _ (hS.inter hA) hSA,
      ← (GroundTheory.Heights₂.Heights.ConeMapAreaFormula.measurePreserving_toLp e).setLIntegral_comp_preimage_emb
        (MeasurableEquiv.toLp 2 (Fin e → ℂ)).measurableEmbedding]
    refine setLIntegral_congr_fun ((measurableSet_image c.e (hS.inter hA) hSA).preimage
      (PiLp.continuous_toLp 2 _).measurable) fun x hx => ?_
    have hxD : x ∈ D := by
      obtain ⟨a, ⟨_, ha⟩, hax⟩ := hx
      exact ⟨a, ha, hax⟩
    exact hval x hxD
  rw [hmeas, lintegral_map' hΦ.aemeasurable hg]
  have hmul := lintegral_withDensity_eq_lintegral_mul₀ hdens (hΦ.comp_aemeasurable (hgc.aemeasurable hD))
  exact hmul.trans (lintegral_congr fun x => mul_comm _ _)

/- English proof (translation)
Set `S : AlgChart p σ e × B.ι → Set (CxPts p σ)` to `fun q => (q.1.restr (ptsIn p σ (B.U q.2)) (isOpen_ptsIn _)).e.source`. Establish `hSo : ∀ q, IsOpen (S q)` using `fun q => (q.1.restr (ptsIn p σ (B.U q.2)) (isOpen_ptsIn _)).e.open_source`. Take `⟨T, hT, hTU⟩` from `TopologicalSpace.isOpen_iUnion_countable S hSo`. Establish `hmemT : ∀ c' : AlgChart p σ e, ∀ y ∈ c'.e.source, ∃ q ∈ T, y ∈ S q`. Introduce `c' y hy`.

Establish `hyS : y ∈ S (c', pick hB y)` using `by show y ∈ (c'.restr (ptsIn p σ (B.U (pick hB y))) (isOpen_ptsIn _)).e.source`. Rewrite using `[AlgChart.restr_source]`. Conclude with `⟨hy, mem_pick hB y⟩`. Establish `hy' : y ∈ ⋃ q ∈ T, S q`. Rewrite using `[hTU]`.

Conclude with `mem_iUnion.2 ⟨_, hyS⟩`. Simplify using `using hy'`. Break down `T.eq_empty_or_nonempty with hTe | hTn` into its components or cases. Use `⟨Empty, inferInstance, fun a => a.elim, fun a => a.elim, fun a => a.elim, fun a => a.elim, fun a => a.elim, fun a => a.elim, fun a => a.elim, ?_⟩` and prove the remaining obligations. Introduce `c' y hy`.

Take `⟨q, hq, _⟩` from `hmemT c' y hy`. Rewrite `hq` using `[hTe]`. Conclude with `hq.elim`. Take `⟨f, hf⟩` from `hT.exists_eq_range hTn`. Set `c : ℕ → AlgChart p σ e` to `fun n => (f n).1.restr (ptsIn p σ (B.U (f n).2)) (isOpen_ptsIn _)`.

Use `⟨ℕ, inferInstance, c, fun n => (f n).2, disjointed fun n => (c n).e.source, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `n show (c n).e.source ⊆ _`. Simplify using `only [c]`. Rewrite using `[AlgChart.restr_source]`. Conclude with `inter_subset_right`.

Conclude with `MeasurableSet.disjointed fun n => (c n).e.open_source.measurableSet`. Conclude with `fun n => disjointed_subset _ n`. Conclude with `disjoint_disjointed _`. Introduce `c' y hy`. Rewrite using `[iUnion_disjointed]`.

Take `⟨q, hq, hyq⟩` from `hmemT c' y hy`. Rewrite `hq` using `[hf]`. Take `⟨n, rfl⟩` from `hq`. Conclude with `mem_iUnion.2 ⟨n, hyq⟩`.
-/
theorem exists_parts (hB : B.IsLB) : ∃ (ι : Type) (_ : Countable ι) (c : ι → AlgChart p σ e) (i : ι → B.ι)
    (A : ι → Set (CxPts p σ)), (∀ a, (c a).e.source ⊆ ptsIn p σ (B.U (i a))) ∧ (∀ a, MeasurableSet (A a)) ∧
      (∀ a, A a ⊆ (c a).e.source) ∧ Pairwise (Function.onFun Disjoint A) ∧
      ∀ c' : AlgChart p σ e, c'.e.source ⊆ ⋃ a, A a := by
  classical
  let S : AlgChart p σ e × B.ι → Set (CxPts p σ) := fun q =>
    (q.1.restr (ptsIn p σ (B.U q.2)) (isOpen_ptsIn _)).e.source
  have hSo : ∀ q, IsOpen (S q) := fun q => (q.1.restr (ptsIn p σ (B.U q.2)) (isOpen_ptsIn _)).e.open_source
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable S hSo
  have hmemT : ∀ c' : AlgChart p σ e, ∀ y ∈ c'.e.source, ∃ q ∈ T, y ∈ S q := by
    intro c' y hy
    have hyS : y ∈ S (c', pick hB y) := by
      show y ∈ (c'.restr (ptsIn p σ (B.U (pick hB y))) (isOpen_ptsIn _)).e.source
      rw [AlgChart.restr_source]
      exact ⟨hy, mem_pick hB y⟩
    have hy' : y ∈ ⋃ q ∈ T, S q := by
      rw [hTU]
      exact mem_iUnion.2 ⟨_, hyS⟩
    simpa using hy'
  rcases T.eq_empty_or_nonempty with hTe | hTn
  · refine ⟨Empty, inferInstance, fun a => a.elim, fun a => a.elim, fun a => a.elim,
      fun a => a.elim, fun a => a.elim, fun a => a.elim, fun a => a.elim, ?_⟩
    intro c' y hy
    obtain ⟨q, hq, _⟩ := hmemT c' y hy
    rw [hTe] at hq
    exact hq.elim
  · obtain ⟨f, hf⟩ := hT.exists_eq_range hTn
    let c : ℕ → AlgChart p σ e := fun n =>
      (f n).1.restr (ptsIn p σ (B.U (f n).2)) (isOpen_ptsIn _)
    refine ⟨ℕ, inferInstance, c, fun n => (f n).2, disjointed fun n => (c n).e.source, ?_, ?_, ?_, ?_, ?_⟩
    · intro n
      show (c n).e.source ⊆ _
      simp only [c]
      rw [AlgChart.restr_source]
      exact inter_subset_right
    · exact MeasurableSet.disjointed fun n => (c n).e.open_source.measurableSet
    · exact fun n => disjointed_subset _ n
    · exact disjoint_disjointed _
    · intro c' y hy
      rw [iUnion_disjointed]
      obtain ⟨q, hq, hyq⟩ := hmemT c' y hy
      rw [hf] at hq
      obtain ⟨n, rfl⟩ := hq
      exact mem_iUnion.2 ⟨n, hyq⟩

/- English proof (translation)
Take `⟨ι, hι, c, ia, A, hsub, hAm, hAs, hdisj, hcov⟩` from `exists_parts (p := p) (σ := σ) (e := e) hE.isLB`. Use `haveI := hι`. Establish `hpt_smul : ∀ (t : ℂ) (w : EuclideanSpace ℂ (Fin m)), h.pointOf (t • w) = t • h.pointOf w`. Introduce `t w`. Use `conv_lhs => rw [← euc_pointOf h w]`.

Rewrite using `[← euc_smul, pointOf_euc]`. Establish `hFco : ∀ j y, y ∈ ptsIn p σ (B.U j) → F (euc h (coords p σ hE.isLB s y)) = F (euc h (loc p s σ j y))`. Introduce `j y hy`. Take `⟨k, hk, hkl⟩` from `loc_eq_smul (s := s) (mem_pick hE.isLB y) hy`. Establish `hco : coords p σ hE.isLB s y = loc p s σ (pick hE.isLB y) y` using `rfl`.

Rewrite using `[hco, hkl, euc_smul, h0 k hk]`. Establish `hvx : ∀ a, ∀ y ∈ A a, WithLp.toLp 2 (sheet s h (c a) (ia a) ((c a).e y).ofLp) = euc h (loc p s σ (ia a) y)` using `fun a y hy => toLp_sheet (c a) (ia a) (hAs a hy)`. Establish `hx_of : ∀ a (x : Fin e → ℂ) y, (c a).e y = WithLp.toLp 2 x → x = ((c a).e y).ofLp`. Introduce `a x y hyx`. Rewrite using `[hyx, WithLp.ofLp_toLp]`.

Establish `hcond : ∀ a, IsOpen ((WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e.target ∩ (c a).e.symm ⁻¹' ptsIn p σ (B.U (ia a)))) ∧ MeasurableSet ((WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e '' A a)) ∧ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e '' A a) ⊆ (WithLp.toLp 2 : (Fin e …`. Introduce `a`. Use `⟨isOpen_dom (c a) (ia a), (measurableSet_image (c a).e (hAm a) (hAs a)).preimage (PiLp.continuous_toLp 2 _).measurable, ?_, differentiableOn_sheet (c a) (ia a)⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨y, hy, hyx⟩` from `hx`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hyx]`. Conclude with `(c a).e.map_source (hAs a hy)`. Rewrite using `[← hyx, Set.mem_preimage, (c a).e.left_inv (hAs a hy)]`. Conclude with `hsub a (hAs a hy)`.

Establish `hne : ∀ a, ∀ x ∈ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e '' A a), sheet s h (c a) (ia a) x ≠ 0`. Introduce `a x hx`. Take `⟨y, hy, hyx⟩` from `hx`. Rewrite using `[hx_of a x y hyx]`. Conclude with `sheet_ne_zero hE (c a) (hAs a hy) (hsub a (hAs a hy))`.

Establish `hinj : InjOn (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (sheet s h (c q.1) (ia q.1) q.2.1)) {q | q.2.1 ∈ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c q.1).e '' A q.1) ∧ q.2.2 ≠ 0}`. Introduce and unpack `⟨a, x, t⟩ ⟨hx, ht⟩ ⟨a', x', t'⟩ ⟨hx', ht'⟩ heq`. Simplify using `only at heq hx hx' ht ht'`. Take `⟨y, hy, hyx⟩` from `hx`. Take `⟨y', hy', hyx'⟩` from `hx'`.

Rewrite `heq` using `[hx_of a x y hyx, hvx a y hy, hx_of a' x' y' hyx', hvx a' y' hy']`. Establish `h2` using `congrArg h.pointOf heq`. Rewrite `h2` using `[hpt_smul, hpt_smul, pointOf_euc, pointOf_euc]`. Establish `hyy : y = y'` using `eq_of_loc hE (hsub a (hAs a hy)) (hsub a' (hAs a' hy')) ht ht' h2`. Substitute `hyy` using the available equality.

Establish `haa : a = a'`. Assume the negation of the conclusion as `hna`. Conclude with `Set.disjoint_left.1 (hdisj hna) hy hy'`. Substitute `haa` using the available equality. Establish `hxx : x = x'` using `(hx_of a x y hyx).trans (hx_of a x' y hyx').symm`.

Substitute `hxx` using the available equality. Establish `hw : euc h (loc p s σ (ia a) y) ≠ 0`. Introduce `hz`. Apply `loc_ne_zero hE (hsub a (hAs a hy))` to reduce the goal to its premises. Apply `euc_injective h` to reduce the goal to its premises.

Rewrite using `[hz]`. Simplify using `[euc]`. Establish `htt : t = t'` using `smul_left_injective ℂ hw heq`. Substitute `htt` using the available equality. Both sides reduce to the same expression.

Establish `hFm : Measurable fun y => F (euc h (coords p σ hE.isLB s y))` using `measurable_coords hE.isLB hm h0`. Establish `harea` using `area_ball (U := fun a => (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e.target ∩ (c a).e.symm ⁻¹' ptsIn p σ (B.U (ia a)))) (D := fun a => (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e '' A a)) (v := fun a => sheet s h (c a) (ia a)) hcond hinj hne hm h0`. Establish `hsub1 : Metric.ball 0 1 ∩ (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (sheet s h (c q.1) (ia q.1) q.2.1)) '' {q | q.2.1 ∈ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c q.1).e '' A q.1) ∧ q.2.2 ≠ 0} ⊆ coneBall h J`. Introduce and unpack `z ⟨hz1, ⟨⟨a, x, t⟩, ⟨hx, ht⟩, rfl⟩⟩`. Take `⟨y, hy, hyx⟩` from `hx`.

Establish `hz : t • WithLp.toLp 2 (sheet s h (c a) (ia a) x) = t • euc h (loc p s σ (ia a) y)`. Rewrite using `[hx_of a x y hyx, hvx a y hy]`. Use `⟨mem_ball_zero_iff.1 hz1, ?_⟩` and prove the remaining obligations. Introduce `r hr`. Use `show MvPolynomial.eval (h.pointOf (t • WithLp.toLp 2 (sheet s h (c a) (ia a) x))) r = 0`.

Rewrite using `[hz, hpt_smul, pointOf_euc]`. Conclude with `(hJ _).2 (fun q' hq' => eval₂_loc_eq_zero (hsub a (hAs a hy)) hq' t) r hr`. Establish `hsub2 : coneBall h J \ (Metric.ball 0 1 ∩ (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (sheet s h (c q.1) (ia q.1) q.2.1)) '' {q | q.2.1 ∈ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c q.1).e '' A q.1) ∧ q.2.2 ≠ 0}) ⊆ {0} ∪ coneBall h J ∩ {y | eval₂ σ (h.pointOf y) q = 0}`. Introduce and unpack `z ⟨hzc, hzn⟩`. Assume the negation of the conclusion as `hcon`.

Establish `hz0 : z ≠ 0` using `fun hz => hcon (Or.inl hz)`. Establish `hq0 : eval₂ σ (h.pointOf z) q ≠ 0` using `fun hz => hcon (Or.inr ⟨hzc, hz⟩)`. Apply `hzn` to reduce the goal to its premises. Use `⟨mem_ball_zero_iff.2 hzc.1, ?_⟩` and prove the remaining obligations. Establish `hx'0 : h.pointOf z ≠ 0`.

Introduce `hz`. Apply `hz0` to reduce the goal to its premises. Rewrite using `[← euc_pointOf h z, hz]`. Simplify using `[euc]`. Establish `hx'J : ∀ q' ∈ ptIdeal p s (genericPoint Z), eval₂ σ (h.pointOf z) q' = 0` using `(hJ _).1 hzc.2`.

Take `⟨y, k, hk, hxk⟩` from `exists_loc hE hx'0 hx'J`. Establish `hco : coords p σ hE.isLB s y = loc p s σ (pick hE.isLB y) y` using `rfl`. Establish `hqy : eval₂ σ (coords p σ hE.isLB s y) q ≠ 0`. Introduce `hz`. Apply `hq0` to reduce the goal to its premises.

Rewrite using `[hxk]`. Establish `hfun : (k • loc p s σ (pick hE.isLB y) y) = fun l => k * loc p s σ (pick hE.isLB y) y l` using `rfl`. Rewrite using `[hfun, eval₂_mul_of_isHomogeneous σ k _ hn, ← hco, hz, mul_zero]`. Take `⟨c', hc'⟩` from `hq y hqy`. Take `⟨a, hya⟩` from `mem_iUnion.1 (hcov c' hc')`.

Take `⟨k', hk', hkl⟩` from `loc_eq_smul (s := s) (mem_pick hE.isLB y) (hsub a (hAs a hya))`. Use `⟨(a, ((c a).e y).ofLp, k * k'), ⟨⟨y, hya, (WithLp.toLp_ofLp 2 _).symm⟩, mul_ne_zero hk hk'⟩, ?_⟩` and prove the remaining obligations. Use `show (k * k') • WithLp.toLp 2 (sheet s h (c a) (ia a) ((c a).e y).ofLp) = z`. Rewrite using `[hvx a y hya, mul_smul, ← euc_smul, ← euc_smul, ← hkl, ← hxk, euc_pointOf]`. Establish `hae : coneBall h J =ᵐ[Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)] (Metric.ball 0 1 ∩ (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (sheet s h (c q.1) (ia q.1) q.2.1)) '' {q | q.2.1 ∈ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c q.1).e '' A q.1) ∧ q.2.2 ≠ 0} : Set _)`.

Rewrite using `[ae_eq_set]`. Use `⟨measure_mono_null hsub2 hnull, ?_⟩` and prove the remaining obligations. Rewrite using `[diff_eq_empty.2 hsub1, measure_empty]`. Establish `hpiece : ∀ a, ∫⁻ x in (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e '' A a), F (WithLp.toLp 2 (sheet s h (c a) (ia a) x)) * ENNReal.ofReal (fsDens (sheet s h (c a) (ia a)) x) = ∫⁻ y in A a, F (euc h (coords p σ hE.isLB s y)) ∂φ.chernPart e 1`. Introduce `a`.

Rewrite using `[lintegral_chart hE hφ hF (c a) (hsub a) (hAm a) (hAs a) hFm]`. Use `setLIntegral_congr_fun (hcond a).2.1 fun x hx => ?_` and prove the remaining obligations. Take `⟨y, hy, hyx⟩` from `hx`. Establish `hsy : (c a).e.symm (WithLp.toLp 2 x) = y` using `by rw [← hyx, (c a).e.left_inv (hAs a hy)]`. Simplify using `only`.

Rewrite using `[hsy, hFco (ia a) y (hsub a (hAs a hy)), ← hvx a y hy, ← hx_of a x y hyx]`. Establish `hWm : MeasurableSet (⋃ a, A a)` using `MeasurableSet.iUnion hAm`. Establish `hres : (φ.chernPart e 1).restrict (⋃ a, A a) = φ.chernPart e 1`. Apply `Measure.restrict_eq_self_of_ae_mem` to reduce the goal to its premises. Rewrite using `[ae_iff]`.

Establish `hcm : ∀ c' : AlgChart p σ e, ∀ ρ : CxPts p σ → ℝ≥0∞, chartMeas c'.e ρ ≤ (chartMeas c'.e ρ).restrict (⋃ a, A a)`. Introduce `c' ρ`. Rewrite using `[Measure.restrict_eq_self_of_ae_mem]`. Rewrite using `[ae_iff]`. Use `show chartMeas c'.e ρ (⋃ a, A a)ᶜ = 0`.

Rewrite using `[chartMeas_apply _ _ hWm.compl]`. Establish `hemp : c'.e.source ∩ (⋃ a, A a)ᶜ = ∅`. Use extensionality with `y`. Simplify using `only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and, not_not]`. Conclude with `fun hy => hcov c' hy`.

Rewrite using `[hemp, Set.image_empty, Measure.restrict_empty, lintegral_zero_measure]`. Establish `key : ∀ μs : AlgChart p σ e → Measure (CxPts p σ), (∀ c', μs c' ≤ (μs c').restrict (⋃ a, A a)) → (⨆ c', μs c') (⋃ a, A a)ᶜ = 0`. Introduce `μs hμ`. Establish `hle : (⨆ c', μs c') ≤ (⨆ c', μs c').restrict (⋃ a, A a)` using `iSup_le fun c' => (hμ c').trans (Measure.restrict_mono subset_rfl (le_iSup μs c'))`. Use `le_antisymm ((Measure.le_iff'.1 hle _).trans ?_) (zero_le)` and prove the remaining obligations.

Rewrite using `[Measure.restrict_apply' hWm, compl_inter_self, measure_empty]`. Unfold `Weight.chernPart glueMeas`. Conclude with `key _ fun c' => hcm c' _`. Rewrite using `[setLIntegral_congr hae, harea]`. Use `congr 1`.

Rewrite using `[tsum_congr hpiece, ← lintegral_iUnion hAm hdisj, hres]`.
-/
theorem lintegral_cone [IsIntegral Z] (hE : Emb p s) (hφ : φ.IsCInf) (hF : IsFS φ s h)
    {J : Ideal (MvPolynomial (Fin m) ℂ)}
    (hJ : ∀ x, (∀ r ∈ J, eval x r = 0) ↔ ∀ q ∈ ptIdeal p s (genericPoint Z), eval₂ σ x q = 0)
    {n : ℕ} {q : MvPolynomial (Fin m) R} (hn : q.IsHomogeneous n)
    (hq : ∀ y : CxPts p σ, eval₂ σ (coords p σ hE.isLB s y) q ≠ 0 → ∃ c : AlgChart p σ e, y ∈ c.e.source)
    (hnull : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
      ({0} ∪ coneBall h J ∩ {y | eval₂ σ (h.pointOf y) q = 0}) = 0)
    {F : EuclideanSpace ℂ (Fin m) → ℝ≥0∞} (hm : Measurable F) (h0 : ∀ t : ℂ, t ≠ 0 → ∀ x, F (t • x) = F x) :
    ∫⁻ y in coneBall h J, F y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin m) | ‖y‖ < 1 ∧ ∀ j : Fin m, e + 1 ≤ (j : ℕ) → y j = 0} *
        ∫⁻ y, F (euc h (coords p σ hE.isLB s y)) ∂φ.chernPart e 1 := by
  classical
  obtain ⟨ι, hι, c, ia, A, hsub, hAm, hAs, hdisj, hcov⟩ := exists_parts (p := p) (σ := σ) (e := e) hE.isLB
  haveI := hι
  have hpt_smul : ∀ (t : ℂ) (w : EuclideanSpace ℂ (Fin m)), h.pointOf (t • w) = t • h.pointOf w := by
    intro t w
    conv_lhs => rw [← euc_pointOf h w]
    rw [← euc_smul, pointOf_euc]
  have hFco : ∀ j y, y ∈ ptsIn p σ (B.U j) →
      F (euc h (coords p σ hE.isLB s y)) = F (euc h (loc p s σ j y)) := by
    intro j y hy
    obtain ⟨k, hk, hkl⟩ := loc_eq_smul (s := s) (mem_pick hE.isLB y) hy
    have hco : coords p σ hE.isLB s y = loc p s σ (pick hE.isLB y) y := rfl
    rw [hco, hkl, euc_smul, h0 k hk]
  have hvx : ∀ a, ∀ y ∈ A a, WithLp.toLp 2 (sheet s h (c a) (ia a) ((c a).e y).ofLp) =
      euc h (loc p s σ (ia a) y) := fun a y hy => toLp_sheet (c a) (ia a) (hAs a hy)
  have hx_of : ∀ a (x : Fin e → ℂ) y, (c a).e y = WithLp.toLp 2 x → x = ((c a).e y).ofLp := by
    intro a x y hyx
    rw [hyx, WithLp.ofLp_toLp]
  have hcond : ∀ a, IsOpen ((WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹'
        ((c a).e.target ∩ (c a).e.symm ⁻¹' ptsIn p σ (B.U (ia a)))) ∧
      MeasurableSet ((WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e '' A a)) ∧
      (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e '' A a) ⊆
        (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e.target ∩ (c a).e.symm ⁻¹' ptsIn p σ (B.U (ia a))) ∧
      DifferentiableOn ℂ (sheet s h (c a) (ia a)) ((WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹'
        ((c a).e.target ∩ (c a).e.symm ⁻¹' ptsIn p σ (B.U (ia a)))) := by
    intro a
    refine ⟨isOpen_dom (c a) (ia a), (measurableSet_image (c a).e (hAm a) (hAs a)).preimage
      (PiLp.continuous_toLp 2 _).measurable, ?_, differentiableOn_sheet (c a) (ia a)⟩
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨?_, ?_⟩
    · rw [← hyx]
      exact (c a).e.map_source (hAs a hy)
    · rw [← hyx, Set.mem_preimage, (c a).e.left_inv (hAs a hy)]
      exact hsub a (hAs a hy)
  have hne : ∀ a, ∀ x ∈ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e '' A a),
      sheet s h (c a) (ia a) x ≠ 0 := by
    intro a x hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [hx_of a x y hyx]
    exact sheet_ne_zero hE (c a) (hAs a hy) (hsub a (hAs a hy))
  have hinj : InjOn (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (sheet s h (c q.1) (ia q.1) q.2.1))
      {q | q.2.1 ∈ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c q.1).e '' A q.1) ∧ q.2.2 ≠ 0} := by
    rintro ⟨a, x, t⟩ ⟨hx, ht⟩ ⟨a', x', t'⟩ ⟨hx', ht'⟩ heq
    simp only at heq hx hx' ht ht'
    obtain ⟨y, hy, hyx⟩ := hx
    obtain ⟨y', hy', hyx'⟩ := hx'
    rw [hx_of a x y hyx, hvx a y hy, hx_of a' x' y' hyx', hvx a' y' hy'] at heq
    have h2 := congrArg h.pointOf heq
    rw [hpt_smul, hpt_smul, pointOf_euc, pointOf_euc] at h2
    have hyy : y = y' := eq_of_loc hE (hsub a (hAs a hy)) (hsub a' (hAs a' hy')) ht ht' h2
    subst hyy
    have haa : a = a' := by
      by_contra hna
      exact Set.disjoint_left.1 (hdisj hna) hy hy'
    subst haa
    have hxx : x = x' := (hx_of a x y hyx).trans (hx_of a x' y hyx').symm
    subst hxx
    have hw : euc h (loc p s σ (ia a) y) ≠ 0 := by
      intro hz
      apply loc_ne_zero hE (hsub a (hAs a hy))
      apply euc_injective h
      rw [hz]
      simp [euc]
    have htt : t = t' := smul_left_injective ℂ hw heq
    subst htt
    rfl
  have hFm : Measurable fun y => F (euc h (coords p σ hE.isLB s y)) := measurable_coords hE.isLB hm h0
  have harea := area_ball (U := fun a => (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹'
        ((c a).e.target ∩ (c a).e.symm ⁻¹' ptsIn p σ (B.U (ia a))))
    (D := fun a => (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e '' A a))
    (v := fun a => sheet s h (c a) (ia a)) hcond hinj hne hm h0
  have hsub1 : Metric.ball 0 1 ∩ (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (sheet s h (c q.1) (ia q.1) q.2.1)) ''
      {q | q.2.1 ∈ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c q.1).e '' A q.1) ∧ q.2.2 ≠ 0} ⊆ coneBall h J := by
    rintro z ⟨hz1, ⟨⟨a, x, t⟩, ⟨hx, ht⟩, rfl⟩⟩
    obtain ⟨y, hy, hyx⟩ := hx
    have hz : t • WithLp.toLp 2 (sheet s h (c a) (ia a) x) = t • euc h (loc p s σ (ia a) y) := by
      rw [hx_of a x y hyx, hvx a y hy]
    refine ⟨mem_ball_zero_iff.1 hz1, ?_⟩
    intro r hr
    show MvPolynomial.eval (h.pointOf (t • WithLp.toLp 2 (sheet s h (c a) (ia a) x))) r = 0
    rw [hz, hpt_smul, pointOf_euc]
    exact (hJ _).2 (fun q' hq' => eval₂_loc_eq_zero (hsub a (hAs a hy)) hq' t) r hr
  have hsub2 : coneBall h J \ (Metric.ball 0 1 ∩ (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (sheet s h (c q.1) (ia q.1) q.2.1)) ''
      {q | q.2.1 ∈ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c q.1).e '' A q.1) ∧ q.2.2 ≠ 0}) ⊆
      {0} ∪ coneBall h J ∩ {y | eval₂ σ (h.pointOf y) q = 0} := by
    rintro z ⟨hzc, hzn⟩
    by_contra hcon
    have hz0 : z ≠ 0 := fun hz => hcon (Or.inl hz)
    have hq0 : eval₂ σ (h.pointOf z) q ≠ 0 := fun hz => hcon (Or.inr ⟨hzc, hz⟩)
    apply hzn
    refine ⟨mem_ball_zero_iff.2 hzc.1, ?_⟩
    have hx'0 : h.pointOf z ≠ 0 := by
      intro hz
      apply hz0
      rw [← euc_pointOf h z, hz]
      simp [euc]
    have hx'J : ∀ q' ∈ ptIdeal p s (genericPoint Z), eval₂ σ (h.pointOf z) q' = 0 := (hJ _).1 hzc.2
    obtain ⟨y, k, hk, hxk⟩ := exists_loc hE hx'0 hx'J
    have hco : coords p σ hE.isLB s y = loc p s σ (pick hE.isLB y) y := rfl
    have hqy : eval₂ σ (coords p σ hE.isLB s y) q ≠ 0 := by
      intro hz
      apply hq0
      rw [hxk]
      have hfun : (k • loc p s σ (pick hE.isLB y) y) = fun l => k * loc p s σ (pick hE.isLB y) y l := rfl
      rw [hfun, eval₂_mul_of_isHomogeneous σ k _ hn, ← hco, hz, mul_zero]
    obtain ⟨c', hc'⟩ := hq y hqy
    obtain ⟨a, hya⟩ := mem_iUnion.1 (hcov c' hc')
    obtain ⟨k', hk', hkl⟩ := loc_eq_smul (s := s) (mem_pick hE.isLB y) (hsub a (hAs a hya))
    refine ⟨(a, ((c a).e y).ofLp, k * k'), ⟨⟨y, hya, (WithLp.toLp_ofLp 2 _).symm⟩, mul_ne_zero hk hk'⟩, ?_⟩
    show (k * k') • WithLp.toLp 2 (sheet s h (c a) (ia a) ((c a).e y).ofLp) = z
    rw [hvx a y hya, mul_smul, ← euc_smul, ← euc_smul, ← hkl, ← hxk, euc_pointOf]
  have hae : coneBall h J =ᵐ[Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)]
      (Metric.ball 0 1 ∩ (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (sheet s h (c q.1) (ia q.1) q.2.1)) ''
      {q | q.2.1 ∈ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c q.1).e '' A q.1) ∧ q.2.2 ≠ 0} : Set _) := by
    rw [ae_eq_set]
    refine ⟨measure_mono_null hsub2 hnull, ?_⟩
    rw [diff_eq_empty.2 hsub1, measure_empty]
  have hpiece : ∀ a, ∫⁻ x in (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e '' A a),
      F (WithLp.toLp 2 (sheet s h (c a) (ia a) x)) * ENNReal.ofReal (fsDens (sheet s h (c a) (ia a)) x) =
      ∫⁻ y in A a, F (euc h (coords p σ hE.isLB s y)) ∂φ.chernPart e 1 := by
    intro a
    rw [lintegral_chart hE hφ hF (c a) (hsub a) (hAm a) (hAs a) hFm]
    refine setLIntegral_congr_fun (hcond a).2.1 fun x hx => ?_
    obtain ⟨y, hy, hyx⟩ := hx
    have hsy : (c a).e.symm (WithLp.toLp 2 x) = y := by rw [← hyx, (c a).e.left_inv (hAs a hy)]
    simp only
    rw [hsy, hFco (ia a) y (hsub a (hAs a hy)), ← hvx a y hy, ← hx_of a x y hyx]
  have hWm : MeasurableSet (⋃ a, A a) := MeasurableSet.iUnion hAm
  have hres : (φ.chernPart e 1).restrict (⋃ a, A a) = φ.chernPart e 1 := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    have hcm : ∀ c' : AlgChart p σ e, ∀ ρ : CxPts p σ → ℝ≥0∞,
        chartMeas c'.e ρ ≤ (chartMeas c'.e ρ).restrict (⋃ a, A a) := by
      intro c' ρ
      rw [Measure.restrict_eq_self_of_ae_mem]
      rw [ae_iff]
      show chartMeas c'.e ρ (⋃ a, A a)ᶜ = 0
      rw [chartMeas_apply _ _ hWm.compl]
      have hemp : c'.e.source ∩ (⋃ a, A a)ᶜ = ∅ := by
        ext y
        simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and, not_not]
        exact fun hy => hcov c' hy
      rw [hemp, Set.image_empty, Measure.restrict_empty, lintegral_zero_measure]
    have key : ∀ μs : AlgChart p σ e → Measure (CxPts p σ), (∀ c', μs c' ≤ (μs c').restrict (⋃ a, A a)) →
        (⨆ c', μs c') (⋃ a, A a)ᶜ = 0 := by
      intro μs hμ
      have hle : (⨆ c', μs c') ≤ (⨆ c', μs c').restrict (⋃ a, A a) :=
        iSup_le fun c' => (hμ c').trans (Measure.restrict_mono subset_rfl (le_iSup μs c'))
      refine le_antisymm ((Measure.le_iff'.1 hle _).trans ?_) (zero_le)
      rw [Measure.restrict_apply' hWm, compl_inter_self, measure_empty]
    unfold Weight.chernPart glueMeas
    exact key _ fun c' => hcm c' _
  rw [setLIntegral_congr hae, harea]
  congr 1
  rw [tsum_congr hpiece, ← lintegral_iUnion hAm hdisj, hres]

end ChowFormHeightComparison₂.CF.C
