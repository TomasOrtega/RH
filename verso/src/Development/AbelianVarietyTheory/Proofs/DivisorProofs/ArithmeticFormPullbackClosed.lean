import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjCompatibleLieMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsMapHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormPullbackHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpressionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarCommPullbackOfSmoothDelDbarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelDbarSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesFormTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesRealFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateChartDerivativeStatement

open CategoryTheory AlgebraicGeometry Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexConjugate

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PullArForm

/- English proof (translation)
Establish `e : swap.comp (pull L') = (pull L).comp (swap (n` using `m)) := by`. Use `ExteriorAlgebra.hom_ext (LinearMap.ext fun u => ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, swap, pull, ExteriorAlgebra.map_apply_ι]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `rcases i with b | b <;>`. Simplify using `[LinearMap.funLeft_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hL]`. Conclude with `congrArg (fun φ : Alt m →ₐ[ℂ] Alt n => φ α) e`.
-/
theorem swap_pull_conj {n m : ℕ} (L L' : V n →L[ℂ] V m)
    (hL : ∀ b a, L' (coordVec b) a = conj (L (coordVec b) a)) (α : Alt m) :
    swap (pull L' α) = pull L (swap α) := by
  have e : swap.comp (pull L') = (pull L).comp (swap (n := m)) := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun u => ?_)
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, swap, pull,
      ExteriorAlgebra.map_apply_ι]
    congr 1
    funext i
    rcases i with b | b <;>
      simp [LinearMap.funLeft_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hL]
  exact congrArg (fun φ : Alt m →ₐ[ℂ] Alt n => φ α) e

/- English proof (translation)
Establish `h1 : spMap σ' = spMap (starRingEnd ℂ) ≫ spMap σ`. Rewrite using `[← x'.2, e, Category.assoc, x.2]`. Establish `h2 : spMap (starRingEnd ℂ) ≫ spMap σ = spMap ((starRingEnd ℂ).comp σ)`. Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.

Establish `h3` using `Spec.map_injective (h1.trans h2)`. Conclude with `congrArg CommRingCat.Hom.hom h3`.
-/
theorem emb_eq_conj {k : Type} [CommRing k] {Y : Scheme.{0}} {q : Y ⟶ Sp k} {σ σ' : k →+* ℂ} (x : CxPts q σ)
    (x' : CxPts q σ') (e : x'.1 = spMap (starRingEnd ℂ) ≫ x.1) : σ' = (starRingEnd ℂ).comp σ := by
  have h1 : spMap σ' = spMap (starRingEnd ℂ) ≫ spMap σ := by
    rw [← x'.2, e, Category.assoc, x.2]
  have h2 : spMap (starRingEnd ℂ) ≫ spMap σ = spMap ((starRingEnd ℂ).comp σ) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  have h3 := Spec.map_injective (h1.trans h2)
  exact congrArg CommRingCat.Hom.hom h3

/- English proof (translation)
Introduce `hκ`. Use `haveI := h.isIntegral`. Establish `hol : ∀ σ, (h.atlas σ).IsHolo (h'.atlas σ) (Points.PtsOver.map f hf (spMap σ))` using `fun σ => GlobalTheory.T.points_map_holomorphic k X p D h σ Y q D' h' f hf`. Establish `loc : ∀ σ (x : (h'.atlas σ).Pt) (c : AlgChart p σ D) (hc : Points.PtsOver.map f hf (spMap σ) x.pt ∈ c.e.source), h.pullFld h' f hf κ σ x = pull (fderiv ℂ (c.e ∘ Points.PtsOver.map f hf (spMap σ) ∘ x.ch.symm) x.crd) (κ σ ⟨(c, _), hc⟩)` using `fun σ x c hc => GlobalTheory.T.holAtlas_pullback_eq_chart_expression _ _ _ _ (h.atlas σ) (h'.atlas σ) _ (κ σ) (hol σ) (hκ.1 σ).1 x c hc`. Use `⟨⟨fun σ => ⟨GlobalTheory.T.holAtlas_isForm_pullback_holomorphic _ _ _ _ _ _ _ _ (hol σ) (hκ.1 σ).1, fun x => ?_⟩, ?_⟩, fun σ => ?_⟩` and prove the remaining obligations.

Take `⟨c, hc⟩` from `(h.atlas σ).cover (Points.PtsOver.map f hf (spMap σ) x.pt)`. Rewrite using `[loc σ x c hc]`. Conclude with `⟨GlobalTheory.T.pullback_preserves_form_type _ _ _ _ _ _ ((hκ.1 σ).2 _).1, GlobalTheory.T.pullback_preserves_real_form _ _ _ _ ((hκ.1 σ).2 _).2⟩`. Introduce `σ σ' x x' e hch`. Take `rfl` from `emb_eq_conj x.pt x'.pt e`.

Use `set F := Points.PtsOver.map f hf (spMap σ) with hFdef`. Use `set F' := Points.PtsOver.map f hf (spMap ((starRingEnd ℂ).comp σ)) with hF'def`. Take `⟨c, hc⟩` from `(h.atlas σ).cover (F x.pt)`. Express the relevant statement in the definitionally equal form `AlgChart p σ D at c`. Set `cP : CxPts p σ ≃ₜ CxPts p ((starRingEnd ℂ).comp σ)` to `ConjChart.conjPts p rfl`.

Set `cQ : CxPts q σ ≃ₜ CxPts q ((starRingEnd ℂ).comp σ)` to `ConjChart.conjPts q rfl`. Set `c' : AlgChart p ((starRingEnd ℂ).comp σ) D` to `ConjChart.conjChart rfl c`. Establish `conjPoint_val : ∀ y, (cP y).1 = spMap (starRingEnd ℂ) ≫ y.1` using `fun _ => rfl`. Establish `cQ_val : ∀ y, (cQ y).1 = spMap (starRingEnd ℂ) ≫ y.1` using `fun _ => rfl`. Establish `c'_apply : ∀ y, c'.e (cP y) = ConjChart.conjCoord D (c.e y)` using `fun y => by`.

Express the relevant statement in the definitionally equal form `ConjChart.conjCoord D (c.e (cP.symm (cP y))) = _`. Rewrite using `[Homeomorph.symm_apply_apply]`. Establish `c'_src : ∀ y, cP y ∈ c'.e.source ↔ y ∈ c.e.source` using `fun y => by`. Express the relevant statement in the definitionally equal form `cP.symm (cP y) ∈ c.e.source ↔ _`. Rewrite using `[Homeomorph.symm_apply_apply]`.

Establish `hFc : ∀ z, F' (cQ z) = cP (F z)` using `fun z => Subtype.ext (by`. Rewrite using `[Points.PtsOver.map_val, conjPoint_val, Points.PtsOver.map_val, cQ_val, Category.assoc])`. Establish `hx' : x'.pt = cQ x.pt` using `Subtype.ext e`. Establish `hc' : F' x'.pt ∈ c'.e.source` using `by rw [hx', hFc, c'_src]; exact hc`. Rewrite using `[loc _ x' c' hc', loc σ x c hc]`.

Establish `hκc` using `hκ.2 σ ((starRingEnd ℂ).comp σ) ⟨(c, F x.pt), hc⟩ ⟨(c', F' x'.pt), hc'⟩ (by change (F' x'.pt).1 = _; rw [hx', hFc]; rfl) (fun z _ z' _ ez a => by`. Take `rfl : z' = cP z` from `Subtype.ext ez`. Express the relevant statement in the definitionally equal form `c'.e (cP z) a = _`. Rewrite using `[c'_apply]`. Use the proof step `rfl)`.

Establish `hv : ConjChart.conjCoord D' x'.crd = x.crd`. Use extensionality with `a`. Use `hch x.pt x.2 x'.pt x'.2 e a` as an intermediate fact. Simplify using `[ConjChart.conjCoord, this]`. Establish `hdiff : DifferentiableAt ℂ (c.e ∘ F ∘ x.ch.symm) x.crd`.

Establish `hs : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' (F ⁻¹' c.e.source))` using `x.ch.isOpen_inter_preimage_symm (c.e.open_source.preimage (hol σ).1)`. Use `((hol σ).2 x.1.1 c).differentiableAt (hs.mem_nhds ⟨x.ch.map_source x.2, ?_⟩)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `F (x.ch.symm x.crd) ∈ c.e.source`. Rewrite using `[x.ch.left_inv x.2]`. Conclude with `hc`.

Establish `heq : (c'.e ∘ F' ∘ x'.ch.symm) =ᶠ[𝓝 x'.crd] fun w => ConjChart.conjCoord D ((c.e ∘ F ∘ x.ch.symm) (ConjChart.conjCoord D' w))`. Establish `hS : IsOpen (F' ⁻¹' c'.e.source ∩ cQ.symm ⁻¹' x.ch.source)` using `(c'.e.open_source.preimage (hol _).1).inter (x.ch.open_source.preimage cQ.symm.continuous)`. Establish `hN` using `x'.ch.isOpen_inter_preimage_symm hS`. Establish `hmem : x'.crd ∈ x'.ch.target ∩ x'.ch.symm ⁻¹' (F' ⁻¹' c'.e.source ∩ cQ.symm ⁻¹' x.ch.source)`. Use `⟨x'.ch.map_source x'.2, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `x'.ch.symm (x'.ch x'.pt) ∈ F' ⁻¹' c'.e.source ∩ cQ.symm ⁻¹' x.ch.source`. Rewrite using `[x'.ch.left_inv x'.2]`. Use `⟨hc', ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `cQ.symm x'.pt ∈ x.ch.source`. Rewrite using `[hx', Homeomorph.symm_apply_apply]`.

Conclude with `x.2`. Use `filter_upwards [hN.mem_nhds hmem] with w hw`. Take `⟨hwt, hw1, hw2⟩` from `hw`. Establish `hz'src : x'.ch.symm w ∈ x'.ch.source` using `x'.ch.map_target hwt`. Generalize the expression as in `hzz : x'.ch.symm w = z' at hw1 hw2 hz'src`.

Take `⟨z, rfl⟩ : ∃ z, z' = cQ z` from `⟨cQ.symm z', (cQ.apply_symm_apply z').symm⟩`. Establish `hzs : z ∈ x.ch.source`. Establish `: cQ.symm (cQ z) ∈ x.ch.source` using `hw2`. Rewrite `this` using `[Homeomorph.symm_apply_apply]`. Then use the resulting hypothesis. Establish `hwz : x'.ch (cQ z) = w` using `by rw [← hzz, x'.ch.right_inv hwt]`.

Establish `hxz : x.ch z = ConjChart.conjCoord D' w`. Use extensionality with `a`. Use `hch z hzs (cQ z) hz'src rfl a` as an intermediate fact. Rewrite `this` using `[hwz]`. Simplify using `[ConjChart.conjCoord, this]`.

Establish `hsymm : x.ch.symm (ConjChart.conjCoord D' w) = z` using `by rw [← hxz, x.ch.left_inv hzs]`. Simplify using `only [Function.comp_apply]`. Rewrite using `[hsymm, hzz, hFc, c'_apply]`. Establish `hT : ∀ b a, fderiv ℂ (c'.e ∘ F' ∘ x'.ch.symm) x'.crd (coordVec b) a = conj (fderiv ℂ (c.e ∘ F ∘ x.ch.symm) x.crd (coordVec b) a)` using `fun b a => by`. Use `GlobalTheory.T.conjugate_chart_derivative _ _ _ _ x'.crd (by rw [hv]; exact hdiff) heq b a` as an intermediate fact.

Rewrite `this` using `[hv]`. Then use the resulting hypothesis. Rewrite using `[swap_pull_conj _ _ hT]`. Conclude with `(congrArg (pull _) hκc).trans (map_smul _ _ _)`. Establish `hF` using `(hκ.1 σ).1`. Take `⟨hd, hdb⟩` from `GlobalTheory.T.holAtlas_isForm_del_dbar_smooth _ _ _ (κ σ) hF`.

Take `⟨e1, e2⟩` from `GlobalTheory.T.del_dbar_comm_pullback_of_smooth_del_dbar _ _ _ _ (h.atlas σ) (h'.atlas σ) _ (κ σ) (hol σ) hF hd hdb`. Establish `z : (h.atlas σ).pullback (h'.atlas σ) (Points.PtsOver.map f hf (spMap σ)) 0 = 0`. Use function extensionality and compare the values at `x`. Conclude with `map_zero _`. Use `⟨fun h0 => ?_, fun h0 => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(h'.atlas σ).del ((h.atlas σ).pullback _ _ _) = 0`. Rewrite using `[e1, h0, z]`. Express the relevant statement in the definitionally equal form `(h'.atlas σ).dbar ((h.atlas σ).pullback _ _ _) = 0`. Rewrite using `[e2, h0, z]`.
-/
theorem pullFld_isArForm (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D D' : ℕ)
    (h : IsRegVar p D) (h' : IsRegVar q D') (f : Y ⟶ X) (hf : f ≫ p = q) (j : ℕ) (κ : h.Fld) :
    h.IsArForm j κ → h'.IsArForm j (h.pullFld h' f hf κ) ∧ ∀ σ,
      ((h.atlas σ).del (κ σ) = 0 → (h'.atlas σ).del (h.pullFld h' f hf κ σ) = 0) ∧
      ((h.atlas σ).dbar (κ σ) = 0 → (h'.atlas σ).dbar (h.pullFld h' f hf κ σ) = 0) := by
  intro hκ
  haveI := h.isIntegral
  have hol : ∀ σ, (h.atlas σ).IsHolo (h'.atlas σ) (Points.PtsOver.map f hf (spMap σ)) := fun σ =>
    GlobalTheory.T.points_map_holomorphic k X p D h σ Y q D' h' f hf
  have loc : ∀ σ (x : (h'.atlas σ).Pt) (c : AlgChart p σ D)
      (hc : Points.PtsOver.map f hf (spMap σ) x.pt ∈ c.e.source),
      h.pullFld h' f hf κ σ x = pull (fderiv ℂ (c.e ∘ Points.PtsOver.map f hf (spMap σ) ∘ x.ch.symm) x.crd)
        (κ σ ⟨(c, _), hc⟩) :=
    fun σ x c hc => GlobalTheory.T.holAtlas_pullback_eq_chart_expression _ _ _ _ (h.atlas σ) (h'.atlas σ) _ (κ σ) (hol σ) (hκ.1 σ).1 x c hc
  refine ⟨⟨fun σ => ⟨GlobalTheory.T.holAtlas_isForm_pullback_holomorphic _ _ _ _ _ _ _ _ (hol σ) (hκ.1 σ).1, fun x => ?_⟩, ?_⟩, fun σ => ?_⟩
  · obtain ⟨c, hc⟩ := (h.atlas σ).cover (Points.PtsOver.map f hf (spMap σ) x.pt)
    rw [loc σ x c hc]
    exact ⟨GlobalTheory.T.pullback_preserves_form_type _ _ _ _ _ _ ((hκ.1 σ).2 _).1, GlobalTheory.T.pullback_preserves_real_form _ _ _ _ ((hκ.1 σ).2 _).2⟩
  · intro σ σ' x x' e hch
    obtain rfl := emb_eq_conj x.pt x'.pt e
    set F := Points.PtsOver.map f hf (spMap σ) with hFdef
    set F' := Points.PtsOver.map f hf (spMap ((starRingEnd ℂ).comp σ)) with hF'def
    obtain ⟨c, hc⟩ := (h.atlas σ).cover (F x.pt)
    change AlgChart p σ D at c
    let cP : CxPts p σ ≃ₜ CxPts p ((starRingEnd ℂ).comp σ) := ConjChart.conjPts p rfl
    let cQ : CxPts q σ ≃ₜ CxPts q ((starRingEnd ℂ).comp σ) := ConjChart.conjPts q rfl
    let c' : AlgChart p ((starRingEnd ℂ).comp σ) D := ConjChart.conjChart rfl c
    have conjPoint_val : ∀ y, (cP y).1 = spMap (starRingEnd ℂ) ≫ y.1 := fun _ => rfl
    have cQ_val : ∀ y, (cQ y).1 = spMap (starRingEnd ℂ) ≫ y.1 := fun _ => rfl
    have c'_apply : ∀ y, c'.e (cP y) = ConjChart.conjCoord D (c.e y) := fun y => by
      change ConjChart.conjCoord D (c.e (cP.symm (cP y))) = _
      rw [Homeomorph.symm_apply_apply]
    have c'_src : ∀ y, cP y ∈ c'.e.source ↔ y ∈ c.e.source := fun y => by
      change cP.symm (cP y) ∈ c.e.source ↔ _
      rw [Homeomorph.symm_apply_apply]
    have hFc : ∀ z, F' (cQ z) = cP (F z) := fun z => Subtype.ext (by
      rw [Points.PtsOver.map_val, conjPoint_val, Points.PtsOver.map_val, cQ_val, Category.assoc])
    have hx' : x'.pt = cQ x.pt := Subtype.ext e
    have hc' : F' x'.pt ∈ c'.e.source := by rw [hx', hFc, c'_src]; exact hc
    rw [loc _ x' c' hc', loc σ x c hc]
    have hκc := hκ.2 σ ((starRingEnd ℂ).comp σ) ⟨(c, F x.pt), hc⟩ ⟨(c', F' x'.pt), hc'⟩
      (by change (F' x'.pt).1 = _; rw [hx', hFc]; rfl)
      (fun z _ z' _ ez a => by
        obtain rfl : z' = cP z := Subtype.ext ez
        change c'.e (cP z) a = _
        rw [c'_apply]; rfl)
    have hv : ConjChart.conjCoord D' x'.crd = x.crd := by
      ext a
      have := hch x.pt x.2 x'.pt x'.2 e a
      simp [ConjChart.conjCoord, this]
    have hdiff : DifferentiableAt ℂ (c.e ∘ F ∘ x.ch.symm) x.crd := by
      have hs : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' (F ⁻¹' c.e.source)) :=
        x.ch.isOpen_inter_preimage_symm (c.e.open_source.preimage (hol σ).1)
      refine ((hol σ).2 x.1.1 c).differentiableAt (hs.mem_nhds ⟨x.ch.map_source x.2, ?_⟩)
      change F (x.ch.symm x.crd) ∈ c.e.source
      rw [x.ch.left_inv x.2]; exact hc
    have heq : (c'.e ∘ F' ∘ x'.ch.symm) =ᶠ[𝓝 x'.crd]
        fun w => ConjChart.conjCoord D ((c.e ∘ F ∘ x.ch.symm) (ConjChart.conjCoord D' w)) := by
      have hS : IsOpen (F' ⁻¹' c'.e.source ∩ cQ.symm ⁻¹' x.ch.source) :=
        (c'.e.open_source.preimage (hol _).1).inter (x.ch.open_source.preimage cQ.symm.continuous)
      have hN := x'.ch.isOpen_inter_preimage_symm hS
      have hmem : x'.crd ∈ x'.ch.target ∩ x'.ch.symm ⁻¹' (F' ⁻¹' c'.e.source ∩ cQ.symm ⁻¹' x.ch.source) := by
        refine ⟨x'.ch.map_source x'.2, ?_⟩
        change x'.ch.symm (x'.ch x'.pt) ∈ F' ⁻¹' c'.e.source ∩ cQ.symm ⁻¹' x.ch.source
        rw [x'.ch.left_inv x'.2]
        refine ⟨hc', ?_⟩
        change cQ.symm x'.pt ∈ x.ch.source
        rw [hx', Homeomorph.symm_apply_apply]; exact x.2
      filter_upwards [hN.mem_nhds hmem] with w hw
      obtain ⟨hwt, hw1, hw2⟩ := hw
      have hz'src : x'.ch.symm w ∈ x'.ch.source := x'.ch.map_target hwt
      generalize hzz : x'.ch.symm w = z' at hw1 hw2 hz'src
      obtain ⟨z, rfl⟩ : ∃ z, z' = cQ z := ⟨cQ.symm z', (cQ.apply_symm_apply z').symm⟩
      have hzs : z ∈ x.ch.source := by
        have : cQ.symm (cQ z) ∈ x.ch.source := hw2
        rwa [Homeomorph.symm_apply_apply] at this
      have hwz : x'.ch (cQ z) = w := by rw [← hzz, x'.ch.right_inv hwt]
      have hxz : x.ch z = ConjChart.conjCoord D' w := by
        ext a
        have := hch z hzs (cQ z) hz'src rfl a
        rw [hwz] at this
        simp [ConjChart.conjCoord, this]
      have hsymm : x.ch.symm (ConjChart.conjCoord D' w) = z := by rw [← hxz, x.ch.left_inv hzs]
      simp only [Function.comp_apply]
      rw [hsymm, hzz, hFc, c'_apply]
    have hT : ∀ b a, fderiv ℂ (c'.e ∘ F' ∘ x'.ch.symm) x'.crd (coordVec b) a =
        conj (fderiv ℂ (c.e ∘ F ∘ x.ch.symm) x.crd (coordVec b) a) := fun b a => by
      have := GlobalTheory.T.conjugate_chart_derivative _ _ _ _ x'.crd (by rw [hv]; exact hdiff) heq b a
      rwa [hv] at this
    rw [swap_pull_conj _ _ hT]
    exact (congrArg (pull _) hκc).trans (map_smul _ _ _)
  · have hF := (hκ.1 σ).1
    obtain ⟨hd, hdb⟩ := GlobalTheory.T.holAtlas_isForm_del_dbar_smooth _ _ _ (κ σ) hF
    obtain ⟨e1, e2⟩ := GlobalTheory.T.del_dbar_comm_pullback_of_smooth_del_dbar _ _ _ _ (h.atlas σ) (h'.atlas σ) _ (κ σ) (hol σ) hF hd hdb
    have z : (h.atlas σ).pullback (h'.atlas σ) (Points.PtsOver.map f hf (spMap σ)) 0 = 0 := by
      funext x; exact map_zero _
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · change (h'.atlas σ).del ((h.atlas σ).pullback _ _ _) = 0
      rw [e1, h0, z]
    · change (h'.atlas σ).dbar ((h.atlas σ).pullback _ _ _) = 0
      rw [e2, h0, z]

end GlobalTheory.PullArForm
