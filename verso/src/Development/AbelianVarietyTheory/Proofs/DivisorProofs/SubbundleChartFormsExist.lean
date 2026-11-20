import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsC1DensityForLinePair
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AngleGlueDim
open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.CurveDens (angleForm)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/- English proof (translation)
Simplify using `only [angleForm, map_add, map_sub, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem angleForm_add (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (ξ η z : E) :
    angleForm n a a' q (ξ + η) z = angleForm n a a' q ξ z + angleForm n a a' q η z := by
  simp only [angleForm, map_add, map_sub, map_mul]
  ring

def angleLin (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (z : E) : E →ₗ[ℂ] ℂ where
  toFun ξ := angleForm n a a' q ξ z
  map_add' ξ η := angleForm_add n a a' q ξ η z
  map_smul' c ξ := GlobalTheory.CurveDens.angleForm_smul n a a' q ξ z c

/- English proof (translation)
Use `map_sum (angleLin n a a' q z) (fun i => w i • ξ i) s` as an intermediate fact. Simplify using `only [LinearMap.map_smul, smul_eq_mul] at this`. Conclude with `this`.
-/
theorem angleForm_sum {ι : Type} (s : Finset ι) (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (w : ι → ℂ) (ξ : ι → E) (z : E) :
    angleForm n a a' q (∑ i ∈ s, w i • ξ i) z = ∑ i ∈ s, w i * angleForm n a a' q (ξ i) z := by
  have := map_sum (angleLin n a a' q z) (fun i => w i • ξ i) s
  simp only [LinearMap.map_smul, smul_eq_mul] at this
  exact this

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {E L L' : X.Modules} {r : ℕ} (h : Met p σ E r) {l : L ⟶ E} {l' : L' ⟶ E}

/- English proof (translation)
Take `⟨f, hf⟩` from `GlobalTheory.AngleGlue.exists_app_eq_smul l t ht s`. Take `⟨g, hg⟩` from `GlobalTheory.AngleGlue.exists_app_eq_smul l' t' ht' s'`. Establish `hW : y ∈ ptsIn p σ (U ⊓ U₂)` using `mem_ptsIn_inf.2 ⟨hy, hy₂⟩`. Establish `hN : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn p σ (U ⊓ U₂)` using `eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn (U ⊓ U₂))).mem_nhds (ChartGlue.mem_over c.e hc hW)) fun _ hv => hv.2`. Establish `hre (a b : ℂ) : (a * starRingEnd ℂ a * b).re = ‖a‖ ^ 2 * b.re`.

Rewrite using `[Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]`. Establish `ef` using `GlobalTheory.AngleGlue.form_eq_of_resM h inf_le_left inf_le_right _ _ _ _ f f hf hf`. Establish `eg` using `GlobalTheory.AngleGlue.form_eq_of_resM h inf_le_left inf_le_right _ _ _ _ g g hg hg`. Establish `eq` using `GlobalTheory.AngleGlue.form_eq_of_resM h inf_le_left inf_le_right _ _ _ _ g f hg hf`. Establish `e0` using `c.e.left_inv hc`.

Establish `hpos₂` using `GlobalTheory.AngleGlue.re_form_pos h hl hL s hs hy₂`. Establish `hpos₂'` using `GlobalTheory.AngleGlue.re_form_pos h hl' hL' s' hs' hy₂`. Use `GlobalTheory.CurveDens.angleForm_frame_indep _ n _ _ _ _ _ _ (fun v => ev p σ (U ⊓ U₂) f (c.e.symm v)) (fun v => ev p σ (U ⊓ U₂) g (c.e.symm v)) ξ (c.e y) ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ hy c hc).differentiableAt (by simp)) ((GlobalTheory.AngleGlue.contDiffAt_ …` and prove the remaining obligations. Simplify using `only [e0]`. Introduce `h0`.

Rewrite `hpos₂` using `[ef _ hW, h0]`. Simplify using `at hpos₂`. Simplify using `only [e0]`. Introduce `h0`. Rewrite `hpos₂'` using `[eg _ hW, h0]`.

Simplify using `at hpos₂'`. Use `filter_upwards [hN] with v hv`. Rewrite using `[ef _ hv, hre]`. Use `filter_upwards [hN] with v hv`. Rewrite using `[eg _ hv, hre]`.

Use `filter_upwards [hN] with v hv`. Rewrite using `[eq _ hv]`.
-/
theorem angleForm_frames (H : h.IsCInf) (hl : IsSubbundle l) (hl' : IsSubbundle l')
    (hL : IsVB L 1) (hL' : IsVB L' 1) (n : ℕ) {U U₂ : X.Opens} (t : Γ(L, U)) (t' : Γ(L', U))
    (s : Γ(L, U₂)) (s' : Γ(L', U₂)) (ht : IsFrame (fun _ : Fin 1 => t))
    (ht' : IsFrame (fun _ : Fin 1 => t')) (hs : IsFrame (fun _ : Fin 1 => s))
    (hs' : IsFrame (fun _ : Fin 1 => s')) {D : ℕ} (c : AlgChart p σ D) {y : CxPts p σ}
    (hc : y ∈ c.e.source) (hy : y ∈ ptsIn p σ U) (hy₂ : y ∈ ptsIn p σ U₂) (ξ : EuclideanSpace ℂ (Fin D)) :
    angleForm n (fun v => (h.form (l.app U₂ s) (l.app U₂ s) (c.e.symm v)).re)
      (fun v => (h.form (l'.app U₂ s') (l'.app U₂ s') (c.e.symm v)).re)
      (fun v => h.form (l'.app U₂ s') (l.app U₂ s) (c.e.symm v)) ξ (c.e y) =
    angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
      (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
      (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) ξ (c.e y) := by
  obtain ⟨f, hf⟩ := GlobalTheory.AngleGlue.exists_app_eq_smul l t ht s
  obtain ⟨g, hg⟩ := GlobalTheory.AngleGlue.exists_app_eq_smul l' t' ht' s'
  have hW : y ∈ ptsIn p σ (U ⊓ U₂) := mem_ptsIn_inf.2 ⟨hy, hy₂⟩
  have hN : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn p σ (U ⊓ U₂) :=
    eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn (U ⊓ U₂))).mem_nhds
      (ChartGlue.mem_over c.e hc hW)) fun _ hv => hv.2
  have hre (a b : ℂ) : (a * starRingEnd ℂ a * b).re = ‖a‖ ^ 2 * b.re := by
    rw [Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
  have ef := GlobalTheory.AngleGlue.form_eq_of_resM h inf_le_left inf_le_right _ _ _ _ f f hf hf
  have eg := GlobalTheory.AngleGlue.form_eq_of_resM h inf_le_left inf_le_right _ _ _ _ g g hg hg
  have eq := GlobalTheory.AngleGlue.form_eq_of_resM h inf_le_left inf_le_right _ _ _ _ g f hg hf
  have e0 := c.e.left_inv hc
  have hpos₂ := GlobalTheory.AngleGlue.re_form_pos h hl hL s hs hy₂
  have hpos₂' := GlobalTheory.AngleGlue.re_form_pos h hl' hL' s' hs' hy₂
  refine GlobalTheory.CurveDens.angleForm_frame_indep _ n _ _ _ _ _ _ (fun v => ev p σ (U ⊓ U₂) f (c.e.symm v))
    (fun v => ev p σ (U ⊓ U₂) g (c.e.symm v)) ξ (c.e y)
    ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ hy c hc).differentiableAt (by simp))
    ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ hy c hc).differentiableAt (by simp))
    ((GlobalTheory.AngleGlue.contDiffAt_form h H _ _ hy c hc).differentiableAt (by simp))
    (by simp only [e0]; exact GlobalTheory.AngleGlue.re_form_pos h hl hL t ht hy)
    (by simp only [e0]; exact GlobalTheory.AngleGlue.re_form_pos h hl' hL' t' ht' hy)
    (c.differentiableAt_ev f hc hW) (c.differentiableAt_ev g hc hW) ?_ ?_ ?_ ?_ ?_
  · simp only [e0]
    intro h0
    rw [ef _ hW, h0] at hpos₂
    simp at hpos₂
  · simp only [e0]
    intro h0
    rw [eg _ hW, h0] at hpos₂'
    simp at hpos₂'
  · filter_upwards [hN] with v hv
    rw [ef _ hv, hre]
  · filter_upwards [hN] with v hv
    rw [eg _ hv, hre]
  · filter_upwards [hN] with v hv
    rw [eq _ hv]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[Finset.sum_apply, EuclideanSpace.single_apply, Pi.single_apply]`.
-/
theorem eq_sum_single {D : ℕ} (w : EuclideanSpace ℂ (Fin D)) :
    w = ∑ a, w a • EuclideanSpace.single a (1 : ℂ) := by
  ext i
  simp [Finset.sum_apply, EuclideanSpace.single_apply, Pi.single_apply]

end GlobalTheory.AngleGlueDim

open GlobalTheory.Twist (resM)

/- English proof (translation)
Introduce `k _ X p σ d V L L' r h l l' H hl hl' hL hL' n`. Set `W : CxPts p σ → X.Opens` to `fun y => (hL.pick y).U ⊓ (hL'.pick y).U`. Set `T : ∀ y, Γ(L, W y)` to `fun y => resM L inf_le_left ((hL.pick y).e 0)`. Set `T' : ∀ y, Γ(L', W y)` to `fun y => resM L' inf_le_right ((hL'.pick y).e 0)`. Establish `hT : ∀ y, IsFrame (fun _ : Fin 1 => T y)` using `fun y => by`.

Use `(hL.pick y).isFrame.res (inf_le_left : W y ≤ _)` as an intermediate fact. Use `this using 2 with i` and compare the differences between its conclusion and the goal. Rewrite using `[Subsingleton.elim i 0]`. Establish `hT' : ∀ y, IsFrame (fun _ : Fin 1 => T' y)` using `fun y => by`. Use `(hL'.pick y).isFrame.res (inf_le_right : W y ≤ _)` as an intermediate fact.

Use `this using 2 with i` and compare the differences between its conclusion and the goal. Rewrite using `[Subsingleton.elim i 0]`. Establish `hW : ∀ y, y ∈ ptsIn p σ (W y)` using `fun y => mem_ptsIn_inf.2 ⟨hL.mem_pick y, hL'.mem_pick y⟩`. Use `⟨fun c y j => CurveDens.angleForm n (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c.e.symm v)).re) (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c.e.symm v)).re) (fun v => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c.e.symm v)) (EuclideanSpace …` and prove the remaining obligations. Introduce `c y hc j`.

Establish `e0` using `c.e.left_inv hc`. Establish `hG` using `(GlobalTheory.CurveDens.angleForm_props _ n (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c.e.symm v)).re) (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c.e.symm v)).re) (fun v => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c.e.symm v)) (Euclid …`. Use `hG.congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [(ChartGlue.isOpen_over c.e (isOpen_ptsIn (W y))).mem_nhds (ChartGlue.mem_over c.e hc (hW y))] with v hv`. Use `GlobalTheory.AngleGlueDim.angleForm_frames h H hl hl' hL hL' n (T y) (T' y) (T (c.e.symm v)) (T' (c.e.symm v)) (hT y) (hT' y) (hT _) (hT' _) c (c.e.map_target hv.1) hv.2 (hW _) (EuclideanSpace.single j 1)` as an intermediate fact.

Conclude with `this.trans (by rw [c.e.right_inv hv.1])`. Introduce `c c' y hc hc' j`. Establish `e0` using `c.e.left_inv hc`. Establish `e0'` using `c'.e.left_inv hc'`. Establish `hN` using `(ChartGlue.isOpen_over c.e c'.e.open_source).mem_nhds (ChartGlue.mem_over c.e hc hc')`.

Establish `hφz : (c'.e ∘ c.e.symm) (c.e y) = c'.e y` using `congrArg c'.e e0`. Establish `hφ : DifferentiableAt ℂ (c'.e ∘ c.e.symm) (c.e y)` using `(c.holo_trans c').differentiableAt hN`. Establish `step1` using `GlobalTheory.CurveDens.angleForm_frame_indep _ n (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c.e.symm v)).re) (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c.e.symm v)).re) (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c'.e.symm ((c'.e …`. Establish `step2` using `(GlobalTheory.CurveDens.angleForm_props _ n (fun w => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c'.e.symm w)).re) (fun w => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c'.e.symm w)).re) (fun w => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c'.e.symm w)) (Euc …`. Rewrite `step2` using `[hφz, GlobalTheory.AngleGlueDim.eq_sum_single (fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (EuclideanSpace.single j 1)), GlobalTheory.AngleGlueDim.angleForm_sum]`.

Conclude with `step1.symm.trans (step2.trans rfl)`. Introduce `U t t' ht ht' c y hc hy j`. Conclude with `GlobalTheory.AngleGlueDim.angleForm_frames h H hl hl' hL hL' n t t' (T y) (T' y) ht ht' (hT y) (hT' y) c hc hy (hW y) _`.
-/
theorem GlobalTheory.angleForm_global_dim : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) (E L L' : X.Modules) (r : ℕ) (h : Met p σ E r) (l : L ⟶ E) (l' : L' ⟶ E), h.IsCInf → IsSubbundle l → IsSubbundle l' → IsVB L 1 → IsVB L' 1 → ∀ n : ℕ, ∃ α : AlgChart p σ (d + 1) → CxPts p σ → Fin (d + 1) → ℂ, (∀ c : AlgChart p σ (d + 1), ∀ y ∈ c.e.source, ∀ j, ContDiffAt ℝ 1 (fun v => α c (c.e.symm v) j) (c.e y)) ∧ (∀ (c c' : AlgChart p σ (d + 1)) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → ∀ j, α c y j = ∑ a, transMat c c' y a j * α c' y a) ∧ ∀ (U : X.Opens) (t : Γ(L, U)) (t' : Γ(L', U)), IsFrame (fun _ : Fin 1 => t) → IsFrame (fun _ : Fin 1 => t') → ∀ c : AlgChart p σ (d + 1), ∀ y ∈ c.e.source, y ∈ ptsIn p σ U → ∀ j, α c y j = CurveDens.angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re) (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re) (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single j 1) (c.e y) := by
  intro k _ X p σ d V L L' r h l l' H hl hl' hL hL' n
  let W : CxPts p σ → X.Opens := fun y => (hL.pick y).U ⊓ (hL'.pick y).U
  let T : ∀ y, Γ(L, W y) := fun y => resM L inf_le_left ((hL.pick y).e 0)
  let T' : ∀ y, Γ(L', W y) := fun y => resM L' inf_le_right ((hL'.pick y).e 0)
  have hT : ∀ y, IsFrame (fun _ : Fin 1 => T y) := fun y => by
    have := (hL.pick y).isFrame.res (inf_le_left : W y ≤ _)
    convert this using 2 with i
    rw [Subsingleton.elim i 0]
  have hT' : ∀ y, IsFrame (fun _ : Fin 1 => T' y) := fun y => by
    have := (hL'.pick y).isFrame.res (inf_le_right : W y ≤ _)
    convert this using 2 with i
    rw [Subsingleton.elim i 0]
  have hW : ∀ y, y ∈ ptsIn p σ (W y) := fun y => mem_ptsIn_inf.2 ⟨hL.mem_pick y, hL'.mem_pick y⟩
  refine ⟨fun c y j => CurveDens.angleForm n
    (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c.e.symm v)).re)
    (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c.e.symm v)).re)
    (fun v => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c.e.symm v))
    (EuclideanSpace.single j 1) (c.e y), ?_, ?_, ?_⟩
  · intro c y hc j
    have e0 := c.e.left_inv hc
    have hG := (GlobalTheory.CurveDens.angleForm_props _ n
      (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c.e.symm v)).re)
      (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c.e.symm v)).re)
      (fun v => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c.e.symm v))
      (EuclideanSpace.single j 1) (c.e y)).2.1
      ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c hc).of_le (by norm_cast))
      ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c hc).of_le (by norm_cast))
      ((GlobalTheory.AngleGlue.contDiffAt_form h H _ _ (hW y) c hc).of_le (by norm_cast))
      (by simp only [e0]; exact GlobalTheory.AngleGlue.re_form_pos h hl hL _ (hT y) (hW y))
      (by simp only [e0]; exact GlobalTheory.AngleGlue.re_form_pos h hl' hL' _ (hT' y) (hW y))
    refine hG.congr_of_eventuallyEq ?_
    filter_upwards [(ChartGlue.isOpen_over c.e (isOpen_ptsIn (W y))).mem_nhds
      (ChartGlue.mem_over c.e hc (hW y))] with v hv
    have := GlobalTheory.AngleGlueDim.angleForm_frames h H hl hl' hL hL' n (T y) (T' y) (T (c.e.symm v))
      (T' (c.e.symm v)) (hT y) (hT' y) (hT _) (hT' _) c (c.e.map_target hv.1) hv.2 (hW _)
      (EuclideanSpace.single j 1)
    exact this.trans (by rw [c.e.right_inv hv.1])
  · intro c c' y hc hc' j
    have e0 := c.e.left_inv hc
    have e0' := c'.e.left_inv hc'
    have hN := (ChartGlue.isOpen_over c.e c'.e.open_source).mem_nhds (ChartGlue.mem_over c.e hc hc')
    have hφz : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e e0
    have hφ : DifferentiableAt ℂ (c'.e ∘ c.e.symm) (c.e y) := (c.holo_trans c').differentiableAt hN
    have step1 := GlobalTheory.CurveDens.angleForm_frame_indep _ n
      (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c.e.symm v)).re)
      (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c.e.symm v)).re)
      (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c'.e.symm ((c'.e ∘ c.e.symm) v))).re)
      (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y))
        (c'.e.symm ((c'.e ∘ c.e.symm) v))).re)
      (fun v => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c.e.symm v))
      (fun v => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c'.e.symm ((c'.e ∘ c.e.symm) v)))
      (fun _ => 1) (fun _ => 1) (EuclideanSpace.single j 1) (c.e y)
      ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c hc).differentiableAt (by simp))
      ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c hc).differentiableAt (by simp))
      ((GlobalTheory.AngleGlue.contDiffAt_form h H _ _ (hW y) c hc).differentiableAt (by simp))
      (by simp only [e0]; exact GlobalTheory.AngleGlue.re_form_pos h hl hL _ (hT y) (hW y))
      (by simp only [e0]; exact GlobalTheory.AngleGlue.re_form_pos h hl' hL' _ (hT' y) (hW y))
      (differentiableAt_const _) (differentiableAt_const _) one_ne_zero one_ne_zero
      (by filter_upwards [hN] with v hv; simp [c'.e.left_inv hv.2])
      (by filter_upwards [hN] with v hv; simp [c'.e.left_inv hv.2])
      (by filter_upwards [hN] with v hv; simp [c'.e.left_inv hv.2])
    have step2 := (GlobalTheory.CurveDens.angleForm_props _ n
      (fun w => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c'.e.symm w)).re)
      (fun w => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c'.e.symm w)).re)
      (fun w => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c'.e.symm w))
      (EuclideanSpace.single j 1) (c.e y)).2.2 (c'.e ∘ c.e.symm) hφ
      (by rw [hφz]; exact (GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c' hc').differentiableAt (by simp))
      (by rw [hφz]; exact (GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c' hc').differentiableAt (by simp))
      (by rw [hφz]; exact (GlobalTheory.AngleGlue.contDiffAt_form h H _ _ (hW y) c' hc').differentiableAt (by simp))
      (by rw [hφz]; simp only [e0']; exact GlobalTheory.AngleGlue.re_form_pos h hl hL _ (hT y) (hW y))
      (by rw [hφz]; simp only [e0']; exact GlobalTheory.AngleGlue.re_form_pos h hl' hL' _ (hT' y) (hW y))
    rw [hφz, GlobalTheory.AngleGlueDim.eq_sum_single (fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (EuclideanSpace.single j 1)),
      GlobalTheory.AngleGlueDim.angleForm_sum] at step2
    exact step1.symm.trans (step2.trans rfl)
  · intro U t t' ht ht' c y hc hy j
    exact GlobalTheory.AngleGlueDim.angleForm_frames h H hl hl' hL hL' n t t' (T y) (T' y) ht ht' (hT y)
      (hT' y) c hc hy (hW y) _
