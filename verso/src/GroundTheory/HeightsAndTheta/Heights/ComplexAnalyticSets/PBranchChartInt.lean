import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchChartInt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicFibreSumInt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchSheetAE
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

namespace BranchChartInt

/- English proof (translation)
Use `analyticOnNhd_pi_iff.2 fun j => ?_` and prove the remaining obligations. Establish `hj : DifferentiableOn ℂ (fun t => f t j) U` using `differentiableOn_pi.1 hf j`. Use `IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_` and prove the remaining obligations. Establish `hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i))`. Rewrite using `[Function.update_eq_self]`.

Conclude with `(hj w hw).differentiableAt (hU.mem_nhds hw)`. Conclude with `hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt`.
-/
theorem analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

/- English proof (translation)
The claim follows from `(Matrix.mulVecLin A).toContinuousLinearMap.differentiable`.
-/
theorem differentiable_mulVec {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) :=
  (Matrix.mulVecLin A).toContinuousLinearMap.differentiable

open Classical in

/- English proof (translation)
Use `set T : (Fin n → ℂ) → ℝ := fun x => if h : ∃ s, IsSheetAt J A x s then γ.image.indicator g x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y else 0 with hT`. Establish `h1 : chartDens J A (γ.image.indicator g) φ y = ∑ᶠ x ∈ fibre J A y, T x` using `rfl`. Establish `h2 : ∑ᶠ x ∈ fibre J A y, T x = ∑ᶠ x ∈ γ.toFun '' {t | t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius ∧ A *ᵥ γ.toFun t = y}, T x`. Apply `finsum_mem_inter_support_eq` to reduce the goal to its premises. Use extensionality with `x`.

Simplify using `only [Set.mem_inter_iff, Function.mem_support]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hTx⟩`. Establish `hxi : x ∈ γ.image`. Assume the negation of the conclusion as `hni`.

Apply `hTx` to reduce the goal to its premises. Simplify using `only [hT, Set.indicator_of_notMem hni, zero_mul, dite_eq_ite, ite_self]`. Take `⟨t, ht, rfl⟩` from `hxi`. Conclude with `⟨⟨t, ⟨ht, hx.2⟩, rfl⟩, hTx⟩`. Introduce and unpack `⟨⟨t, ⟨ht, hty⟩, rfl⟩, hTx⟩`.

Conclude with `⟨⟨γ.mapsTo ht, hty⟩, hTx⟩`. Rewrite using `[h1, h2, finsum_mem_image (γ.injOn.mono fun t ht => ht.1)]`. Use `finsum_mem_congr rfl fun t ht => ?_` and prove the remaining obligations. Establish `hti : γ.toFun t ∈ γ.image` using `⟨t, ht.1, rfl⟩`. Simplify using `only [hT, Set.indicator_of_mem hti, ht.2]`.
-/
theorem chartDens_indicator_image {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {p : Fin n → ℂ} (γ : VarBranch J d p) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (y : Fin d → ℂ) :
    chartDens J A (γ.image.indicator g) φ y =
      ∑ᶠ t ∈ {t | t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius ∧ A *ᵥ γ.toFun t = y},
        (if h : ∃ s, IsSheetAt J A (γ.toFun t) s then
          g (γ.toFun t) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ γ.toFun t) else 0) := by
  set T : (Fin n → ℂ) → ℝ := fun x => if h : ∃ s, IsSheetAt J A x s then
      γ.image.indicator g x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y else 0 with hT
  have h1 : chartDens J A (γ.image.indicator g) φ y = ∑ᶠ x ∈ fibre J A y, T x := rfl
  have h2 : ∑ᶠ x ∈ fibre J A y, T x =
      ∑ᶠ x ∈ γ.toFun '' {t | t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius ∧ A *ᵥ γ.toFun t = y}, T x := by
    apply finsum_mem_inter_support_eq
    ext x
    simp only [Set.mem_inter_iff, Function.mem_support]
    constructor
    · rintro ⟨hx, hTx⟩
      have hxi : x ∈ γ.image := by
        by_contra hni
        apply hTx
        simp only [hT, Set.indicator_of_notMem hni, zero_mul, dite_eq_ite, ite_self]
      obtain ⟨t, ht, rfl⟩ := hxi
      exact ⟨⟨t, ⟨ht, hx.2⟩, rfl⟩, hTx⟩
    · rintro ⟨⟨t, ⟨ht, hty⟩, rfl⟩, hTx⟩
      exact ⟨⟨γ.mapsTo ht, hty⟩, hTx⟩
  rw [h1, h2, finsum_mem_image (γ.injOn.mono fun t ht => ht.1)]
  refine finsum_mem_congr rfl fun t ht => ?_
  have hti : γ.toFun t ∈ γ.image := ⟨t, ht.1, rfl⟩
  simp only [hT, Set.indicator_of_mem hti, ht.2]

/- English proof (translation)
Take `⟨U, hUo, hxU, hsd, hsx, -, V, hV, hVeq⟩` from `hs`. Use `set τ : (Fin d → ℂ) → Fin d → ℂ := fun t => A *ᵥ γ.toFun t with hτ`. Establish `hτd : DifferentiableOn ℂ τ (Metric.ball 0 γ.radius)` using `(differentiable_mulVec A).comp_differentiableOn γ.differentiableOn`. Establish `hτa : AnalyticAt ℂ τ t` using `analyticOnNhd_of_differentiableOn Metric.isOpen_ball hτd t ht`. Establish `hΔ : Metric.ball (0 : Fin d → ℂ) γ.radius ∈ 𝓝 t` using `Metric.isOpen_ball.mem_nhds ht`.

Establish `hγc : ContinuousAt γ.toFun t` using `γ.differentiableOn.continuousOn.continuousAt hΔ`. Establish `hev : ∀ k, φ k ∘ γ.toFun =ᶠ[𝓝 t] (φ k ∘ s) ∘ τ`. Introduce `k`. Use `filter_upwards [hΔ, hγc.preimage_mem_nhds hV, hτa.continuousAt.preimage_mem_nhds (hUo.mem_nhds hxU)] with t' ht' hV' hU'`. Simplify using `only [Function.comp_apply]`.

Rewrite using `[← hVeq (γ.toFun t') ⟨γ.mapsTo ht', hV'⟩ hU']`. Establish `hmd : ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t = ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) t`. Unfold `ReciprocityTheory.AnForm.maDens`. Use `congr 3`. Use function extensionality and compare the values at `k`.

Establish `h2 : fderiv ℝ (fderiv ℝ (φ k ∘ γ.toFun)) t = fderiv ℝ (fderiv ℝ ((φ k ∘ s) ∘ τ)) t` using `((hev k).fderiv (𝕜 := ℝ)).fderiv_eq`. Unfold `ReciprocityTheory.AnForm.hessC`. Rewrite using `[h2]`. Establish `hsa : AnalyticAt ℂ s (τ t)` using `analyticOnNhd_of_differentiableOn hUo hsd (τ t) hxU`. Establish `hc : ∀ k, ContDiffAt ℝ 2 (φ k ∘ s) (τ t)`.

Introduce `k`. Take `⟨O, hOo, hZO, hφO⟩` from `hφ k`. Establish `hmem : s (τ t) ∈ O`. Rewrite using `[show s (τ t) = γ.toFun t from hsx]`. Conclude with `hZO (γ.mapsTo ht)`.

Conclude with `((hφO.contDiffAt (hOo.mem_nhds hmem)).of_le (WithTop.coe_le_coe.2 le_top)).comp (τ t) (hsa.contDiffAt.restrict_scalars ℝ)`. Rewrite using `[hmd]`. Conclude with `maDens_comp (fun k => φ k ∘ s) τ t hτa hc`.
-/
theorem maDens_branch_eq {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {p : Fin n → ℂ} (γ : VarBranch J d p) {φ : Fin d → (Fin n → ℂ) → ℝ}
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k)) {t : Fin d → ℂ} (ht : t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius)
    {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A (γ.toFun t) s) :
    ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t =
      ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (A *ᵥ γ.toFun t) *
        Complex.normSq (jacC (fun t => A *ᵥ γ.toFun t) t).det := by
  obtain ⟨U, hUo, hxU, hsd, hsx, -, V, hV, hVeq⟩ := hs
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun t => A *ᵥ γ.toFun t with hτ
  have hτd : DifferentiableOn ℂ τ (Metric.ball 0 γ.radius) :=
    (differentiable_mulVec A).comp_differentiableOn γ.differentiableOn
  have hτa : AnalyticAt ℂ τ t := analyticOnNhd_of_differentiableOn Metric.isOpen_ball hτd t ht
  have hΔ : Metric.ball (0 : Fin d → ℂ) γ.radius ∈ 𝓝 t := Metric.isOpen_ball.mem_nhds ht
  have hγc : ContinuousAt γ.toFun t := γ.differentiableOn.continuousOn.continuousAt hΔ
  have hev : ∀ k, φ k ∘ γ.toFun =ᶠ[𝓝 t] (φ k ∘ s) ∘ τ := by
    intro k
    filter_upwards [hΔ, hγc.preimage_mem_nhds hV,
      hτa.continuousAt.preimage_mem_nhds (hUo.mem_nhds hxU)] with t' ht' hV' hU'
    simp only [Function.comp_apply]
    rw [← hVeq (γ.toFun t') ⟨γ.mapsTo ht', hV'⟩ hU']
  have hmd : ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t =
      ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) t := by
    unfold ReciprocityTheory.AnForm.maDens
    congr 3
    funext k
    have h2 : fderiv ℝ (fderiv ℝ (φ k ∘ γ.toFun)) t = fderiv ℝ (fderiv ℝ ((φ k ∘ s) ∘ τ)) t :=
      ((hev k).fderiv (𝕜 := ℝ)).fderiv_eq
    unfold ReciprocityTheory.AnForm.hessC
    rw [h2]
  have hsa : AnalyticAt ℂ s (τ t) := analyticOnNhd_of_differentiableOn hUo hsd (τ t) hxU
  have hc : ∀ k, ContDiffAt ℝ 2 (φ k ∘ s) (τ t) := by
    intro k
    obtain ⟨O, hOo, hZO, hφO⟩ := hφ k
    have hmem : s (τ t) ∈ O := by
      rw [show s (τ t) = γ.toFun t from hsx]
      exact hZO (γ.mapsTo ht)
    exact ((hφO.contDiffAt (hOo.mem_nhds hmem)).of_le (WithTop.coe_le_coe.2 le_top)).comp (τ t)
      (hsa.contDiffAt.restrict_scalars ℝ)
  rw [hmd]
  exact maDens_comp (fun k => φ k ∘ s) τ t hτa hc

/- English proof (translation)
Take `⟨K, hKc, hKΔ, hK0⟩` from `hK`. Establish `hγ : ContDiffOn ℝ 2 γ.toFun (Metric.ball 0 γ.radius)` using `((analyticOnNhd_of_differentiableOn Metric.isOpen_ball γ.differentiableOn).contDiffOn_of_completeSpace ).restrict_scalars ℝ`. Establish `hc2 : ∀ k, ContDiffOn ℝ 2 (φ k ∘ γ.toFun) (Metric.ball 0 γ.radius)`. Introduce `k`. Take `⟨O, -, hZO, hφO⟩` from `hφ k`.

Conclude with `(hφO.of_le (WithTop.coe_le_coe.2 le_top)).comp hγ fun t ht => hZO (γ.mapsTo ht)`. Establish `hcont : ContinuousOn (fun t => (g ∘ γ.toFun) t * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t) (Metric.ball 0 γ.radius)` using `(hg.comp_continuousOn γ.differentiableOn.continuousOn).mul (ReciprocityTheory.AnForm.M.maDens_continuousOn _ _ Metric.isOpen_ball hc2)`. Use `((hcont.mono hKΔ).integrableOn_compact hKc).of_forall_sdiff_eq_zero measurableSet_ball ?_` and prove the remaining obligations. Introduce and unpack `t ⟨htΔ, htK⟩`. Simplify using `[hK0 t htΔ htK]`.
-/
theorem integrableOn_branch {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (γ : VarBranch J d p) {g : (Fin n → ℂ) → ℝ} {φ : Fin d → (Fin n → ℂ) → ℝ} (hg : Continuous g)
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k))
    (hK : ∃ K : Set (Fin d → ℂ), IsCompact K ∧ K ⊆ Metric.ball 0 γ.radius ∧
      ∀ t ∈ Metric.ball 0 γ.radius, t ∉ K → g (γ.toFun t) = 0) :
    IntegrableOn (fun t => (g ∘ γ.toFun) t * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t)
      (Metric.ball 0 γ.radius) := by
  obtain ⟨K, hKc, hKΔ, hK0⟩ := hK
  have hγ : ContDiffOn ℝ 2 γ.toFun (Metric.ball 0 γ.radius) :=
    ((analyticOnNhd_of_differentiableOn Metric.isOpen_ball γ.differentiableOn).contDiffOn_of_completeSpace
      ).restrict_scalars ℝ
  have hc2 : ∀ k, ContDiffOn ℝ 2 (φ k ∘ γ.toFun) (Metric.ball 0 γ.radius) := by
    intro k
    obtain ⟨O, -, hZO, hφO⟩ := hφ k
    exact (hφO.of_le (WithTop.coe_le_coe.2 le_top)).comp hγ fun t ht => hZO (γ.mapsTo ht)
  have hcont : ContinuousOn (fun t => (g ∘ γ.toFun) t * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t)
      (Metric.ball 0 γ.radius) :=
    (hg.comp_continuousOn γ.differentiableOn.continuousOn).mul
      (ReciprocityTheory.AnForm.M.maDens_continuousOn _ _ Metric.isOpen_ball hc2)
  refine ((hcont.mono hKΔ).integrableOn_compact hKc).of_forall_sdiff_eq_zero measurableSet_ball ?_
  rintro t ⟨htΔ, htK⟩
  simp [hK0 t htΔ htK]

end BranchChartInt

open BranchChartInt in

/- English proof (translation)
Introduce `n d J A p γ g φ hJ hdim hfin hg hφ hK`. Use `set Δ := Metric.ball (0 : Fin d → ℂ) γ.radius with hΔ`. Use `set τ : (Fin d → ℂ) → Fin d → ℂ := fun t => A *ᵥ γ.toFun t with hτ`. Use `set H : (Fin d → ℂ) → ℝ := fun t => if h : ∃ s, IsSheetAt J A (γ.toFun t) s then g (γ.toFun t) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ γ.toFun t) else 0 with hH`. Establish `hτd : DifferentiableOn ℂ τ Δ` using `(differentiable_mulVec A).comp_differentiableOn γ.differentiableOn`.

Establish `hFin : ∀ y, {t | t ∈ Δ ∧ τ t = y}.Finite`. Introduce `y`. Use `Set.Finite.of_finite_image ((hF n d J A hJ hdim hfin y).2.1.subset ?_) (γ.injOn.mono fun t ht => ht.1)` and prove the remaining obligations. Introduce and unpack `x ⟨t, ⟨ht, hty⟩, rfl⟩`. Conclude with `⟨γ.mapsTo ht, hty⟩`.

Establish `hae : ∀ᵐ t ∂(volume.restrict Δ), (g ∘ γ.toFun) t * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t = Complex.normSq (jacC τ t).det * H t` using `by filter_upwards [hS n d J A p γ hJ hdim hfin, ae_restrict_mem measurableSet_ball] with t hts htΔ`. Simplify using `only [hH, dif_pos hts, Function.comp_apply]`. Rewrite using `[maDens_branch_eq γ hφ htΔ hts.choose_spec]`. Expand and normalize the polynomial expressions, which then agree. Establish `hint : IntegrableOn (fun t => Complex.normSq (jacC τ t).det * H t) Δ` using `(integrableOn_branch γ hg hφ hK).congr hae`.

Take `⟨hIi, hIeq⟩` from `hA d Δ τ H Metric.isOpen_ball hτd hFin hint`. Establish `hcd : chartDens J A (γ.image.indicator g) φ = fun y => ∑ᶠ t ∈ {t | t ∈ Δ ∧ τ t = y}, H t`. Use function extensionality and compare the values at `fun y => chartDens_indicator_image J A γ g φ y`. Use `⟨hcd ▸ hIi, ?_⟩` and prove the remaining obligations. Unfold `chartInt ReciprocityTheory.AnForm.maInt`.

Rewrite using `[hcd, hIeq]`. Conclude with `(integral_congr_ae hae).symm`.
-/
theorem BranchChartInt.proof (hA : HolomorphicFibreSumInt.Statement) (hS : BranchSheetAE.Statement)
    (hF : ComplexSets.FibreBound.Statement) : BranchChartInt.Statement := by
  classical
  intro n d J A p γ g φ hJ hdim hfin hg hφ hK
  set Δ := Metric.ball (0 : Fin d → ℂ) γ.radius with hΔ
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun t => A *ᵥ γ.toFun t with hτ
  set H : (Fin d → ℂ) → ℝ := fun t => if h : ∃ s, IsSheetAt J A (γ.toFun t) s then
      g (γ.toFun t) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ γ.toFun t) else 0 with hH
  have hτd : DifferentiableOn ℂ τ Δ := (differentiable_mulVec A).comp_differentiableOn γ.differentiableOn
  have hFin : ∀ y, {t | t ∈ Δ ∧ τ t = y}.Finite := by
    intro y
    refine Set.Finite.of_finite_image ((hF n d J A hJ hdim hfin y).2.1.subset ?_)
      (γ.injOn.mono fun t ht => ht.1)
    rintro x ⟨t, ⟨ht, hty⟩, rfl⟩
    exact ⟨γ.mapsTo ht, hty⟩
  have hae : ∀ᵐ t ∂(volume.restrict Δ), (g ∘ γ.toFun) t * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t =
      Complex.normSq (jacC τ t).det * H t := by
    filter_upwards [hS n d J A p γ hJ hdim hfin, ae_restrict_mem measurableSet_ball] with t hts htΔ
    simp only [hH, dif_pos hts, Function.comp_apply]
    rw [maDens_branch_eq γ hφ htΔ hts.choose_spec]
    ring
  have hint : IntegrableOn (fun t => Complex.normSq (jacC τ t).det * H t) Δ :=
    (integrableOn_branch γ hg hφ hK).congr hae
  obtain ⟨hIi, hIeq⟩ := hA d Δ τ H Metric.isOpen_ball hτd hFin hint
  have hcd : chartDens J A (γ.image.indicator g) φ = fun y => ∑ᶠ t ∈ {t | t ∈ Δ ∧ τ t = y}, H t :=
    funext fun y => chartDens_indicator_image J A γ g φ y
  refine ⟨hcd ▸ hIi, ?_⟩
  unfold chartInt ReciprocityTheory.AnForm.maInt
  rw [hcd, hIeq]
  exact (integral_congr_ae hae).symm

end

end GroundTheory.Heights₂.Heights
