import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageMetrics
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ProjLine
open scoped Topology

noncomputable section

namespace BlockImageMetrics

/- English proof (translation)
Use `set Lr : (E → ℂ) →L[ℝ] (F → ℂ) := L.restrictScalars ℝ with hLr`. Establish `hev : fderiv ℝ (fun y => φ (L y)) =ᶠ[𝓝 z] fun y => (fderiv ℝ φ (Lr y)).comp Lr`. Establish `h1 : ∀ᶠ x in 𝓝 (L z), ContDiffAt ℝ 2 φ x` using `hφ.eventually (by simp)`. Establish `h2 : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 φ (L y)` using `(L.continuous.tendsto z).eventually h1`. Use `filter_upwards [h2] with y hy`.

Establish `hd : DifferentiableAt ℝ φ (Lr y)` using `hy.differentiableAt (by norm_num)`. Conclude with `(hd.hasFDerivAt.comp y Lr.hasFDerivAt).fderiv`. Establish `hd2 : DifferentiableAt ℝ (fderiv ℝ φ) (Lr z)` using `(hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `hD : HasFDerivAt (fun y => (fderiv ℝ φ (Lr y)).comp Lr) ((ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ (fderiv ℝ φ (Lr z))).comp 0 + ((ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ).flip Lr).comp ((fderiv ℝ (fderiv ℝ φ) (Lr z)).comp Lr)) z` using `(hd2.hasFDerivAt.comp z Lr.hasFDerivAt).clm_comp (hasFDerivAt_const Lr z)`. Establish `hIw : L (Complex.I • w) = Complex.I • L w` using `L.map_smul _ _`.

Unfold `leviForm`. Rewrite using `[hev.fderiv_eq, hD.fderiv]`. Simplify using `[hLr, hIw]`.
-/
theorem leviForm_comp_clm {E F : Type} [Fintype E] [Fintype F] (L : (E → ℂ) →L[ℂ] (F → ℂ))
    {φ : (F → ℂ) → ℝ} {z : E → ℂ} (hφ : ContDiffAt ℝ 2 φ (L z)) (w : E → ℂ) :
    leviForm (fun y => φ (L y)) z w = leviForm φ (L z) (L w) := by
  set Lr : (E → ℂ) →L[ℝ] (F → ℂ) := L.restrictScalars ℝ with hLr
  have hev : fderiv ℝ (fun y => φ (L y)) =ᶠ[𝓝 z] fun y => (fderiv ℝ φ (Lr y)).comp Lr := by
    have h1 : ∀ᶠ x in 𝓝 (L z), ContDiffAt ℝ 2 φ x := hφ.eventually (by simp)
    have h2 : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 φ (L y) := (L.continuous.tendsto z).eventually h1
    filter_upwards [h2] with y hy
    have hd : DifferentiableAt ℝ φ (Lr y) := hy.differentiableAt (by norm_num)
    exact (hd.hasFDerivAt.comp y Lr.hasFDerivAt).fderiv
  have hd2 : DifferentiableAt ℝ (fderiv ℝ φ) (Lr z) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hD : HasFDerivAt (fun y => (fderiv ℝ φ (Lr y)).comp Lr)
      ((ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ (fderiv ℝ φ (Lr z))).comp 0 +
        ((ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ).flip Lr).comp
          ((fderiv ℝ (fderiv ℝ φ) (Lr z)).comp Lr)) z :=
    (hd2.hasFDerivAt.comp z Lr.hasFDerivAt).clm_comp (hasFDerivAt_const Lr z)
  have hIw : L (Complex.I • w) = Complex.I • L w := L.map_smul _ _
  unfold leviForm
  rw [hev.fderiv_eq, hD.fderiv]
  simp [hLr, hIw]

/- English proof (translation)
Establish `hsm : ∀ z, L z ≠ 0 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fsMetric F).ρ (L z)` using `fun z hz => (isSmoothMetric_fs (J := F) (L z) hz).contDiffAt (isOpen_ne.mem_nhds hz)`. Use `⟨?_, fun z hz w _ => ?_⟩` and prove the remaining obligations. Unfold `IsSmoothHerm`. Rewrite using `[hA]`. Introduce `z hz`.

Conclude with `((hsm z (hL z hz)).comp z (L.restrictScalars ℝ).contDiff.contDiffAt).contDiffWithinAt`. Establish `hz0` using `hL z hz.1`. Establish `hlog : ContDiffAt ℝ 2 (fun x => Real.log ((fsMetric F).ρ x)) (L z)` using `((hsm z hz0).of_le (WithTop.coe_le_coe.2 le_top)).log ((fsMetric F).pos _ hz0).ne'`. Rewrite using `[show (fun z => Real.log (A.h z)) = fun y => (fun x => Real.log ((fsMetric F).ρ x)) (L y) by rw [hA]]`. Rewrite using `[leviForm_comp_clm L hlog w]`.

Conclude with `leviForm_log_fs_nonneg hz0 _`.
-/
theorem isSemipositiveRel_of_linear {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {F : Type}
    [Fintype F] (A : HermLine ι) (L : ((Σ k, ι k) → ℂ) →L[ℂ] (F → ℂ))
    (hA : A.h = fun z => (fsMetric F).ρ (L z)) (hL : ∀ z, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → L z ≠ 0)
    (P0 P : Ideal (MRing ι)) : IsSemipositiveRel P0 P A := by
  have hsm : ∀ z, L z ≠ 0 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fsMetric F).ρ (L z) := fun z hz =>
    (isSmoothMetric_fs (J := F) (L z) hz).contDiffAt (isOpen_ne.mem_nhds hz)
  refine ⟨?_, fun z hz w _ => ?_⟩
  · unfold IsSmoothHerm
    rw [hA]
    intro z hz
    exact ((hsm z (hL z hz)).comp z (L.restrictScalars ℝ).contDiff.contDiffAt).contDiffWithinAt
  · have hz0 := hL z hz.1
    have hlog : ContDiffAt ℝ 2 (fun x => Real.log ((fsMetric F).ρ x)) (L z) :=
      ((hsm z hz0).of_le (WithTop.coe_le_coe.2 le_top)).log ((fsMetric F).pos _ hz0).ne'
    rw [show (fun z => Real.log (A.h z)) = fun y => (fun x => Real.log ((fsMetric F).ρ x)) (L y) by rw [hA]]
    rw [leviForm_comp_clm L hlog w]
    exact leviForm_log_fs_nonneg hz0 _

def matCLM {κ J : Type} [Fintype κ] [Fintype J] (N : Matrix κ J ℤ) : (J → ℂ) →L[ℂ] (κ → ℂ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin (N.map (Int.cast : ℤ → ℂ)))

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[matCLM, Matrix.mulVec, dotProduct]`.
-/
theorem matCLM_apply {κ J : Type} [Fintype κ] [Fintype J] (N : Matrix κ J ℤ) (u : J → ℂ) :
    matCLM N u = fun i => ∑ j, (N i j : ℂ) * u j := by
  funext i
  simp [matCLM, Matrix.mulVec, dotProduct]

def blockCLM {K : Type} {ι : K → Type} (k₀ : K) : ((Σ k, ι k) → ℂ) →L[ℂ] (ι k₀ → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (⟨k₀, i⟩ : Σ k, ι k)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blockCLM_apply {K : Type} {ι : K → Type} (k₀ : K) (z : (Σ k, ι k) → ℂ) :
    blockCLM k₀ z = fun i => z ⟨k₀, i⟩ := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `κ J _ _ N hN P`. Use `isSemipositiveRel_of_linear _ (matCLM N) ?_ ?_ ⊥ P` and prove the remaining obligations. Use function extensionality and compare the values at `u`. Rewrite using `[matCLM_apply]`.

Both sides reduce to the same expression. Introduce `z hz h0`. Rewrite `h0` using `[matCLM_apply]`. Take `⟨i, hi⟩` from `hz ()`. Conclude with `hi (congrFun (hN z h0) _)`.

Introduce `K _ _ ι _ k₀ P`. Use `isSemipositiveRel_of_linear _ (blockCLM k₀) ?_ ?_ ⊥ P` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Rewrite using `[blockCLM_apply]`. Simplify using `only [HermLine.ofMetrics]`.

Rewrite using `[Finset.prod_eq_single k₀ (fun k _ hk => by simp [unitDeg, hk]) (by simp)]`. Simplify using `[unitDeg]`. Introduce `z hz h0`. Take `⟨i, hi⟩` from `hz k₀`. Conclude with `hi (congrFun h0 i)`.
-/
theorem proof : BlockImageMetrics.Statement := by
  constructor
  · intro κ J _ _ N hN P
    refine isSemipositiveRel_of_linear _ (matCLM N) ?_ ?_ ⊥ P
    · funext u
      rw [matCLM_apply]
      rfl
    · intro z hz h0
      rw [matCLM_apply] at h0
      obtain ⟨i, hi⟩ := hz ()
      exact hi (congrFun (hN z h0) _)
  · intro K _ _ ι _ k₀ P
    refine isSemipositiveRel_of_linear _ (blockCLM k₀) ?_ ?_ ⊥ P
    · funext z
      rw [blockCLM_apply]
      simp only [HermLine.ofMetrics]
      rw [Finset.prod_eq_single k₀ (fun k _ hk => by simp [unitDeg, hk]) (by simp)]
      simp [unitDeg]
    · intro z hz h0
      obtain ⟨i, hi⟩ := hz k₀
      exact hi (congrFun h0 i)

end BlockImageMetrics

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
