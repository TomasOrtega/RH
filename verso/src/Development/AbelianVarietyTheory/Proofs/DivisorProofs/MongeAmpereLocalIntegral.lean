import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff

namespace GlobalTheory

/- English proof (translation)
Establish `hs : IsOpen (Metric.ball (0 : Fin e → ℂ) r ∩ ψ.symm ⁻¹' O)` using `(ψ.continuousOn_symm.mono hball).isOpen_inter_preimage Metric.isOpen_ball hO`. Establish `himg : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (ψ.symm '' Metric.ball (0 : Fin e → ℂ) r ∩ O) = (A.chart j ∘ ψ.symm) '' (Metric.ball (0 : Fin e → ℂ) r ∩ ψ.symm ⁻¹' O)`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy, ⟨z, hz, hzy⟩, hyO⟩`.

Use `⟨z, ⟨hz, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show ψ.symm z ∈ O`. Rewrite using `[hzy]`. Conclude with `hyO`. Simplify using `only [Function.comp_apply]`.

Rewrite using `[hzy, (A.chart j).right_inv hy]`. Introduce and unpack `⟨z, ⟨hz, hzO⟩, rfl⟩`. Establish `h1 : (A.chart j).symm (A.chart j (ψ.symm z)) = ψ.symm z` using `(A.chart j).left_inv (hsrc z hz)`. Use `⟨(A.chart j).map_source (hsrc z hz), ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Set.mem_preimage]`.

Rewrite using `[h1]`. Conclude with `⟨⟨z, hz, rfl⟩, hzO⟩`. Establish `han : AnalyticOnNhd ℂ (A.chart j ∘ ψ.symm) (Metric.ball (0 : Fin e → ℂ) r ∩ ψ.symm ⁻¹' O)` using `fun z hz => (hψ j).2 z ⟨hball hz.1, hsrc z hz.1⟩`. Establish `hinj : Set.InjOn (A.chart j ∘ ψ.symm) (Metric.ball (0 : Fin e → ℂ) r ∩ ψ.symm ⁻¹' O)`. Introduce `z hz z' hz' h`.

Establish `h1 : ψ.symm z = ψ.symm z'` using `(A.chart j).injOn (hsrc z hz.1) (hsrc z' hz'.1) h`. Conclude with `ψ.symm.injOn (hball hz.1) (hball hz'.1) h1`. Rewrite using `[himg, ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul _ _ hs han hinj]`. Use `le_of_eq (setLIntegral_congr_fun hs.measurableSet fun z hz => ?_)` and prove the remaining obligations. Establish `h1 : (A.chart j).symm (A.chart j (ψ.symm z)) = ψ.symm z` using `(A.chart j).left_inv (hsrc z hz.1)`.

Establish `hTz : (A.chart j ∘ ψ.symm) z ∈ (A.chart j).target` using `(A.chart j).map_source (hsrc z hz.1)`. Establish `hc : ContDiffAt ℝ 2 (P.φ (ψ.symm z) ∘ (A.chart j).symm) ((A.chart j ∘ ψ.symm) z)`. Establish `hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U (ψ.symm z) ∩ O) ∈ nhds ((A.chart j ∘ ψ.symm) z)`. Use `((A.chart j).isOpen_inter_preimage_symm ((P.isOpen_U _).inter hO)).mem_nhds ⟨hTz, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Set.mem_preimage]`.

Rewrite using `[h1]`. Conclude with `⟨P.mem_U _, hz.2⟩`. Conclude with `((hP.1 (ψ.symm z) j).contDiffAt hmem).of_le (WithTop.coe_le_coe.2 le_top)`. Establish `hev : (P.φ (ψ.symm z) ∘ ψ.symm) =ᶠ[nhds z] (P.φ (ψ.symm z) ∘ (A.chart j).symm) ∘ (A.chart j ∘ ψ.symm)` using `by filter_upwards [Metric.isOpen_ball.mem_nhds hz.1] with w hw`. Simplify using `only [Function.comp_apply, (A.chart j).left_inv (hsrc w hw)]`.

Establish `h2 : maDens (fun _ => P.φ (ψ.symm z) ∘ ψ.symm) z = maDens (fun _ => P.φ (ψ.symm z) ∘ (A.chart j).symm) ((A.chart j ∘ ψ.symm) z) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC (A.chart j ∘ ψ.symm) z).det` using `(maDens_congr_eventuallyEq (fun _ => hev)).trans (ReciprocityTheory.AnForm.A.maDens_comp (fun _ => P.φ (ψ.symm z) ∘ (A.chart j).symm) (A.chart j ∘ ψ.symm) z (han z hz) (fun _ => hc))`. Establish `h3 : locDens A (fun _ => P) j ((A.chart j ∘ ψ.symm) z) = maDens (fun _ => P.φ (ψ.symm z) ∘ (A.chart j).symm) ((A.chart j ∘ ψ.symm) z)`. Unfold `locDens`. Establish `h4 : (A.chart j).symm ((A.chart j ∘ ψ.symm) z) = ψ.symm z` using `h1`. Rewrite using `[h4]`.

Both sides reduce to the same expression. Use `show _ = ENNReal.ofReal (maDens (fun _ => P.φ (ψ.symm z) ∘ ψ.symm) z)`. Rewrite using `[h2, h3, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm]`.
-/
theorem lintegral_locDens_le_compatChart {e : ℕ} {X : Type} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (P : LocPot X) (O : Set X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (j : Fin A.n) (r : ℝ) (hO : IsOpen O)
    (hP : IsPotentialOn A O P) (hψ : IsCompatChart A ψ)
    (hball : Metric.ball (0 : Fin e → ℂ) r ⊆ ψ.target)
    (hsrc : ∀ z ∈ Metric.ball (0 : Fin e → ℂ) r, ψ.symm z ∈ (A.chart j).source) :
    ∫⁻ y in (A.chart j).target ∩
        (A.chart j).symm ⁻¹' (ψ.symm '' Metric.ball (0 : Fin e → ℂ) r ∩ O),
        ENNReal.ofReal (locDens A (fun _ => P) j y) ≤
      ∫⁻ z in Metric.ball (0 : Fin e → ℂ) r ∩ ψ.symm ⁻¹' O,
        ENNReal.ofReal (maDens (fun _ => P.φ (ψ.symm z) ∘ ψ.symm) z) := by
  have hs : IsOpen (Metric.ball (0 : Fin e → ℂ) r ∩ ψ.symm ⁻¹' O) :=
    (ψ.continuousOn_symm.mono hball).isOpen_inter_preimage Metric.isOpen_ball hO
  have himg : (A.chart j).target ∩
      (A.chart j).symm ⁻¹' (ψ.symm '' Metric.ball (0 : Fin e → ℂ) r ∩ O) =
      (A.chart j ∘ ψ.symm) '' (Metric.ball (0 : Fin e → ℂ) r ∩ ψ.symm ⁻¹' O) := by
    ext y
    constructor
    · rintro ⟨hy, ⟨z, hz, hzy⟩, hyO⟩
      refine ⟨z, ⟨hz, ?_⟩, ?_⟩
      · show ψ.symm z ∈ O
        rw [hzy]; exact hyO
      · simp only [Function.comp_apply]
        rw [hzy, (A.chart j).right_inv hy]
    · rintro ⟨z, ⟨hz, hzO⟩, rfl⟩
      have h1 : (A.chart j).symm (A.chart j (ψ.symm z)) = ψ.symm z :=
        (A.chart j).left_inv (hsrc z hz)
      refine ⟨(A.chart j).map_source (hsrc z hz), ?_⟩
      simp only [Function.comp_apply, Set.mem_preimage]
      rw [h1]
      exact ⟨⟨z, hz, rfl⟩, hzO⟩
  have han : AnalyticOnNhd ℂ (A.chart j ∘ ψ.symm)
      (Metric.ball (0 : Fin e → ℂ) r ∩ ψ.symm ⁻¹' O) :=
    fun z hz => (hψ j).2 z ⟨hball hz.1, hsrc z hz.1⟩
  have hinj : Set.InjOn (A.chart j ∘ ψ.symm)
      (Metric.ball (0 : Fin e → ℂ) r ∩ ψ.symm ⁻¹' O) := by
    intro z hz z' hz' h
    have h1 : ψ.symm z = ψ.symm z' := (A.chart j).injOn (hsrc z hz.1) (hsrc z' hz'.1) h
    exact ψ.symm.injOn (hball hz.1) (hball hz'.1) h1
  rw [himg, ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul _ _ hs han hinj]
  refine le_of_eq (setLIntegral_congr_fun hs.measurableSet fun z hz => ?_)
  have h1 : (A.chart j).symm (A.chart j (ψ.symm z)) = ψ.symm z :=
    (A.chart j).left_inv (hsrc z hz.1)
  have hTz : (A.chart j ∘ ψ.symm) z ∈ (A.chart j).target := (A.chart j).map_source (hsrc z hz.1)
  have hc : ContDiffAt ℝ 2 (P.φ (ψ.symm z) ∘ (A.chart j).symm) ((A.chart j ∘ ψ.symm) z) := by
    have hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U (ψ.symm z) ∩ O) ∈
        nhds ((A.chart j ∘ ψ.symm) z) := by
      refine ((A.chart j).isOpen_inter_preimage_symm ((P.isOpen_U _).inter hO)).mem_nhds
        ⟨hTz, ?_⟩
      simp only [Function.comp_apply, Set.mem_preimage]
      rw [h1]
      exact ⟨P.mem_U _, hz.2⟩
    exact ((hP.1 (ψ.symm z) j).contDiffAt hmem).of_le (WithTop.coe_le_coe.2 le_top)
  have hev : (P.φ (ψ.symm z) ∘ ψ.symm) =ᶠ[nhds z]
      (P.φ (ψ.symm z) ∘ (A.chart j).symm) ∘ (A.chart j ∘ ψ.symm) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz.1] with w hw
    simp only [Function.comp_apply, (A.chart j).left_inv (hsrc w hw)]
  have h2 : maDens (fun _ => P.φ (ψ.symm z) ∘ ψ.symm) z =
      maDens (fun _ => P.φ (ψ.symm z) ∘ (A.chart j).symm) ((A.chart j ∘ ψ.symm) z) *
        Complex.normSq (ReciprocityTheory.AnForm.A.jacC (A.chart j ∘ ψ.symm) z).det :=
    (maDens_congr_eventuallyEq (fun _ => hev)).trans
      (ReciprocityTheory.AnForm.A.maDens_comp (fun _ => P.φ (ψ.symm z) ∘ (A.chart j).symm)
        (A.chart j ∘ ψ.symm) z (han z hz) (fun _ => hc))
  have h3 : locDens A (fun _ => P) j ((A.chart j ∘ ψ.symm) z) =
      maDens (fun _ => P.φ (ψ.symm z) ∘ (A.chart j).symm) ((A.chart j ∘ ψ.symm) z) := by
    unfold locDens
    have h4 : (A.chart j).symm ((A.chart j ∘ ψ.symm) z) = ψ.symm z := h1
    rw [h4]
    rfl
  show _ = ENNReal.ofReal (maDens (fun _ => P.φ (ψ.symm z) ∘ ψ.symm) z)
  rw [h2, h3, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm]

end GlobalTheory
