import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartSheetCompare
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreSheetFormCompare
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreSheetFormCompare
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm pot segre)
open ComplexSets Matrix Filter Topology

namespace SegreChartSheetComparison

/- English proof (translation)
Unfold `ReciprocityTheory.AnForm.hessC`. Rewrite using `[(h.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]`.
-/
theorem hessC_congr_germ {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : f =ᶠ[𝓝 y] g) :
    ReciprocityTheory.AnForm.hessC f y = ReciprocityTheory.AnForm.hessC g y := by
  unfold ReciprocityTheory.AnForm.hessC
  rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish `hle : segreChartIdeal P σ i ≤ J` using `(mem_segreChartComponents.1 hJ).1.2`. Use function extensionality and compare the values at `a`. Use `set q : MvPolynomial (Fin m) ℂ := MvPolynomial.X a - ∏ k, MvPolynomial.X (σ.symm (Function.update i k (σ a k))) with hq`. Establish `heval : ∀ w : Fin m → ℂ, MvPolynomial.eval w q = w a - segre (chartLift σ i w) (σ a)` using `fun w => by`. Simplify using `[hq, segre, chartLift, map_prod]`.

Establish `hmem : q ∈ segreChartIdeal P σ i`. Rewrite using `[segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]`. Introduce and unpack `_ ⟨z, -, hzi, rfl⟩`. Use `show MvPolynomial.eval _ q = 0`. Rewrite using `[heval, segre_chartLift σ i z hzi, sub_self]`.

Establish `h` using `hx q (hle hmem)`. Rewrite `h` using `[heval]`. Conclude with `sub_eq_zero.1 h`.
-/
theorem eq_segre_chartLift {P : Ideal (MRing ι)} {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ segreChartComponents P σ i)
    {x : Fin m → ℂ} (hx : x ∈ zeroSet J) : x = fun a => segre (chartLift σ i x) (σ a) := by
  have hle : segreChartIdeal P σ i ≤ J := (mem_segreChartComponents.1 hJ).1.2
  funext a
  set q : MvPolynomial (Fin m) ℂ := MvPolynomial.X a -
    ∏ k, MvPolynomial.X (σ.symm (Function.update i k (σ a k))) with hq
  have heval : ∀ w : Fin m → ℂ, MvPolynomial.eval w q = w a - segre (chartLift σ i w) (σ a) := fun w => by
    simp [hq, segre, chartLift, map_prod]
  have hmem : q ∈ segreChartIdeal P σ i := by
    rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, -, hzi, rfl⟩
    show MvPolynomial.eval _ q = 0
    rw [heval, segre_chartLift σ i z hzi, sub_self]
  have h := hx q (hle hmem)
  rw [heval] at h
  exact sub_eq_zero.1 h

end SegreChartSheetComparison

open SegreChartSheetComparison in

/- English proof (translation)
Introduce `K _ _ ι _ P e m σ i L hL`. Take `⟨C, hC⟩` from `hF K ι e L hL`. Use `⟨|C|, fun J hJ A x s hx hs => ?_⟩` and prove the remaining obligations. Take `⟨U, hU, hyU, hsd, hsx, hsU, -⟩` from `hs`. Use `set z : (Fin e → ℂ) → (Σ k, ι k) → ℂ := chartLift σ i ∘ s with hzdef`.

Establish `hz : DifferentiableOn ℂ z U` using `differentiableOn_pi.2 fun p => (differentiableOn_pi.1 hsd) (σ.symm (Function.update i p.1 p.2))`. Establish `hblk : ∀ k, ∃ j, z (A *ᵥ x) ⟨k, j⟩ ≠ 0`. Establish `h1 : s (A *ᵥ x) (σ.symm i) = 1` using `by rw [hsx]; exact chart_coord_eq_one hJ hx`. Conclude with `chartLift_blockNonzero σ i h1`. Establish `h1` using `hC z U (A *ᵥ x) hU hyU hz hblk`.

Establish `hfs : (fun w => Real.log ((HermNorm.std m).dualNorm w)) ∘ s =ᶠ[𝓝 (A *ᵥ x)] (fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z` using `by filter_upwards [hU.mem_nhds hyU] with y' hy'`. Establish `he` using `eq_segre_chartLift hJ (hsU y' hy').2`. Simplify using `only [Function.comp_apply, hzdef]`. Use `congr 1`. Establish `hd : (HermNorm.std m).dualNorm (s y') = √(∑ a, ‖s y' a‖ ^ 2)`.

Simplify using `[HermNorm.dualNorm, HermNorm.std]`. Rewrite using `[hd]`. Use `congr 1`. Use `conv_lhs => rw [he]`. Conclude with `Equiv.sum_comp σ (fun i' => ‖segre (chartLift σ i (s y')) i'‖ ^ 2)`.

Establish `hden : ReciprocityTheory.AnForm.maDens (fun _ => (fun w => Real.log ((HermNorm.std m).dualNorm w)) ∘ s) (A *ᵥ x) = ReciprocityTheory.AnForm.maDens (fun _ => (fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z) (A *ᵥ x)`. Unfold `ReciprocityTheory.AnForm.maDens`. Simplify using `only`. Rewrite using `[hessC_congr_germ hfs]`. Establish `hpot : (fun k => chartPot σ i L k ∘ s) = fun j => pot L j ∘ z` using `rfl`.

Rewrite using `[hpot, hden]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem SegreChartSheetCompare.of_segreSheetFormCompare (hF : SegreSheetFormCompare.Statement) :
    SegreChartSheetCompare.Statement := by
  intro K _ _ ι _ P e m σ i L hL
  obtain ⟨C, hC⟩ := hF K ι e L hL
  refine ⟨|C|, fun J hJ A x s hx hs => ?_⟩
  obtain ⟨U, hU, hyU, hsd, hsx, hsU, -⟩ := hs
  set z : (Fin e → ℂ) → (Σ k, ι k) → ℂ := chartLift σ i ∘ s with hzdef
  have hz : DifferentiableOn ℂ z U :=
    differentiableOn_pi.2 fun p => (differentiableOn_pi.1 hsd) (σ.symm (Function.update i p.1 p.2))
  have hblk : ∀ k, ∃ j, z (A *ᵥ x) ⟨k, j⟩ ≠ 0 := by
    have h1 : s (A *ᵥ x) (σ.symm i) = 1 := by rw [hsx]; exact chart_coord_eq_one hJ hx
    exact chartLift_blockNonzero σ i h1
  have h1 := hC z U (A *ᵥ x) hU hyU hz hblk
  have hfs : (fun w => Real.log ((HermNorm.std m).dualNorm w)) ∘ s =ᶠ[𝓝 (A *ᵥ x)]
      (fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z := by
    filter_upwards [hU.mem_nhds hyU] with y' hy'
    have he := eq_segre_chartLift hJ (hsU y' hy').2
    simp only [Function.comp_apply, hzdef]
    congr 1
    have hd : (HermNorm.std m).dualNorm (s y') = √(∑ a, ‖s y' a‖ ^ 2) := by
      simp [HermNorm.dualNorm, HermNorm.std]
    rw [hd]
    congr 1
    conv_lhs => rw [he]
    exact Equiv.sum_comp σ (fun i' => ‖segre (chartLift σ i (s y')) i'‖ ^ 2)
  have hden : ReciprocityTheory.AnForm.maDens
      (fun _ => (fun w => Real.log ((HermNorm.std m).dualNorm w)) ∘ s) (A *ᵥ x) =
      ReciprocityTheory.AnForm.maDens (fun _ => (fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z)
        (A *ᵥ x) := by
    unfold ReciprocityTheory.AnForm.maDens
    dsimp only
    rw [hessC_congr_germ hfs]
  have hpot : (fun k => chartPot σ i L k ∘ s) = fun j => pot L j ∘ z := rfl
  rw [hpot, hden]
  calc _ ≤ _ := h1
    _ ≤ |C * ReciprocityTheory.AnForm.maDens
          (fun _ => (fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z) (A *ᵥ x)| := le_abs_self _
    _ = _ := abs_mul _ _

/- English proof (translation)
The claim follows from `SegreChartSheetCompare.of_segreSheetFormCompare SegreSheetFormCompare.proof`.
-/
theorem SegreChartSheetCompare.proof : SegreChartSheetCompare.Statement :=
  SegreChartSheetCompare.of_segreSheetFormCompare SegreSheetFormCompare.proof

end GroundTheory.Heights₂.Heights
