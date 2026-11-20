import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TrDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.DiagOnly
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.JointTrace

open GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

/- English proof (translation)
Set `e` to `stdOrthonormalBasis ℂ K`. Establish `hP : ∀ x : H, K.starProjection x = ∑ j, ⟪(e j : H), x⟫_ℂ • (e j : H)`. Introduce `x`. Establish `h` using `congrArg (fun v : K => (v : H)) (e.sum_repr' ⟨K.starProjection x, K.starProjection_apply_mem x⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h`.

Rewrite using `[← h]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 (e j).2]`. Establish `h1 : ∀ j, ⟪(e j : H), (e j : H)⟫_ℂ = 1`. Introduce `j`.

Rewrite using `[← Submodule.coe_inner, inner_self_eq_norm_sq_to_K, e.orthonormal.1 j]`. Simplify using the standard rewrite rules. Establish `hs` using `hasSum_sum (s := Finset.univ) (fun j _ => (stdHilbertBasis ℂ H).hasSum_inner_mul_inner (e j : H) (e j : H))`. Simplify using `only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs`. Rewrite using `[← hs.tsum_eq, trace]`.

Use `tsum_congr fun i => ?_` and prove the remaining obligations. Rewrite using `[hP, inner_sum]`. Simplify using `only [inner_smul_right]`.
-/
private theorem trace_starProjection {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] [FiniteDimensional ℂ K] :
    trace K.starProjection = (Module.finrank ℂ K : ℂ) := by
  classical
  let e := stdOrthonormalBasis ℂ K
  have hP : ∀ x : H, K.starProjection x = ∑ j, ⟪(e j : H), x⟫_ℂ • (e j : H) := by
    intro x
    have h := congrArg (fun v : K => (v : H)) (e.sum_repr' ⟨K.starProjection x, K.starProjection_apply_mem x⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 (e j).2]
  have h1 : ∀ j, ⟪(e j : H), (e j : H)⟫_ℂ = 1 := by
    intro j
    rw [← Submodule.coe_inner, inner_self_eq_norm_sq_to_K, e.orthonormal.1 j]
    simp
  have hs := hasSum_sum (s := Finset.univ)
    (fun j _ => (stdHilbertBasis ℂ H).hasSum_inner_mul_inner (e j : H) (e j : H))
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  rw [← hs.tsum_eq, trace]
  refine tsum_congr fun i => ?_
  rw [hP, inner_sum]
  simp only [inner_smul_right]

/- English proof (translation)
Establish `hc : W.topologicalClosure = W` using `W.closed_of_finiteDimensional.submodule_topologicalClosure_eq`. Use `haveI : FiniteDimensional ℂ W.topologicalClosure := by rw [hc]; infer_instance`. Establish `hp : prj W ∘L (1 : H →L[ℂ] H) ∘L prj W = W.topologicalClosure.starProjection`. Use extensionality with `x`. Simplify using `only [prj, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]`.

Conclude with `Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ x)`. Rewrite using `[trOn, hp, trace_starProjection, hc]`.
-/
private theorem trOn_one {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule ℂ H) [FiniteDimensional ℂ W] :
    trOn W 1 = (Module.finrank ℂ W : ℂ) := by
  have hc : W.topologicalClosure = W := W.closed_of_finiteDimensional.submodule_topologicalClosure_eq
  haveI : FiniteDimensional ℂ W.topologicalClosure := by rw [hc]; infer_instance
  have hp : prj W ∘L (1 : H →L[ℂ] H) ∘L prj W = W.topologicalClosure.starProjection := by
    ext x
    simp only [prj, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
    exact Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ x)
  rw [trOn, hp, trace_starProjection, hc]

/- English proof (translation)
Introduce `Γ G H _ _ _ _ _ _ π V m ι E A U hS y hy hfin`. Take `⟨hle, hdiag⟩` from `UpperTheory.ConvolutionTheory.L1.diagOnly Γ G H π V m ι E A U hS y hy hfin`. Use `haveI hfin' : FiniteDimensional ℂ (UpperTheory.ConvolutionTheory.L1.jointEig V E A y) := Submodule.finiteDimensional_of_le hle`. Take `⟨c, hc, htr⟩` from `UpperTheory.ConvolutionTheory.L1.jointTrace Γ G H π V m ι E A U hS y hfin'`. Use `⟨c, hc, ?_, fun i₀ S h1 h2 => (hdiag i₀ S h1).trans (htr i₀ S h1 h2)⟩` and prove the remaining obligations.

Establish `h` using `(hdiag 0 1 fun _ _ _ => rfl).trans (htr 0 1 (fun _ _ _ => rfl) fun _ _ _ _ => rfl)`. Rewrite `h` using `[trOn_one]`. Conclude with `h`.
-/
theorem UpperTheory.ConvolutionTheory.L1.twTrace :
    UpperTheory.ConvolutionTheory.L1.TwTrace := by
  intro Γ G H _ _ _ _ _ _ π V m ι E A U hS y hy hfin
  obtain ⟨hle, hdiag⟩ := UpperTheory.ConvolutionTheory.L1.diagOnly Γ G H π V m ι E A U hS y hy hfin
  haveI hfin' : FiniteDimensional ℂ (UpperTheory.ConvolutionTheory.L1.jointEig V E A y) := Submodule.finiteDimensional_of_le hle
  obtain ⟨c, hc, htr⟩ := UpperTheory.ConvolutionTheory.L1.jointTrace Γ G H π V m ι E A U hS y hfin'
  refine ⟨c, hc, ?_, fun i₀ S h1 h2 => (hdiag i₀ S h1).trans (htr i₀ S h1 h2)⟩
  have h := (hdiag 0 1 fun _ _ _ => rfl).trans (htr 0 1 (fun _ _ _ => rfl) fun _ _ _ _ => rfl)
  rw [trOn_one] at h
  exact h
