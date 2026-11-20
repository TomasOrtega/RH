import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidFactorizationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenvalueAdjointFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowMatrixStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelAdjointSmoothStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateSobolevStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateCommutesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowLeftInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelActionFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveRepresentationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveUniquenessStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiResolventIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveIntegralIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowSupportStatement

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `: Continuous f ∧ Tendsto f (cocompact ℝ) (𝓝 0)` using `⟨h₁, h₂⟩`. Simplify using `only [toC0]`. Rewrite using `[dif_pos this]`. Both sides reduce to the same expression.
-/
theorem coe_toC0 {f : ℝ → ℂ} (h₁ : Continuous f) (h₂ : Tendsto f (cocompact ℝ) (𝓝 0)) (y : ℝ) : toC0 f y = f y := by
  have : Continuous f ∧ Tendsto f (cocompact ℝ) (𝓝 0) := ⟨h₁, h₂⟩
  simp only [toC0]
  rw [dif_pos this]
  rfl

/- English proof (translation)
Establish `hmul : ∀ v, E.ρ k (E.ρ k⁻¹ v) = v` using `fun v => by`. Use `congrArg (fun L : E.V →L[ℂ] E.V => L v) (E.ρ.map_mul k k⁻¹)` as an intermediate fact. Simplify using `using this.symm`. Establish `hmul' : ∀ v, E.ρ k⁻¹ (E.ρ k v) = v` using `fun v => by`. Use `congrArg (fun L : E.V →L[ℂ] E.V => L v) (E.ρ.map_mul k⁻¹ k)` as an intermediate fact.

Simplify using `using this.symm`. Set `I : E.V →ₗᵢ[ℂ] E.V` to `⟨(E.ρ k).toLinearMap, fun v => E.iso k v⟩`. Use extensionality with `v`. Use `ext_inner_right ℂ fun w => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.adjoint_inner_left]`.

Use `I.inner_map_map v (E.ρ k⁻¹ w)` as an intermediate fact. Establish `e : ∀ z, I z = E.ρ k z` using `fun _ => rfl`. Rewrite `this` using `[e, e, hmul]`. Conclude with `this.symm`.
-/
theorem adj_rho {n : ℕ} (E : KMod n) [CompleteSpace E.V] (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ContinuousLinearMap.adjoint (E.ρ k⁻¹) = E.ρ k := by
  have hmul : ∀ v, E.ρ k (E.ρ k⁻¹ v) = v := fun v => by
    have := congrArg (fun L : E.V →L[ℂ] E.V => L v) (E.ρ.map_mul k k⁻¹)
    simpa using this.symm
  have hmul' : ∀ v, E.ρ k⁻¹ (E.ρ k v) = v := fun v => by
    have := congrArg (fun L : E.V →L[ℂ] E.V => L v) (E.ρ.map_mul k⁻¹ k)
    simpa using this.symm
  let I : E.V →ₗᵢ[ℂ] E.V := ⟨(E.ρ k).toLinearMap, fun v => E.iso k v⟩
  ext v
  refine ext_inner_right ℂ fun w => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  have := I.inner_map_map v (E.ρ k⁻¹ w)
  have e : ∀ z, I z = E.ρ k z := fun _ => rfl
  rw [e, e, hmul] at this
  exact this.symm

/- English proof (translation)
Introduce `n _ _ μ _ E g T₀ hb hLg hUn hRC hSG hAE hWS hWC hCS hSO hPW`. Use `haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V`. Take `⟨hAbsFC, hAbsCut, hFc, hWv, hCls, hSobOps, hCptSob, hSB, hPres, hConc, hCJ, hFr, hOmF, hIbp, hDD⟩` from `id hCS`. Take `⟨hMrep, Ω, T, hDense, hSym, hEx, hLeft, hOm⟩` from `hConc n μ E.V hLg hUn hRC hSG hPres hFr hCls hSobOps hCptSob hOmF hIbp hDD`. Take `⟨F⟩` from `hAbsFC _ _ Ω T hDense hSym hEx hLeft`.

Take `⟨c, hc⟩` from `hSB n μ E hLg hUn hRC`. Establish `hStd : Std μ E F c` using `⟨hLg, hUn, hRC, hSG, hAE, hWS, hWC, hCS, hSO, hPW, hMrep, hSym, hEx, hLeft, hOm, hc⟩`. Establish `hPW1` using `(hPW c g T₀ hb).1`. Establish `hPW2` using `(hPW c g T₀ hb).2`. Establish `hC0 : ∀ y, toC0 (hg c g) y = hg c g y` using `fun y => by`.

Use `hPW1 0` as an intermediate fact. Simplify using `only [pow_zero, one_mul] at this`. Conclude with `coe_toC0 this.1 (by simpa using this.2) y`. Establish `hR : Rapid (toC0 (hg c g))` using `fun m => ⟨toC0 (fun y : ℝ => (y : ℂ) ^ m * hg c g y), fun y => by`. Rewrite using `[coe_toC0 (hPW1 m).1 (hPW1 m).2, hC0]⟩`.

Take `⟨A, hA⟩` from `hRM n μ E Ω T F c hStd _ (hFR n μ E Ω T F c hStd _ hR)`. Establish `hWV : ∀ f ∈ CE E, Cpt f → ∀ u, IsWave E u → (∀ x ∈ GLs n, u 0 x = f x) → ∀ f', Sob μ f' → IsSec E f' → cls μ f' = F.Φ (toC0 (hg c g)) (cls μ f) → ∀ x ∈ GLs n, ∫ t, (g t : ℂ) • u t x = f' x`. Introduce `f hf hcpt u hu h0 f' hs _ hcl x hx`. Take `⟨N, b, U, hN, hT, hUw, hU0, hUt⟩` from `hWR n μ E Ω T F c hStd f hf hcpt`. Establish `huU : ∀ t, u t x = U t x` using `fun t => hWU hWS hCS hRC n E u U hu hUw (fun y hy => by rw [h0 y hy, hU0 y hy]) t x hx`.

Establish `hcl' : cls μ f' = F.Φ (toC0 (fun y => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * hg c g y)) b`. Rewrite using `[hPR n μ E Ω T F c hStd g T₀ hb N hN, hcl, ← hT]`. Both sides reduce to the same expression. Use `hWI n μ E Ω T F c hStd g T₀ hb N b U hN hUw hUt f' hs hcl' x hx` as an intermediate fact. Simplify `this` using `only [huU]`.

Take `⟨R, hRsup⟩` from `hSR n μ E Ω T F c hStd g T₀ _ hb hR hWV`. Establish `hKdef : ∀ k : Matrix.unitaryGroup (Fin n) ℂ, ∀ y ∈ GLs n, A (y * k.1) = E.ρ k⁻¹ * A y`. Introduce `k y hy`. Use extensionality with `v`. Conclude with `(hA v).2.1 y hy k`.

Establish `hkG : ∀ k : Matrix.unitaryGroup (Fin n) ℂ, ∀ y ∈ GLs n, k.1 * y ∈ GLs n`. Introduce `k y hy`. Establish `hk : (k.1 : Mat n).det ≠ 0` using `(Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.1 k.2)).ne_zero`. Simplify using `only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at hy ⊢`. Conclude with `mul_ne_zero hk hy`.

Use `⟨fun y => ContinuousLinearMap.adjoint (A y), hAS _ _ A _ fun v => (hA v).1.1, ⟨R, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy hl`. Establish `: A y = 0`. Use extensionality with `v`. Conclude with `hRsup v _ (hA v) y hy hl`.

Simplify using `[this]`. Introduce `y hy k₁ k₂`. Establish `e1 : A (k₁.1 * y * k₂.1) = E.ρ k₂⁻¹ * A (k₁.1 * y)` using `hKdef k₂ _ (hkG k₁ y hy)`. Establish `e2 : A (k₁.1 * y) = A y * E.ρ k₁⁻¹`. Use extensionality with `v`.

Conclude with `hRL n μ E Ω T F c hStd _ A hR hA k₁ y hy v`. Use `show ContinuousLinearMap.adjoint (A (k₁.1 * y * k₂.1)) = _`. Rewrite using `[e1, e2]`. Simplify using `only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.mul_def, adj_rho]`. Introduce `f hf hcpt u hu h0 x hx`.

Establish `hSf : Sob μ f` using `(hCptSob n μ E.V hLg hRC f hf.1 hcpt).1`. Take `⟨C, hC⟩` from `hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm (toC0 (hg c g)) hR`. Take `⟨f', hf's, hf'e, hf'c, -⟩` from `hC (cls μ f) (subset_closure ⟨f, hSf, hf.2, rfl⟩)`. Rewrite using `[hAF n μ E Ω T F c hStd _ A hA f hf hcpt f' hf's hf'e hf'c x hx, hWV f hf hcpt u hu h0 f' hf's hf'e hf'c x hx]`.
-/
theorem kerCore_of (hFR : RowExists) (hRM : RowMatrix) (hAS : AdjSmooth) (hRL : RowLeft) (hAF : ActFormula)
    (hWR : WaveRep) (hWU : WaveUniq) (hPR : PhiRes) (hWI : WaveInt) (hSR : SupportRow) : KerCore := by
  intro n _ _ μ _ E g T₀ hb hLg hUn hRC hSG hAE hWS hWC hCS hSO hPW
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  obtain ⟨hAbsFC, hAbsCut, hFc, hWv, hCls, hSobOps, hCptSob, hSB, hPres, hConc, hCJ, hFr, hOmF, hIbp, hDD⟩ := id hCS
  obtain ⟨hMrep, Ω, T, hDense, hSym, hEx, hLeft, hOm⟩ :=
    hConc n μ E.V hLg hUn hRC hSG hPres hFr hCls hSobOps hCptSob hOmF hIbp hDD
  obtain ⟨F⟩ := hAbsFC _ _ Ω T hDense hSym hEx hLeft
  obtain ⟨c, hc⟩ := hSB n μ E hLg hUn hRC
  have hStd : Std μ E F c :=
    ⟨hLg, hUn, hRC, hSG, hAE, hWS, hWC, hCS, hSO, hPW, hMrep, hSym, hEx, hLeft, hOm, hc⟩
  have hPW1 := (hPW c g T₀ hb).1
  have hPW2 := (hPW c g T₀ hb).2
  have hC0 : ∀ y, toC0 (hg c g) y = hg c g y := fun y => by
    have := hPW1 0
    simp only [pow_zero, one_mul] at this
    exact coe_toC0 this.1 (by simpa using this.2) y
  have hR : Rapid (toC0 (hg c g)) := fun m =>
    ⟨toC0 (fun y : ℝ => (y : ℂ) ^ m * hg c g y), fun y => by
      rw [coe_toC0 (hPW1 m).1 (hPW1 m).2, hC0]⟩
  obtain ⟨A, hA⟩ := hRM n μ E Ω T F c hStd _ (hFR n μ E Ω T F c hStd _ hR)
  have hWV : ∀ f ∈ CE E, Cpt f → ∀ u, IsWave E u → (∀ x ∈ GLs n, u 0 x = f x) → ∀ f', Sob μ f' → IsSec E f' →
      cls μ f' = F.Φ (toC0 (hg c g)) (cls μ f) → ∀ x ∈ GLs n, ∫ t, (g t : ℂ) • u t x = f' x := by
    intro f hf hcpt u hu h0 f' hs _ hcl x hx
    obtain ⟨N, b, U, hN, hT, hUw, hU0, hUt⟩ := hWR n μ E Ω T F c hStd f hf hcpt
    have huU : ∀ t, u t x = U t x := fun t =>
      hWU hWS hCS hRC n E u U hu hUw (fun y hy => by rw [h0 y hy, hU0 y hy]) t x hx
    have hcl' : cls μ f' = F.Φ (toC0 (fun y => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * hg c g y)) b := by
      rw [hPR n μ E Ω T F c hStd g T₀ hb N hN, hcl, ← hT]
      rfl
    have := hWI n μ E Ω T F c hStd g T₀ hb N b U hN hUw hUt f' hs hcl' x hx
    simpa only [huU] using this
  obtain ⟨R, hRsup⟩ := hSR n μ E Ω T F c hStd g T₀ _ hb hR hWV
  have hKdef : ∀ k : Matrix.unitaryGroup (Fin n) ℂ, ∀ y ∈ GLs n, A (y * k.1) = E.ρ k⁻¹ * A y := by
    intro k y hy
    ext v
    exact (hA v).2.1 y hy k
  have hkG : ∀ k : Matrix.unitaryGroup (Fin n) ℂ, ∀ y ∈ GLs n, k.1 * y ∈ GLs n := by
    intro k y hy
    have hk : (k.1 : Mat n).det ≠ 0 :=
      (Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.1 k.2)).ne_zero
    simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at hy ⊢
    exact mul_ne_zero hk hy
  refine ⟨fun y => ContinuousLinearMap.adjoint (A y), hAS _ _ A _ fun v => (hA v).1.1, ⟨R, ?_⟩, ?_, ?_⟩
  · intro y hy hl
    have : A y = 0 := by
      ext v
      exact hRsup v _ (hA v) y hy hl
    simp [this]
  · intro y hy k₁ k₂
    have e1 : A (k₁.1 * y * k₂.1) = E.ρ k₂⁻¹ * A (k₁.1 * y) := hKdef k₂ _ (hkG k₁ y hy)
    have e2 : A (k₁.1 * y) = A y * E.ρ k₁⁻¹ := by
      ext v
      exact hRL n μ E Ω T F c hStd _ A hR hA k₁ y hy v
    show ContinuousLinearMap.adjoint (A (k₁.1 * y * k₂.1)) = _
    rw [e1, e2]
    simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.mul_def, adj_rho]
  · intro f hf hcpt u hu h0 x hx
    have hSf : Sob μ f := (hCptSob n μ E.V hLg hRC f hf.1 hcpt).1
    obtain ⟨C, hC⟩ := hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm (toC0 (hg c g)) hR
    obtain ⟨f', hf's, hf'e, hf'c, -⟩ := hC (cls μ f) (subset_closure ⟨f, hSf, hf.2, rfl⟩)
    rw [hAF n μ E Ω T F c hStd _ A hA f hf hcpt f' hf's hf'e hf'c x hx,
      hWV f hf hcpt u hu h0 f' hf's hf'e hf'c x hx]

/- English proof (translation)
The claim follows from `have hLC := GlobalTheory.T.left_translate_commutes GlobalTheory.T.left_translate_sobolev kerCore_of (GlobalTheory.T.kernel_row_exists GlobalTheory.T.rapid_factorization GlobalTheory.T.eigenvalue_adjoint_facts) GlobalTheory.T.kernel_row_matrix GlobalTheory.T.kernel_adjoint_smooth …`.
-/
theorem kerCore : KerCore :=
  have hLC := GlobalTheory.T.left_translate_commutes GlobalTheory.T.left_translate_sobolev
  kerCore_of (GlobalTheory.T.kernel_row_exists GlobalTheory.T.rapid_factorization GlobalTheory.T.eigenvalue_adjoint_facts) GlobalTheory.T.kernel_row_matrix GlobalTheory.T.kernel_adjoint_smooth
    (GlobalTheory.T.kernel_row_left_invariant GlobalTheory.T.left_translate_sobolev hLC) (GlobalTheory.T.kernel_action_formula GlobalTheory.T.left_translate_sobolev hLC) GlobalTheory.T.wave_representation GlobalTheory.T.wave_uniqueness GlobalTheory.T.phi_resolvent_identity
    GlobalTheory.T.wave_integral_identity GlobalTheory.T.kernel_row_support

end GlobalTheory.CompanionTheory.KerFc
