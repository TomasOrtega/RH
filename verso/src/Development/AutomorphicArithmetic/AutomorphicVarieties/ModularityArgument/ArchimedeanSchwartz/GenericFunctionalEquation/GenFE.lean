import GroundTheory.AutomorphicForms.GL2.GJStandardL

noncomputable section

open NumberField IsDedekindDomain MeasureTheory NumberField.mixedEmbedding
open GroundTheory.Automorphic GroundTheory.Automorphic.GJStandardL GroundTheory.Automorphic.GodementJacquet GroundTheory.Automorphic.GLnLocal
open scoped SchwartzMap Classical

namespace UpperTheory.V.Z.Inf

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Establish `hn0 : 0 < n` using `by omega`. Use `set μi : Measure (AdelicGLn.InfiniteAdelicGL K n) := Measure.haar with hμi`. Use `set ν : Measure (AdelicGLn.AdelicGL K n) := Measure.haar with hν`. Establish `hfc : Continuous (GJGlobal.matrixCoeff μ φ₁ φ₂)` using `continuous_globalMatrixCoeff hn0 μ h₁ h₂ hA`. Take `⟨σu, hu⟩` from `exists_unramified hn μ h₁ h₂ hA S π ξ ℓ hξ hℓs hsph hℓK (fun v _ ↦ hirr v) (fun v _ ↦ hadm v) z hz fi hf hf0`.

Take `⟨g₀, hg₀⟩` from `hf0`. Establish `hfic : Continuous fi` using `(factor_nonvanishing hfc S π ξ ℓ hsph fi hf hg₀).1`. Establish `hfd` using `inv_factorization π ξ ℓ fi hf`. Establish `hsphd : ∀ v ∉ S, ℓ v ∈ fixedVectors (Representation.dual (π v)) (integralGL (v.adicCompletion K) n) ∧ Module.Dual.eval ℂ (V v) (ξ v) (ℓ v) = 1` using `fun v hv ↦ ⟨hℓK v hv, (hsph v hv).2⟩`. Establish `hfic' : Continuous fun x : AdelicGLn.InfiniteAdelicGL K n ↦ fi x⁻¹` using `hfic.comp continuous_inv`.

Take `⟨C, hC, hFour⟩` from `exists_adelicMatrixFourier_matrixTensor (K := K) (n := n)`. Take `⟨hSB1, hS01⟩` from `tensor_hyps_fourier hRS hSB hS0`. Use `set cE : ℂ := (((prodConst ν μi : ℝ) * finConst K n : ℝ) : ℂ) with hcE`. Establish `hcE0 : cE ≠ 0`. Rewrite using `[hcE]`.

Conclude with `(mul_pos (NNReal.coe_pos.2 (prodConst_pos ν μi)) finConst_pos).ne'` after adjusting the coercions. Use `⟨cE, C * cE, hcE0, mul_ne_zero hC hcE0, hSB1, fun φ ↦ ?_⟩` and prove the remaining obligations. Take `⟨σ₀, Λ, Λ', hΛ, -, hZ, hZ', hfe⟩` from `GJGlobal.globalZeta_entire_functionalEquation hn μ ν h₁ h₂ hA (matrixTensor_mem φ S Φ hSB hS0)`. Use `set s₀ : ℂ := ((max σ₀ σu + 1 : ℝ) : ℂ) with hs₀def`. Establish `hs₀re : s₀.re = max σ₀ σu + 1` using `by rw [hs₀def, Complex.ofReal_re]`.

Take `⟨-, -, -, -, hbp0, -⟩` from `hu s₀ (by rw [hs₀re]; linarith [le_max_right σ₀ σu])`. Use `⟨max σ₀ σu + 3, Λ, hΛ, fun s hs ↦ ?_⟩` and prove the remaining obligations. Establish `hs₀ : σ₀ < s.re` using `by linarith [le_max_left σ₀ σu]`. Establish `hsu : σu < s.re` using `by linarith [le_max_right σ₀ σu]`. Establish `hre : s₀.re + 2 ≤ s.re` using `by rw [hs₀re]; linarith`.

Take `⟨hZp, hLp, hZd, hLd, -, -⟩` from `hu s hsu`. Use `⟨ne_zero_of_hasProd_inv_prod hLp (fun v i ↦ (z v i : ℂ) * qs ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) s) (fun v ↦ ((hbp0 v v.2).2 s)) (summable_residueCard_inv_sq S) (fun v i ↦ norm_mul_qs_le _ ((hbp0 v v.2).1 i) hre) (fun v i ↦ lt_of_le_of_lt (norm_mul_qs_le _ ((hbp0 v v …` and prove the remaining obligations. Take `⟨hint, hΛs⟩` from `hZ s hs₀`. Take `⟨hE, -⟩` from `globalZeta_eq_euler ν μi φ hSB hS0 hξ hsph hfic hf hint`. Establish `hall` using `hasProd_of_hasProd_compl (f := fun v ↦ zetaIntegral (localHaar n v) (Φ v) (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s) S (hLp.congr_fun fun v ↦ by rw [hS0 v v.2]; exact hZp v v.2)`.

Rewrite using `[← hΛs, hE, hall.tprod_eq]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨hint, hΛs⟩` from `hZ' s hs₀`. Rewrite `hint`, `hΛs` using `[hFour φ S Φ hSB hS0]`. Rewrite `hint` using `[zetaIntegrand_smul]`.

Establish `hint3` using `(integrable_const_mul_iff (isUnit_iff_ne_zero.2 hC) _).1 hint`. Establish `hΛ1 : Λ (1 - s) = Λ' s` using `by rw [hfe]; congr 1; ring`. Take `⟨hE, -⟩` from `globalZeta_eq_euler (f := fun g ↦ GJGlobal.matrixCoeff μ φ₁ φ₂ g⁻¹) ν μi _ hSB1 hS01 hℓs hsphd hfic' hfd hint3`. Establish `hall` using `hasProd_of_hasProd_compl (f := fun v ↦ zetaIntegral (localHaar n v) (GJMatrix.localMatrixFourier (GroundTheory.Global.localAdelicChar K v) (Φ v)) (Parabolic.matrixCoeff (F := v.adicCompletion K) (Representation.dual (π v)) (ℓ v) (Module.Dual.eval ℂ (V v) (ξ v))) s) S (hLd.congr_f …`. Establish `h3` using `hS01 v v.2`.

Rewrite using `[h3]`. Conclude with `hZd v v.2)`. Rewrite using `[hΛ1, ← hΛs, GJGlobal.globalZeta, zetaIntegrand_smul, integral_const_mul, ← GJGlobal.globalZeta, hE, hall.tprod_eq]`. Express the relevant statement in the definitionally equal form `_ = C * cE * _ * (∏ v ∈ S, zetaIntegral (localHaar n v) (GJMatrix.localMatrixFourier (GroundTheory.Global.localAdelicChar K v) (Φ v)) (Parabolic.matrixCoeff (F := v.adicCompletion K) (Representation.dual (π v)) (ℓ v) (Module.Dual.eval ℂ (V v) (ξ v))) s) * _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem genFE (hn : 2 ≤ n) (μ : Measure (Reduction.normOneGL K n))
    [μ.IsHaarMeasure] {φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ} (h₁ : φ₁ ∈ AutomorphicForm.cuspForms K n)
    (h₂ : φ₂ ∈ AutomorphicForm.cuspForms K n)
    (hA : ∀ (t : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n),
      φ₁ (Reduction.centralSection K n t * x) = φ₁ x)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hRS : ramifiedPlaces K ⊆ S)
    {V : HeightOneSpectrum (𝓞 K) → Type} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
    (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)) (ξ : ∀ v, V v)
    (ℓ : ∀ v, Module.Dual ℂ (V v)) (hξ : ∀ v, ξ v ∈ smoothVectors (π v))
    (hℓs : ∀ v : HeightOneSpectrum (𝓞 K), ℓ v ∈ smoothVectors (Representation.dual (π v)))
    (hsph : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (integralGL (v.adicCompletion K) n) ∧ ℓ v (ξ v) = 1)
    (hℓK : ∀ v ∉ S, ℓ v ∈ fixedVectors (Representation.dual (π v)) (integralGL (v.adicCompletion K) n))
    (hirr : ∀ v, (π v).IsIrreducible) (hadm : ∀ v, IsAdmissible (π v))
    (z : HeightOneSpectrum (𝓞 K) → Fin n → ℂˣ)
    (hz : ∀ v ∉ S, Spherical.IsSatakeParameter (F := v.adicCompletion K) (π v) (localHaar n v) (z v))
    (fi : AdelicGLn.InfiniteAdelicGL K n → ℂ)
    (hf : ∀ g, GJGlobal.matrixCoeff μ φ₁ φ₂ g = fi (archComp K n g) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)
        (localComp n v g))
    (hf0 : ∃ g, GJGlobal.matrixCoeff μ φ₁ φ₂ g ≠ 0)
    (Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ)
    (hSB : ∀ v ∈ S, IsSchwartzBruhat (Φ v)) (hS0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n) :
    ∃ c c' : ℂ, c ≠ 0 ∧ c' ≠ 0 ∧ (∀ v ∈ S, IsSchwartzBruhat
      (GJMatrix.localMatrixFourier (GroundTheory.Global.localAdelicChar K v) (Φ v))) ∧
      ∀ φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ), ∃ (σ : ℝ) (Λ : ℂ → ℂ), Differentiable ℂ Λ ∧ ∀ s : ℂ, σ < s.re →
        partialL S π s ≠ 0 ∧
        Λ s = c * archZeta Measure.haar φ fi s * (∏ v ∈ S, zetaIntegral (localHaar n v) (Φ v)
          (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s) * partialL S π s ∧
        Λ (1 - s) = c' * archZeta Measure.haar (archMatrixFourier φ) (fun x ↦ fi x⁻¹) s *
          (∏ v ∈ S, zetaIntegral (localHaar n v) (GJMatrix.localMatrixFourier (GroundTheory.Global.localAdelicChar K v) (Φ v))
            (fun g ↦ Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) g⁻¹) s) * dualPartialL S π s := by
  have hn0 : 0 < n := by omega
  set μi : Measure (AdelicGLn.InfiniteAdelicGL K n) := Measure.haar with hμi
  set ν : Measure (AdelicGLn.AdelicGL K n) := Measure.haar with hν
  have hfc : Continuous (GJGlobal.matrixCoeff μ φ₁ φ₂) := continuous_globalMatrixCoeff hn0 μ h₁ h₂ hA
  obtain ⟨σu, hu⟩ := exists_unramified hn μ h₁ h₂ hA S π ξ ℓ hξ hℓs hsph hℓK (fun v _ ↦ hirr v)
    (fun v _ ↦ hadm v) z hz fi hf hf0
  obtain ⟨g₀, hg₀⟩ := hf0
  have hfic : Continuous fi := (factor_nonvanishing hfc S π ξ ℓ hsph fi hf hg₀).1
  have hfd := inv_factorization π ξ ℓ fi hf
  have hsphd : ∀ v ∉ S, ℓ v ∈ fixedVectors (Representation.dual (π v)) (integralGL (v.adicCompletion K) n) ∧
      Module.Dual.eval ℂ (V v) (ξ v) (ℓ v) = 1 := fun v hv ↦ ⟨hℓK v hv, (hsph v hv).2⟩
  have hfic' : Continuous fun x : AdelicGLn.InfiniteAdelicGL K n ↦ fi x⁻¹ := hfic.comp continuous_inv
  obtain ⟨C, hC, hFour⟩ := exists_adelicMatrixFourier_matrixTensor (K := K) (n := n)
  obtain ⟨hSB1, hS01⟩ := tensor_hyps_fourier hRS hSB hS0
  set cE : ℂ := (((prodConst ν μi : ℝ) * finConst K n : ℝ) : ℂ) with hcE
  have hcE0 : cE ≠ 0 := by
    rw [hcE]
    exact_mod_cast (mul_pos (NNReal.coe_pos.2 (prodConst_pos ν μi)) finConst_pos).ne'
  refine ⟨cE, C * cE, hcE0, mul_ne_zero hC hcE0, hSB1, fun φ ↦ ?_⟩
  obtain ⟨σ₀, Λ, Λ', hΛ, -, hZ, hZ', hfe⟩ :=
    GJGlobal.globalZeta_entire_functionalEquation hn μ ν h₁ h₂ hA (matrixTensor_mem φ S Φ hSB hS0)
  set s₀ : ℂ := ((max σ₀ σu + 1 : ℝ) : ℂ) with hs₀def
  have hs₀re : s₀.re = max σ₀ σu + 1 := by rw [hs₀def, Complex.ofReal_re]
  obtain ⟨-, -, -, -, hbp0, -⟩ := hu s₀ (by rw [hs₀re]; linarith [le_max_right σ₀ σu])
  refine ⟨max σ₀ σu + 3, Λ, hΛ, fun s hs ↦ ?_⟩
  have hs₀ : σ₀ < s.re := by linarith [le_max_left σ₀ σu]
  have hsu : σu < s.re := by linarith [le_max_right σ₀ σu]
  have hre : s₀.re + 2 ≤ s.re := by rw [hs₀re]; linarith
  obtain ⟨hZp, hLp, hZd, hLd, -, -⟩ := hu s hsu
  refine ⟨ne_zero_of_hasProd_inv_prod hLp
    (fun v i ↦ (z v i : ℂ) * qs ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) s)
    (fun v ↦ ((hbp0 v v.2).2 s)) (summable_residueCard_inv_sq S)
    (fun v i ↦ norm_mul_qs_le _ ((hbp0 v v.2).1 i) hre)
    (fun v i ↦ lt_of_le_of_lt (norm_mul_qs_le _ ((hbp0 v v.2).1 i) hre) (residueCard_inv_sq_lt_one _)), ?_, ?_⟩
  · obtain ⟨hint, hΛs⟩ := hZ s hs₀
    obtain ⟨hE, -⟩ := globalZeta_eq_euler ν μi φ hSB hS0 hξ hsph hfic hf hint
    have hall := hasProd_of_hasProd_compl (f := fun v ↦ zetaIntegral (localHaar n v) (Φ v)
      (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s) S
      (hLp.congr_fun fun v ↦ by rw [hS0 v v.2]; exact hZp v v.2)
    rw [← hΛs, hE, hall.tprod_eq]
    ring
  · obtain ⟨hint, hΛs⟩ := hZ' s hs₀
    rw [hFour φ S Φ hSB hS0] at hint hΛs
    rw [zetaIntegrand_smul] at hint
    have hint3 := (integrable_const_mul_iff (isUnit_iff_ne_zero.2 hC) _).1 hint
    have hΛ1 : Λ (1 - s) = Λ' s := by rw [hfe]; congr 1; ring
    obtain ⟨hE, -⟩ := globalZeta_eq_euler (f := fun g ↦ GJGlobal.matrixCoeff μ φ₁ φ₂ g⁻¹) ν μi _ hSB1 hS01 hℓs hsphd
      hfic' hfd hint3
    have hall := hasProd_of_hasProd_compl (f := fun v ↦ zetaIntegral (localHaar n v)
      (GJMatrix.localMatrixFourier (GroundTheory.Global.localAdelicChar K v) (Φ v))
      (Parabolic.matrixCoeff (F := v.adicCompletion K) (Representation.dual (π v)) (ℓ v)
        (Module.Dual.eval ℂ (V v) (ξ v))) s) S (hLd.congr_fun fun v ↦ by
          have h3 := hS01 v v.2
          rw [h3]; exact hZd v v.2)
    rw [hΛ1, ← hΛs, GJGlobal.globalZeta, zetaIntegrand_smul, integral_const_mul, ← GJGlobal.globalZeta, hE, hall.tprod_eq]
    change _ = C * cE * _ * (∏ v ∈ S, zetaIntegral (localHaar n v)
      (GJMatrix.localMatrixFourier (GroundTheory.Global.localAdelicChar K v) (Φ v))
      (Parabolic.matrixCoeff (F := v.adicCompletion K) (Representation.dual (π v)) (ℓ v)
        (Module.Dual.eval ℂ (V v) (ξ v))) s) * _
    ring

end UpperTheory.V.Z.Inf
