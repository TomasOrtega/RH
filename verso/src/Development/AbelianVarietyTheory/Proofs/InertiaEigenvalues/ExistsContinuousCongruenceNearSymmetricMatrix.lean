import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `F E _ _ _ _ hU r H₀ hsym hdet`. Use `haveI : CharZero F := hU.charZero`. Use `haveI : LocallyCompactSpace F := hU.lcF`. Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`. Use `letI : NormedRing (Matrix (Fin r) (Fin r) F) := Matrix.linftyOpNormedRing`.

Use `letI : NormedAlgebra F (Matrix (Fin r) (Fin r) F) := Matrix.linftyOpNormedAlgebra`. Use `haveI : @CompleteSpace (Matrix (Fin r) (Fin r) F) PseudoMetricSpace.toUniformSpace := FiniteDimensional.complete F _`. Establish `h2 : (2 : F) ≠ 0` using `two_ne_zero`. Set `L : Matrix (Fin r) (Fin r) F ≃L[F] Matrix (Fin r) (Fin r) F` to `ContinuousLinearEquiv.equivOfInverse ((2 : F) • ContinuousLinearMap.id F _) ((2 : F)⁻¹ • ContinuousLinearMap.id F _) (by intro x; simp [smul_smul, inv_mul_cancel₀ h2]) (by intro x; simp [smul_smul, mul_inv_cancel₀ h2])`. Establish `hf : HasStrictFDerivAt (fun Y : Matrix (Fin r) (Fin r) F => Y * Y) (L : Matrix (Fin r) (Fin r) F →L[F] Matrix (Fin r) (Fin r) F) 1`.

Establish `h` using `(hasStrictFDerivAt_id (𝕜 := F) (1 : Matrix (Fin r) (Fin r) F)).mul' (hasStrictFDerivAt_id 1)`. Establish `e : (L : Matrix (Fin r) (Fin r) F →L[F] Matrix (Fin r) (Fin r) F) = (id 1 : Matrix (Fin r) (Fin r) F) • ContinuousLinearMap.id F (Matrix (Fin r) (Fin r) F) + MulOpposite.op (id 1 : Matrix (Fin r) (Fin r) F) • ContinuousLinearMap.id F (Matrix (Fin r) (Fin r) F)` using `by ext1 D`. Simplify using `[L, two_smul]`. Rewrite using `[e]`. Conclude with `h`.

Use `set P := hf.toOpenPartialHomeomorph _ with hPdef`. Establish `hPc : ∀ Y, P Y = Y * Y` using `fun Y => by`. Rewrite using `[hPdef, hf.toOpenPartialHomeomorph_coe]`. Establish `h1s : (1 : Matrix (Fin r) (Fin r) F) ∈ P.source` using `hf.mem_toOpenPartialHomeomorph_source`. Establish `h1t : (1 : Matrix (Fin r) (Fin r) F) ∈ P.target`.

Use `hf.image_mem_toOpenPartialHomeomorph_target` as an intermediate fact. Simplify using `using this`. Establish `hS1 : P.symm 1 = 1`. Use `P.left_inv h1s` as an intermediate fact. Rewrite `this` using `[hPc, one_mul]`. Then use the resulting hypothesis.

Establish `hu : IsUnit H₀.det` using `isUnit_iff_ne_zero.mpr hdet`. Use `set A := H₀⁻¹ with hA`. Establish `hAH : A * H₀ = 1` using `Matrix.nonsing_inv_mul H₀ hu`. Establish `hHA : H₀ * A = 1` using `Matrix.mul_nonsing_inv H₀ hu`. Establish `hAT : Aᵀ = A`.

Rewrite using `[hA, Matrix.transpose_nonsing_inv, hsym.eq]`. Set `φ : Matrix (Fin r) (Fin r) F → Matrix (Fin r) (Fin r) F` to `fun Y => A * Yᵀ * H₀`. Establish `hφc : Continuous φ`. Conclude with `(continuous_const.matrix_mul (continuous_id.matrix_transpose)).matrix_mul continuous_const`. Set `ψ : Matrix (Fin r) (Fin r) F → Matrix (Fin r) (Fin r) F` to `fun H => A * H`.

Establish `hψc : Continuous ψ` using `continuous_const.matrix_mul continuous_id`. Establish `hT : IsOpen (P.target ∩ P.symm ⁻¹' (φ ⁻¹' P.source))` using `P.continuousOn_symm.isOpen_inter_preimage P.open_target (P.open_source.preimage hφc)`. Use `⟨ψ ⁻¹' (P.target ∩ P.symm ⁻¹' (φ ⁻¹' P.source)), fun H => P.symm (A * H), hT.preimage hψc, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show A * H₀ ∈ P.target ∩ P.symm ⁻¹' (φ ⁻¹' P.source)`. Rewrite using `[hAH]`.

Use `⟨h1t, ?_⟩` and prove the remaining obligations. Use `show φ (P.symm 1) ∈ P.source`. Simplify using `only [φ, hS1, Matrix.transpose_one, Matrix.mul_one, hAH]`. Conclude with `h1s`. Conclude with `P.continuousOn_symm.comp hψc.continuousOn (fun H hH => hH.1)`.

Use `show P.symm (A * H₀) = 1`. Rewrite using `[hAH, hS1]`. Introduce `H hH hHs`. Take `⟨hX, hφS⟩` from `hH`. Use `set S := P.symm (A * H) with hSdef`.

Establish `hSs : S ∈ P.source` using `P.map_target hX`. Establish `hSS : S * S = A * H` using `by rw [← hPc]; exact P.right_inv hX`. Establish `hφφ : φ S * φ S = S * S` using `by show A * Sᵀ * H₀ * (A * Sᵀ * H₀) = S * S`. Establish `e1 : A * Sᵀ * H₀ * (A * Sᵀ * H₀) = A * (S * S)ᵀ * H₀`. Rewrite using `[Matrix.transpose_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc H₀ A, hHA, Matrix.one_mul]`. Rewrite using `[e1, hSS, Matrix.transpose_mul, hAT, hHs.eq, Matrix.mul_assoc, Matrix.mul_assoc, hAH, Matrix.mul_one]`. Establish `heq : φ S = S` using `P.injOn hφS hSs (by rw [hPc, hPc]; exact hφφ)`. Establish `hcomm : Sᵀ * H₀ = H₀ * S`.

Establish `: H₀ * (A * Sᵀ * H₀) = H₀ * S` using `by rw [show A * Sᵀ * H₀ = φ S from rfl, heq]`. Rewrite `this` using `[Matrix.mul_assoc, ← Matrix.mul_assoc H₀ A, hHA, Matrix.one_mul]`. Then use the resulting hypothesis. Rewrite using `[hcomm, Matrix.mul_assoc, hSS, ← Matrix.mul_assoc, hHA, Matrix.one_mul]`.
-/
theorem symm_congr_local_continuous : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (H₀ : Matrix (Fin r) (Fin r) F), H₀.IsSymm → H₀.det ≠ 0 →
    ∃ (Ω : Set (Matrix (Fin r) (Fin r) F)) (k : Matrix (Fin r) (Fin r) F → Matrix (Fin r) (Fin r) F),
      IsOpen Ω ∧ H₀ ∈ Ω ∧ ContinuousOn k Ω ∧ k H₀ = 1 ∧ ∀ H ∈ Ω, H.IsSymm → (k H)ᵀ * H₀ * k H = H := by
  intro F E _ _ _ _ hU r H₀ hsym hdet
  haveI : CharZero F := hU.charZero
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  letI : NormedRing (Matrix (Fin r) (Fin r) F) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra F (Matrix (Fin r) (Fin r) F) := Matrix.linftyOpNormedAlgebra
  haveI : @CompleteSpace (Matrix (Fin r) (Fin r) F) PseudoMetricSpace.toUniformSpace := FiniteDimensional.complete F _
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  let L : Matrix (Fin r) (Fin r) F ≃L[F] Matrix (Fin r) (Fin r) F :=
    ContinuousLinearEquiv.equivOfInverse ((2 : F) • ContinuousLinearMap.id F _)
      ((2 : F)⁻¹ • ContinuousLinearMap.id F _)
      (by intro x; simp [smul_smul, inv_mul_cancel₀ h2]) (by intro x; simp [smul_smul, mul_inv_cancel₀ h2])
  have hf : HasStrictFDerivAt (fun Y : Matrix (Fin r) (Fin r) F => Y * Y)
      (L : Matrix (Fin r) (Fin r) F →L[F] Matrix (Fin r) (Fin r) F) 1 := by
    have h := (hasStrictFDerivAt_id (𝕜 := F) (1 : Matrix (Fin r) (Fin r) F)).mul' (hasStrictFDerivAt_id 1)
    have e : (L : Matrix (Fin r) (Fin r) F →L[F] Matrix (Fin r) (Fin r) F) =
        (id 1 : Matrix (Fin r) (Fin r) F) • ContinuousLinearMap.id F (Matrix (Fin r) (Fin r) F) +
          MulOpposite.op (id 1 : Matrix (Fin r) (Fin r) F) • ContinuousLinearMap.id F (Matrix (Fin r) (Fin r) F) := by
      ext1 D
      simp [L, two_smul]
    rw [e]
    exact h
  set P := hf.toOpenPartialHomeomorph _ with hPdef
  have hPc : ∀ Y, P Y = Y * Y := fun Y => by
    rw [hPdef, hf.toOpenPartialHomeomorph_coe]
  have h1s : (1 : Matrix (Fin r) (Fin r) F) ∈ P.source := hf.mem_toOpenPartialHomeomorph_source
  have h1t : (1 : Matrix (Fin r) (Fin r) F) ∈ P.target := by
    have := hf.image_mem_toOpenPartialHomeomorph_target
    simpa using this
  have hS1 : P.symm 1 = 1 := by
    have := P.left_inv h1s
    rwa [hPc, one_mul] at this
  have hu : IsUnit H₀.det := isUnit_iff_ne_zero.mpr hdet
  set A := H₀⁻¹ with hA
  have hAH : A * H₀ = 1 := Matrix.nonsing_inv_mul H₀ hu
  have hHA : H₀ * A = 1 := Matrix.mul_nonsing_inv H₀ hu
  have hAT : Aᵀ = A := by
    rw [hA, Matrix.transpose_nonsing_inv, hsym.eq]
  let φ : Matrix (Fin r) (Fin r) F → Matrix (Fin r) (Fin r) F := fun Y => A * Yᵀ * H₀
  have hφc : Continuous φ := by
    exact (continuous_const.matrix_mul (continuous_id.matrix_transpose)).matrix_mul continuous_const
  let ψ : Matrix (Fin r) (Fin r) F → Matrix (Fin r) (Fin r) F := fun H => A * H
  have hψc : Continuous ψ := continuous_const.matrix_mul continuous_id
  have hT : IsOpen (P.target ∩ P.symm ⁻¹' (φ ⁻¹' P.source)) :=
    P.continuousOn_symm.isOpen_inter_preimage P.open_target (P.open_source.preimage hφc)
  refine ⟨ψ ⁻¹' (P.target ∩ P.symm ⁻¹' (φ ⁻¹' P.source)), fun H => P.symm (A * H), hT.preimage hψc, ?_, ?_, ?_, ?_⟩
  · show A * H₀ ∈ P.target ∩ P.symm ⁻¹' (φ ⁻¹' P.source)
    rw [hAH]
    refine ⟨h1t, ?_⟩
    show φ (P.symm 1) ∈ P.source
    simp only [φ, hS1, Matrix.transpose_one, Matrix.mul_one, hAH]
    exact h1s
  · exact P.continuousOn_symm.comp hψc.continuousOn (fun H hH => hH.1)
  · show P.symm (A * H₀) = 1
    rw [hAH, hS1]
  · intro H hH hHs
    obtain ⟨hX, hφS⟩ := hH
    set S := P.symm (A * H) with hSdef
    have hSs : S ∈ P.source := P.map_target hX
    have hSS : S * S = A * H := by rw [← hPc]; exact P.right_inv hX
    have hφφ : φ S * φ S = S * S := by
      show A * Sᵀ * H₀ * (A * Sᵀ * H₀) = S * S
      have e1 : A * Sᵀ * H₀ * (A * Sᵀ * H₀) = A * (S * S)ᵀ * H₀ := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc H₀ A, hHA, Matrix.one_mul]
      rw [e1, hSS, Matrix.transpose_mul, hAT, hHs.eq, Matrix.mul_assoc, Matrix.mul_assoc, hAH, Matrix.mul_one]
    have heq : φ S = S := P.injOn hφS hSs (by rw [hPc, hPc]; exact hφφ)
    have hcomm : Sᵀ * H₀ = H₀ * S := by
      have : H₀ * (A * Sᵀ * H₀) = H₀ * S := by rw [show A * Sᵀ * H₀ = φ S from rfl, heq]
      rwa [Matrix.mul_assoc, ← Matrix.mul_assoc H₀ A, hHA, Matrix.one_mul] at this
    rw [hcomm, Matrix.mul_assoc, hSS, ← Matrix.mul_assoc, hHA, Matrix.one_mul]

end GlobalTheory
