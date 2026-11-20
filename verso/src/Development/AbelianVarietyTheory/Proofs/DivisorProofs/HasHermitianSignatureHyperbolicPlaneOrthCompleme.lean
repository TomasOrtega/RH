import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureComplementHyperbolicPlane
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

noncomputable section

namespace GlobalTheory.PlaneSkewSig

open Matrix

/- English proof (translation)
Take `⟨hn, A, hA⟩` from `h`. Use `set D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hD`. Establish `hDD : D * D = 1`. Simplify using `[hD, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]`. Establish `hDh : Dᴴ = D`.

Simplify using `[hD, Matrix.fromBlocks_conjTranspose]`. Establish `hAh : Aᵀ * Mᴴ * A.map star = D`. Establish `a1 : (A.map star)ᴴ = Aᵀ` using `by ext; simp [conjTranspose_apply]`. Establish `a2 : (Aᵀ)ᴴ = A.map star` using `by ext; simp [conjTranspose_apply]`. Establish `: (Aᵀ * M * A.map star)ᴴ = Aᵀ * Mᴴ * A.map star`.

Rewrite using `[conjTranspose_mul, conjTranspose_mul, a1, a2, Matrix.mul_assoc]`. Rewrite using `[← this, hA, hDh]`. Establish `e : Fin r ⊕ Fin s ≃ Fin n` using `(finSumFinEquiv).trans (finCongr hn)`. Establish `k1 : M * (A.map star * D * Aᵀ) = 1`. Establish `: Aᵀ * (M * A.map star * D) = 1` using `by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, hDD]`.

Use `(Matrix.mul_eq_one_comm_of_equiv e).1 this` as an intermediate fact. Simplify `this` using `[Matrix.mul_assoc]`. Establish `k2 : Mᴴ * (A.map star * D * Aᵀ) = 1`. Establish `: Aᵀ * (Mᴴ * A.map star * D) = 1` using `by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAh, hDD]`. Use `(Matrix.mul_eq_one_comm_of_equiv e).1 this` as an intermediate fact.

Simplify `this` using `[Matrix.mul_assoc]`. Establish `k3 : (A.map star * D * Aᵀ) * M = 1` using `mul_eq_one_comm.1 k1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem conjTranspose_eq_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : Mᴴ = M := by
  obtain ⟨hn, A, hA⟩ := h
  set D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hD
  have hDD : D * D = 1 := by
    simp [hD, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hDh : Dᴴ = D := by
    simp [hD, Matrix.fromBlocks_conjTranspose]
  have hAh : Aᵀ * Mᴴ * A.map star = D := by
    have a1 : (A.map star)ᴴ = Aᵀ := by ext; simp [conjTranspose_apply]
    have a2 : (Aᵀ)ᴴ = A.map star := by ext; simp [conjTranspose_apply]
    have : (Aᵀ * M * A.map star)ᴴ = Aᵀ * Mᴴ * A.map star := by
      rw [conjTranspose_mul, conjTranspose_mul, a1, a2, Matrix.mul_assoc]
    rw [← this, hA, hDh]
  have e : Fin r ⊕ Fin s ≃ Fin n := (finSumFinEquiv).trans (finCongr hn)
  have k1 : M * (A.map star * D * Aᵀ) = 1 := by
    have : Aᵀ * (M * A.map star * D) = 1 := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, hDD]
    have := (Matrix.mul_eq_one_comm_of_equiv e).1 this
    simpa [Matrix.mul_assoc] using this
  have k2 : Mᴴ * (A.map star * D * Aᵀ) = 1 := by
    have : Aᵀ * (Mᴴ * A.map star * D) = 1 := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAh, hDD]
    have := (Matrix.mul_eq_one_comm_of_equiv e).1 this
    simpa [Matrix.mul_assoc] using this
  have k3 : (A.map star * D * Aᵀ) * M = 1 := mul_eq_one_comm.1 k1
  calc Mᴴ = Mᴴ * ((A.map star * D * Aᵀ) * M) := by rw [k3, Matrix.mul_one]
    _ = M := by rw [← Matrix.mul_assoc, k2, Matrix.one_mul]

/- English proof (translation)
Establish `hker : LinearMap.ker (Matrix.mulVecLin ι) = ⊥` using `LinearMap.ker_eq_bot.2 h`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective _ hker`. Use `⟨LinearMap.toMatrix' g, ?_⟩` and prove the remaining obligations. Use `congrArg LinearMap.toMatrix' hg` as an intermediate fact. Rewrite `this` using `[LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id]`.

Establish `e : LinearMap.toMatrix' ι.mulVecLin = ι` using `LinearMap.toMatrix'_toLin' ι`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem exists_left_inverse {m k : ℕ} (ι : Matrix (Fin m) (Fin k) ℂ) (h : Function.Injective ι.mulVec) :
    ∃ P : Matrix (Fin k) (Fin m) ℂ, P * ι = 1 := by
  have hker : LinearMap.ker (Matrix.mulVecLin ι) = ⊥ := LinearMap.ker_eq_bot.2 h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
  have e : LinearMap.toMatrix' ι.mulVecLin = ι := LinearMap.toMatrix'_toLin' ι
  rwa [e] at this

/- English proof (translation)
Use extensionality with `j`. Use `h (Pi.single j 1)` as an intermediate fact. Rewrite `this` using `[dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, single_dotProduct]`. Simplify using `using this`.
-/
theorem transpose_mulVec_eq_zero {m k : ℕ} (ι : Matrix (Fin m) (Fin k) ℂ) (v : Fin m → ℂ)
    (h : ∀ u, (ι *ᵥ u) ⬝ᵥ v = 0) : ιᵀ *ᵥ v = 0 := by
  ext j
  have := h (Pi.single j 1)
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, single_dotProduct] at this
  simpa using this

/- English proof (translation)
Introduce `n₁ M X Y ι r s hs _ _ hXX hYY hXY horth hinj`. Use `set c := X ⬝ᵥ M *ᵥ star Y with hc`. Use `set Y' : Fin (n₁ + 2) → ℂ := (star c)⁻¹ • Y with hY'`. Establish `hsY : star Y' = c⁻¹ • star Y`. Rewrite using `[hY', star_smul, star_inv₀, star_star]`.

Establish `hXY' : X ⬝ᵥ M *ᵥ star Y' = 1`. Rewrite using `[hsY, mulVec_smul, dotProduct_smul, smul_eq_mul, ← hc, inv_mul_cancel₀ hXY]`. Establish `hYY' : Y' ⬝ᵥ M *ᵥ star Y' = 0`. Rewrite using `[hsY, mulVec_smul, dotProduct_smul, hY', smul_dotProduct, hYY]`. Simplify using the standard rewrite rules.

Establish `hιX : ιᵀ *ᵥ (M *ᵥ star X) = 0` using `transpose_mulVec_eq_zero ι _ fun u => (horth u).1`. Establish `hιY : ιᵀ *ᵥ (M *ᵥ star Y') = 0`. Rewrite using `[hsY, mulVec_smul, mulVec_smul, transpose_mulVec_eq_zero ι _ fun u => (horth u).2, smul_zero]`. Take `⟨P, hP⟩` from `exists_left_inverse ι hinj`. Conclude with `GlobalTheory.PlaneSig.hasSig_complement_plane (n₁ + 2) n₁ M X Y' ι P r s rfl (conjTranspose_eq_of_hasSig hs) hXX hYY' hXY' hιX hιY hP hs`.
-/
theorem hasSig_complement : ∀ (n₁ : ℕ) (M : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ) (X Y : Fin (n₁ + 2) → ℂ)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (r s : ℕ), HasSig M r s → 1 ≤ r → 1 ≤ s →
    X ⬝ᵥ M *ᵥ star X = 0 → Y ⬝ᵥ M *ᵥ star Y = 0 → X ⬝ᵥ M *ᵥ star Y ≠ 0 →
    (∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0) → Function.Injective ι.mulVec →
    HasSig (ιᵀ * M * ι.map star) (r - 1) (s - 1) := by
  intro n₁ M X Y ι r s hs _ _ hXX hYY hXY horth hinj
  set c := X ⬝ᵥ M *ᵥ star Y with hc
  set Y' : Fin (n₁ + 2) → ℂ := (star c)⁻¹ • Y with hY'
  have hsY : star Y' = c⁻¹ • star Y := by
    rw [hY', star_smul, star_inv₀, star_star]
  have hXY' : X ⬝ᵥ M *ᵥ star Y' = 1 := by
    rw [hsY, mulVec_smul, dotProduct_smul, smul_eq_mul, ← hc, inv_mul_cancel₀ hXY]
  have hYY' : Y' ⬝ᵥ M *ᵥ star Y' = 0 := by
    rw [hsY, mulVec_smul, dotProduct_smul, hY', smul_dotProduct, hYY]; simp
  have hιX : ιᵀ *ᵥ (M *ᵥ star X) = 0 := transpose_mulVec_eq_zero ι _ fun u => (horth u).1
  have hιY : ιᵀ *ᵥ (M *ᵥ star Y') = 0 := by
    rw [hsY, mulVec_smul, mulVec_smul, transpose_mulVec_eq_zero ι _ fun u => (horth u).2, smul_zero]
  obtain ⟨P, hP⟩ := exists_left_inverse ι hinj
  exact GlobalTheory.PlaneSig.hasSig_complement_plane (n₁ + 2) n₁ M X Y' ι P r s rfl (conjTranspose_eq_of_hasSig hs)
    hXX hYY' hXY' hιX hιY hP hs

end GlobalTheory.PlaneSkewSig
