import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.InversionStatement

noncomputable section

open Complex Matrix ReciprocityTheory.PTheta

namespace ReciprocityTheory.ChartRestriction.G.Key.Chi

def nAut {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  (cMat γ).toBlocks₁₁ * τ + (cMat γ).toBlocks₁₂

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jAut_eq {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    jAut γ τ = (cMat γ).toBlocks₂₁ * τ + (cMat γ).toBlocks₂₂ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nAut_eq {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    nAut γ τ = (cMat γ).toBlocks₁₁ * τ + (cMat γ).toBlocks₁₂ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem spAct_eq {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    spAct γ τ = nAut γ τ * (jAut γ τ)⁻¹ := rfl

/- English proof (translation)
Establish `h : (γ * δ).map (Int.castRingHom ℂ) = γ.map (Int.castRingHom ℂ) * δ.map (Int.castRingHom ℂ)` using `Matrix.map_mul`. Simplify `h` using `[cMat]`.
-/
theorem cMat_mul {g : ℕ} (γ δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    cMat (γ * δ) = cMat γ * cMat δ := by
  have h : (γ * δ).map (Int.castRingHom ℂ) = γ.map (Int.castRingHom ℂ) * δ.map (Int.castRingHom ℂ) :=
    Matrix.map_mul
  simpa [cMat] using h

/- English proof (translation)
Establish `h` using `fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂`. Rewrite `h` using `[fromBlocks_toBlocks, fromBlocks_toBlocks]`. Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
theorem blocks_mul {g : ℕ} (M N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ + M.toBlocks₁₂ * N.toBlocks₂₁ ∧
    (M * N).toBlocks₁₂ = M.toBlocks₁₁ * N.toBlocks₁₂ + M.toBlocks₁₂ * N.toBlocks₂₂ ∧
    (M * N).toBlocks₂₁ = M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁ ∧
    (M * N).toBlocks₂₂ = M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂ := by
  have h := fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂
    N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂
  rw [fromBlocks_toBlocks, fromBlocks_toBlocks] at h
  rw [h]
  simp

/- English proof (translation)
Take `⟨-, -, h21, h22⟩` from `blocks_mul (cMat γ) (cMat δ)`. Establish `hj : (jAut δ τ)⁻¹ * jAut δ τ = 1` using `Matrix.nonsing_inv_mul _ h`. Rewrite using `[spAct_eq, jAut_eq γ, add_mul, Matrix.mul_assoc _ (nAut δ τ * _), Matrix.mul_assoc (nAut δ τ), hj, Matrix.mul_one]`. Rewrite using `[jAut_eq (γ * δ), cMat_mul, h21, h22, nAut_eq δ, jAut_eq δ]`. Use `noncomm_ring`.
-/
theorem jAut_mul {g : ℕ} (γ δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (τ : Matrix (Fin g) (Fin g) ℂ) (h : IsUnit (jAut δ τ).det) :
    jAut (γ * δ) τ = jAut γ (spAct δ τ) * jAut δ τ := by
  obtain ⟨-, -, h21, h22⟩ := blocks_mul (cMat γ) (cMat δ)
  have hj : (jAut δ τ)⁻¹ * jAut δ τ = 1 := Matrix.nonsing_inv_mul _ h
  rw [spAct_eq, jAut_eq γ, add_mul, Matrix.mul_assoc _ (nAut δ τ * _), Matrix.mul_assoc (nAut δ τ),
    hj, Matrix.mul_one]
  rw [jAut_eq (γ * δ), cMat_mul, h21, h22, nAut_eq δ, jAut_eq δ]
  noncomm_ring

/- English proof (translation)
Take `⟨h11, h12, -, -⟩` from `blocks_mul (cMat γ) (cMat δ)`. Establish `hj : (jAut δ τ)⁻¹ * jAut δ τ = 1` using `Matrix.nonsing_inv_mul _ h`. Rewrite using `[spAct_eq, nAut_eq γ, add_mul, Matrix.mul_assoc _ (nAut δ τ * _), Matrix.mul_assoc (nAut δ τ), hj, Matrix.mul_one]`. Rewrite using `[nAut_eq (γ * δ), cMat_mul, h11, h12, nAut_eq δ, jAut_eq δ]`. Use `noncomm_ring`.
-/
theorem nAut_mul {g : ℕ} (γ δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (τ : Matrix (Fin g) (Fin g) ℂ) (h : IsUnit (jAut δ τ).det) :
    nAut (γ * δ) τ = nAut γ (spAct δ τ) * jAut δ τ := by
  obtain ⟨h11, h12, -, -⟩ := blocks_mul (cMat γ) (cMat δ)
  have hj : (jAut δ τ)⁻¹ * jAut δ τ = 1 := Matrix.nonsing_inv_mul _ h
  rw [spAct_eq, nAut_eq γ, add_mul, Matrix.mul_assoc _ (nAut δ τ * _), Matrix.mul_assoc (nAut δ τ),
    hj, Matrix.mul_one]
  rw [nAut_eq (γ * δ), cMat_mul, h11, h12, nAut_eq δ, jAut_eq δ]
  noncomm_ring

/- English proof (translation)
Rewrite using `[spAct_eq (γ * δ), nAut_mul γ δ τ h, jAut_mul γ δ τ h, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (jAut δ τ), Matrix.mul_nonsing_inv _ h, Matrix.one_mul, spAct_eq γ]`.
-/
theorem spAct_mul {g : ℕ} (γ δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (τ : Matrix (Fin g) (Fin g) ℂ) (h : IsUnit (jAut δ τ).det) :
    spAct (γ * δ) τ = spAct γ (spAct δ τ) := by
  rw [spAct_eq (γ * δ), nAut_mul γ δ τ h, jAut_mul γ δ τ h, Matrix.mul_inv_rev, Matrix.mul_assoc,
    ← Matrix.mul_assoc (jAut δ τ), Matrix.mul_nonsing_inv _ h, Matrix.one_mul, spAct_eq γ]

/- English proof (translation)
Simplify using `only [zAct, jAut_mul γ δ τ h, Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.mulVec_mulVec]`.
-/
theorem zAct_mul {g : ℕ} (γ δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (τ : Matrix (Fin g) (Fin g) ℂ) (h : IsUnit (jAut δ τ).det) (z : Fin g → ℂ) :
    zAct (γ * δ) τ z = zAct γ (spAct δ τ) (zAct δ τ z) := by
  simp only [zAct, jAut_mul γ δ τ h, Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.mulVec_mulVec]

/- English proof (translation)
Rewrite using `[jAut_mul γ δ τ h, det_mul]`.
-/
theorem det_jAut_mul {g : ℕ} (γ δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (τ : Matrix (Fin g) (Fin g) ℂ) (h : IsUnit (jAut δ τ).det) :
    (jAut (γ * δ) τ).det = (jAut γ (spAct δ τ)).det * (jAut δ τ).det := by
  rw [jAut_mul γ δ τ h, det_mul]

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]`.
-/
theorem dot_conj {g : ℕ} (P Y : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    z ⬝ᵥ ((P * Y * Pᵀ) *ᵥ z) = (Pᵀ *ᵥ z) ⬝ᵥ (Y *ᵥ (Pᵀ *ᵥ z)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.mulVec_transpose]

/- English proof (translation)
Take `⟨-, -, h21, -⟩` from `blocks_mul (cMat γ) (cMat δ)`. Establish `hN : (cMat δ).toBlocks₁₁ = ((jAut δ τ)⁻¹)ᵀ + spAct δ τ * (cMat δ).toBlocks₂₁` using `sub_eq_iff_eq_add.mp hA`. Establish `hM : (cMat γ).toBlocks₂₁ * (cMat δ).toBlocks₁₁ + (cMat γ).toBlocks₂₂ * (cMat δ).toBlocks₂₁ = (cMat γ).toBlocks₂₁ * ((jAut δ τ)⁻¹)ᵀ + jAut γ (spAct δ τ) * (cMat δ).toBlocks₂₁`. Rewrite using `[hN, jAut_eq γ]`. Use `noncomm_ring`.

Establish `key : (jAut (γ * δ) τ)⁻¹ * (cMat (γ * δ)).toBlocks₂₁ = (jAut δ τ)⁻¹ * ((jAut γ (spAct δ τ))⁻¹ * (cMat γ).toBlocks₂₁) * ((jAut δ τ)⁻¹)ᵀ + (jAut δ τ)⁻¹ * (cMat δ).toBlocks₂₁`. Rewrite using `[jAut_mul γ δ τ hδ, Matrix.mul_inv_rev, cMat_mul, h21, hM]`. Simplify using `only [Matrix.mul_add, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hγ]`. Rewrite using `[expArg, key, Matrix.add_mulVec, dotProduct_add, dot_conj]`. Both sides reduce to the same expression.
-/
theorem expArg_mul {g : ℕ} (γ δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (τ : Matrix (Fin g) (Fin g) ℂ) (hδ : IsUnit (jAut δ τ).det)
    (hγ : IsUnit (jAut γ (spAct δ τ)).det)
    (hA : (cMat δ).toBlocks₁₁ - spAct δ τ * (cMat δ).toBlocks₂₁ = ((jAut δ τ)⁻¹)ᵀ)
    (z : Fin g → ℂ) :
    expArg (γ * δ) τ z = expArg γ (spAct δ τ) (zAct δ τ z) + expArg δ τ z := by
  obtain ⟨-, -, h21, -⟩ := blocks_mul (cMat γ) (cMat δ)
  have hN : (cMat δ).toBlocks₁₁ = ((jAut δ τ)⁻¹)ᵀ + spAct δ τ * (cMat δ).toBlocks₂₁ :=
    sub_eq_iff_eq_add.mp hA
  have hM : (cMat γ).toBlocks₂₁ * (cMat δ).toBlocks₁₁ + (cMat γ).toBlocks₂₂ * (cMat δ).toBlocks₂₁ =
      (cMat γ).toBlocks₂₁ * ((jAut δ τ)⁻¹)ᵀ + jAut γ (spAct δ τ) * (cMat δ).toBlocks₂₁ := by
    rw [hN, jAut_eq γ]
    noncomm_ring
  have key : (jAut (γ * δ) τ)⁻¹ * (cMat (γ * δ)).toBlocks₂₁ =
      (jAut δ τ)⁻¹ * ((jAut γ (spAct δ τ))⁻¹ * (cMat γ).toBlocks₂₁) * ((jAut δ τ)⁻¹)ᵀ +
        (jAut δ τ)⁻¹ * (cMat δ).toBlocks₂₁ := by
    rw [jAut_mul γ δ τ hδ, Matrix.mul_inv_rev, cMat_mul, h21, hM]
    simp only [Matrix.mul_add, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hγ]
  rw [expArg, key, Matrix.add_mulVec, dotProduct_add, dot_conj]
  rfl

/- English proof (translation)
Rewrite `hγ` using `[SymplecticGroup.mem_iff']`. Establish `h` using `congrArg (Int.castRingHom ℂ).mapMatrix hγ`. Rewrite `h` using `[map_mul, map_mul]`. Establish `hc : (Int.castRingHom ℂ).mapMatrix γ = cMat γ` using `rfl`. Establish `ht : (Int.castRingHom ℂ).mapMatrix γᵀ = (cMat γ)ᵀ` using `rfl`.

Establish `hJ : (Int.castRingHom ℂ).mapMatrix (Matrix.J (Fin g) ℤ) = Matrix.J (Fin g) ℂ` using `Matrix.map_J (Fin g) (Int.castRingHom ℂ)`. Rewrite `h` using `[hc, ht, hJ]`. Rewrite `h` using `[← fromBlocks_toBlocks (cMat γ), fromBlocks_transpose, Matrix.J, fromBlocks_multiply, fromBlocks_multiply]`. Take `⟨e11, e12, e21, e22⟩` from `Matrix.fromBlocks_inj.mp h`. Simplify using `only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, zero_add, add_zero] at e11 e12 e21 e22`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← e11]`. Normalize the expressions using the abelian group laws. Rewrite using `[← e12]`. Normalize the expressions using the abelian group laws.

Rewrite using `[← e21]`. Normalize the expressions using the abelian group laws. Rewrite using `[← e22]`. Normalize the expressions using the abelian group laws.
-/
theorem sp_rel {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    ((cMat γ).toBlocks₂₁ᵀ * (cMat γ).toBlocks₁₁ - (cMat γ).toBlocks₁₁ᵀ * (cMat γ).toBlocks₂₁ = 0) ∧
    ((cMat γ).toBlocks₂₁ᵀ * (cMat γ).toBlocks₁₂ - (cMat γ).toBlocks₁₁ᵀ * (cMat γ).toBlocks₂₂ = -1) ∧
    ((cMat γ).toBlocks₂₂ᵀ * (cMat γ).toBlocks₁₁ - (cMat γ).toBlocks₁₂ᵀ * (cMat γ).toBlocks₂₁ = 1) ∧
    ((cMat γ).toBlocks₂₂ᵀ * (cMat γ).toBlocks₁₂ - (cMat γ).toBlocks₁₂ᵀ * (cMat γ).toBlocks₂₂ = 0) := by
  rw [SymplecticGroup.mem_iff'] at hγ
  have h := congrArg (Int.castRingHom ℂ).mapMatrix hγ
  rw [map_mul, map_mul] at h
  have hc : (Int.castRingHom ℂ).mapMatrix γ = cMat γ := rfl
  have ht : (Int.castRingHom ℂ).mapMatrix γᵀ = (cMat γ)ᵀ := rfl
  have hJ : (Int.castRingHom ℂ).mapMatrix (Matrix.J (Fin g) ℤ) = Matrix.J (Fin g) ℂ :=
    Matrix.map_J (Fin g) (Int.castRingHom ℂ)
  rw [hc, ht, hJ] at h
  rw [← fromBlocks_toBlocks (cMat γ), fromBlocks_transpose, Matrix.J, fromBlocks_multiply,
    fromBlocks_multiply] at h
  obtain ⟨e11, e12, e21, e22⟩ := Matrix.fromBlocks_inj.mp h
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
    zero_add, add_zero] at e11 e12 e21 e22
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e11]; abel
  · rw [← e12]; abel
  · rw [← e21]; abel
  · rw [← e22]; abel

end ReciprocityTheory.ChartRestriction.G.Key.Chi
