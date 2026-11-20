import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussC

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

/- English proof (translation)
Assume the negation of the conclusion as `hv`. Establish `hpos` using `Matrix.PosDef.dotProduct_mulVec_pos hZ hv`. Rewrite `hpos` using `[smul_mulVec, dotProduct_smul, h, smul_zero]`. Conclude with `lt_irrefl _ hpos`.
-/
theorem eq_zero_of_siegel {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSiegel Z) {v : Fin n → ℂ}
    (h : star v ⬝ᵥ ((Z - Zᴴ) *ᵥ v) = 0) : v = 0 := by
  by_contra hv
  have hpos := Matrix.PosDef.dotProduct_mulVec_pos hZ hv
  rw [smul_mulVec, dotProduct_smul, h, smul_zero] at hpos
  exact lt_irrefl _ hpos

/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero]`. Introduce `hdet`. Take `⟨v, hv, hMv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Establish `hid` using `identG hg Zᴴ Zᴴ`. Rewrite `hid` using `[conjTranspose_conjTranspose]`.

Establish `h0 : star v ⬝ᵥ ((Z - Zᴴ) *ᵥ v) = 0`. Rewrite using `[← hid, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hMv, mulVec_zero, dotProduct_sub, dotProduct_zero, dotProduct_mulVec, ← star_mulVec, hMv]`. Simplify using the standard rewrite rules. Conclude with `hv (eq_zero_of_siegel hZ h0)`.
-/
theorem det_CZhD {g : M2 n} (hg : InG g) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSiegel Z) :
    IsUnit (g.toBlocks₂₁ * Zᴴ + g.toBlocks₂₂).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hid := identG hg Zᴴ Zᴴ
  rw [conjTranspose_conjTranspose] at hid
  have h0 : star v ⬝ᵥ ((Z - Zᴴ) *ᵥ v) = 0 := by
    rw [← hid, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hMv, mulVec_zero, dotProduct_sub,
      dotProduct_zero, dotProduct_mulVec, ← star_mulVec, hMv]
    simp
  exact hv (eq_zero_of_siegel hZ h0)

/- English proof (translation)
Unfold `IsSiegel`. Establish `hs : -(Complex.I / 2) * (Complex.I - star Complex.I) = 1`. Rewrite using `[Complex.star_def, Complex.conj_I]`. Take the linear combination `(-1 : ℂ) * Complex.I_sq`. Rewrite using `[conjTranspose_smul, conjTranspose_one, ← sub_smul, smul_smul, hs, one_smul]`.

Conclude with `Matrix.PosDef.one`.
-/
theorem isSiegel_I : IsSiegel (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  unfold IsSiegel
  have hs : -(Complex.I / 2) * (Complex.I - star Complex.I) = 1 := by
    rw [Complex.star_def, Complex.conj_I]
    linear_combination (-1 : ℂ) * Complex.I_sq
  rw [conjTranspose_smul, conjTranspose_one, ← sub_smul, smul_smul, hs, one_smul]
  exact Matrix.PosDef.one

/- English proof (translation)
Use `congrArg toBlocks₁₁ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)` as an intermediate fact. Simplify `this` using `only [fromBlocks_toBlocks, toBlocks_fromBlocks₁₁]`.
-/
theorem toBlocks₁₁_mul (M N : M2 n) : (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ + M.toBlocks₁₂ * N.toBlocks₂₁ := by
  have := congrArg toBlocks₁₁ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁
    M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)
  simpa only [fromBlocks_toBlocks, toBlocks_fromBlocks₁₁] using this

/- English proof (translation)
Use `congrArg toBlocks₁₂ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)` as an intermediate fact. Simplify `this` using `only [fromBlocks_toBlocks, toBlocks_fromBlocks₁₂]`.
-/
theorem toBlocks₁₂_mul (M N : M2 n) : (M * N).toBlocks₁₂ = M.toBlocks₁₁ * N.toBlocks₁₂ + M.toBlocks₁₂ * N.toBlocks₂₂ := by
  have := congrArg toBlocks₁₂ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁
    M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)
  simpa only [fromBlocks_toBlocks, toBlocks_fromBlocks₁₂] using this

/- English proof (translation)
Use `congrArg toBlocks₂₁ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)` as an intermediate fact. Simplify `this` using `only [fromBlocks_toBlocks, toBlocks_fromBlocks₂₁]`.
-/
theorem toBlocks₂₁_mul (M N : M2 n) : (M * N).toBlocks₂₁ = M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁ := by
  have := congrArg toBlocks₂₁ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁
    M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)
  simpa only [fromBlocks_toBlocks, toBlocks_fromBlocks₂₁] using this

/- English proof (translation)
Use `congrArg toBlocks₂₂ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)` as an intermediate fact. Simplify `this` using `only [fromBlocks_toBlocks, toBlocks_fromBlocks₂₂]`.
-/
theorem toBlocks₂₂_mul (M N : M2 n) : (M * N).toBlocks₂₂ = M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂ := by
  have := congrArg toBlocks₂₂ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁
    M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)
  simpa only [fromBlocks_toBlocks, toBlocks_fromBlocks₂₂] using this

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_mul (y y' : GR n) : mR (y * y') = mR y * mR y' := rfl

/- English proof (translation)
The claim follows from `y.2`.
-/
theorem inG_mR (y : GR n) : InG (mR y) := y.2

/- English proof (translation)
Rewrite using `[toBlocks₁₁_mul, toBlocks₁₂_mul, toBlocks₂₁_mul, toBlocks₂₂_mul]`. Prove the components needed by the constructor for the conclusion. Establish `e : (M.toBlocks₁₁ * W + M.toBlocks₁₂) * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) = M.toBlocks₁₁ * (W * (N.toBlocks₂₁ * Z + N.toBlocks₂₂)) + M.toBlocks₁₂ * (N.toBlocks₂₁ * Z + N.toBlocks₂₂)` using `by noncomm_ring`. Rewrite using `[e, hW]`. Use `noncomm_ring`.

Establish `e : (M.toBlocks₂₁ * W + M.toBlocks₂₂) * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) = M.toBlocks₂₁ * (W * (N.toBlocks₂₁ * Z + N.toBlocks₂₂)) + M.toBlocks₂₂ * (N.toBlocks₂₁ * Z + N.toBlocks₂₂)` using `by noncomm_ring`. Rewrite using `[e, hW]`. Use `noncomm_ring`.
-/
theorem num_den_mul (M N : M2 n) (Z W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) = N.toBlocks₁₁ * Z + N.toBlocks₁₂) :
    (M * N).toBlocks₁₁ * Z + (M * N).toBlocks₁₂ = (M.toBlocks₁₁ * W + M.toBlocks₁₂) * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) ∧
    (M * N).toBlocks₂₁ * Z + (M * N).toBlocks₂₂ = (M.toBlocks₂₁ * W + M.toBlocks₂₂) * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) := by
  rw [toBlocks₁₁_mul, toBlocks₁₂_mul, toBlocks₂₁_mul, toBlocks₂₂_mul]
  constructor
  · have e : (M.toBlocks₁₁ * W + M.toBlocks₁₂) * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) =
        M.toBlocks₁₁ * (W * (N.toBlocks₂₁ * Z + N.toBlocks₂₂)) +
          M.toBlocks₁₂ * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) := by noncomm_ring
    rw [e, hW]
    noncomm_ring
  · have e : (M.toBlocks₂₁ * W + M.toBlocks₂₂) * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) =
        M.toBlocks₂₁ * (W * (N.toBlocks₂₁ * Z + N.toBlocks₂₂)) +
          M.toBlocks₂₂ * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) := by noncomm_ring
    rw [e, hW]
    noncomm_ring

end PositivityTheory.Rg.Sw.Glob.GaussH
