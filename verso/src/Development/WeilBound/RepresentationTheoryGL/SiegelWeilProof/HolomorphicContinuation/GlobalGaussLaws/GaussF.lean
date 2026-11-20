import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussE

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

variable {n : ℕ}

/- English proof (translation)
Introduce `n e p q y y' Z hZ`. Establish `hg` using `inG_mR y'`. Establish `hD` using `det_CZD hg hZ`. Establish `hDh` using `det_CZhD hg hZ`. Establish `hW : IsSiegel (actZ y' Z)` using `isSiegel_actZ y' hZ`.

Establish `hD'` using `det_CZD (inG_mR y) hW`. Establish `e1 : actZ y' Z * (toBlocks₂₁ (mR y') * Z + toBlocks₂₂ (mR y')) = toBlocks₁₁ (mR y') * Z + toBlocks₁₂ (mR y')`. Unfold `actZ`. Conclude with `Matrix.nonsing_inv_mul_cancel_right _ _ hD`. Establish `e2 : (actZ y' Z)ᴴ * (toBlocks₂₁ (mR y') * Zᴴ + toBlocks₂₂ (mR y')) = toBlocks₁₁ (mR y') * Zᴴ + toBlocks₁₂ (mR y')`.

Rewrite using `[actZ_conj y' hZ]`. Conclude with `Matrix.nonsing_inv_mul_cancel_right _ _ hDh`. Take `⟨n1, n2⟩` from `num_den_mul (mR y) (mR y') Z _ e1`. Take `⟨-, n3⟩` from `num_den_mul (mR y) (mR y') Zᴴ _ e2`. Use `⟨hD, hDh, hW, ?_, ?_⟩` and prove the remaining obligations.

Use `show ((mR (y * y')).toBlocks₁₁ * Z + (mR (y * y')).toBlocks₁₂) * ((mR (y * y')).toBlocks₂₁ * Z + (mR (y * y')).toBlocks₂₂)⁻¹ = actZ y (actZ y' Z)`. Rewrite using `[mR_mul, n1, n2, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (toBlocks₂₁ (mR y') * Z + toBlocks₂₂ (mR y')), Matrix.mul_nonsing_inv _ hD, Matrix.one_mul]`. Both sides reduce to the same expression. Simplify using `only [jF]`. Rewrite using `[mR_mul, n2, n3, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, mul_zpow, mul_zpow, mul_zpow]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cocycleZ : CocycleZ := by
  intro n e p q y y' Z hZ
  have hg := inG_mR y'
  have hD := det_CZD hg hZ
  have hDh := det_CZhD hg hZ
  have hW : IsSiegel (actZ y' Z) := isSiegel_actZ y' hZ
  have hD' := det_CZD (inG_mR y) hW
  have e1 : actZ y' Z * (toBlocks₂₁ (mR y') * Z + toBlocks₂₂ (mR y')) =
      toBlocks₁₁ (mR y') * Z + toBlocks₁₂ (mR y') := by
    unfold actZ
    exact Matrix.nonsing_inv_mul_cancel_right _ _ hD
  have e2 : (actZ y' Z)ᴴ * (toBlocks₂₁ (mR y') * Zᴴ + toBlocks₂₂ (mR y')) =
      toBlocks₁₁ (mR y') * Zᴴ + toBlocks₁₂ (mR y') := by
    rw [actZ_conj y' hZ]
    exact Matrix.nonsing_inv_mul_cancel_right _ _ hDh
  obtain ⟨n1, n2⟩ := num_den_mul (mR y) (mR y') Z _ e1
  obtain ⟨-, n3⟩ := num_den_mul (mR y) (mR y') Zᴴ _ e2
  refine ⟨hD, hDh, hW, ?_, ?_⟩
  · show ((mR (y * y')).toBlocks₁₁ * Z + (mR (y * y')).toBlocks₁₂) *
        ((mR (y * y')).toBlocks₂₁ * Z + (mR (y * y')).toBlocks₂₂)⁻¹ = actZ y (actZ y' Z)
    rw [mR_mul, n1, n2, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (toBlocks₂₁ (mR y') * Z + toBlocks₂₂ (mR y')),
      Matrix.mul_nonsing_inv _ hD, Matrix.one_mul]
    rfl
  · simp only [jF]
    rw [mR_mul, n2, n3, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, mul_zpow, mul_zpow, mul_zpow]
    ring

end PositivityTheory.Rg.Sw.Glob

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

/- English proof (translation)
Take `⟨hC, hD⟩` from `inK_blocks hk`. Establish `hu` using `det_CZD hk.1 (isSiegel_I (n := n))`. Establish `key : toBlocks₁₁ (mR k) * (Complex.I • 1) + toBlocks₁₂ (mR k) = (Complex.I • 1) * (toBlocks₂₁ (mR k) * (Complex.I • 1) + toBlocks₂₂ (mR k))`. Rewrite using `[hC, hD]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_add, smul_neg, smul_smul, Complex.I_mul_I, neg_smul, one_smul, neg_neg]`.

Normalize the expressions using the abelian group laws. Unfold `actZ`. Rewrite using `[key, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]`.
-/
theorem actZ_K {k : GR n} (hk : InK (mR k)) : actZ k (Complex.I • 1) = Complex.I • 1 := by
  obtain ⟨hC, hD⟩ := inK_blocks hk
  have hu := det_CZD hk.1 (isSiegel_I (n := n))
  have key : toBlocks₁₁ (mR k) * (Complex.I • 1) + toBlocks₁₂ (mR k) =
      (Complex.I • 1) * (toBlocks₂₁ (mR k) * (Complex.I • 1) + toBlocks₂₂ (mR k)) := by
    rw [hC, hD]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_add, smul_neg,
      smul_smul, Complex.I_mul_I, neg_smul, one_smul, neg_neg]
    abel
  unfold actZ
  rw [key, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

def mkGR (M : M2 n) (hM : M.det ≠ 0) (hG : InG M) : GR n := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hM, hG⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_mkGR (M : M2 n) (hM : M.det ≠ 0) (hG : InG M) : mR (mkGR M hM hG) = M := rfl

/- English proof (translation)
Unfold `InG nU JJ`. Rewrite using `[Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `[hb]`.
-/
theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (nU b) := by
  unfold InG nU JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hb]

/- English proof (translation)
Establish `ha' : IsUnit aᴴ.det`. Rewrite using `[Matrix.det_conjTranspose]`. Conclude with `ha.star`. Unfold `InG mM JJ`. Rewrite using `[Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`.

Simplify using `[Matrix.conjTranspose_nonsing_inv, Matrix.mul_nonsing_inv _ ha', Matrix.nonsing_inv_mul _ ha]`.
-/
theorem inG_mM {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a.det) : InG (mM a) := by
  have ha' : IsUnit aᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact ha.star
  unfold InG mM JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.conjTranspose_nonsing_inv, Matrix.mul_nonsing_inv _ ha', Matrix.nonsing_inv_mul _ ha]

/- English proof (translation)
Simplify using `[nU, Matrix.det_fromBlocks_zero₂₁]`.
-/
theorem det_nU (b : Matrix (Fin n) (Fin n) ℂ) : (nU b).det = 1 := by
  simp [nU, Matrix.det_fromBlocks_zero₂₁]

/- English proof (translation)
Establish `ha' : IsUnit aᴴ.det`. Rewrite using `[Matrix.det_conjTranspose]`. Conclude with `ha.star`. Unfold `mM`. Rewrite using `[Matrix.det_fromBlocks_zero₂₁]`.

Conclude with `(ha.mul (Matrix.isUnit_nonsing_inv_det _ ha')).ne_zero`.
-/
theorem det_mM {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a.det) : (mM a).det ≠ 0 := by
  have ha' : IsUnit aᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact ha.star
  unfold mM
  rw [Matrix.det_fromBlocks_zero₂₁]
  exact (ha.mul (Matrix.isUnit_nonsing_inv_det _ ha')).ne_zero

end PositivityTheory.Rg.Sw.Glob.GaussH
