import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DecompB

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob.DecH

variable {n : ℕ}

def mkGR (M : M2 n) (hu : IsUnit M.det) (hg : InG M) : GR n := ⟨M.nonsingInvUnit hu, hg⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_mkGR (M : M2 n) (hu : IsUnit M.det) (hg : InG M) : mR (mkGR M hu hg) = M := rfl

/- English proof (translation)
Unfold `InG nU JJ`. Rewrite using `[fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `[hb]`.
-/
theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (nU b) := by
  unfold InG nU JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hb]

/- English proof (translation)
Unfold `InG nbar JJ`. Rewrite using `[fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `[hc]`.
-/
theorem inG_nbar {c : Matrix (Fin n) (Fin n) ℂ} (hc : cᴴ = c) : InG (nbar c) := by
  unfold InG nbar JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hc]

/- English proof (translation)
Establish `hu : IsUnit aᴴ.det`. Rewrite using `[det_conjTranspose]`. Conclude with `ha.star`. Unfold `InG mM JJ`. Rewrite using `[fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]`.

Simplify using `[conjTranspose_nonsing_inv, mul_nonsing_inv _ hu, nonsing_inv_mul _ ha]`.
-/
theorem inG_mM {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a.det) : InG (mM a) := by
  have hu : IsUnit aᴴ.det := by
    rw [det_conjTranspose]
    exact ha.star
  unfold InG mM JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [conjTranspose_nonsing_inv, mul_nonsing_inv _ hu, nonsing_inv_mul _ ha]

/- English proof (translation)
Simplify using `[nU, det_fromBlocks_zero₂₁]`.
-/
theorem det_nU (b : Matrix (Fin n) (Fin n) ℂ) : (nU b).det = 1 := by
  simp [nU, det_fromBlocks_zero₂₁]

/- English proof (translation)
Simplify using `[nbar, det_fromBlocks_zero₁₂]`.
-/
theorem det_nbar (c : Matrix (Fin n) (Fin n) ℂ) : (nbar c).det = 1 := by
  simp [nbar, det_fromBlocks_zero₁₂]

/- English proof (translation)
Establish `hu : IsUnit aᴴ.det`. Rewrite using `[det_conjTranspose]`. Conclude with `ha.star`. Unfold `mM`. Rewrite using `[det_fromBlocks_zero₂₁]`.

Conclude with `ha.mul (isUnit_nonsing_inv_det _ hu)`.
-/
theorem isUnit_det_mM {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a.det) : IsUnit (mM a).det := by
  have hu : IsUnit aᴴ.det := by
    rw [det_conjTranspose]
    exact ha.star
  unfold mM
  rw [det_fromBlocks_zero₂₁]
  exact ha.mul (isUnit_nonsing_inv_det _ hu)

end PositivityTheory.Rg.Sw.Glob.DecH

namespace PositivityTheory.Rg.Sw.Glob

open PositivityTheory.Rg.Sw.Glob.DecH

/- English proof (translation)
Introduce `n y`. Establish `hmul : ∀ {X Y : M2 n}, InG X → InG Y → InG (X * Y)`. Introduce `X Y hX hY`. Unfold `InG at *`. Rewrite using `[conjTranspose_mul]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = JJ n := by rw [hX, hY]`. Establish `hg : InG (mR y)` using `y.2`. Establish `hdet : IsUnit (mR y).det` using `Matrix.isUnits_det_units (y : GL (Fin n ⊕ Fin n) ℂ)`.

Take `⟨A, B, C, D, e⟩ : ∃ A B C D : Matrix (Fin n) (Fin n) ℂ, mR y = fromBlocks A B C D` from `⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩`. Rewrite `hg`, `hdet` using `[e]`. Take `⟨t, ht⟩` from `exists_real_det_ne_zero (det_sub_I_smul_ne_zero hg hdet)`. Take `⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ, P = A - (t : ℂ) • C` from `⟨_, rfl⟩`. Take `⟨Q, hQ⟩ : ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q = B - (t : ℂ) • D` from `⟨_, rfl⟩`.

Rewrite `ht` using `[← hP]`. Establish `hPu : IsUnit P.det` using `isUnit_iff_ne_zero.mpr ht`. Establish `hPHu : IsUnit Pᴴ.det`. Rewrite using `[det_conjTranspose]`. Conclude with `hPu.star`.

Establish `hshift : nU ((-(t : ℂ)) • 1) * fromBlocks A B C D = fromBlocks P Q C D`. Unfold `nU`. Rewrite using `[fromBlocks_multiply]`. Simplify using `[hP, hQ, sub_eq_add_neg]`. Establish `hG : InG (fromBlocks P Q C D)`.

Rewrite using `[← hshift]`. Conclude with `hmul (inG_nU (by simp)) hg`. Take `⟨r1, -, -⟩` from `inG_blocks hG`. Take `⟨s1, -, s3, -⟩` from `inG_blocks_dual hG`. Establish `hb : (P⁻¹ * Q)ᴴ = P⁻¹ * Q`.

Rewrite using `[conjTranspose_mul, conjTranspose_nonsing_inv]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc P⁻¹, nonsing_inv_mul _ hPu, Matrix.one_mul]`. Use `_ = P⁻¹ * (Q * Pᴴ) * Pᴴ⁻¹ := by rw [s1]`. Use `_ = P⁻¹ * Q := by`.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hPHu, Matrix.mul_one]`. Establish `hc : (C * P⁻¹)ᴴ = C * P⁻¹`. Rewrite using `[conjTranspose_mul, conjTranspose_nonsing_inv]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc (Pᴴ⁻¹), Matrix.mul_assoc Cᴴ, mul_nonsing_inv _ hPu, Matrix.mul_one]`.

Use `_ = Pᴴ⁻¹ * (Pᴴ * C) * P⁻¹ := by rw [r1]`. Use `_ = C * P⁻¹ := by`. Rewrite using `[← Matrix.mul_assoc, nonsing_inv_mul _ hPHu, Matrix.one_mul]`. Establish `hD : D = C * (P⁻¹ * Q) + Pᴴ⁻¹`. Establish `h1 : D * Pᴴ = C * Qᴴ + 1`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `hb`. Rewrite `h2` using `[conjTranspose_mul, conjTranspose_nonsing_inv]`. Combine the equalities or inequalities in the displayed calculation. Establish `hinner : nbar (C * P⁻¹) * mM P * nU (P⁻¹ * Q) = fromBlocks P Q C D`.

Unfold `nbar mM nU`. Rewrite using `[fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]`. Rewrite using `[fromBlocks_inj]`. Use `⟨rfl, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Matrix.mul_assoc, mul_nonsing_inv _ hPu, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, nonsing_inv_mul _ hPu, Matrix.mul_one]`. Rewrite using `[hD, Matrix.mul_assoc C, nonsing_inv_mul _ hPu, Matrix.mul_one]`. Establish `hfront : nU ((t : ℂ) • 1) * fromBlocks P Q C D = fromBlocks A B C D`. Unfold `nU`.

Rewrite using `[fromBlocks_multiply]`. Simplify using `[hP, hQ]`. Use `⟨mkGR (nU ((t : ℂ) • 1)) (by rw [det_nU]; exact isUnit_one) (inG_nU (by simp)), mkGR (nbar (C * P⁻¹)) (by rw [det_nbar]; exact isUnit_one) (inG_nbar hc), mkGR (mM P) (isUnit_det_mM hPu) (inG_mM hPu), mkGR (nU (P⁻¹ * Q)) (by rw [det_nU]; exact isUnit_one) (inG_nU hb), ?_, ⟨t, mR_m …` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Use `show mR y = mR _ * mR _ * mR _ * mR _`. Rewrite using `[mR_mkGR, mR_mkGR, mR_mkGR, mR_mkGR, e, ← hfront, ← hinner]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem decomp : Decomp := by
  intro n y
  have hmul : ∀ {X Y : M2 n}, InG X → InG Y → InG (X * Y) := by
    intro X Y hX hY
    unfold InG at *
    rw [conjTranspose_mul]
    calc Yᴴ * Xᴴ * JJ n * (X * Y) = Yᴴ * (Xᴴ * JJ n * X) * Y := by
          simp only [Matrix.mul_assoc]
      _ = JJ n := by rw [hX, hY]
  have hg : InG (mR y) := y.2
  have hdet : IsUnit (mR y).det := Matrix.isUnits_det_units (y : GL (Fin n ⊕ Fin n) ℂ)
  obtain ⟨A, B, C, D, e⟩ : ∃ A B C D : Matrix (Fin n) (Fin n) ℂ, mR y = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩
  rw [e] at hg hdet
  obtain ⟨t, ht⟩ := exists_real_det_ne_zero (det_sub_I_smul_ne_zero hg hdet)
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ, P = A - (t : ℂ) • C := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q = B - (t : ℂ) • D := ⟨_, rfl⟩
  rw [← hP] at ht
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr ht
  have hPHu : IsUnit Pᴴ.det := by
    rw [det_conjTranspose]
    exact hPu.star
  have hshift : nU ((-(t : ℂ)) • 1) * fromBlocks A B C D = fromBlocks P Q C D := by
    unfold nU
    rw [fromBlocks_multiply]
    simp [hP, hQ, sub_eq_add_neg]
  have hG : InG (fromBlocks P Q C D) := by
    rw [← hshift]
    exact hmul (inG_nU (by simp)) hg
  obtain ⟨r1, -, -⟩ := inG_blocks hG
  obtain ⟨s1, -, s3, -⟩ := inG_blocks_dual hG
  have hb : (P⁻¹ * Q)ᴴ = P⁻¹ * Q := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc Qᴴ * Pᴴ⁻¹ = P⁻¹ * (P * Qᴴ) * Pᴴ⁻¹ := by
          rw [← Matrix.mul_assoc P⁻¹, nonsing_inv_mul _ hPu, Matrix.one_mul]
      _ = P⁻¹ * (Q * Pᴴ) * Pᴴ⁻¹ := by rw [s1]
      _ = P⁻¹ * Q := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hPHu, Matrix.mul_one]
  have hc : (C * P⁻¹)ᴴ = C * P⁻¹ := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc Pᴴ⁻¹ * Cᴴ = Pᴴ⁻¹ * (Cᴴ * P) * P⁻¹ := by
          rw [Matrix.mul_assoc (Pᴴ⁻¹), Matrix.mul_assoc Cᴴ, mul_nonsing_inv _ hPu, Matrix.mul_one]
      _ = Pᴴ⁻¹ * (Pᴴ * C) * P⁻¹ := by rw [r1]
      _ = C * P⁻¹ := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hPHu, Matrix.one_mul]
  have hD : D = C * (P⁻¹ * Q) + Pᴴ⁻¹ := by
    have h1 : D * Pᴴ = C * Qᴴ + 1 := by
      calc D * Pᴴ = C * Qᴴ - (C * Qᴴ - D * Pᴴ) := by abel
        _ = C * Qᴴ + 1 := by rw [s3]; abel
    have h2 := hb
    rw [conjTranspose_mul, conjTranspose_nonsing_inv] at h2
    calc D = D * Pᴴ * Pᴴ⁻¹ := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hPHu, Matrix.mul_one]
      _ = (C * Qᴴ + 1) * Pᴴ⁻¹ := by rw [h1]
      _ = C * (Qᴴ * Pᴴ⁻¹) + Pᴴ⁻¹ := by rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = C * (P⁻¹ * Q) + Pᴴ⁻¹ := by rw [h2]
  have hinner : nbar (C * P⁻¹) * mM P * nU (P⁻¹ * Q) = fromBlocks P Q C D := by
    unfold nbar mM nU
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [fromBlocks_inj]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · rw [← Matrix.mul_assoc, mul_nonsing_inv _ hPu, Matrix.one_mul]
    · rw [Matrix.mul_assoc, nonsing_inv_mul _ hPu, Matrix.mul_one]
    · rw [hD, Matrix.mul_assoc C, nonsing_inv_mul _ hPu, Matrix.mul_one]
  have hfront : nU ((t : ℂ) • 1) * fromBlocks P Q C D = fromBlocks A B C D := by
    unfold nU
    rw [fromBlocks_multiply]
    simp [hP, hQ]
  refine ⟨mkGR (nU ((t : ℂ) • 1)) (by rw [det_nU]; exact isUnit_one) (inG_nU (by simp)),
    mkGR (nbar (C * P⁻¹)) (by rw [det_nbar]; exact isUnit_one) (inG_nbar hc),
    mkGR (mM P) (isUnit_det_mM hPu) (inG_mM hPu),
    mkGR (nU (P⁻¹ * Q)) (by rw [det_nU]; exact isUnit_one) (inG_nU hb), ?_,
    ⟨t, mR_mkGR _ _ _⟩, ⟨C * P⁻¹, hc, mR_mkGR _ _ _⟩, ⟨P, hPu, mR_mkGR _ _ _⟩,
    ⟨P⁻¹ * Q, hb, mR_mkGR _ _ _⟩⟩
  apply Subtype.ext
  apply Units.ext
  show mR y = mR _ * mR _ * mR _ * mR _
  rw [mR_mkGR, mR_mkGR, mR_mkGR, mR_mkGR, e, ← hfront, ← hinner]
  simp only [Matrix.mul_assoc]

end PositivityTheory.Rg.Sw.Glob
