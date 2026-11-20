import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkM

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

open MeasureTheory Matrix

/- English proof (translation)
Use extensionality with `i j`. Take `⟨i', rfl⟩` from `finSumFinEquiv.surjective i`. Take `⟨j', rfl⟩` from `finSumFinEquiv.surjective j`. Apply the tactic sequence `rcases i' with i' | i' <;> rcases j' with j' | j'`. Simplify using `[blkM, Matrix.one_apply]`.

Establish `h : ¬Fin.castAdd 1 i' = Fin.natAdd n j'`. Rewrite using `[Fin.ext_iff]`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using `[blkM, Matrix.one_apply, h]`.

Establish `h : ¬Fin.natAdd n i' = Fin.castAdd 1 j'`. Rewrite using `[Fin.ext_iff]`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using `[blkM, Matrix.one_apply, h]`.

Take `rfl` from `Subsingleton.elim i' j'`. Simplify using `[blkM]`.
-/
theorem one_add_I_blkM_eq {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) + Complex.I • blkM b u d =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (1 + Complex.I • b) (Complex.I • Matrix.replicateCol (Fin 1) u)
          (Complex.I • Matrix.replicateRow (Fin 1) (star u))
          (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ))) := by
  ext i j
  obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · simp [blkM, Matrix.one_apply]
  · have h : ¬Fin.castAdd 1 i' = Fin.natAdd n j' := by
      rw [Fin.ext_iff]; simp; omega
    simp [blkM, Matrix.one_apply, h]
  · have h : ¬Fin.natAdd n i' = Fin.castAdd 1 j' := by
      rw [Fin.ext_iff]; simp; omega
    simp [blkM, Matrix.one_apply, h]
  · obtain rfl := Subsingleton.elim i' j'
    simp [blkM]

/- English proof (translation)
Rewrite using `[one_add_I_blkM_eq, Matrix.det_reindex_self]`. Use `set D : Matrix (Fin n) (Fin n) ℂ := 1 + Complex.I • b with hD`. Use `set u : Fin n → ℂ := D *ᵥ v with hu`. Establish `hcol : D * Matrix.replicateCol (Fin 1) v = Matrix.replicateCol (Fin 1) u`. Use extensionality with `i j`.

Simplify using `[hu, Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Establish `hmul : Matrix.fromBlocks D (Complex.I • Matrix.replicateCol (Fin 1) u) (Complex.I • Matrix.replicateRow (Fin 1) (star u)) (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ)) * Matrix.fromBlocks 1 (-Complex.I • Matrix.replicateCol (Fin 1) v) 0 (1 : Matrix (Fin 1) (Fin 1) ℂ) = Matrix.fr …`. Rewrite using `[Matrix.fromBlocks_multiply]`. Use `congr 1`. Simplify using the standard rewrite rules.

Simplify using `[Matrix.mul_smul, hcol]`. Simplify using the standard rewrite rules. Use extensionality with `i j`. Establish `hI : Complex.I * Complex.I = -1` using `Complex.I_mul_I`. Simplify using `[Matrix.mul_apply, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm]`.

Simplify using `only [← mul_assoc, hI, neg_mul, one_mul, Finset.sum_neg_distrib, neg_neg]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdet` using `congrArg Matrix.det hmul`. Rewrite `hdet` using `[Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂]`. Simplify using `using hdet`.
-/
theorem det_one_add_I_blkM {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (d : ℝ) :
    Matrix.det (1 + Complex.I • blkM b ((1 + Complex.I • b) *ᵥ v) d) =
      Matrix.det (1 + Complex.I • b) *
        (1 + Complex.I * (d : ℂ) + star ((1 + Complex.I • b) *ᵥ v) ⬝ᵥ v) := by
  rw [one_add_I_blkM_eq, Matrix.det_reindex_self]
  set D : Matrix (Fin n) (Fin n) ℂ := 1 + Complex.I • b with hD
  set u : Fin n → ℂ := D *ᵥ v with hu
  have hcol : D * Matrix.replicateCol (Fin 1) v = Matrix.replicateCol (Fin 1) u := by
    ext i j
    simp [hu, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hmul :
      Matrix.fromBlocks D (Complex.I • Matrix.replicateCol (Fin 1) u)
          (Complex.I • Matrix.replicateRow (Fin 1) (star u))
          (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ)) *
        Matrix.fromBlocks 1 (-Complex.I • Matrix.replicateCol (Fin 1) v) 0
          (1 : Matrix (Fin 1) (Fin 1) ℂ) =
      Matrix.fromBlocks D 0 (Complex.I • Matrix.replicateRow (Fin 1) (star u))
        (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ) + star u ⬝ᵥ v) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp [Matrix.mul_smul, hcol]
    · simp
    · ext i j
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      simp [Matrix.mul_apply, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm]
      simp only [← mul_assoc, hI, neg_mul, one_mul, Finset.sum_neg_distrib, neg_neg]
      ring
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂] at hdet
  simpa using hdet

/- English proof (translation)
Establish `h : star (star v ⬝ᵥ (b *ᵥ v)) = star v ⬝ᵥ (b *ᵥ v)`. Rewrite using `[← Matrix.star_dotProduct, Matrix.star_mulVec, hb.eq, Matrix.dotProduct_mulVec]`. Conclude with `Complex.conj_eq_iff_re.1 h`.
-/
theorem quad_real {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (v : Fin n → ℂ) :
    ((star v ⬝ᵥ (b *ᵥ v)).re : ℂ) = star v ⬝ᵥ (b *ᵥ v) := by
  have h : star (star v ⬝ᵥ (b *ᵥ v)) = star v ⬝ᵥ (b *ᵥ v) := by
    rw [← Matrix.star_dotProduct, Matrix.star_mulVec, hb.eq, Matrix.dotProduct_mulVec]
  exact Complex.conj_eq_iff_re.1 h

/- English proof (translation)
Rewrite using `[quad_real hb, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]`. Establish `hH : (1 + Complex.I • b)ᴴ = 1 - Complex.I • b`. Simplify using `[Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hb.eq, sub_eq_add_neg]`. Rewrite using `[hH, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]`. Use `congr 1`.

Simplify using `[dotProduct, Complex.normSq_eq_conj_mul_self]`.
-/
theorem star_mulVec_dot {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (v : Fin n → ℂ) :
    star ((1 + Complex.I • b) *ᵥ v) ⬝ᵥ v =
      ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) - Complex.I * ((star v ⬝ᵥ (b *ᵥ v)).re : ℂ) := by
  rw [quad_real hb, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  have hH : (1 + Complex.I • b)ᴴ = 1 - Complex.I • b := by
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hb.eq, sub_eq_add_neg]
  rw [hH, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]
  congr 1
  simp [dotProduct, Complex.normSq_eq_conj_mul_self]

/- English proof (translation)
Rewrite using `[det_one_add_I_blkM, map_mul, star_mulVec_dot hb]`. Use `congr 1`. Use `set r : ℝ := ∑ i, Complex.normSq (v i)`. Use `set m : ℝ := (star v ⬝ᵥ (b *ᵥ v)).re`. Establish `: (1 + Complex.I * (d : ℂ) + ((r : ℂ) - Complex.I * (m : ℂ))) = (((1 + r : ℝ) : ℂ)) + (((d - m : ℝ) : ℂ)) * Complex.I` using `by push_cast; ring`.

Rewrite using `[this, Complex.normSq_add_mul_I]`.
-/
theorem normSq_det_one_add_I_blkM (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian)
    (_hdet : Matrix.det (1 + Complex.I • b) ≠ 0) (v : Fin n → ℂ) (d : ℝ) :
    Complex.normSq (Matrix.det (1 + Complex.I • blkM b ((1 + Complex.I • b) *ᵥ v) d)) =
      Complex.normSq (Matrix.det (1 + Complex.I • b)) *
        ((1 + ∑ i, Complex.normSq (v i)) ^ 2 + (d - (star v ⬝ᵥ (b *ᵥ v)).re) ^ 2) := by
  rw [det_one_add_I_blkM, map_mul, star_mulVec_dot hb]
  congr 1
  set r : ℝ := ∑ i, Complex.normSq (v i)
  set m : ℝ := (star v ⬝ᵥ (b *ᵥ v)).re
  have : (1 + Complex.I * (d : ℂ) + ((r : ℂ) - Complex.I * (m : ℂ))) =
      (((1 + r : ℝ) : ℂ)) + (((d - m : ℝ) : ℂ)) * Complex.I := by
    push_cast; ring
  rw [this, Complex.normSq_add_mul_I]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
