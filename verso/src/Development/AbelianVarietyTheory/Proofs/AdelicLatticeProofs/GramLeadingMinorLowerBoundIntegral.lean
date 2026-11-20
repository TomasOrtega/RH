import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Use `⟨(hA.eigenvectorUnitary : Matrix n n ℝ), Unitary.coe_mul_star_self _, ?_⟩` and prove the remaining obligations. Establish `hU : (hA.eigenvectorUnitary : Matrix n n ℝ) * star (hA.eigenvectorUnitary : Matrix n n ℝ) = 1` using `Unitary.coe_mul_star_self _`. Establish `hD : diagonal (fun i => hA.eigenvalues i + t) = diagonal (RCLike.ofReal ∘ hA.eigenvalues) + t • (1 : Matrix n n ℝ)`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [diagonal, h]`.

Use `conv_lhs => rw [hA.spectral_theorem]`. Rewrite using `[Unitary.conjStarAlgAut_apply, hD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← star_eq_conjTranspose, hU]`.
-/
theorem gramLB_shift {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (t : ℝ) :
    ∃ U : Matrix n n ℝ, U * Uᴴ = 1 ∧
      A + t • (1 : Matrix n n ℝ) = U * diagonal (fun i => hA.eigenvalues i + t) * Uᴴ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℝ), Unitary.coe_mul_star_self _, ?_⟩
  have hU : (hA.eigenvectorUnitary : Matrix n n ℝ) * star (hA.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    Unitary.coe_mul_star_self _
  have hD : diagonal (fun i => hA.eigenvalues i + t) =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) + t • (1 : Matrix n n ℝ) := by
    ext i j
    by_cases h : i = j <;> simp [diagonal, h]
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, hD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, ← star_eq_conjTranspose, hU]

/- English proof (translation)
Take `⟨U, hU, hEq⟩` from `gramLB_shift hR.1 1`. Rewrite `hEq` using `[one_smul]`. Establish `hdet : U.det * Uᴴ.det = 1` using `by rw [← det_mul, hU, det_one]`. Rewrite using `[hEq, det_mul, det_mul, det_diagonal]`. Establish `e : U.det * (∏ i, (hR.1.eigenvalues i + 1)) * Uᴴ.det = ∏ i, (hR.1.eigenvalues i + 1)`.

Take the linear combination `(∏ i, (hR.1.eigenvalues i + 1)) * hdet`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem gramLB_one_le_det {n : Type} [Fintype n] [DecidableEq n] {R : Matrix n n ℝ}
    (hR : R.PosSemidef) : 1 ≤ (R + 1).det := by
  obtain ⟨U, hU, hEq⟩ := gramLB_shift hR.1 1
  rw [one_smul] at hEq
  have hdet : U.det * Uᴴ.det = 1 := by rw [← det_mul, hU, det_one]
  rw [hEq, det_mul, det_mul, det_diagonal]
  have e : U.det * (∏ i, (hR.1.eigenvalues i + 1)) * Uᴴ.det = ∏ i, (hR.1.eigenvalues i + 1) := by
    linear_combination (∏ i, (hR.1.eigenvalues i + 1)) * hdet
  rw [e]
  calc (1 : ℝ) = ∏ _i : n, (1 : ℝ) := by simp
    _ ≤ ∏ i, (hR.1.eigenvalues i + 1) :=
      Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => by linarith [hR.eigenvalues_nonneg i]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ i, m ≤ hA.1.eigenvalues i := by`. Break down `isEmpty_or_nonempty n with hn | hn` into its components or cases. Conclude with `⟨1, one_pos, fun i => isEmptyElim i⟩`. Take `⟨i0, hi0⟩` from `Finite.exists_min hA.1.eigenvalues`. Conclude with `⟨_, hA.eigenvalues_pos i0, hi0⟩`.

Use `⟨min 1 m, lt_min one_pos hm0, min_le_left _ _, ?_⟩` and prove the remaining obligations. Take `⟨U, -, hEq⟩` from `gramLB_shift hA.1 (-(min 1 m))`. Rewrite using `[sub_eq_add_neg, ← neg_smul, hEq]`. Conclude with `(posSemidef_diagonal_iff.2 fun i => by linarith [hm i, min_le_right 1 m]).mul_mul_conjTranspose_same U`.
-/
theorem gramLB_exists_shift {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosDef) : ∃ k : ℝ, 0 < k ∧ k ≤ 1 ∧ (A - k • (1 : Matrix n n ℝ)).PosSemidef := by
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ i, m ≤ hA.1.eigenvalues i := by
    rcases isEmpty_or_nonempty n with hn | hn
    · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
    · obtain ⟨i0, hi0⟩ := Finite.exists_min hA.1.eigenvalues
      exact ⟨_, hA.eigenvalues_pos i0, hi0⟩
  refine ⟨min 1 m, lt_min one_pos hm0, min_le_left _ _, ?_⟩
  obtain ⟨U, -, hEq⟩ := gramLB_shift hA.1 (-(min 1 m))
  rw [sub_eq_add_neg, ← neg_smul, hEq]
  exact (posSemidef_diagonal_iff.2 fun i => by linarith [hm i, min_le_right 1 m]).mul_mul_conjTranspose_same U

open scoped MatrixOrder in
/- English proof (translation)
Take `⟨U, hU, hEq⟩` from `gramLB_shift hP.1 0`. Simplify using `only [zero_smul, add_zero] at hEq`. Establish `hd : ∀ i, 0 < hP.1.eigenvalues i` using `hP.eigenvalues_pos`. Establish `hUU : Uᴴ * U = 1` using `mul_eq_one_comm.mp hU`. Set `s : n → ℝ` to `fun i => (Real.sqrt (hP.1.eigenvalues i))⁻¹`.

Set `B : Matrix n n ℝ` to `U * diagonal s`. Establish `hBt : Bᴴ = diagonal s * Uᴴ`. Simplify using `[B]`. Establish `hBPB : Bᴴ * P * B = 1`. Rewrite using `[hBt, hEq]`.

Simplify using `only [B, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul, ← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `hs : Real.sqrt (hP.1.eigenvalues i) * Real.sqrt (hP.1.eigenvalues i) = hP.1.eigenvalues i` using `Real.mul_self_sqrt (hd i).le`.

Establish `hs0 : Real.sqrt (hP.1.eigenvalues i) ≠ 0` using `(Real.sqrt_pos.2 (hd i)).ne'`. Simplify using `only [s]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try nlinarith [hs, Real.sq_sqrt (hd i).le]`. Establish `hsum : Bᴴ * (P + Q) * B = 1 + Bᴴ * Q * B`.

Rewrite using `[Matrix.mul_add, Matrix.add_mul, hBPB]`. Establish `h1 : Bᴴ.det * B.det * P.det = 1`. Establish `e` using `congrArg det hBPB`. Rewrite `e` using `[det_mul, det_mul, det_one]`. Take the linear combination `e`.

Establish `h2 : Bᴴ.det * B.det * (P + Q).det = (1 + Bᴴ * Q * B).det`. Rewrite using `[← hsum, det_mul (Bᴴ * (P + Q)) B, det_mul Bᴴ (P + Q)]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : 1 ≤ (1 + Bᴴ * Q * B).det`. Rewrite using `[add_comm]`.

Conclude with `gramLB_one_le_det (hQ.conjTranspose_mul_mul_same B)`. Establish `hc : 0 < Bᴴ.det * B.det`. Use `hP.det_pos` as an intermediate fact. Assume the negation of the conclusion as `hneg`. Use polynomial arithmetic with `[not_lt.mp hneg]`.

Conclude with `le_of_mul_le_mul_left (by linarith) hc`.
-/
theorem gramLB_det_mono {n : Type} [Fintype n] [DecidableEq n] {P Q : Matrix n n ℝ}
    (hP : P.PosDef) (hQ : Q.PosSemidef) : P.det ≤ (P + Q).det := by
  obtain ⟨U, hU, hEq⟩ := gramLB_shift hP.1 0
  simp only [zero_smul, add_zero] at hEq
  have hd : ∀ i, 0 < hP.1.eigenvalues i := hP.eigenvalues_pos
  have hUU : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  let s : n → ℝ := fun i => (Real.sqrt (hP.1.eigenvalues i))⁻¹
  let B : Matrix n n ℝ := U * diagonal s
  have hBt : Bᴴ = diagonal s * Uᴴ := by
    simp [B]
  have hBPB : Bᴴ * P * B = 1 := by
    rw [hBt, hEq]
    simp only [B, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul, ← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul,
      diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hs : Real.sqrt (hP.1.eigenvalues i) * Real.sqrt (hP.1.eigenvalues i) = hP.1.eigenvalues i :=
      Real.mul_self_sqrt (hd i).le
    have hs0 : Real.sqrt (hP.1.eigenvalues i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
    simp only [s]
    field_simp
    try nlinarith [hs, Real.sq_sqrt (hd i).le]
  have hsum : Bᴴ * (P + Q) * B = 1 + Bᴴ * Q * B := by
    rw [Matrix.mul_add, Matrix.add_mul, hBPB]
  have h1 : Bᴴ.det * B.det * P.det = 1 := by
    have e := congrArg det hBPB
    rw [det_mul, det_mul, det_one] at e
    linear_combination e
  have h2 : Bᴴ.det * B.det * (P + Q).det = (1 + Bᴴ * Q * B).det := by
    rw [← hsum, det_mul (Bᴴ * (P + Q)) B, det_mul Bᴴ (P + Q)]
    ring
  have h3 : 1 ≤ (1 + Bᴴ * Q * B).det := by
    rw [add_comm]
    exact gramLB_one_le_det (hQ.conjTranspose_mul_mul_same B)
  have hc : 0 < Bᴴ.det * B.det := by
    have := hP.det_pos
    by_contra hneg
    nlinarith [not_lt.mp hneg]
  exact le_of_mul_le_mul_left (by linarith) hc

/- English proof (translation)
Rewrite using `[← conjTranspose_eq_transpose_of_trivial]`. Conclude with `PosDef.conjTranspose_mul_self g (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det g).2 (Ne.isUnit hg)))`.
-/
theorem gramLB_posDef {n : Type} [Fintype n] [DecidableEq n] {g : Matrix n n ℝ}
    (hg : g.det ≠ 0) : (gᵀ * g).PosDef := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact PosDef.conjTranspose_mul_self g
    (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det g).2 (Ne.isUnit hg)))

/- English proof (translation)
Introduce `N g hg`. Take `⟨k, hk0, hk1, hkQ⟩` from `gramLB_exists_shift (gramLB_posDef hg)`. Use `⟨k ^ N, pow_pos hk0 N, fun γ hγ j hj => ?_⟩` and prove the remaining obligations. Use `set Γ : Matrix (Fin N) (Fin N) ℝ := γ.map (Int.cast : ℤ → ℝ) with hΓ`. Use `set E : Fin j → Fin N := Fin.castLE hj with hE`.

Set `C : Matrix (Fin N) (Fin j) ℝ` to `Γ.submatrix id E`. Set `Cz : Matrix (Fin N) (Fin j) ℤ` to `γ.submatrix id E`. Establish `hGram : ((g * Γ)ᵀ * (g * Γ)).submatrix E E = Cᵀ * (gᵀ * g) * C`. Establish `e1 : (g * Γ)ᵀ * (g * Γ) = Γᵀ * (gᵀ * g) * Γ`. Rewrite using `[transpose_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e1, Matrix.submatrix_mul _ _ E id E Function.bijective_id, Matrix.submatrix_mul _ _ E id id Function.bijective_id, submatrix_id_id, transpose_submatrix]`. Establish `hsplit : Cᵀ * (gᵀ * g) * C = k • (Cᵀ * C) + Cᵀ * (gᵀ * g - k • 1) * C`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]`. Normalize the expressions using the abelian group laws.

Establish `hΓdet : Γ.det ≠ 0`. Establish `e` using `(Int.castRingHom ℝ).map_det γ`. Rewrite using `[show Γ = (Int.castRingHom ℝ).mapMatrix γ from rfl, ← e]`. Simplify using `using hγ`. Establish `hCinj : Function.Injective C.mulVec`.

Establish `hC : C = Γ * (1 : Matrix (Fin N) (Fin N) ℝ).submatrix id E`. Rewrite using `[← Matrix.submatrix_id_id Γ, ← Matrix.submatrix_mul _ _ id id E Function.bijective_id, Matrix.mul_one]`. Establish `hI : Function.Injective ((1 : Matrix (Fin N) (Fin N) ℝ).submatrix id E).mulVec`. Introduce `x y hxy`. Use function extensionality and compare the values at `a`.

Establish `hEinj : Function.Injective E` using `Fin.castLE_injective hj`. Establish `e` using `congrFun hxy (E a)`. Simplify `e` using `[mulVec, dotProduct, Matrix.one_apply, hEinj.eq_iff]`. Rewrite using `[hC]`. Introduce `x y hxy`.

Rewrite `hxy` using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Conclude with `hI (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det Γ).2 (Ne.isUnit hΓdet)) hxy)`. Establish `hCC : (Cᵀ * C).PosDef`. Rewrite using `[← conjTranspose_eq_transpose_of_trivial]`. Conclude with `PosDef.conjTranspose_mul_self C hCinj`.

Establish `hQ' : (Cᵀ * (gᵀ * g - k • 1) * C).PosSemidef`. Rewrite using `[← conjTranspose_eq_transpose_of_trivial]`. Conclude with `hkQ.conjTranspose_mul_mul_same C`. Establish `hCz : Cᵀ * C = (Int.castRingHom ℝ).mapMatrix (Czᵀ * Cz)`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]`.

Both sides reduce to the same expression. Establish `hdet1 : 1 ≤ (Cᵀ * C).det`. Establish `hpos` using `hCC.det_pos`. Rewrite `hpos` using `[hCz, ← RingHom.map_det, eq_intCast]`. Rewrite using `[hCz, ← RingHom.map_det, eq_intCast]`.

Establish `hz : 0 < (Czᵀ * Cz).det` using `by exact_mod_cast hpos`. Establish `hz1 : (1 : ℤ) ≤ (Czᵀ * Cz).det` using `hz`. Conclude with `hz1` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation.
-/
theorem gram_leading_minor_lower_bound :
    ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∀ γ : Matrix (Fin N) (Fin N) ℤ, γ.det ≠ 0 → ∀ (j : ℕ) (h : j ≤ N), c ≤ (((g * γ.map (Int.cast : ℤ → ℝ))ᵀ * (g * γ.map (Int.cast : ℤ → ℝ))).submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  intro N g hg
  obtain ⟨k, hk0, hk1, hkQ⟩ := gramLB_exists_shift (gramLB_posDef hg)
  refine ⟨k ^ N, pow_pos hk0 N, fun γ hγ j hj => ?_⟩
  set Γ : Matrix (Fin N) (Fin N) ℝ := γ.map (Int.cast : ℤ → ℝ) with hΓ
  set E : Fin j → Fin N := Fin.castLE hj with hE
  let C : Matrix (Fin N) (Fin j) ℝ := Γ.submatrix id E
  let Cz : Matrix (Fin N) (Fin j) ℤ := γ.submatrix id E
  have hGram : ((g * Γ)ᵀ * (g * Γ)).submatrix E E = Cᵀ * (gᵀ * g) * C := by
    have e1 : (g * Γ)ᵀ * (g * Γ) = Γᵀ * (gᵀ * g) * Γ := by
      rw [transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [e1, Matrix.submatrix_mul _ _ E id E Function.bijective_id,
      Matrix.submatrix_mul _ _ E id id Function.bijective_id, submatrix_id_id, transpose_submatrix]
  have hsplit : Cᵀ * (gᵀ * g) * C = k • (Cᵀ * C) + Cᵀ * (gᵀ * g - k • 1) * C := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    abel
  have hΓdet : Γ.det ≠ 0 := by
    have e := (Int.castRingHom ℝ).map_det γ
    rw [show Γ = (Int.castRingHom ℝ).mapMatrix γ from rfl, ← e]
    simpa using hγ
  have hCinj : Function.Injective C.mulVec := by
    have hC : C = Γ * (1 : Matrix (Fin N) (Fin N) ℝ).submatrix id E := by
      rw [← Matrix.submatrix_id_id Γ, ← Matrix.submatrix_mul _ _ id id E Function.bijective_id,
        Matrix.mul_one]
    have hI : Function.Injective ((1 : Matrix (Fin N) (Fin N) ℝ).submatrix id E).mulVec := by
      intro x y hxy
      funext a
      have hEinj : Function.Injective E := Fin.castLE_injective hj
      have e := congrFun hxy (E a)
      simpa [mulVec, dotProduct, Matrix.one_apply, hEinj.eq_iff] using e
    rw [hC]
    intro x y hxy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hxy
    exact hI (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det Γ).2 (Ne.isUnit hΓdet)) hxy)
  have hCC : (Cᵀ * C).PosDef := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact PosDef.conjTranspose_mul_self C hCinj
  have hQ' : (Cᵀ * (gᵀ * g - k • 1) * C).PosSemidef := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hkQ.conjTranspose_mul_mul_same C
  have hCz : Cᵀ * C = (Int.castRingHom ℝ).mapMatrix (Czᵀ * Cz) := by
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]
    rfl
  have hdet1 : 1 ≤ (Cᵀ * C).det := by
    have hpos := hCC.det_pos
    rw [hCz, ← RingHom.map_det, eq_intCast] at hpos
    rw [hCz, ← RingHom.map_det, eq_intCast]
    have hz : 0 < (Czᵀ * Cz).det := by exact_mod_cast hpos
    have hz1 : (1 : ℤ) ≤ (Czᵀ * Cz).det := hz
    exact_mod_cast hz1
  calc k ^ N ≤ k ^ j := pow_le_pow_of_le_one hk0.le hk1 hj
    _ ≤ k ^ j * (Cᵀ * C).det := le_mul_of_one_le_right (pow_nonneg hk0.le _) hdet1
    _ = (k • (Cᵀ * C)).det := by rw [det_smul, Fintype.card_fin]
    _ ≤ (k • (Cᵀ * C) + Cᵀ * (gᵀ * g - k • 1) * C).det := gramLB_det_mono (hCC.smul hk0) hQ'
    _ = _ := by rw [← hsplit, ← hGram]

end GlobalTheory.ClassFin
