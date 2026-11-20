import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

namespace GlobalTheory.RealLift.SpLie

open Matrix

def sgnD {p q : ℕ} : Ix p q → ℂ
  | .inl _ => 1
  | .inr _ => -1

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;>`. Apply the tactic sequence `simp [Jm, Formalism.UG.Jpq, sgnD, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp`.
-/
theorem Jm_eq_diagonal (p q : ℕ) : Jm p q = Matrix.diagonal sgnD := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, sgnD, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

/- English proof (translation)
Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp [lineSign, sgnD]`.
-/
theorem lineSign_eq_mul {p q r s : ℕ} (a : Ix p q) (b : Ix r s) : lineSign a b = sgnD a * sgnD b := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign, sgnD]

/- English proof (translation)
Establish `h : (Yᴴ * Jm r s + Jm r s * Y) b k = 0`. Rewrite using `[show Yᴴ * Jm r s + Jm r s * Y = 0 from hY]`. Both sides reduce to the same expression. Rewrite `h` using `[Jm_eq_diagonal]`. Simplify `h` using `[Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]`.
-/
theorem upq_entry {r s : ℕ} {Y : Mat r s} (hY : Y ∈ upq r s) (b k : Ix r s) :
    star (Y k b) * sgnD k + sgnD b * Y b k = 0 := by
  have h : (Yᴴ * Jm r s + Jm r s * Y) b k = 0 := by
    rw [show Yᴴ * Jm r s + Jm r s * Y = 0 from hY]; rfl
  rw [Jm_eq_diagonal] at h
  simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h

/- English proof (translation)
Simplify using `[sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, ite_mul, Finset.sum_ite_eq]`. Simplify using `only [mul_comm (v _)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sympl_eq_dot {l : Type} [Fintype l] [DecidableEq l] (u v : l ⊕ l → ℝ) :
    sympl u v = -(u ⬝ᵥ (Matrix.J l ℝ *ᵥ v)) := by
  simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.one_apply, ite_mul, Finset.sum_ite_eq]
  simp only [mul_comm (v _)]
  ring

/- English proof (translation)
Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Establish `e1 : ∀ b, lineSign a b * (c * Yᵀ) a b * star (c' a b) = ∑ k, sgnD a * c a k * star (c' a b) * (sgnD b * Y b k)`. Introduce `b`. Rewrite using `[lineSign_eq_mul, mul_apply, Finset.mul_sum, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [transpose_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∀ b, lineSign a b * c a b * star ((c' * Yᵀ) a b) = ∑ k, sgnD a * c a b * star (c' a k) * (sgnD b * star (Y b k))`. Introduce `b`.

Rewrite using `[lineSign_eq_mul, mul_apply, star_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [transpose_apply, star_mul']`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e1, e2]`.

Rewrite using `[Finset.sum_comm (f := fun b k => sgnD a * c a b * star (c' a k) * (sgnD b * star (Y b k))), ← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `linear_combination (sgnD a * c a k * star (c' a b)) * upq_entry hY b k`.
-/
theorem sum_zero {P Q R S : ℕ} (c c' : Matrix (Ix P Q) (Ix R S) ℂ) (Y : Mat R S) (hY : Y ∈ upq R S) :
    (∑ a, ∑ b, lineSign a b * (c * Yᵀ) a b * star (c' a b)) +
      ∑ a, ∑ b, lineSign a b * c a b * star ((c' * Yᵀ) a b) = 0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  have e1 : ∀ b, lineSign a b * (c * Yᵀ) a b * star (c' a b) =
      ∑ k, sgnD a * c a k * star (c' a b) * (sgnD b * Y b k) := by
    intro b
    rw [lineSign_eq_mul, mul_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [transpose_apply]; ring
  have e2 : ∀ b, lineSign a b * c a b * star ((c' * Yᵀ) a b) =
      ∑ k, sgnD a * c a b * star (c' a k) * (sgnD b * star (Y b k)) := by
    intro b
    rw [lineSign_eq_mul, mul_apply, star_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [transpose_apply, star_mul']; ring
  simp only [e1, e2]
  rw [Finset.sum_comm (f := fun b k => sgnD a * c a b * star (c' a k) * (sgnD b * star (Y b k))),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  linear_combination (sgnD a * c a k * star (c' a b)) * upq_entry hY b k

/- English proof (translation)
Rewrite using `[LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]`. Use `show Zᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -Z`. Use extensionality with `a b`. Establish `h1` using `h (Pi.single a 1) (Pi.single b 1)`. Rewrite `h1` using `[sympl_eq_dot, sympl_eq_dot]`.

Simplify using `[mulVec, dotProduct, Pi.single_apply, mul_apply] at h1 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mem_sp_of_sympl {l : Type} [Fintype l] [DecidableEq l] (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ u v, sympl (Z *ᵥ u) v + sympl u (Z *ᵥ v) = 0) : Z ∈ LieAlgebra.Symplectic.sp l ℝ := by
  rw [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  show Zᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -Z
  ext a b
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  rw [sympl_eq_dot, sympl_eq_dot] at h1
  simp [mulVec, dotProduct, Pi.single_apply, mul_apply] at h1 ⊢
  linarith

/- English proof (translation)
Introduce `ι l _ _ _ _ P Q R S φ hφ Y hY`. Set `G : (ι → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (ι → Matrix (Ix P Q) (Ix R S) ℂ)` to `{ toFun := fun c w => c w * (Y w)ᵀ map_add' := fun c c' => by ext w : 1; simp [Matrix.add_mul] map_smul' := fun r c => by ext w : 1; simp [Matrix.smul_mul] }`. Use `set Z := LinearMap.toMatrix' (φ.toLinearMap ∘ₗ G ∘ₗ φ.symm.toLinearMap) with hZdef`. Establish `hZ : ∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ`. Introduce `c`.

Rewrite using `[hZdef, LinearMap.toMatrix'_mulVec]`. Simplify using `[G]`. Use `⟨Z, ?_, hZ, ?_⟩` and prove the remaining obligations. Use `mem_sp_of_sympl Z fun u v => ?_` and prove the remaining obligations. Take `⟨c, rfl⟩` from `φ.surjective u`.

Take `⟨c', rfl⟩` from `φ.surjective v`. Establish `hs : (∑ w, ∑ a, ∑ b, lineSign a b * (c w * (Y w)ᵀ) a b * star (c' w a b)) + (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star ((c' w * (Y w)ᵀ) a b)) = 0`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_eq_zero fun w _ => sum_zero _ _ _ (hY w)`. Rewrite using `[hZ, hZ, hφ, hφ, ← mul_add, ← Complex.add_im]`.

Simplify using `only [hs, Complex.zero_im, mul_zero]`. Introduce `t c`. Establish `hpow : ∀ (n : ℕ) (c : ι → Matrix (Ix P Q) (Ix R S) ℂ), (t • Z) ^ n *ᵥ φ c = φ fun w => c w * ((t • Y w) ^ n)ᵀ`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro c`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `c`. Rewrite using `[pow_succ, ← mulVec_mulVec, Matrix.smul_mulVec, hZ, ← φ.map_smul]`.

Establish `: (t • fun w => c w * (Y w)ᵀ) = fun w => c w * (t • Y w)ᵀ`. Use function extensionality and compare the values at `w`. Simplify using `[Matrix.transpose_smul, Matrix.mul_smul]`. Rewrite using `[this, ih]`. Use `congr 1`.

Use function extensionality and compare the values at `w`. Rewrite using `[pow_succ, Matrix.transpose_mul, Matrix.mul_assoc]`. Use `letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra`. Use `letI : NormedRing (Mat R S) := Matrix.linftyOpNormedRing`.

Use `letI : NormedAlgebra ℝ (Mat R S) := Matrix.linftyOpNormedAlgebra`. Establish `h1 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • (t • Z) ^ n) *ᵥ φ c) (NormedSpace.exp (t • Z) *ᵥ φ c)` using `(NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Z)).map (Matrix.mulVec.addMonoidHomLeft (φ c)) (Continuous.matrix_mulVec continuous_id continuous_const)`. Establish `hw : ∀ w, HasSum (fun n : ℕ => c w * (((n.factorial : ℝ)⁻¹ • (t • Y w) ^ n))ᵀ) (c w * (NormedSpace.exp (t • Y w))ᵀ)`. Introduce `w`. Use `(NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Y w)).matrix_transpose` as an intermediate fact.

Conclude with `this.map (AddMonoidHom.mk' (fun M => c w * M) fun _ _ => Matrix.mul_add _ _ _) (continuous_const.matrix_mul continuous_id)`. Establish `h2` using `(Pi.hasSum.2 hw).map φ (LinearMap.continuous_of_finiteDimensional φ.toLinearMap)`. Use `h1.unique ?_` and prove the remaining obligations. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `n`.

Simplify using `only [Function.comp_def]`. Rewrite using `[Matrix.smul_mulVec, hpow, ← φ.map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `w`. Simplify using `[Matrix.transpose_smul, Matrix.mul_smul]`.
-/
theorem exists_sp_rightAct : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ Y : ι → Mat R S, (∀ w, Y w ∈ upq R S) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) ∧
      ∀ (t : ℝ) c, NormedSpace.exp (t • Z) *ᵥ φ c = φ fun w => c w * (NormedSpace.exp (t • Y w))ᵀ := by
  intro ι l _ _ _ _ P Q R S φ hφ Y hY
  let G : (ι → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (ι → Matrix (Ix P Q) (Ix R S) ℂ) :=
    { toFun := fun c w => c w * (Y w)ᵀ
      map_add' := fun c c' => by ext w : 1; simp [Matrix.add_mul]
      map_smul' := fun r c => by ext w : 1; simp [Matrix.smul_mul] }
  set Z := LinearMap.toMatrix' (φ.toLinearMap ∘ₗ G ∘ₗ φ.symm.toLinearMap) with hZdef
  have hZ : ∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ := by
    intro c; rw [hZdef, LinearMap.toMatrix'_mulVec]; simp [G]
  refine ⟨Z, ?_, hZ, ?_⟩
  · refine mem_sp_of_sympl Z fun u v => ?_
    obtain ⟨c, rfl⟩ := φ.surjective u
    obtain ⟨c', rfl⟩ := φ.surjective v
    have hs : (∑ w, ∑ a, ∑ b, lineSign a b * (c w * (Y w)ᵀ) a b * star (c' w a b)) +
        (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star ((c' w * (Y w)ᵀ) a b)) = 0 := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun w _ => sum_zero _ _ _ (hY w)
    rw [hZ, hZ, hφ, hφ, ← mul_add, ← Complex.add_im]
    simp only [hs, Complex.zero_im, mul_zero]
  · intro t c
    have hpow : ∀ (n : ℕ) (c : ι → Matrix (Ix P Q) (Ix R S) ℂ),
        (t • Z) ^ n *ᵥ φ c = φ fun w => c w * ((t • Y w) ^ n)ᵀ := by
      intro n
      induction n with
      | zero => intro c; simp
      | succ n ih =>
        intro c
        rw [pow_succ, ← mulVec_mulVec, Matrix.smul_mulVec, hZ, ← φ.map_smul]
        have : (t • fun w => c w * (Y w)ᵀ) = fun w => c w * (t • Y w)ᵀ := by
          funext w; simp [Matrix.transpose_smul, Matrix.mul_smul]
        rw [this, ih]
        congr 1; funext w
        rw [pow_succ, Matrix.transpose_mul, Matrix.mul_assoc]
    letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
    letI : NormedRing (Mat R S) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Mat R S) := Matrix.linftyOpNormedAlgebra
    have h1 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • (t • Z) ^ n) *ᵥ φ c)
        (NormedSpace.exp (t • Z) *ᵥ φ c) :=
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Z)).map
        (Matrix.mulVec.addMonoidHomLeft (φ c)) (Continuous.matrix_mulVec continuous_id continuous_const)
    have hw : ∀ w, HasSum (fun n : ℕ => c w * (((n.factorial : ℝ)⁻¹ • (t • Y w) ^ n))ᵀ)
        (c w * (NormedSpace.exp (t • Y w))ᵀ) := by
      intro w
      have := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Y w)).matrix_transpose
      exact this.map (AddMonoidHom.mk' (fun M => c w * M) fun _ _ => Matrix.mul_add _ _ _)
        (continuous_const.matrix_mul continuous_id)
    have h2 := (Pi.hasSum.2 hw).map φ (LinearMap.continuous_of_finiteDimensional φ.toLinearMap)
    refine h1.unique ?_
    convert h2 using 1
    funext n
    simp only [Function.comp_def]
    rw [Matrix.smul_mulVec, hpow, ← φ.map_smul]
    congr 1; funext w
    simp [Matrix.transpose_smul, Matrix.mul_smul]

end GlobalTheory.RealLift.SpLie
