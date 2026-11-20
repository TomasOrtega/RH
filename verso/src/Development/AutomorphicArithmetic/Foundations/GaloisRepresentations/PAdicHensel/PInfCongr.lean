import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

open scoped MatrixOrder ComplexOrder in
/- English proof (translation)
Establish `h0 : 0 ≤ A` using `hA.posSemidef.nonneg`. Establish `h1` using `CFC.sqrt_mul_sqrt_self A h0`. Establish `h2 : IsSelfAdjoint (CFC.sqrt A)` using `(CFC.sqrt_nonneg A).isSelfAdjoint`. Use `⟨CFC.sqrt A, ?_, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (CFC.sqrt A * CFC.sqrt A)`.

Rewrite using `[h1]`. Conclude with `hA.isUnit`. Conclude with `isUnit_of_mul_isUnit_left hu`. Rewrite using `[← Matrix.star_eq_conjTranspose, h2.star_eq, h1]`.
-/
private lemma exists_factor {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B ∧ A = Bᴴ * B := by
  have h0 : 0 ≤ A := hA.posSemidef.nonneg
  have h1 := CFC.sqrt_mul_sqrt_self A h0
  have h2 : IsSelfAdjoint (CFC.sqrt A) := (CFC.sqrt_nonneg A).isSelfAdjoint
  refine ⟨CFC.sqrt A, ?_, ?_⟩
  · have hu : IsUnit (CFC.sqrt A * CFC.sqrt A) := by
      rw [h1]
      exact hA.isUnit
    exact isUnit_of_mul_isUnit_left hu
  · rw [← Matrix.star_eq_conjTranspose, h2.star_eq, h1]

open scoped ComplexOrder in
/- English proof (translation)
Establish `hH : ((ε : ℂ) • M).IsHermitian`. Unfold `Matrix.IsHermitian`. Rewrite using `[Matrix.conjTranspose_smul, hM.eq]`. Simplify using the standard rewrite rules. Use `Matrix.PosDef.of_dotProduct_mulVec_pos hH ?_` and prove the remaining obligations.

Introduce `x hx`. Establish `him` using `hM.im_star_dotProduct_mulVec_self x`. Establish `e : star x ⬝ᵥ ((ε : ℂ) • M) *ᵥ x = (ε : ℂ) * (star x ⬝ᵥ M *ᵥ x)`. Simplify using `[Matrix.smul_mulVec, dotProduct_smul]`. Rewrite using `[e, Complex.lt_def]`.

Simplify using `only [RCLike.im_to_complex] at him`. Prove the components needed by the constructor for the conclusion. Simplify `h x hx` using `[him]`. Simplify using `[him]`.
-/
private lemma smul_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) {ε : ℝ}
    (h : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < ε * (star x ⬝ᵥ (M *ᵥ x)).re) : ((ε : ℂ) • M).PosDef := by
  have hH : ((ε : ℂ) • M).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hM.eq]
    simp
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH ?_
  intro x hx
  have him := hM.im_star_dotProduct_mulVec_self x
  have e : star x ⬝ᵥ ((ε : ℂ) • M) *ᵥ x = (ε : ℂ) * (star x ⬝ᵥ M *ᵥ x) := by
    simp [Matrix.smul_mulVec, dotProduct_smul]
  rw [e, Complex.lt_def]
  simp only [RCLike.im_to_complex] at him
  constructor
  · simpa [him] using h x hx
  · simp [him]

/- English proof (translation)
Introduce `n G G' hG hG' ε h h'`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality. Use `⟨1, by simp, ?_⟩` and prove the remaining obligations. Conclude with `Subsingleton.elim _ _`.

Establish `hε : (ε : ℂ) ≠ 0`. Introduce `h0`. Establish `hx : (fun i : Fin n => if i = ⟨0, hn⟩ then (1 : ℂ) else 0) ≠ 0`. Introduce `hz`. Use `congrFun hz ⟨0, hn⟩` as an intermediate fact.

Simplify using `at this`. Use `h _ hx` as an intermediate fact. Rewrite `this` using `[Complex.ofReal_eq_zero.1 h0]`. Simplify using `at this`. Take `⟨B, hB, hBe⟩` from `exists_factor (smul_posDef hG h)`.

Take `⟨C, hC, hCe⟩` from `exists_factor (smul_posDef hG' h')`. Establish `hBd : IsUnit B.det` using `(Matrix.isUnit_iff_isUnit_det B).1 hB`. Establish `hCd : IsUnit C.det` using `(Matrix.isUnit_iff_isUnit_det C).1 hC`. Use `set P := B⁻¹ * C with hP`. Establish `hBP : B * P = C`.

Rewrite using `[hP, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv B hBd, Matrix.one_mul]`. Establish `key : (ε : ℂ) • G' = (ε : ℂ) • (Pᴴ * G * P)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = Pᴴ * ((ε : ℂ) • G) * P := by rw [hBe]`. Use `_ = (ε : ℂ) • (Pᴴ * G * P) := by rw [Matrix.mul_smul, Matrix.smul_mul]`. Establish `hG'P : G' = Pᴴ * G * P` using `smul_right_injective _ hε key`. Use `⟨P.map (starRingEnd ℂ), ?_, ?_⟩` and prove the remaining obligations. Establish `hdet` using `(starRingEnd ℂ).map_det P`.

Rewrite `hdet` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← hdet, map_ne_zero, hP, Matrix.det_mul]`. Conclude with `((Matrix.isUnit_nonsing_inv_det B hBd).mul hCd).ne_zero`. Establish `e1 : (P.map (starRingEnd ℂ))ᵀ = Pᴴ`. Use extensionality with `i j`.

Simplify using `[Matrix.conjTranspose_apply]`. Establish `e2 : (P.map (starRingEnd ℂ)).map (starRingEnd ℂ) = P`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[e1, e2]`.

Conclude with `hG'P`.
-/
theorem UpperTheory.Gal.G1.pInfCongr :
    InfCongr := by
  intro n G G' hG hG' ε h h'
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, by simp, ?_⟩
    exact Subsingleton.elim _ _
  have hε : (ε : ℂ) ≠ 0 := by
    intro h0
    have hx : (fun i : Fin n => if i = ⟨0, hn⟩ then (1 : ℂ) else 0) ≠ 0 := by
      intro hz
      have := congrFun hz ⟨0, hn⟩
      simp at this
    have := h _ hx
    rw [Complex.ofReal_eq_zero.1 h0] at this
    simp at this
  obtain ⟨B, hB, hBe⟩ := exists_factor (smul_posDef hG h)
  obtain ⟨C, hC, hCe⟩ := exists_factor (smul_posDef hG' h')
  have hBd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 hB
  have hCd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).1 hC
  set P := B⁻¹ * C with hP
  have hBP : B * P = C := by
    rw [hP, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv B hBd, Matrix.one_mul]
  have key : (ε : ℂ) • G' = (ε : ℂ) • (Pᴴ * G * P) := by
    calc (ε : ℂ) • G' = Cᴴ * C := hCe
      _ = (B * P)ᴴ * (B * P) := by rw [hBP]
      _ = Pᴴ * (Bᴴ * B) * P := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = Pᴴ * ((ε : ℂ) • G) * P := by rw [hBe]
      _ = (ε : ℂ) • (Pᴴ * G * P) := by rw [Matrix.mul_smul, Matrix.smul_mul]
  have hG'P : G' = Pᴴ * G * P := smul_right_injective _ hε key
  refine ⟨P.map (starRingEnd ℂ), ?_, ?_⟩
  · have hdet := (starRingEnd ℂ).map_det P
    rw [RingHom.mapMatrix_apply] at hdet
    rw [← hdet, map_ne_zero, hP, Matrix.det_mul]
    exact ((Matrix.isUnit_nonsing_inv_det B hBd).mul hCd).ne_zero
  · have e1 : (P.map (starRingEnd ℂ))ᵀ = Pᴴ := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    have e2 : (P.map (starRingEnd ℂ)).map (starRingEnd ℂ) = P := by
      ext i j
      simp
    rw [e1, e2]
    exact hG'P
