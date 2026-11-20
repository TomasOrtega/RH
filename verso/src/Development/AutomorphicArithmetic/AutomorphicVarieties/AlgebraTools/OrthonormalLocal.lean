import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DiagLocal

open Polynomial Matrix IsLocalRing TensorProduct

/- English proof (translation)
Take `⟨b, hb⟩` from `hs`. Take `⟨a₀, rfl⟩` from `IsLocalRing.residue_surjective b`. Establish `hres : residue R' (a₀ ^ 2 - u) = 0` using `by rw [map_sub, map_pow, hb, pow_two, sub_self]`. Establish `ha₀ : IsUnit a₀`. Rewrite using `[← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]`.

Introduce `h0`. Establish `hu0 : residue R' u = 0` using `by rw [hb, h0, mul_zero]`. Conclude with `(hu.map (residue R')).ne_zero hu0`. Establish `hev : eval a₀ (X ^ 2 - C u) ∈ maximalIdeal R'`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff]`.

Simplify using `using hres`. Establish `hd : eval a₀ (derivative (X ^ 2 - C u)) = 2 * a₀`. Simplify using `only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C, eval_pow, eval_X]`. Evaluate the numerical expressions. Establish `hdu : IsUnit (eval a₀ (derivative (X ^ 2 - C u)))`.

Rewrite using `[hd]`. Conclude with `h2.mul ha₀`. Take `⟨a, ha, -⟩` from `HenselianLocalRing.is_henselian (X ^ 2 - C u) (monic_X_pow_sub_C u two_ne_zero) a₀ hev hdu`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `h0` using `ha.eq_zero`.

Simplify using `only [eval_sub, eval_pow, eval_X, eval_C] at h0`. Rewrite using `[← pow_two]`. Conclude with `sub_eq_zero.mp h0`.
-/
private theorem UpperTheory.V.AlgebraTools.sqrt_of_residue {R' : Type} [CommRing R'] [HenselianLocalRing R']
    (h2 : IsUnit (2 : R')) (u : R') (hu : IsUnit u) (hs : IsSquare (residue R' u)) :
    ∃ a : R', a * a = u := by
  obtain ⟨b, hb⟩ := hs
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective b
  have hres : residue R' (a₀ ^ 2 - u) = 0 := by rw [map_sub, map_pow, hb, pow_two, sub_self]
  have ha₀ : IsUnit a₀ := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]
    intro h0
    have hu0 : residue R' u = 0 := by rw [hb, h0, mul_zero]
    exact (hu.map (residue R')).ne_zero hu0
  have hev : eval a₀ (X ^ 2 - C u) ∈ maximalIdeal R' := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simpa using hres
  have hd : eval a₀ (derivative (X ^ 2 - C u)) = 2 * a₀ := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C,
      eval_pow, eval_X]
    norm_num
  have hdu : IsUnit (eval a₀ (derivative (X ^ 2 - C u))) := by
    rw [hd]
    exact h2.mul ha₀
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (X ^ 2 - C u)
    (monic_X_pow_sub_C u two_ne_zero) a₀ hev hdu
  refine ⟨a, ?_⟩
  have h0 := ha.eq_zero
  simp only [eval_sub, eval_pow, eval_X, eval_C] at h0
  rw [← pow_two]
  exact sub_eq_zero.mp h0

/- English proof (translation)
Introduce `R R' _ _ _ _ φ n H h2 hT hdet hsq`. Take `⟨P, c, hP⟩` from `UpperTheory.V.AlgebraTools.diag_local H h2 hT hdet`. Establish `h2' : IsUnit (2 : R')`. Establish `h` using `h2.map φ`. Rewrite `h` using `[map_ofNat]`. Then use the resulting hypothesis.

Establish `hroot : ∀ i, ∃ a : R', a * a = φ (c i)` using `fun i => UpperTheory.V.AlgebraTools.sqrt_of_residue h2' _ ((c i).isUnit.map φ) (hsq (c i))`. Use `choose a ha using hroot`. Establish `hau : ∀ i, IsUnit (a i)` using `fun i => isUnit_of_mul_isUnit_left (y := a i) (by rw [ha i]; exact (c i).isUnit.map φ)`. Set `D : GL (Fin n) R'` to `⟨diagonal fun i => (((hau i).unit⁻¹ : R'ˣ) : R'), diagonal fun i => a i, by rw [diagonal_mul_diagonal]; convert diagonal_one using 2; simp, by rw [diagonal_mul_diagonal]; convert diagonal_one using 2; simp⟩`. Establish `hmap : ((Matrix.GeneralLinearGroup.map φ P : GL (Fin n) R') : Matrix (Fin n) (Fin n) R') = (P : Matrix (Fin n) (Fin n) R).map φ`.

Use extensionality with `i j`. Conclude with `Matrix.GeneralLinearGroup.map_apply φ i j P`. Establish `key : ((P : Matrix (Fin n) (Fin n) R).map φ)ᵀ * H.map φ * (P : Matrix (Fin n) (Fin n) R).map φ = diagonal fun i => φ (c i)`. Rewrite using `[← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hP, diagonal_map (map_zero φ)]`. Use `⟨Matrix.GeneralLinearGroup.map φ P * D, ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mul, hmap, Matrix.transpose_mul]`. Establish `hD : ((D : GL (Fin n) R') : Matrix (Fin n) (Fin n) R') = diagonal fun i => (((hau i).unit⁻¹ : R'ˣ) : R')` using `rfl`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by`.

Rewrite using `[key, hD, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]`. Use `diagonal_one using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Rewrite using `[← ha i]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [IsUnit.unit_spec]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = 1 := by simp`.
-/
theorem UpperTheory.V.AlgebraTools.orthonormal_local :
    ∀ {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [HenselianLocalRing R'] (φ : R →+* R') {n : ℕ} (H : Matrix (Fin n) (Fin n) R), IsUnit (2 : R) → Hᵀ = H → IsUnit H.det → (∀ c : Rˣ, IsSquare (residue R' (φ c))) → ∃ P : GL (Fin n) R', (P : Matrix (Fin n) (Fin n) R')ᵀ * H.map φ * P = 1 := by
  intro R R' _ _ _ _ φ n H h2 hT hdet hsq
  obtain ⟨P, c, hP⟩ := UpperTheory.V.AlgebraTools.diag_local H h2 hT hdet
  have h2' : IsUnit (2 : R') := by
    have h := h2.map φ
    rwa [map_ofNat] at h
  have hroot : ∀ i, ∃ a : R', a * a = φ (c i) := fun i =>
    UpperTheory.V.AlgebraTools.sqrt_of_residue h2' _ ((c i).isUnit.map φ) (hsq (c i))
  choose a ha using hroot
  have hau : ∀ i, IsUnit (a i) := fun i =>
    isUnit_of_mul_isUnit_left (y := a i) (by rw [ha i]; exact (c i).isUnit.map φ)
  let D : GL (Fin n) R' :=
    ⟨diagonal fun i => (((hau i).unit⁻¹ : R'ˣ) : R'), diagonal fun i => a i,
      by rw [diagonal_mul_diagonal]; convert diagonal_one using 2; simp,
      by rw [diagonal_mul_diagonal]; convert diagonal_one using 2; simp⟩
  have hmap : ((Matrix.GeneralLinearGroup.map φ P : GL (Fin n) R') : Matrix (Fin n) (Fin n) R') =
      (P : Matrix (Fin n) (Fin n) R).map φ := by
    ext i j
    exact Matrix.GeneralLinearGroup.map_apply φ i j P
  have key : ((P : Matrix (Fin n) (Fin n) R).map φ)ᵀ * H.map φ *
      (P : Matrix (Fin n) (Fin n) R).map φ = diagonal fun i => φ (c i) := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hP, diagonal_map (map_zero φ)]
  refine ⟨Matrix.GeneralLinearGroup.map φ P * D, ?_⟩
  rw [Units.val_mul, hmap, Matrix.transpose_mul]
  have hD : ((D : GL (Fin n) R') : Matrix (Fin n) (Fin n) R') =
      diagonal fun i => (((hau i).unit⁻¹ : R'ˣ) : R') := rfl
  calc ((D : Matrix (Fin n) (Fin n) R'))ᵀ * ((P : Matrix (Fin n) (Fin n) R).map φ)ᵀ * H.map φ *
        ((P : Matrix (Fin n) (Fin n) R).map φ * (D : Matrix (Fin n) (Fin n) R'))
      = ((D : Matrix (Fin n) (Fin n) R'))ᵀ * (((P : Matrix (Fin n) (Fin n) R).map φ)ᵀ * H.map φ *
        (P : Matrix (Fin n) (Fin n) R).map φ) * (D : Matrix (Fin n) (Fin n) R') := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [key, hD, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
      convert diagonal_one using 2
      funext i
      rw [← ha i]
      calc ((hau i).unit⁻¹ : R'ˣ).val * (a i * a i) * ((hau i).unit⁻¹ : R'ˣ).val
          = (((hau i).unit⁻¹ : R'ˣ).val * (hau i).unit.val) *
            ((hau i).unit.val * ((hau i).unit⁻¹ : R'ˣ).val) := by
            simp only [IsUnit.unit_spec]; ring
        _ = 1 := by simp
