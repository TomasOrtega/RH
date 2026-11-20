import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardSumNormFibres

namespace Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts

open Matrix

variable {A k : Type*} [CommRing A] [StarRing A] [Field k]
variable {m : Type*} [Fintype m] [DecidableEq m]

/- English proof (translation)
Establish `h1 : C * C⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hC`. Establish `h2 : C⁻¹ * C = 1` using `Matrix.nonsing_inv_mul _ hC`. Establish `h3 : C⁻¹ᴴ * Cᴴ = 1` using `by rw [← conjTranspose_mul, h1, conjTranspose_one]`. Use `Nat.card_congr { toFun := fun X => ⟨C * X.1 * C⁻¹, ?_⟩ invFun := fun Y => ⟨C⁻¹ * Y.1 * C, ?_⟩ left_inv := ?_ right_inv := ?_ }` and prove the remaining obligations. Establish `hX` using `X.2`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (C⁻¹ᴴ * Cᴴ) * (C * C⁻¹) := by rw [hX]; simp only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [h1, h3, Matrix.mul_one]`. Establish `hY` using `Y.2`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Cᴴ * C := by rw [h1, h3, Matrix.one_mul, Matrix.one_mul, hY, Matrix.mul_one]`. Introduce `X`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show C⁻¹ * (C * X.1 * C⁻¹) * C = X.1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = X.1 := by rw [h2, Matrix.one_mul, Matrix.mul_one]`. Introduce `Y`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show C * (C⁻¹ * Y.1 * C) * C⁻¹ = Y.1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Y.1 := by rw [h1, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem card_conj (C : Matrix m m A) (hC : IsUnit C.det) :
    Nat.card {X : Matrix m m A // Xᴴ * (Cᴴ * C) * X = Cᴴ * C} =
      Nat.card {Y : Matrix m m A // Yᴴ * Y = 1} := by
  have h1 : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv _ hC
  have h2 : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul _ hC
  have h3 : C⁻¹ᴴ * Cᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  refine Nat.card_congr
    { toFun := fun X => ⟨C * X.1 * C⁻¹, ?_⟩
      invFun := fun Y => ⟨C⁻¹ * Y.1 * C, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hX := X.2
    calc (C * X.1 * C⁻¹)ᴴ * (C * X.1 * C⁻¹) = C⁻¹ᴴ * (X.1ᴴ * (Cᴴ * C) * X.1) * C⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (C⁻¹ᴴ * Cᴴ) * (C * C⁻¹) := by rw [hX]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, h3, Matrix.mul_one]
  · have hY := Y.2
    calc (C⁻¹ * Y.1 * C)ᴴ * (Cᴴ * C) * (C⁻¹ * Y.1 * C)
        = Cᴴ * (Y.1ᴴ * ((C⁻¹ᴴ * Cᴴ) * ((C * C⁻¹) * Y.1))) * C := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Cᴴ * C := by rw [h1, h3, Matrix.one_mul, Matrix.one_mul, hY, Matrix.mul_one]
  · intro X
    apply Subtype.ext
    show C⁻¹ * (C * X.1 * C⁻¹) * C = X.1
    calc C⁻¹ * (C * X.1 * C⁻¹) * C = (C⁻¹ * C) * X.1 * (C⁻¹ * C) := by
          simp only [Matrix.mul_assoc]
      _ = X.1 := by rw [h2, Matrix.one_mul, Matrix.mul_one]
  · intro Y
    apply Subtype.ext
    show C * (C⁻¹ * Y.1 * C) * C⁻¹ = Y.1
    calc C * (C⁻¹ * Y.1 * C) * C⁻¹ = (C * C⁻¹) * Y.1 * (C * C⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Y.1 := by rw [h1, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, conjTranspose_apply, map_sum, hφ]`.
-/
private theorem map_conjTranspose_mul_eq_map_transpose_mul (φ : A ≃+* k) (σ : k ≃+* k) (hφ : ∀ a, φ (star a) = σ (φ a))
    (Y : Matrix m m A) :
    ((Y.map φ).map σ).transpose * Y.map φ = (Yᴴ * Y).map φ := by
  ext i j
  simp [Matrix.mul_apply, conjTranspose_apply, map_sum, hφ]

/- English proof (translation)
Use `Nat.card_congr { toFun := fun Y => ⟨Y.1.map φ, ?_⟩ invFun := fun X => ⟨X.1.map φ.symm, ?_⟩ left_inv := ?_ right_inv := ?_ }` and prove the remaining obligations. Rewrite using `[map_conjTranspose_mul_eq_map_transpose_mul φ σ hφ, Y.2]`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply]`. Establish `h1 : ((X.1.map φ.symm)ᴴ * X.1.map φ.symm).map φ = 1`.

Rewrite using `[← map_conjTranspose_mul_eq_map_transpose_mul φ σ hφ]`. Establish `: (X.1.map φ.symm).map φ = X.1` using `by ext i j; simp`. Rewrite using `[this, X.2]`. Establish `h2 : (X.1.map φ.symm)ᴴ * X.1.map φ.symm = (((X.1.map φ.symm)ᴴ * X.1.map φ.symm).map φ).map φ.symm`. Use extensionality with `i j`.

Rewrite using `[Matrix.map_apply, Matrix.map_apply, RingEquiv.symm_apply_apply]`. Rewrite using `[h2, h1]`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply]`. Introduce `Y`.

Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `i j`. Simplify using the standard rewrite rules. Introduce `X`. Apply `Subtype.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem card_map_equiv (φ : A ≃+* k) (σ : k ≃+* k) (hφ : ∀ a, φ (star a) = σ (φ a)) :
    Nat.card {Y : Matrix m m A // Yᴴ * Y = 1} =
      Nat.card {X : Matrix m m k // (X.map σ).transpose * X = 1} := by
  refine Nat.card_congr
    { toFun := fun Y => ⟨Y.1.map φ, ?_⟩
      invFun := fun X => ⟨X.1.map φ.symm, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [map_conjTranspose_mul_eq_map_transpose_mul φ σ hφ, Y.2]
    ext i j
    simp [Matrix.one_apply]
  · have h1 : ((X.1.map φ.symm)ᴴ * X.1.map φ.symm).map φ = 1 := by
      rw [← map_conjTranspose_mul_eq_map_transpose_mul φ σ hφ]
      have : (X.1.map φ.symm).map φ = X.1 := by ext i j; simp
      rw [this, X.2]
    have h2 : (X.1.map φ.symm)ᴴ * X.1.map φ.symm
        = (((X.1.map φ.symm)ᴴ * X.1.map φ.symm).map φ).map φ.symm := by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply, RingEquiv.symm_apply_apply]
    rw [h2, h1]
    ext i j
    simp [Matrix.one_apply]
  · intro Y; apply Subtype.ext; ext i j; simp
  · intro X; apply Subtype.ext; ext i j; simp

/- English proof (translation)
Distinguish the cases in `h0 : c = 0`. Conclude with `⟨0, by simp [h0]⟩`. Establish `h` using `Formalism.HermitianLattices.Ext.L3.FiniteNormFibres.card_norm_fibre σ hσ hne q hq c hc`. Rewrite `h` using `[if_neg h0]`. Establish `hpos : 0 < (Finset.univ.filter fun y : k => σ y * y = c).card`.

Assume the negation of the conclusion as `hz`. Use `push_neg at hz`. Establish `hz' : (Finset.univ.filter fun y : k => σ y * y = c).card = 0` using `by omega`. Simplify using `only [hz'] at h`. Move the coercions through the operations in `at h`.

Use linear arithmetic over natural numbers and integers. Take `⟨y, hy⟩` from `Finset.card_pos.mp hpos`. Conclude with `⟨y, (Finset.mem_filter.mp hy).2⟩`.
-/
theorem exists_norm [Fintype k] (σ : k ≃+* k) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (q : ℕ)
    (hq : Fintype.card k = q ^ 2) (c : k) (hc : σ c = c) : ∃ y, σ y * y = c := by
  classical
  by_cases h0 : c = 0
  · exact ⟨0, by simp [h0]⟩
  · have h := Formalism.HermitianLattices.Ext.L3.FiniteNormFibres.card_norm_fibre σ hσ hne q hq c hc
    rw [if_neg h0] at h
    have hpos : 0 < (Finset.univ.filter fun y : k => σ y * y = c).card := by
      by_contra hz
      push_neg at hz
      have hz' : (Finset.univ.filter fun y : k => σ y * y = c).card = 0 := by omega
      simp only [hz'] at h
      push_cast at h
      omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
    exact ⟨y, (Finset.mem_filter.mp hy).2⟩

/- English proof (translation)
Establish `hy : ∀ i, ∃ y, σ y * y = φ (u i)` using `fun i => exists_norm σ hσ hne q hq (φ (u i)) (by rw [← hφ, hu])`. Use `choose y hy using hy`. Use `set a : m → A := fun i => φ.symm (y i) with ha_def`. Establish `ha : ∀ i, star (a i) * a i = u i`. Introduce `i`.

Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[map_mul, hφ]`. Simplify using `[ha_def, hy]`. Establish `hCC : (diagonal a)ᴴ * diagonal a = diagonal u`. Rewrite using `[diagonal_conjTranspose, diagonal_mul_diagonal]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `ha i`. Establish `hau : ∀ i, IsUnit (a i)` using `fun i => isUnit_of_mul_isUnit_right (by rw [ha i]; exact hunit i)`. Establish `hC : IsUnit (diagonal a).det` using `(Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr hau))`.

Rewrite using `[← hCC, card_conj (diagonal a) hC, card_map_equiv φ σ hφ]`.
-/
theorem card_inert [Fintype k] (φ : A ≃+* k) (σ : k ≃+* k) (hφ : ∀ a, φ (star a) = σ (φ a))
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (q : ℕ) (hq : Fintype.card k = q ^ 2)
    (u : m → A) (hu : ∀ i, star (u i) = u i) (hunit : ∀ i, IsUnit (u i)) :
    Nat.card {X : Matrix m m A // Xᴴ * diagonal u * X = diagonal u} =
      Nat.card {X : Matrix m m k // (X.map σ).transpose * X = 1} := by
  have hy : ∀ i, ∃ y, σ y * y = φ (u i) := fun i =>
    exists_norm σ hσ hne q hq (φ (u i)) (by rw [← hφ, hu])
  choose y hy using hy
  set a : m → A := fun i => φ.symm (y i) with ha_def
  have ha : ∀ i, star (a i) * a i = u i := by
    intro i
    apply φ.injective
    rw [map_mul, hφ]
    simp [ha_def, hy]
  have hCC : (diagonal a)ᴴ * diagonal a = diagonal u := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext i
    exact ha i
  have hau : ∀ i, IsUnit (a i) := fun i =>
    isUnit_of_mul_isUnit_right (by rw [ha i]; exact hunit i)
  have hC : IsUnit (diagonal a).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr hau))
  rw [← hCC, card_conj (diagonal a) hC, card_map_equiv φ σ hφ]

/- English proof (translation)
Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Use `congr 2`.
-/
private theorem map_conjTranspose_mul_mul_eq (φ : A →+* k) (X H : Matrix m m A) :
    (Xᴴ * H * X).map φ = (X.map fun a => φ (star a))ᵀ * H.map φ * X.map φ := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2

/- English proof (translation)
Use extensionality with `i j`. Establish `h` using `congrFun (congrFun hM j) i`. Rewrite `h` using `[conjTranspose_apply]`. Simplify using `only [map_apply, transpose_apply]`. Rewrite using `[h]`.
-/
private theorem map_star_eq_transpose_map_of_isHermitian (φ : A →+* k) {M : Matrix m m A} (hM : Mᴴ = M) :
    M.map (fun a => φ (star a)) = (M.map φ)ᵀ := by
  ext i j
  have h := congrFun (congrFun hM j) i
  rw [conjTranspose_apply] at h
  simp only [map_apply, transpose_apply]
  rw [h]

/- English proof (translation)
Use extensionality with `i j`. Apply `hb.1` to reduce the goal to its premises. Conclude with `Prod.ext (congrFun (congrFun h2 i) j) (congrFun (congrFun h1 i) j)`.
-/
private theorem matrix_eq_of_map_and_map_star_eq (φ : A →+* k) (hb : Function.Bijective fun a : A => (φ (star a), φ a))
    {M N : Matrix m m A} (h1 : M.map φ = N.map φ)
    (h2 : M.map (fun a => φ (star a)) = N.map (fun a => φ (star a))) : M = N := by
  ext i j
  apply hb.1
  exact Prod.ext (congrFun (congrFun h2 i) j) (congrFun (congrFun h1 i) j)

/- English proof (translation)
Establish `hdet : (H.map φ).det = φ H.det`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply]`. Establish `hGu : IsUnit (H.map φ).det`. Rewrite using `[hdet]`. Conclude with `hu.map φ`.

Establish `cond : ∀ X : Matrix m m A, Xᴴ * H * X = H ↔ (X.map fun a => φ (star a))ᵀ * H.map φ * X.map φ = H.map φ`. Introduce `X`. Rewrite using `[← map_conjTranspose_mul_mul_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite using `[h]`. Introduce `h`. Apply `matrix_eq_of_map_and_map_star_eq φ hb h` to reduce the goal to its premises. Establish `hM : (Xᴴ * H * X)ᴴ = Xᴴ * H * X`. Simplify using `[conjTranspose_mul, hH, Matrix.mul_assoc]`.

Rewrite using `[map_star_eq_transpose_map_of_isHermitian φ hM, map_star_eq_transpose_map_of_isHermitian φ hH, h]`. Establish `hP : ∀ X : {X : Matrix m m A // Xᴴ * H * X = H}, IsUnit (X.1.map φ).det`. Introduce `X`. Establish `h` using `congrArg Matrix.det ((cond X.1).mp X.2)`. Rewrite `h` using `[det_mul, det_mul]`.

Use `isUnit_iff_ne_zero.mpr fun h0 => ?_` and prove the remaining obligations. Rewrite `h` using `[h0, mul_zero]`. Conclude with `hGu.ne_zero h.symm`. Establish `key : ∀ X : {X : Matrix m m A // Xᴴ * H * X = H}, (X.1.map fun a => φ (star a))ᵀ = H.map φ * (H.map φ * X.1.map φ)⁻¹`. Introduce `X`.

Establish `h` using `(cond X.1).mp X.2`. Establish `hu' : IsUnit (H.map φ * X.1.map φ).det`. Rewrite using `[det_mul]`. Conclude with `hGu.mul (hP X)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_assoc _ (H.map φ * X.1.map φ), Matrix.mul_nonsing_inv _ hu', Matrix.mul_one]`. Use `_ = H.map φ * (H.map φ * X.1.map φ)⁻¹ := by`. Rewrite using `[← Matrix.mul_assoc _ (H.map φ), h]`. Use `Nat.card_eq_of_bijective (fun X => Matrix.nonsingInvUnit (X.1.map φ) (hP X)) ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `X Y hXY`.

Establish `hPe : X.1.map φ = Y.1.map φ` using `congrArg Units.val hXY`. Establish `hQe : X.1.map (fun a => φ (star a)) = Y.1.map (fun a => φ (star a))`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Subtype.ext (matrix_eq_of_map_and_map_star_eq φ hb hPe hQe)`. Introduce `U`.

Set `e` to `Equiv.ofBijective _ hb`. Set `X : Matrix m m A` to `Matrix.of fun i j => e.symm ((H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹)ᵀ i j, (↑U : Matrix m m k) i j)`. Establish `hX : ∀ i j, (φ (star (X i j)), φ (X i j)) = ((H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹)ᵀ i j, (↑U : Matrix m m k) i j)` using `fun i j => e.apply_symm_apply _`. Establish `hXP : X.map φ = (↑U : Matrix m m k)`. Use extensionality with `i j`.

Conclude with `congrArg Prod.snd (hX i j)`. Establish `hXQ : X.map (fun a => φ (star a)) = (H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹)ᵀ`. Use extensionality with `i j`. Conclude with `congrArg Prod.fst (hX i j)`. Establish `hc : Xᴴ * H * X = H`.

Rewrite using `[cond, hXP, hXQ, transpose_transpose]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = H.map φ := by`. Rewrite using `[Matrix.nonsing_inv_mul _ hGu, Matrix.mul_one, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`.

Use `⟨⟨X, hc⟩, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Conclude with `hXP`.
-/
theorem card_split (φ : A →+* k) (hb : Function.Bijective fun a : A => (φ (star a), φ a))
    (H : Matrix m m A) (hH : Hᴴ = H) (hu : IsUnit H.det) :
    Nat.card {X : Matrix m m A // Xᴴ * H * X = H} = Nat.card (GL m k) := by
  classical
  have hdet : (H.map φ).det = φ H.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hGu : IsUnit (H.map φ).det := by
    rw [hdet]; exact hu.map φ
  have cond : ∀ X : Matrix m m A, Xᴴ * H * X = H ↔
      (X.map fun a => φ (star a))ᵀ * H.map φ * X.map φ = H.map φ := by
    intro X
    rw [← map_conjTranspose_mul_mul_eq]
    constructor
    · intro h; rw [h]
    · intro h
      apply matrix_eq_of_map_and_map_star_eq φ hb h
      have hM : (Xᴴ * H * X)ᴴ = Xᴴ * H * X := by
        simp [conjTranspose_mul, hH, Matrix.mul_assoc]
      rw [map_star_eq_transpose_map_of_isHermitian φ hM, map_star_eq_transpose_map_of_isHermitian φ hH, h]
  have hP : ∀ X : {X : Matrix m m A // Xᴴ * H * X = H}, IsUnit (X.1.map φ).det := by
    intro X
    have h := congrArg Matrix.det ((cond X.1).mp X.2)
    rw [det_mul, det_mul] at h
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, mul_zero] at h
    exact hGu.ne_zero h.symm
  have key : ∀ X : {X : Matrix m m A // Xᴴ * H * X = H},
      (X.1.map fun a => φ (star a))ᵀ = H.map φ * (H.map φ * X.1.map φ)⁻¹ := by
    intro X
    have h := (cond X.1).mp X.2
    have hu' : IsUnit (H.map φ * X.1.map φ).det := by
      rw [det_mul]; exact hGu.mul (hP X)
    calc (X.1.map fun a => φ (star a))ᵀ
        = (X.1.map fun a => φ (star a))ᵀ * (H.map φ * X.1.map φ) * (H.map φ * X.1.map φ)⁻¹ := by
          rw [Matrix.mul_assoc _ (H.map φ * X.1.map φ), Matrix.mul_nonsing_inv _ hu', Matrix.mul_one]
      _ = H.map φ * (H.map φ * X.1.map φ)⁻¹ := by
          rw [← Matrix.mul_assoc _ (H.map φ), h]
  refine Nat.card_eq_of_bijective (fun X => Matrix.nonsingInvUnit (X.1.map φ) (hP X)) ⟨?_, ?_⟩
  · intro X Y hXY
    have hPe : X.1.map φ = Y.1.map φ := congrArg Units.val hXY
    have hQe : X.1.map (fun a => φ (star a)) = Y.1.map (fun a => φ (star a)) := by
      calc X.1.map (fun a => φ (star a)) = ((X.1.map fun a => φ (star a))ᵀ)ᵀ :=
            (transpose_transpose _).symm
        _ = (H.map φ * (H.map φ * Y.1.map φ)⁻¹)ᵀ := by rw [key X, hPe]
        _ = Y.1.map (fun a => φ (star a)) := by rw [← key Y, transpose_transpose]
    exact Subtype.ext (matrix_eq_of_map_and_map_star_eq φ hb hPe hQe)
  · intro U
    let e := Equiv.ofBijective _ hb
    let X : Matrix m m A := Matrix.of fun i j =>
      e.symm ((H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹)ᵀ i j, (↑U : Matrix m m k) i j)
    have hX : ∀ i j, (φ (star (X i j)), φ (X i j)) =
        ((H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹)ᵀ i j, (↑U : Matrix m m k) i j) :=
      fun i j => e.apply_symm_apply _
    have hXP : X.map φ = (↑U : Matrix m m k) := by
      ext i j; exact congrArg Prod.snd (hX i j)
    have hXQ : X.map (fun a => φ (star a)) = (H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹)ᵀ := by
      ext i j; exact congrArg Prod.fst (hX i j)
    have hc : Xᴴ * H * X = H := by
      rw [cond, hXP, hXQ, transpose_transpose]
      calc H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹ * H.map φ * (↑U : Matrix m m k)
          = H.map φ * (↑U⁻¹ : Matrix m m k) * ((H.map φ)⁻¹ * H.map φ) * (↑U : Matrix m m k) := by
            simp only [Matrix.mul_assoc]
        _ = H.map φ := by
            rw [Matrix.nonsing_inv_mul _ hGu, Matrix.mul_one, Matrix.mul_assoc, Units.inv_mul,
              Matrix.mul_one]
    refine ⟨⟨X, hc⟩, ?_⟩
    apply Units.ext
    exact hXP

end Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts
