import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixGaussSumSingularAndInvertible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexMatrixGaussSumNormIntegralGaloisStatement
open Matrix Formalism.IndefR.Datum
open Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `a ha h`. Apply `hψ (neg_ne_zero.mpr ha)` to reduce the goal to its premises. Use extensionality with `x`. Use `DFunLike.congr_fun h x` as an intermediate fact. Simplify `this` using `[AddChar.mulShift_apply, AddChar.inv_apply, neg_mul]`.
-/
theorem addChar_inv_isPrimitive_of_isPrimitive {k : Type} [Field k] {R : Type} [CommRing R] (ψ : AddChar k R)
    (hψ : ψ.IsPrimitive) : (ψ⁻¹).IsPrimitive := by
  intro a ha h
  apply hψ (neg_ne_zero.mpr ha)
  ext x
  have := DFunLike.congr_fun h x
  simpa [AddChar.mulShift_apply, AddChar.inv_apply, neg_mul] using this

/- English proof (translation)
Use `split_ifs with hm`. Substitute `hm` using the available equality. Simplify using `only [Matrix.mul_zero, trace_zero, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]`. Rewrite using `[show Fintype.card (Matrix (Fin r) (Fin t) k) = Fintype.card (Fin r → Fin t → k) from rfl]`. Simplify using `[Fintype.card_fun, ← pow_mul, mul_comm]`.

Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij⟩ : ∃ i j, m i j ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hm (Matrix.ext h)`. Establish `h1` using `hψ hij`.

Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c, ψ (m i j * c) ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `h1` to reduce the goal to its premises. Use extensionality with `c`.

Simplify using `[AddChar.mulShift_apply, h]`. Use `set a₀ : Matrix (Fin r) (Fin t) k := Matrix.single j i c`. Establish `ha₀ : trace (a₀ * m) = m i j * c`. Simplify using `[a₀, Matrix.trace_single_mul, mul_comm]`. Use `set S := ∑ a : Matrix (Fin r) (Fin t) k, ψ (trace (a * m))`.

Establish `hS : S = ψ (trace (a₀ * m)) * S`. Rewrite using `[Finset.mul_sum]`. Use `Fintype.sum_equiv (Equiv.subRight a₀) _ _ (fun a => ?_)` and prove the remaining obligations. Simplify using `only [Equiv.subRight_apply, ← AddChar.map_add_eq_mul, Matrix.sub_mul, trace_sub]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hS` using `[ha₀]`. Establish `: (1 - ψ (m i j * c)) * S = 0` using `by rw [sub_mul, one_mul, ← hS, sub_self]`. Break down `mul_eq_zero.mp this with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h).symm hc`.

Conclude with `h`.
-/
theorem sum_addChar_trace_rectMatrix_mul {k : Type} [Field k] [Fintype k] {R : Type} [CommRing R] [IsDomain R]
    (ψ : AddChar k R) (hψ : ψ.IsPrimitive) {r t : ℕ} (m : Matrix (Fin t) (Fin r) k) :
    ∑ b : Matrix (Fin r) (Fin t) k, ψ (trace (b * m)) =
      if m = 0 then (Fintype.card k : R) ^ (r * t) else 0 := by
  split_ifs with hm
  · subst hm
    simp only [Matrix.mul_zero, trace_zero, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [show Fintype.card (Matrix (Fin r) (Fin t) k) = Fintype.card (Fin r → Fin t → k) from rfl]
    simp [Fintype.card_fun, ← pow_mul, mul_comm]
  · obtain ⟨i, j, hij⟩ : ∃ i j, m i j ≠ 0 := by
      by_contra h; push_neg at h; exact hm (Matrix.ext h)
    have h1 := hψ hij
    obtain ⟨c, hc⟩ : ∃ c, ψ (m i j * c) ≠ 1 := by
      by_contra h; push_neg at h; apply h1; ext c; simp [AddChar.mulShift_apply, h]
    set a₀ : Matrix (Fin r) (Fin t) k := Matrix.single j i c
    have ha₀ : trace (a₀ * m) = m i j * c := by
      simp [a₀, Matrix.trace_single_mul, mul_comm]
    set S := ∑ a : Matrix (Fin r) (Fin t) k, ψ (trace (a * m))
    have hS : S = ψ (trace (a₀ * m)) * S := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight a₀) _ _ (fun a => ?_)
      simp only [Equiv.subRight_apply, ← AddChar.map_add_eq_mul, Matrix.sub_mul, trace_sub]
      congr 1; ring
    rw [ha₀] at hS
    have : (1 - ψ (m i j * c)) * S = 0 := by rw [sub_mul, one_mul, ← hS, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h).symm hc
    · exact h

variable {k : Type} [Field k] {r t : ℕ}

def squareAndRectColumnsEquivWideMatrix : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin t) k ≃ Matrix (Fin r) (Fin (r + t)) k where
  toFun p := fun i j => Fin.addCases (p.1 i) (p.2 i) j
  invFun y := (y.submatrix id (Fin.castAdd t), y.submatrix id (Fin.natAdd r))
  left_inv p := by
    ext i j
    · exact Fin.addCases_left (motive := fun _ => k) j
    · exact Fin.addCases_right (motive := fun _ => k) j
  right_inv y := by
    funext i j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp

/- English proof (translation)
Use extensionality with `i j; simp only [topL]; rw [dif_pos ⟨i.2, by omega⟩]; rfl`.
-/
theorem topLeftBlock_neg_eq_submatrix_castAdd (y : Matrix (Fin r) (Fin (r + t)) k) :
    topL r (-y) = -(y.submatrix id (Fin.castAdd t)) := by
  ext i j; simp only [topL]; rw [dif_pos ⟨i.2, by omega⟩]; rfl

/- English proof (translation)
Use extensionality with `i j; simp only [topL]; rw [dif_pos ⟨by omega, j.2⟩]; rfl`.
-/
theorem topLeftBlock_eq_submatrix_castAdd (u : Matrix (Fin (r + t)) (Fin r) k) :
    topL r u = u.submatrix (Fin.castAdd t) id := by
  ext i j; simp only [topL]; rw [dif_pos ⟨by omega, j.2⟩]; rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h; ext i j; exact h (Fin.natAdd r i) j (by simp) j.2`. Introduce `h i j hi _`. Take `⟨i', rfl⟩ : ∃ i' : Fin t, i = Fin.natAdd r i'` from `⟨⟨i.val - r, by omega⟩, Fin.ext (by simp; omega)⟩`. Simplify using `using congr_fun (congr_fun h i') j`.
-/
theorem lowZero_iff_submatrix_natAdd_eq_zero (u : Matrix (Fin (r + t)) (Fin r) k) :
    LowZero r u ↔ u.submatrix (Fin.natAdd r) id = 0 := by
  constructor
  · intro h; ext i j; exact h (Fin.natAdd r i) j (by simp) j.2
  · intro h i j hi _
    obtain ⟨i', rfl⟩ : ∃ i' : Fin t, i = Fin.natAdd r i' := ⟨⟨i.val - r, by omega⟩, Fin.ext (by simp; omega)⟩
    simpa using congr_fun (congr_fun h i') j

/- English proof (translation)
Simplify using `[Matrix.trace, Matrix.mul_apply, Fin.sum_univ_add, Finset.sum_add_distrib]`.
-/
theorem trace_mul_split_castAdd_natAdd (y : Matrix (Fin r) (Fin (r + t)) k) (u : Matrix (Fin (r + t)) (Fin r) k) :
    trace (y * u) = trace (y.submatrix id (Fin.castAdd t) * u.submatrix (Fin.castAdd t) id) +
      trace (y.submatrix id (Fin.natAdd r) * u.submatrix (Fin.natAdd r) id) := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_add, Finset.sum_add_distrib]

/- English proof (translation)
Use `symm`. Use `Fintype.sum_of_injective (fun x : GL (Fin r) k => -(x : Matrix (Fin r) (Fin r) k)) (fun x y e => Units.ext (neg_injective e)) _ _ ?_ ?_` and prove the remaining obligations. Introduce `a ha`. Rewrite using `[dif_neg, zero_mul]`. Introduce `h`.

Conclude with `ha ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (-a) h.ne_zero, by simp⟩`. Introduce `x`. Establish `hx : IsUnit (-(-(x : Matrix (Fin r) (Fin r) k))).det`. Rewrite using `[neg_neg]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).mp x.isUnit`.

Rewrite using `[dif_pos hx]`. Establish `hu : hx.unit = Matrix.GeneralLinearGroup.det x` using `Units.ext (by simp)`. Rewrite using `[hu, MonoidHom.inv_apply, inv_inv, AddChar.inv_apply, Matrix.trace_mul_comm w, neg_mul, trace_neg]`.
-/
theorem sum_GL_character_neg_det_addChar_trace (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ)
    (w : Matrix (Fin r) (Fin r) k) :
    ∑ a : Matrix (Fin r) (Fin r) k, (if h : IsUnit (-a).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace (a * w))
      = ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
          ψ⁻¹ (trace (w * (x : Matrix (Fin r) (Fin r) k))) := by
  symm
  refine Fintype.sum_of_injective (fun x : GL (Fin r) k => -(x : Matrix (Fin r) (Fin r) k))
    (fun x y e => Units.ext (neg_injective e)) _ _ ?_ ?_
  · intro a ha
    rw [dif_neg, zero_mul]
    intro h
    exact ha ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (-a) h.ne_zero, by simp⟩
  · intro x
    have hx : IsUnit (-(-(x : Matrix (Fin r) (Fin r) k))).det := by
      rw [neg_neg]; exact (Matrix.isUnit_iff_isUnit_det _).mp x.isUnit
    rw [dif_pos hx]
    have hu : hx.unit = Matrix.GeneralLinearGroup.det x := Units.ext (by simp)
    rw [hu, MonoidHom.inv_apply, inv_inv, AddChar.inv_apply, Matrix.trace_mul_comm w, neg_mul, trace_neg]

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ _ ψ ξ r n hψ hξ`. Break down `lt_or_ge n r with hnr | hrn` into its components or cases. Use `⟨1, 0, one_ne_zero, isIntegral_one, by simpa using isIntegral_one, fun u => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ y : Matrix (Fin r) (Fin n) k, (topL r (-y)).det = 0` using `fun y => Matrix.det_eq_zero_of_column_eq_zero ⟨n, hnr⟩ (fun i => by simp [topL])`. Establish `h2 : (topL r u).det = 0` using `Matrix.det_eq_zero_of_row_eq_zero ⟨n, hnr⟩ (fun j => by simp [topL])`.

Rewrite using `[one_mul, dif_neg (by rintro ⟨-, h⟩; rw [h2] at h; exact not_isUnit_zero h)]`. Use `Finset.sum_eq_zero fun y _ => ?_` and prove the remaining obligations. Rewrite using `[dif_neg (by rw [h1 y]; exact not_isUnit_zero), zero_mul]`. Take `⟨t, rfl⟩` from `Nat.exists_eq_add_of_le hrn`. Establish `hψ' : (ψ⁻¹).IsPrimitive` using `addChar_inv_isPrimitive_of_isPrimitive ψ hψ`.

Establish `hξ' : ξ⁻¹ ≠ 1` using `inv_ne_one.mpr hξ`. Take `⟨hsing, hinv⟩` from `GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ⁻¹ ξ⁻¹ r hψ' hξ'`. Use `set G : ℂ := ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) * ψ⁻¹ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) with hG`. Take `⟨hnorm, hGint, hGinv, -⟩` from `GlobalTheory.T.galois_matrix_gaussSum_eq_char_pow_mul k ψ⁻¹ ξ⁻¹ r hψ' hξ' G rfl`. Use `set q : ℂ := (Fintype.card k : ℂ) with hq`.

Establish `hq0 : q ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Establish `hG0 : G ≠ 0`. Introduce `h0`. Rewrite `hnorm` using `[h0, norm_zero]`. Establish `: (0 : ℝ) < (Fintype.card k : ℝ) ^ (r ^ 2)` using `pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _`.

Rewrite `this` using `[← hnorm]`. Evaluate the numerical expressions using `at this`. Use `⟨q ^ (r * t) * G, r * t + r ^ 2, mul_ne_zero (pow_ne_zero _ hq0) hG0, ?_, ?_, fun u => ?_⟩` and prove the remaining obligations. Use `IsIntegral.mul (IsIntegral.pow ?_ _) hGint` and prove the remaining obligations. Rewrite using `[hq]`.

Conclude with `(isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ (Fintype.card k : ℤ)))` after adjusting the coercions. Establish `: q ^ (r * t + r ^ 2) * (q ^ (r * t) * G)⁻¹ = q ^ (r ^ 2) * G⁻¹`. Rewrite using `[pow_add, mul_inv]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Conclude with `hGinv`. Use `set u₁ := u.submatrix (Fin.castAdd t) id`. Use `set u₂ := u.submatrix (Fin.natAdd r) id`. Establish `hsplit : ∀ p : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin t) k, ((if h : IsUnit (-p.1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace (p.1 * u₁))) * ψ (trace (p.2 * u₂)) = (if h : IsUnit (topL r (-(squareAndRectColumnsEquivWideMatrix p))).det then ((ξ h.unit : ℂˣ) : ℂ) els …`. Introduce `p`.

Establish `e1 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.castAdd t) = p.1` using `congrArg Prod.fst (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)`. Establish `e2 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.natAdd r) = p.2` using `congrArg Prod.snd (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)`. Rewrite using `[mul_assoc, ← AddChar.map_add_eq_mul, trace_mul_split_castAdd_natAdd _ u, topLeftBlock_neg_eq_submatrix_castAdd, e1, e2]`. Rewrite using `[← Fintype.sum_equiv squareAndRectColumnsEquivWideMatrix _ _ hsplit, Fintype.sum_prod_type]`. Rewrite using `[show (∑ x : Matrix (Fin r) (Fin r) k, ∑ y : Matrix (Fin r) (Fin t) k, (if h : IsUnit (-(x, y).1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace ((x, y).1 * u₁)) * ψ (trace ((x, y).2 * u₂))) = (∑ x : Matrix (Fin r) (Fin r) k, (if h : IsUnit (-x).det then ((ξ h.unit : ℂˣ) : ℂ) …`.

Rewrite using `[Finset.sum_mul_sum]]`. Rewrite using `[sum_GL_character_neg_det_addChar_trace, sum_addChar_trace_rectMatrix_mul ψ hψ u₂]`. Distinguish the cases in `hu2 : u₂ = 0`. Use `swap`. Rewrite using `[if_neg hu2, mul_zero, dif_neg (fun h => hu2 ((lowZero_iff_submatrix_natAdd_eq_zero u).mp h.1)), mul_zero]`.

Rewrite using `[if_pos hu2]`. Distinguish the cases in `hdet : IsUnit u₁.det`. Use `swap`. Establish `h0 : u₁.det = 0`. Assume the negation of the conclusion as `h`.

Conclude with `hdet (isUnit_iff_ne_zero.mpr h)`. Rewrite using `[hsing u₁ h0, zero_mul, dif_neg, mul_zero]`. Introduce and unpack `⟨-, h⟩`. Rewrite `h` using `[topLeftBlock_eq_submatrix_castAdd]`. Conclude with `hdet h`.

Establish `hh : LowZero r u ∧ IsUnit (topL r u).det` using `⟨(lowZero_iff_submatrix_natAdd_eq_zero u).mpr hu2, by rw [topLeftBlock_eq_submatrix_castAdd]; exact hdet⟩`. Rewrite using `[dif_pos hh]`. Use `set a : GL (Fin r) k := Matrix.GeneralLinearGroup.mkOfDetNeZero u₁ hdet.ne_zero`. Establish `ha` using `hinv a`. Simplify using `only [Matrix.one_mul] at ha`.

Establish `hau : (a : Matrix (Fin r) (Fin r) k) = u₁` using `rfl`. Rewrite `ha` using `[hau]`. Rewrite using `[ha, ← hG]`. Establish `hunit : hh.2.unit = Matrix.GeneralLinearGroup.det a` using `Units.ext (by simp [hau, topLeftBlock_eq_submatrix_castAdd, u₁])`. Rewrite using `[hunit, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, _root_.zpow_neg_one]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fourier_flatDatum_finite : ∀ (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r n : ℕ), ψ.IsPrimitive → ξ ≠ 1 → ∃ (C : ℂ) (m : ℕ), C ≠ 0 ∧ IsIntegral ℤ C ∧ IsIntegral ℤ ((Fintype.card k : ℂ) ^ m * C⁻¹) ∧ ∀ u : Matrix (Fin n) (Fin r) k, (∑ y : Matrix (Fin r) (Fin n) k, (if h : IsUnit (topL r (-y)).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (Matrix.trace (y * u))) = C * (if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) := by
  intro k _ _ ψ ξ r n hψ hξ
  rcases lt_or_ge n r with hnr | hrn
  · refine ⟨1, 0, one_ne_zero, isIntegral_one, by simpa using isIntegral_one, fun u => ?_⟩
    have h1 : ∀ y : Matrix (Fin r) (Fin n) k, (topL r (-y)).det = 0 := fun y =>
      Matrix.det_eq_zero_of_column_eq_zero ⟨n, hnr⟩ (fun i => by simp [topL])
    have h2 : (topL r u).det = 0 := Matrix.det_eq_zero_of_row_eq_zero ⟨n, hnr⟩ (fun j => by simp [topL])
    rw [one_mul, dif_neg (by rintro ⟨-, h⟩; rw [h2] at h; exact not_isUnit_zero h)]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [dif_neg (by rw [h1 y]; exact not_isUnit_zero), zero_mul]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrn
  have hψ' : (ψ⁻¹).IsPrimitive := addChar_inv_isPrimitive_of_isPrimitive ψ hψ
  have hξ' : ξ⁻¹ ≠ 1 := inv_ne_one.mpr hξ
  obtain ⟨hsing, hinv⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ⁻¹ ξ⁻¹ r hψ' hξ'
  set G : ℂ := ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
    ψ⁻¹ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) with hG
  obtain ⟨hnorm, hGint, hGinv, -⟩ := GlobalTheory.T.galois_matrix_gaussSum_eq_char_pow_mul k ψ⁻¹ ξ⁻¹ r hψ' hξ' G rfl
  set q : ℂ := (Fintype.card k : ℂ) with hq
  have hq0 : q ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hG0 : G ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    have : (0 : ℝ) < (Fintype.card k : ℝ) ^ (r ^ 2) := pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _
    rw [← hnorm] at this
    norm_num at this
  refine ⟨q ^ (r * t) * G, r * t + r ^ 2, mul_ne_zero (pow_ne_zero _ hq0) hG0, ?_, ?_, fun u => ?_⟩
  · refine IsIntegral.mul (IsIntegral.pow ?_ _) hGint
    rw [hq]
    exact_mod_cast (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ (Fintype.card k : ℤ)))
  · have : q ^ (r * t + r ^ 2) * (q ^ (r * t) * G)⁻¹ = q ^ (r ^ 2) * G⁻¹ := by
      rw [pow_add, mul_inv]
      field_simp
    rw [this]
    exact hGinv

  set u₁ := u.submatrix (Fin.castAdd t) id
  set u₂ := u.submatrix (Fin.natAdd r) id
  have hsplit : ∀ p : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin t) k,
      ((if h : IsUnit (-p.1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace (p.1 * u₁))) *
        ψ (trace (p.2 * u₂)) =
      (if h : IsUnit (topL r (-(squareAndRectColumnsEquivWideMatrix p))).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (Matrix.trace (squareAndRectColumnsEquivWideMatrix p * u)) := by
    intro p
    have e1 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.castAdd t) = p.1 :=
      congrArg Prod.fst (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    have e2 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.natAdd r) = p.2 :=
      congrArg Prod.snd (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    rw [mul_assoc, ← AddChar.map_add_eq_mul, trace_mul_split_castAdd_natAdd _ u, topLeftBlock_neg_eq_submatrix_castAdd, e1, e2]
  rw [← Fintype.sum_equiv squareAndRectColumnsEquivWideMatrix _ _ hsplit, Fintype.sum_prod_type]
  rw [show (∑ x : Matrix (Fin r) (Fin r) k, ∑ y : Matrix (Fin r) (Fin t) k,
      (if h : IsUnit (-(x, y).1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace ((x, y).1 * u₁)) *
        ψ (trace ((x, y).2 * u₂))) =
      (∑ x : Matrix (Fin r) (Fin r) k, (if h : IsUnit (-x).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (trace (x * u₁))) * ∑ y : Matrix (Fin r) (Fin t) k, ψ (trace (y * u₂)) by
    rw [Finset.sum_mul_sum]]
  rw [sum_GL_character_neg_det_addChar_trace, sum_addChar_trace_rectMatrix_mul ψ hψ u₂]
  by_cases hu2 : u₂ = 0
  swap
  · rw [if_neg hu2, mul_zero, dif_neg (fun h => hu2 ((lowZero_iff_submatrix_natAdd_eq_zero u).mp h.1)), mul_zero]
  rw [if_pos hu2]
  by_cases hdet : IsUnit u₁.det
  swap
  · have h0 : u₁.det = 0 := by
      by_contra h; exact hdet (isUnit_iff_ne_zero.mpr h)
    rw [hsing u₁ h0, zero_mul, dif_neg, mul_zero]
    rintro ⟨-, h⟩
    rw [topLeftBlock_eq_submatrix_castAdd] at h
    exact hdet h
  have hh : LowZero r u ∧ IsUnit (topL r u).det := ⟨(lowZero_iff_submatrix_natAdd_eq_zero u).mpr hu2, by rw [topLeftBlock_eq_submatrix_castAdd]; exact hdet⟩
  rw [dif_pos hh]
  set a : GL (Fin r) k := Matrix.GeneralLinearGroup.mkOfDetNeZero u₁ hdet.ne_zero
  have ha := hinv a
  simp only [Matrix.one_mul] at ha
  have hau : (a : Matrix (Fin r) (Fin r) k) = u₁ := rfl
  rw [hau] at ha
  rw [ha, ← hG]
  have hunit : hh.2.unit = Matrix.GeneralLinearGroup.det a := Units.ext (by simp [hau, topLeftBlock_eq_submatrix_castAdd, u₁])
  rw [hunit, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, _root_.zpow_neg_one]
  ring

end GlobalTheory
