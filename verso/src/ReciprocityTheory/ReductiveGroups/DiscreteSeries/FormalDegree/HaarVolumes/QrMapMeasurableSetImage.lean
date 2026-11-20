import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens

noncomputable section

open Finset Matrix MeasureTheory InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

/- English proof (translation)
Unfold `Jm`. Simplify using the standard rewrite rules.
-/
lemma qrA_Jm_one : Jm (fun _ : Fin N => true) = 1 := by
  unfold Jm
  simp

/- English proof (translation)
Establish `h : (toM k)ᴴ * Jm (fun _ : Fin N => true) * toM k = Jm (fun _ : Fin N => true)` using `k.2`. Rewrite `h` using `[qrA_Jm_one, Matrix.mul_one]`. Then use the resulting hypothesis.
-/
lemma qrA_unitary (k : UNgrp N) : (toM k)ᴴ * toM k = 1 := by
  have h : (toM k)ᴴ * Jm (fun _ : Fin N => true) * toM k = Jm (fun _ : Fin N => true) := k.2
  rwa [qrA_Jm_one, Matrix.mul_one] at h

/- English proof (translation)
Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Distinguish the cases in `hab : a = b`. Simplify using `only [upMat, if_pos hab]`. Conclude with `Complex.continuous_ofReal.comp ((continuous_apply a).comp continuous_fst)`. Distinguish the cases in `h : a < b`.

Simplify using `only [upMat, if_neg hab, dif_pos h]`. Conclude with `(continuous_apply _).comp continuous_snd`. Simplify using `only [upMat, if_neg hab, dif_neg h]`. Conclude with `continuous_const`.
-/
lemma qrA_upMat_continuous : Continuous (upMat (N := N)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  by_cases hab : a = b
  · simp only [upMat, if_pos hab]
    exact Complex.continuous_ofReal.comp ((continuous_apply a).comp continuous_fst)
  · by_cases h : a < b
    · simp only [upMat, if_neg hab, dif_pos h]
      exact (continuous_apply _).comp continuous_snd
    · simp only [upMat, if_neg hab, dif_neg h]
      exact continuous_const

/- English proof (translation)
Use `show Continuous fun kt : UNgrp N × TriCo N => toM kt.1 * upMat kt.2`. Conclude with `((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).matrix_mul (qrA_upMat_continuous.comp continuous_snd)`.
-/
theorem qrMap_continuous : Continuous (qrMap (N := N)) := by
  show Continuous fun kt : UNgrp N × TriCo N => toM kt.1 * upMat kt.2
  exact ((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).matrix_mul
    (qrA_upMat_continuous.comp continuous_snd)

/- English proof (translation)
Introduce `i j hij`. Establish `h1 : i ≠ j` using `ne_of_gt hij`. Establish `h2 : ¬ i < j` using `not_lt.2 (le_of_lt hij)`. Simplify using `only [upMat, if_neg h1, dif_neg h2]`.
-/
lemma qrA_upMat_tri (t : TriCo N) : (upMat t).IsUpperTriangular := by
  intro i j hij
  have h1 : i ≠ j := ne_of_gt hij
  have h2 : ¬ i < j := not_lt.2 (le_of_lt hij)
  simp only [upMat, if_neg h1, dif_neg h2]

/- English proof (translation)
Simplify using `[upMat]`.
-/
lemma qrA_upMat_diag (t : TriCo N) (i : Fin N) : upMat t i i = ((t.1 i : ℝ) : ℂ) := by
  simp [upMat]

/- English proof (translation)
Rewrite using `[Matrix.det_of_upperTriangular (qrA_upMat_tri t)]`. Conclude with `Finset.prod_congr rfl fun i _ => qrA_upMat_diag t i`.
-/
lemma qrA_upMat_det (t : TriCo N) : (upMat t).det = ∏ j, ((t.1 j : ℝ) : ℂ) := by
  rw [Matrix.det_of_upperTriangular (qrA_upMat_tri t)]
  exact Finset.prod_congr rfl fun i _ => qrA_upMat_diag t i

/- English proof (translation)
Rewrite using `[qrA_upMat_det]`. Conclude with `Finset.prod_ne_zero_iff.2 fun j _ => Complex.ofReal_ne_zero.2 (ht j).ne'`.
-/
lemma qrA_upMat_det_ne (t : TriCo N) (ht : t ∈ triPos N) : (upMat t).det ≠ 0 := by
  rw [qrA_upMat_det]
  exact Finset.prod_ne_zero_iff.2 fun j _ => Complex.ofReal_ne_zero.2 (ht j).ne'

/- English proof (translation)
Use `Prod.ext (funext fun j => ?_) (funext fun ab => ?_)` and prove the remaining obligations. Simplify using `[triCoOf, upMat]`. Simplify using `only [triCoOf, upMat, if_neg (ne_of_lt ab.2), dif_pos ab.2]`.
-/
lemma qrA_triCoOf_upMat (t : TriCo N) : triCoOf (upMat t) = t := by
  refine Prod.ext (funext fun j => ?_) (funext fun ab => ?_)
  · simp [triCoOf, upMat]
  · simp only [triCoOf, upMat, if_neg (ne_of_lt ab.2), dif_pos ab.2]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Introduce `b _ hb`. Break down `lt_or_gt_of_ne hb with h | h` into its components or cases. Rewrite using `[hA h, zero_mul]`. Rewrite using `[hB h, mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
lemma qrA_mul_diag {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsUpperTriangular)
    (hB : B.IsUpperTriangular) (i : Fin N) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Use `haveI : Invertible R := R.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hd)`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hR`.
-/
lemma qrA_inv_tri {R : Matrix (Fin N) (Fin N) ℂ} (hR : R.IsUpperTriangular) (hd : R.det ≠ 0) :
    (R⁻¹).IsUpperTriangular := by
  haveI : Invertible R := R.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hd)
  exact Matrix.blockTriangular_inv_of_blockTriangular hR

/- English proof (translation)
Establish `hu : IsUnit R.det` using `isUnit_iff_ne_zero.2 hd`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma qrA_upMat_cancel {A B : Matrix (Fin N) (Fin N) ℂ} {R : Matrix (Fin N) (Fin N) ℂ} (hd : R.det ≠ 0)
    (h : A * R = B * R) : A = B := by
  have hu : IsUnit R.det := isUnit_iff_ne_zero.2 hd
  calc A = A * R * R⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = B * R * R⁻¹ := by rw [h]
    _ = B := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

/- English proof (translation)
Substitute `hR` using the available equality. Substitute `hR'` using the available equality. Establish `hd` using `qrA_upMat_det_ne t ht`. Establish `hd'` using `qrA_upMat_det_ne t' ht'`. Establish `hRt` using `qrA_upMat_tri t`.

Establish `hRt'` using `qrA_upMat_tri t'`. Establish `hu : IsUnit (upMat t).det` using `isUnit_iff_ne_zero.2 hd`. Establish `hu' : IsUnit (upMat t').det` using `isUnit_iff_ne_zero.2 hd'`. Establish `hU : U = upMat t' * (upMat t)⁻¹`. Rewrite using `[← h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]`.

Establish `hUh : Uᴴ = upMat t * (upMat t')⁻¹`. Rewrite using `[← h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu', Matrix.mul_one]`. Establish `hUt : U.IsUpperTriangular` using `hU ▸ hRt'.mul (qrA_inv_tri hRt hd)`. Establish `hUht : Uᴴ.IsUpperTriangular` using `hUh ▸ hRt.mul (qrA_inv_tri hRt' hd')`. Establish `hinvd : ∀ M : Matrix (Fin N) (Fin N) ℂ, M.IsUpperTriangular → M.det ≠ 0 → ∀ i, M⁻¹ i i = (M i i)⁻¹`.

Introduce `M hM hMd i`. Establish `h` using `congrFun (congrFun (Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.2 hMd)) i) i`. Rewrite `h` using `[qrA_mul_diag hM (qrA_inv_tri hM hMd), Matrix.one_apply_eq]`. Conclude with `eq_inv_of_mul_eq_one_right h`. Establish `hdiag : ∀ i, U i i = ((t'.1 i : ℝ) : ℂ) * (((t.1 i : ℝ) : ℂ))⁻¹`.

Introduce `i`. Rewrite using `[hU, qrA_mul_diag hRt' (qrA_inv_tri hRt hd), hinvd _ hRt hd, qrA_upMat_diag, qrA_upMat_diag]`. Establish `hdiag' : ∀ i, Uᴴ i i = ((t.1 i : ℝ) : ℂ) * (((t'.1 i : ℝ) : ℂ))⁻¹`. Introduce `i`. Rewrite using `[hUh, qrA_mul_diag hRt (qrA_inv_tri hRt' hd'), hinvd _ hRt' hd', qrA_upMat_diag, qrA_upMat_diag]`.

Establish `heq : ∀ i, t.1 i = t'.1 i`. Introduce `i`. Establish `e1` using `hdiag' i`. Rewrite `e1` using `[Matrix.conjTranspose_apply, hdiag i]`. Establish `ha` using `ht i`.

Establish `hb` using `ht' i`. Establish `e2 : t'.1 i * (t.1 i)⁻¹ = t.1 i * (t'.1 i)⁻¹`. Establish `e3 : ((t'.1 i * (t.1 i)⁻¹ : ℝ) : ℂ) = ((t.1 i * (t'.1 i)⁻¹ : ℝ) : ℂ)`. Use `push_cast`. Rewrite using `[← e1]`.

Simplify using `[Complex.conj_ofReal]`. Conclude with `e3` after adjusting the coercions. Clear denominators, using `at e2` for the nonvanishing conditions. Use the polynomial consequences of the given equalities and inequalities. Establish `hU1 : U = 1`.

Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[hdiag i, heq i, Matrix.one_apply_eq]`. Conclude with `mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 (ht' i).ne')`.

Rewrite using `[Matrix.one_apply_ne hij]`. Break down `lt_or_gt_of_ne hij with h | h` into its components or cases. Establish `e` using `hUht h`. Rewrite `e` using `[Matrix.conjTranspose_apply]`. Simplify using `using e`.

Conclude with `hUt h`. Rewrite `h1` using `[hU1, Matrix.one_mul]`. Rewrite using `[← qrA_triCoOf_upMat t, h1, qrA_triCoOf_upMat]`.
-/
lemma qrA_tri_unique {U R R' : Matrix (Fin N) (Fin N) ℂ} {t t' : TriCo N} (ht : t ∈ triPos N)
    (ht' : t' ∈ triPos N) (hR : R = upMat t) (hR' : R' = upMat t')
    (h1 : U * R = R') (h2 : Uᴴ * R' = R) : t = t' := by
  subst hR
  subst hR'
  have hd := qrA_upMat_det_ne t ht
  have hd' := qrA_upMat_det_ne t' ht'
  have hRt := qrA_upMat_tri t
  have hRt' := qrA_upMat_tri t'
  have hu : IsUnit (upMat t).det := isUnit_iff_ne_zero.2 hd
  have hu' : IsUnit (upMat t').det := isUnit_iff_ne_zero.2 hd'
  have hU : U = upMat t' * (upMat t)⁻¹ := by
    rw [← h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have hUh : Uᴴ = upMat t * (upMat t')⁻¹ := by
    rw [← h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu', Matrix.mul_one]
  have hUt : U.IsUpperTriangular := hU ▸ hRt'.mul (qrA_inv_tri hRt hd)
  have hUht : Uᴴ.IsUpperTriangular := hUh ▸ hRt.mul (qrA_inv_tri hRt' hd')
  have hinvd : ∀ M : Matrix (Fin N) (Fin N) ℂ, M.IsUpperTriangular → M.det ≠ 0 →
      ∀ i, M⁻¹ i i = (M i i)⁻¹ := by
    intro M hM hMd i
    have h := congrFun (congrFun (Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.2 hMd)) i) i
    rw [qrA_mul_diag hM (qrA_inv_tri hM hMd), Matrix.one_apply_eq] at h
    exact eq_inv_of_mul_eq_one_right h
  have hdiag : ∀ i, U i i = ((t'.1 i : ℝ) : ℂ) * (((t.1 i : ℝ) : ℂ))⁻¹ := by
    intro i
    rw [hU, qrA_mul_diag hRt' (qrA_inv_tri hRt hd), hinvd _ hRt hd, qrA_upMat_diag, qrA_upMat_diag]
  have hdiag' : ∀ i, Uᴴ i i = ((t.1 i : ℝ) : ℂ) * (((t'.1 i : ℝ) : ℂ))⁻¹ := by
    intro i
    rw [hUh, qrA_mul_diag hRt (qrA_inv_tri hRt' hd'), hinvd _ hRt' hd', qrA_upMat_diag, qrA_upMat_diag]
  have heq : ∀ i, t.1 i = t'.1 i := by
    intro i
    have e1 := hdiag' i
    rw [Matrix.conjTranspose_apply, hdiag i] at e1
    have ha := ht i
    have hb := ht' i
    have e2 : t'.1 i * (t.1 i)⁻¹ = t.1 i * (t'.1 i)⁻¹ := by
      have e3 : ((t'.1 i * (t.1 i)⁻¹ : ℝ) : ℂ) = ((t.1 i * (t'.1 i)⁻¹ : ℝ) : ℂ) := by
        push_cast
        rw [← e1]
        simp [Complex.conj_ofReal]
      exact_mod_cast e3
    field_simp at e2
    nlinarith
  have hU1 : U = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [hdiag i, heq i, Matrix.one_apply_eq]
      exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 (ht' i).ne')
    · rw [Matrix.one_apply_ne hij]
      rcases lt_or_gt_of_ne hij with h | h
      · have e := hUht h
        rw [Matrix.conjTranspose_apply] at e
        simpa using e
      · exact hUt h
  rw [hU1, Matrix.one_mul] at h1
  rw [← qrA_triCoOf_upMat t, h1, qrA_triCoOf_upMat]

/- English proof (translation)
Introduce and unpack `⟨k, t⟩ ⟨-, ht⟩ ⟨k', t'⟩ ⟨-, ht'⟩ h`. Establish `h' : toM k * upMat t = toM k' * upMat t'` using `h`. Establish `e1 : (toM k')ᴴ * toM k * upMat t = upMat t'`. Rewrite using `[Matrix.mul_assoc, h', ← Matrix.mul_assoc, qrA_unitary, Matrix.one_mul]`. Establish `e2 : ((toM k')ᴴ * toM k)ᴴ * upMat t' = upMat t`.

Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, ← h', ← Matrix.mul_assoc, qrA_unitary, Matrix.one_mul]`. Establish `htt : t = t'` using `qrA_tri_unique ht ht' rfl rfl e1 e2`. Substitute `htt` using the available equality. Establish `hk : toM k = toM k'` using `qrA_upMat_cancel (qrA_upMat_det_ne t ht) h'`. Establish `hk' : k = k'` using `Subtype.ext (Units.ext hk)`.

Rewrite using `[hk']`.
-/
theorem qrMap_injOn : Set.InjOn (qrMap (N := N)) (Set.univ ×ˢ triPos N) := by
  rintro ⟨k, t⟩ ⟨-, ht⟩ ⟨k', t'⟩ ⟨-, ht'⟩ h
  have h' : toM k * upMat t = toM k' * upMat t' := h
  have e1 : (toM k')ᴴ * toM k * upMat t = upMat t' := by
    rw [Matrix.mul_assoc, h', ← Matrix.mul_assoc, qrA_unitary, Matrix.one_mul]
  have e2 : ((toM k')ᴴ * toM k)ᴴ * upMat t' = upMat t := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, ← h',
      ← Matrix.mul_assoc, qrA_unitary, Matrix.one_mul]
  have htt : t = t' := qrA_tri_unique ht ht' rfl rfl e1 e2
  subst htt
  have hk : toM k = toM k' := qrA_upMat_cancel (qrA_upMat_det_ne t ht) h'
  have hk' : k = k' := Subtype.ext (Units.ext hk)
  rw [hk']

/- English proof (translation)
Take `⟨C, hC, hmem⟩ : ∃ C : Set (Fin N → Fin N → ℂ), IsClosed C ∧ ∀ Z, Z ∈ C ↔ (Matrix.of Z)ᴴ * Matrix.of Z = 1` from `⟨{Z | (Matrix.of Z)ᴴ * Matrix.of Z = 1}, isClosed_eq ((continuous_id : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of Z).matrix_conjTranspose.matrix_mul (continuous_id : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of Z)) continuous_const, fun Z => Iff.rfl⟩`. Use `haveI : PolishSpace C := hC.polishSpace`. Establish `hCt : Continuous (fun Z : C => (Z : Fin N → Fin N → ℂ))` using `continuous_subtype_val`. Set `e : UNgrp N ≃ₜ C` to `{ toFun := fun k => ⟨Matrix.of.symm (toM k), (hmem _).2 (qrA_unitary k)⟩ invFun := fun Z => ⟨⟨Matrix.of Z.1, (Matrix.of Z.1)ᴴ, mul_eq_one_comm.1 ((hmem _).1 Z.2), (hmem _).1 Z.2⟩, by show (Matrix.of Z.1)ᴴ * Jm (fun _ : Fin N => true) * Matrix.of Z.1 = Jm (fun _ : Fin N => true)`. Rewrite using `[qrA_Jm_one, Matrix.mul_one]`.

Conclude with `(hmem _).1 Z.2⟩`. Use `left_inv := fun k => Subtype.ext (Units.ext rfl)`. Use `right_inv := fun Z => rfl`. Use `continuous_toFun := continuous_induced_rng.2 (Units.continuous_val.comp continuous_subtype_val : Continuous fun k : UNgrp N => ((k : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Matrix (Fin N) (Fin N) ℂ))`. Use `continuous_invFun := continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hCt, hCt.matrix_conjTranspose⟩) }`.

Conclude with `e.isClosedEmbedding.polishSpace`.
-/
private theorem qrMap_measurableSet_image_lemma (N : ℕ) : PolishSpace (UNgrp N) := by
  obtain ⟨C, hC, hmem⟩ : ∃ C : Set (Fin N → Fin N → ℂ), IsClosed C ∧
      ∀ Z, Z ∈ C ↔ (Matrix.of Z)ᴴ * Matrix.of Z = 1 :=
    ⟨{Z | (Matrix.of Z)ᴴ * Matrix.of Z = 1},
      isClosed_eq ((continuous_id : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of Z).matrix_conjTranspose.matrix_mul
        (continuous_id : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of Z)) continuous_const,
      fun Z => Iff.rfl⟩
  haveI : PolishSpace C := hC.polishSpace
  have hCt : Continuous (fun Z : C => (Z : Fin N → Fin N → ℂ)) := continuous_subtype_val
  let e : UNgrp N ≃ₜ C :=
    { toFun := fun k => ⟨Matrix.of.symm (toM k), (hmem _).2 (qrA_unitary k)⟩
      invFun := fun Z => ⟨⟨Matrix.of Z.1, (Matrix.of Z.1)ᴴ, mul_eq_one_comm.1 ((hmem _).1 Z.2),
          (hmem _).1 Z.2⟩, by
        show (Matrix.of Z.1)ᴴ * Jm (fun _ : Fin N => true) * Matrix.of Z.1 = Jm (fun _ : Fin N => true)
        rw [qrA_Jm_one, Matrix.mul_one]
        exact (hmem _).1 Z.2⟩
      left_inv := fun k => Subtype.ext (Units.ext rfl)
      right_inv := fun Z => rfl
      continuous_toFun := continuous_induced_rng.2
        (Units.continuous_val.comp continuous_subtype_val :
          Continuous fun k : UNgrp N => ((k : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Matrix (Fin N) (Fin N) ℂ))
      continuous_invFun := continuous_induced_rng.2 (Units.continuous_iff.2
        ⟨hCt, hCt.matrix_conjTranspose⟩) }
  exact e.isClosedEmbedding.polishSpace

/- English proof (translation)
Use `haveI : PolishSpace (UNgrp N) := qrMap_measurableSet_image_lemma N`. Conclude with `hS.image_of_continuousOn_injOn qrMap_continuous.continuousOn (qrMap_injOn.mono hS0)`.
-/
theorem qrMap_measurableSet_image (S : Set (UNgrp N × TriCo N)) (hS : MeasurableSet S)
    (hS0 : S ⊆ Set.univ ×ˢ triPos N) : MeasurableSet (qrMap '' S) := by
  haveI : PolishSpace (UNgrp N) := qrMap_measurableSet_image_lemma N
  exact hS.image_of_continuousOn_injOn qrMap_continuous.continuousOn (qrMap_injOn.mono hS0)

/- English proof (translation)
Set `f : Fin N → EuclideanSpace ℂ (Fin N)` to `fun j => WithLp.toLp 2 (Z.col j)`. Establish `hli : LinearIndependent ℂ f`. Establish `h0` using `Matrix.linearIndependent_cols_of_isUnit ((Matrix.isUnit_iff_isUnit_det Z).2 (isUnit_iff_ne_zero.2 hZ))`. Conclude with `h0.map' (WithLp.linearEquiv 2 ℂ (Fin N → ℂ)).symm.toLinearMap (LinearEquiv.ker _)`. Establish `hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) = Fintype.card (Fin N)` using `by simp`.

Set `b` to `InnerProductSpace.gramSchmidtOrthonormalBasis hdim f`. Establish `hgs : ∀ j, InnerProductSpace.gramSchmidt ℂ f j ≠ 0` using `fun j => InnerProductSpace.gramSchmidt_ne_zero j hli`. Establish `hb : ∀ i, b i = InnerProductSpace.gramSchmidtNormed ℂ f i`. Introduce `i`. Use `InnerProductSpace.gramSchmidtOrthonormalBasis_apply hdim ?_` and prove the remaining obligations.

Introduce `h`. Use `InnerProductSpace.gramSchmidtNormed_unit_length i hli` as an intermediate fact. Rewrite `this` using `[h, norm_zero]`. Conclude with `zero_ne_one this`. Take `⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin N) (Fin N) ℂ, ∀ a i, Q a i = (b i).ofLp a` from `⟨Matrix.of fun a i => (b i).ofLp a, fun _ _ => rfl⟩`.

Take `⟨R, hRdef⟩ : ∃ R : Matrix (Fin N) (Fin N) ℂ, ∀ i j, R i j = inner ℂ (b i) (f j)` from `⟨Matrix.of fun i j => inner ℂ (b i) (f j), fun _ _ => rfl⟩`. Establish `hRup : R.IsUpperTriangular`. Introduce `i j hji`. Rewrite using `[hRdef]`. Conclude with `InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular hdim f hji`.

Establish `hself : ∀ j, inner ℂ (InnerProductSpace.gramSchmidt ℂ f j) (f j) = (‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℂ) ^ 2`. Introduce `j`. Establish `hf : f j = InnerProductSpace.gramSchmidt ℂ f j + ∑ i ∈ Finset.Iio j, (ℂ ∙ InnerProductSpace.gramSchmidt ℂ f i).starProjection (f j)`. Rewrite using `[InnerProductSpace.gramSchmidt_def ℂ f j]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hf, inner_add_right, inner_sum, Finset.sum_eq_zero (fun i hi => ?_), add_zero, inner_self_eq_norm_sq_to_K]`. Both sides reduce to the same expression. Rewrite using `[Submodule.starProjection_singleton, inner_smul_right, InnerProductSpace.gramSchmidt_orthogonal ℂ f (ne_of_gt (Finset.mem_Iio.1 hi)), mul_zero]`. Establish `hdiag : ∀ j, R j j = ((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ)`. Introduce `j`.

Establish `ha : ‖InnerProductSpace.gramSchmidt ℂ f j‖ ≠ 0` using `norm_ne_zero_iff.2 (hgs j)`. Rewrite using `[hRdef, hb j, InnerProductSpace.gramSchmidtNormed, inner_smul_left, hself j]`. Simplify using `only [map_inv₀, RCLike.conj_ofReal, Complex.conj_ofReal]`. Express the relevant statement in the definitionally equal form `(((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ))⁻¹ * ((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ) ^ 2 = ((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ)`. Establish `hc : ((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 ha`.

Rewrite using `[sq, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]`. Establish `ht : triCoOf R ∈ triPos N`. Introduce `j`. Use `show 0 < (R j j).re`. Rewrite using `[hdiag j, Complex.ofReal_re]`.

Conclude with `norm_pos_iff.2 (hgs j)`. Establish `hupR : upMat (triCoOf R) = R`. Use extensionality with `a c`. Distinguish the cases in `hac : a = c`. Substitute `hac` using the available equality.

Simplify using `only [upMat, triCoOf, if_true]`. Rewrite using `[hdiag a, Complex.ofReal_re]`. Distinguish the cases in `h : a < c`. Simplify using `only [upMat, triCoOf, if_neg hac, dif_pos h]`. Simplify using `only [upMat, if_neg hac, dif_neg h]`.

Conclude with `(hRup (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hac))).symm`. Establish `hQ : Qᴴ * Q = 1`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Establish `e` using `(orthonormal_iff_ite.1 b.orthonormal) i j`.

Rewrite `e` using `[PiLp.inner_apply]`. Rewrite using `[Matrix.one_apply, ← e]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_apply, hQdef, hQdef, RCLike.inner_apply, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hQR : Q * R = Z`. Use extensionality with `a j`. Rewrite using `[Matrix.mul_apply]`. Establish `e` using `congrArg (fun v : EuclideanSpace ℂ (Fin N) => v.ofLp a) (b.sum_repr' (f j))`. Simplify using `only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f, PiLp.toLp_apply, Matrix.col_apply] at e`.

Rewrite using `[← e]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hQdef, hRdef]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨Q, triCoOf R, hQ, ht, by rw [hupR]; exact hQR⟩`.
-/
lemma qrA_exists (Z : Matrix (Fin N) (Fin N) ℂ) (hZ : Z.det ≠ 0) :
    ∃ Q : Matrix (Fin N) (Fin N) ℂ, ∃ t : TriCo N, Qᴴ * Q = 1 ∧ t ∈ triPos N ∧ Q * upMat t = Z := by
  classical
  let f : Fin N → EuclideanSpace ℂ (Fin N) := fun j => WithLp.toLp 2 (Z.col j)
  have hli : LinearIndependent ℂ f := by
    have h0 := Matrix.linearIndependent_cols_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det Z).2 (isUnit_iff_ne_zero.2 hZ))
    exact h0.map' (WithLp.linearEquiv 2 ℂ (Fin N → ℂ)).symm.toLinearMap (LinearEquiv.ker _)
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) = Fintype.card (Fin N) := by simp
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis hdim f
  have hgs : ∀ j, InnerProductSpace.gramSchmidt ℂ f j ≠ 0 := fun j =>
    InnerProductSpace.gramSchmidt_ne_zero j hli
  have hb : ∀ i, b i = InnerProductSpace.gramSchmidtNormed ℂ f i := by
    intro i
    refine InnerProductSpace.gramSchmidtOrthonormalBasis_apply hdim ?_
    intro h
    have := InnerProductSpace.gramSchmidtNormed_unit_length i hli
    rw [h, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin N) (Fin N) ℂ, ∀ a i, Q a i = (b i).ofLp a :=
    ⟨Matrix.of fun a i => (b i).ofLp a, fun _ _ => rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : Matrix (Fin N) (Fin N) ℂ, ∀ i j, R i j = inner ℂ (b i) (f j) :=
    ⟨Matrix.of fun i j => inner ℂ (b i) (f j), fun _ _ => rfl⟩
  have hRup : R.IsUpperTriangular := by
    intro i j hji
    rw [hRdef]
    exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular hdim f hji
  have hself : ∀ j, inner ℂ (InnerProductSpace.gramSchmidt ℂ f j) (f j) =
      (‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℂ) ^ 2 := by
    intro j
    have hf : f j = InnerProductSpace.gramSchmidt ℂ f j +
        ∑ i ∈ Finset.Iio j, (ℂ ∙ InnerProductSpace.gramSchmidt ℂ f i).starProjection (f j) := by
      rw [InnerProductSpace.gramSchmidt_def ℂ f j]
      abel
    rw [hf, inner_add_right, inner_sum, Finset.sum_eq_zero (fun i hi => ?_), add_zero,
      inner_self_eq_norm_sq_to_K]
    · rfl
    · rw [Submodule.starProjection_singleton, inner_smul_right,
        InnerProductSpace.gramSchmidt_orthogonal ℂ f (ne_of_gt (Finset.mem_Iio.1 hi)), mul_zero]
  have hdiag : ∀ j, R j j = ((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ) := by
    intro j
    have ha : ‖InnerProductSpace.gramSchmidt ℂ f j‖ ≠ 0 := norm_ne_zero_iff.2 (hgs j)
    rw [hRdef, hb j, InnerProductSpace.gramSchmidtNormed, inner_smul_left, hself j]
    simp only [map_inv₀, RCLike.conj_ofReal, Complex.conj_ofReal]
    change (((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ))⁻¹ *
        ((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ) ^ 2 = ((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ)
    have hc : ((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha
    rw [sq, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have ht : triCoOf R ∈ triPos N := by
    intro j
    show 0 < (R j j).re
    rw [hdiag j, Complex.ofReal_re]
    exact norm_pos_iff.2 (hgs j)
  have hupR : upMat (triCoOf R) = R := by
    ext a c
    by_cases hac : a = c
    · subst hac
      simp only [upMat, triCoOf, if_true]
      rw [hdiag a, Complex.ofReal_re]
    · by_cases h : a < c
      · simp only [upMat, triCoOf, if_neg hac, dif_pos h]
      · simp only [upMat, if_neg hac, dif_neg h]
        exact (hRup (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hac))).symm
  have hQ : Qᴴ * Q = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have e := (orthonormal_iff_ite.1 b.orthonormal) i j
    rw [PiLp.inner_apply] at e
    rw [Matrix.one_apply, ← e]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.conjTranspose_apply, hQdef, hQdef, RCLike.inner_apply, Complex.star_def]
    ring
  have hQR : Q * R = Z := by
    ext a j
    rw [Matrix.mul_apply]
    have e := congrArg (fun v : EuclideanSpace ℂ (Fin N) => v.ofLp a) (b.sum_repr' (f j))
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      f, PiLp.toLp_apply, Matrix.col_apply] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hQdef, hRdef]
    ring
  exact ⟨Q, triCoOf R, hQ, ht, by rw [hupR]; exact hQR⟩

/- English proof (translation)
Use extensionality with `Z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨k, t⟩, ⟨-, ht⟩, rfl⟩ show (toM k * upMat t).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Use `mul_ne_zero ?_ (qrA_upMat_det_ne t ht)` and prove the remaining obligations.

Introduce `h0`. Establish `e` using `congrArg Matrix.det (qrA_unitary k)`. Rewrite `e` using `[Matrix.det_mul, h0, mul_zero, Matrix.det_one]`. Conclude with `zero_ne_one e`. Introduce `hZ`.

Take `⟨Q, t, hQ, ht, hQt⟩` from `qrA_exists (Matrix.of Z) hZ`. Use `⟨(⟨⟨Q, Qᴴ, mul_eq_one_comm.1 hQ, hQ⟩, ?_⟩, t), ⟨Set.mem_univ _, ht⟩, ?_⟩` and prove the remaining obligations. Use `show Qᴴ * Jm (fun _ : Fin N => true) * Q = Jm (fun _ : Fin N => true)`. Rewrite using `[qrA_Jm_one, Matrix.mul_one]`. Conclude with `hQ`.

Use `show Matrix.of.symm (Q * upMat t) = Z`. Rewrite using `[hQt]`. Both sides reduce to the same expression.
-/
theorem qrMap_image :
    qrMap '' (Set.univ ×ˢ triPos N) = {Z : Fin N → Fin N → ℂ | (Matrix.of Z).det ≠ 0} := by
  ext Z
  constructor
  · rintro ⟨⟨k, t⟩, ⟨-, ht⟩, rfl⟩
    show (toM k * upMat t).det ≠ 0
    rw [Matrix.det_mul]
    refine mul_ne_zero ?_ (qrA_upMat_det_ne t ht)
    intro h0
    have e := congrArg Matrix.det (qrA_unitary k)
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at e
    exact zero_ne_one e
  · intro hZ
    obtain ⟨Q, t, hQ, ht, hQt⟩ := qrA_exists (Matrix.of Z) hZ
    refine ⟨(⟨⟨Q, Qᴴ, mul_eq_one_comm.1 hQ, hQ⟩, ?_⟩, t), ⟨Set.mem_univ _, ht⟩, ?_⟩
    · show Qᴴ * Jm (fun _ : Fin N => true) * Q = Jm (fun _ : Fin N => true)
      rw [qrA_Jm_one, Matrix.mul_one]
      exact hQ
    · show Matrix.of.symm (Q * upMat t) = Z
      rw [hQt]
      rfl

end ReciprocityTheory.ChartRestriction.DS
