import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartShortOf

noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField Matrix
open scoped ComplexOrder

/- English proof (translation)
Rewrite using `[Matrix.star_eq_conjTranspose, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]`. Establish `h : star z ᵥ* U = star (Uᴴ *ᵥ z)`. Rewrite using `[Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]`. Rewrite using `[h]`. Simplify using `only [dotProduct, Pi.star_apply, Matrix.mulVec_diagonal]`.
-/
theorem svM_conj_form {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (d z : Fin n → ℂ) :
    star z ⬝ᵥ ((U * diagonal d * star U) *ᵥ z) =
      ∑ i, star ((star U *ᵥ z) i) * (d i * (star U *ᵥ z) i) := by
  rw [Matrix.star_eq_conjTranspose, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  have h : star z ᵥ* U = star (Uᴴ *ᵥ z) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [h]
  simp only [dotProduct, Pi.star_apply, Matrix.mulVec_diagonal]

/- English proof (translation)
Simplify using `only [Complex.star_def, Complex.ofReal_mul, Complex.ofReal_pow]`. Rewrite using `[mul_left_comm, Complex.conj_mul']`.
-/
theorem svM_term (r : ℝ) (w : ℂ) : star w * ((r : ℂ) * w) = ((r * ‖w‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Complex.star_def, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [mul_left_comm, Complex.conj_mul']

/- English proof (translation)
Introduce `n J hJ hdet`. Use `set U : Matrix (Fin n) (Fin n) ℂ := (hJ.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef`. Use `set ev := hJ.eigenvalues with hev`. Establish `hspec : J = U * diagonal (fun i => ((ev i : ℝ) : ℂ)) * star U`. Establish `h` using `hJ.spectral_theorem`.

Rewrite `h` using `[Unitary.conjStarAlgAut_apply]`. Conclude with `h`. Establish `hUU : star U * U = 1` using `Matrix.mem_unitaryGroup_iff'.1 hJ.eigenvectorUnitary.2`. Establish `hUU' : U * star U = 1` using `Matrix.mem_unitaryGroup_iff.1 hJ.eigenvectorUnitary.2`. Establish `hev0 : ∀ i, ev i ≠ 0`.

Introduce `i h`. Apply `hdet` to reduce the goal to its premises. Rewrite using `[hJ.det_eq_prod_eigenvalues]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← hev, h]; simp)`. Use `⟨U * diagonal (fun i => ((|ev i| : ℝ) : ℂ)) * star U, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hD : (diagonal (fun i => ((|ev i| : ℝ) : ℂ))).PosDef`. Rewrite using `[Matrix.posDef_diagonal_iff]`. Introduce `i`. Conclude with `Complex.zero_lt_real.2 (abs_pos.2 (hev0 i))`. Establish `hinj : Function.Injective (star U).mulVec`.

Introduce `x y hxy`. Use `congrArg (fun v => U *ᵥ v) hxy` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, hUU']`. Establish `h2` using `hD.conjTranspose_mul_mul_same hinj`. Rewrite `h2` using `[Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis.

Establish `hdU : U.det * (star U).det = 1` using `by rw [← Matrix.det_mul, hUU', Matrix.det_one]`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, mul_right_comm, hdU, one_mul, Matrix.det_diagonal, hJ.det_eq_prod_eigenvalues, norm_prod]`. Use `push_cast`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `i _`.

Simplify using `[hev]`. Introduce `z`. Rewrite using `[hspec, svM_conj_form, svM_conj_form]`. Simplify using `only [svM_term]`. Rewrite using `[← Complex.ofReal_sum, ← Complex.ofReal_sum, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs]`.

Use `(Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))` and prove the remaining obligations. Rewrite using `[abs_mul, abs_sq]`.
-/
theorem successive_vector_majorant : SvMaj := by
  intro n J hJ hdet
  set U : Matrix (Fin n) (Fin n) ℂ := (hJ.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  set ev := hJ.eigenvalues with hev
  have hspec : J = U * diagonal (fun i => ((ev i : ℝ) : ℂ)) * star U := by
    have h := hJ.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hJ.eigenvectorUnitary.2
  have hUU' : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hJ.eigenvectorUnitary.2
  have hev0 : ∀ i, ev i ≠ 0 := by
    intro i h
    apply hdet
    rw [hJ.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← hev, h]; simp)
  refine ⟨U * diagonal (fun i => ((|ev i| : ℝ) : ℂ)) * star U, ?_, ?_, ?_⟩
  · have hD : (diagonal (fun i => ((|ev i| : ℝ) : ℂ))).PosDef := by
      rw [Matrix.posDef_diagonal_iff]
      intro i
      exact Complex.zero_lt_real.2 (abs_pos.2 (hev0 i))
    have hinj : Function.Injective (star U).mulVec := by
      intro x y hxy
      have := congrArg (fun v => U *ᵥ v) hxy
      simpa [Matrix.mulVec_mulVec, hUU'] using this
    have h2 := hD.conjTranspose_mul_mul_same hinj
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
      ← Matrix.star_eq_conjTranspose] at h2
  · have hdU : U.det * (star U).det = 1 := by rw [← Matrix.det_mul, hUU', Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, hdU, one_mul, Matrix.det_diagonal,
      hJ.det_eq_prod_eigenvalues, norm_prod]
    push_cast
    apply Finset.prod_congr rfl
    intro i _
    simp [hev]
  · intro z
    rw [hspec, svM_conj_form, svM_conj_form]
    simp only [svM_term]
    rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, Complex.norm_real, Complex.ofReal_re,
      Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [abs_mul, abs_sq]

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hCM m J hJ hdet`. Establish `hstar : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)` using `hCM.cmUnram.2.1`. Establish `hTC : NumberField.IsTotallyComplex E` using `hCM.cmUnram.1`. Establish `hne : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ`. Introduce `φ h`.

Establish `hc` using `hTC.isComplex (InfinitePlace.mk φ)`. Rewrite `hc` using `[InfinitePlace.isComplex_mk_iff]`. Conclude with `hc (ComplexEmbedding.isReal_iff.2 h)`. Establish `hJe : ∀ i j, star (J j i) = J i j`. Introduce `i j`.

Use `congrFun (congrFun hJ i) j` as an intermediate fact. Simplify using `only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this`. Conclude with `this`. Establish `hherm : ∀ φ : E →+* ℂ, (J.map φ).IsHermitian`. Introduce `φ`.

Use `Matrix.IsHermitian.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.map_apply]`. Rewrite using `[← hJe i j, hstar]`. Both sides reduce to the same expression. Establish `hdetφ : ∀ φ : E →+* ℂ, (J.map φ).det ≠ 0`.

Introduce `φ`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(map_ne_zero φ).2 hdet`. Establish `hmapT : ∀ M : Matrix (Fin m) (Fin m) ℂ, M.IsHermitian → M.map (starRingEnd ℂ) = Mᵀ`. Introduce `M hM`.

Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, Matrix.transpose_apply, ← hM.apply j i]`. Both sides reduce to the same expression. Establish `hid : ∀ (N : Matrix (Fin m) (Fin m) ℂ) (z : Fin m → ℂ), star z ⬝ᵥ (N.map (starRingEnd ℂ) *ᵥ z) = starRingEnd ℂ (z ⬝ᵥ (N *ᵥ star z))`. Introduce `N z`.

Simplify using `[dotProduct, mulVec, map_sum, map_mul]`. Use `choose H0 hH0 using fun φ : E →+* ℂ => successive_vector_majorant m (J.map φ) (hherm φ) (hdetφ φ)`. Set `ι` to `Fintype.equivFin (E →+* ℂ)`. Use `⟨fun φ => if ι φ < ι (ComplexEmbedding.conjugate φ) then H0 φ else (H0 (ComplexEmbedding.conjugate φ)).map (starRingEnd ℂ), ?_⟩` and prove the remaining obligations. Introduce `φ`.

Establish `hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ` using `star_star φ`. Distinguish the cases in `hp : ι φ < ι (ComplexEmbedding.conjugate φ)`. Establish `hp' : ¬ ι (ComplexEmbedding.conjugate φ) < ι φ` using `lt_asymm hp`. Simplify using `only [if_pos hp]`. Use `⟨(hH0 φ).1, (hH0 φ).2.1, (hH0 φ).2.2, ?_⟩` and prove the remaining obligations.

Rewrite using `[hcc, if_neg hp']`. Use `set ψ := ComplexEmbedding.conjugate φ with hψ`. Establish `hψφ : ι ψ < ι (ComplexEmbedding.conjugate ψ)`. Rewrite using `[hψ, hcc]`. Use `lt_of_le_of_ne (not_lt.1 hp) fun h => hne φ (ι.injective h.symm ▸ rfl)` and prove the remaining obligations.

Establish `hJφ : J.map φ = (J.map ψ).map (starRingEnd ℂ)`. Use extensionality with `i j`. Simplify using `[hψ, ComplexEmbedding.conjugate_coe_eq]`. Establish `hM` using `hH0 ψ`. Simplify using `only [if_neg hp, if_pos hψφ, ← hψ]`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hmapT _ hM.1.1]`. Conclude with `hM.1.transpose`. Establish `hdc : ∀ N : Matrix (Fin m) (Fin m) ℂ, (N.map (starRingEnd ℂ)).det = starRingEnd ℂ N.det` using `fun N => by`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`.

Rewrite using `[hmapT _ hM.1.1, Matrix.det_transpose, hM.2.1, hJφ, hdc, Complex.norm_conj]`. Introduce `z`. Establish `h1` using `hM.2.2 (star z)`. Rewrite `h1` using `[star_star]`. Rewrite using `[hJφ, hid, hid, Complex.norm_conj, Complex.conj_re]`.

Conclude with `h1`. Rewrite using `[Matrix.map_map]`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem successive_vector_majorant_e : SvMajE := by
  intro F E _ _ _ _ _ _ hCM m J hJ hdet
  have hstar : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a) := hCM.cmUnram.2.1
  have hTC : NumberField.IsTotallyComplex E := hCM.cmUnram.1
  have hne : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := by
    intro φ h
    have hc := hTC.isComplex (InfinitePlace.mk φ)
    rw [InfinitePlace.isComplex_mk_iff] at hc
    exact hc (ComplexEmbedding.isReal_iff.2 h)
  have hJe : ∀ i j, star (J j i) = J i j := by
    intro i j
    have := congrFun (congrFun hJ i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  have hherm : ∀ φ : E →+* ℂ, (J.map φ).IsHermitian := by
    intro φ
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.map_apply]
    rw [← hJe i j, hstar]
    rfl
  have hdetφ : ∀ φ : E →+* ℂ, (J.map φ).det ≠ 0 := by
    intro φ
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero φ).2 hdet
  have hmapT : ∀ M : Matrix (Fin m) (Fin m) ℂ, M.IsHermitian → M.map (starRingEnd ℂ) = Mᵀ := by
    intro M hM
    ext i j
    rw [Matrix.map_apply, Matrix.transpose_apply, ← hM.apply j i]
    rfl
  have hid : ∀ (N : Matrix (Fin m) (Fin m) ℂ) (z : Fin m → ℂ),
      star z ⬝ᵥ (N.map (starRingEnd ℂ) *ᵥ z) = starRingEnd ℂ (z ⬝ᵥ (N *ᵥ star z)) := by
    intro N z
    simp [dotProduct, mulVec, map_sum, map_mul]
  choose H0 hH0 using fun φ : E →+* ℂ => successive_vector_majorant m (J.map φ) (hherm φ) (hdetφ φ)
  let ι := Fintype.equivFin (E →+* ℂ)
  refine ⟨fun φ => if ι φ < ι (ComplexEmbedding.conjugate φ) then H0 φ
    else (H0 (ComplexEmbedding.conjugate φ)).map (starRingEnd ℂ), ?_⟩
  intro φ
  have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := star_star φ
  by_cases hp : ι φ < ι (ComplexEmbedding.conjugate φ)
  · have hp' : ¬ ι (ComplexEmbedding.conjugate φ) < ι φ := lt_asymm hp
    simp only [if_pos hp]
    refine ⟨(hH0 φ).1, (hH0 φ).2.1, (hH0 φ).2.2, ?_⟩
    rw [hcc, if_neg hp']
  · set ψ := ComplexEmbedding.conjugate φ with hψ
    have hψφ : ι ψ < ι (ComplexEmbedding.conjugate ψ) := by
      rw [hψ, hcc]
      refine lt_of_le_of_ne (not_lt.1 hp) fun h => hne φ (ι.injective h.symm ▸ rfl)
    have hJφ : J.map φ = (J.map ψ).map (starRingEnd ℂ) := by
      ext i j
      simp [hψ, ComplexEmbedding.conjugate_coe_eq]
    have hM := hH0 ψ
    simp only [if_neg hp, if_pos hψφ, ← hψ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hmapT _ hM.1.1]
      exact hM.1.transpose
    · have hdc : ∀ N : Matrix (Fin m) (Fin m) ℂ,
          (N.map (starRingEnd ℂ)).det = starRingEnd ℂ N.det := fun N => by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      rw [hmapT _ hM.1.1, Matrix.det_transpose, hM.2.1, hJφ, hdc, Complex.norm_conj]
    · intro z
      have h1 := hM.2.2 (star z)
      rw [star_star] at h1
      rw [hJφ, hid, hid, Complex.norm_conj, Complex.conj_re]
      exact h1
    · rw [Matrix.map_map]
      ext i j
      simp

end PIW.AdelClassFin
