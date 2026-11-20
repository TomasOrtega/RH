import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IsPureTIff
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Take `⟨hrs, A, hA⟩` from `h`. Set `e : Fin r ⊕ Fin s ≃ Fin m` to `finSumFinEquiv.trans (finCongr hrs)`. Set `A' : Matrix (Fin m) (Fin m) ℂ` to `A.submatrix id e.symm`. Establish `hA' : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm`. Rewrite using `[← hA]`.

Use extensionality with `i j`. Simplify using `[A', Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply]`. Establish `hd : (A'ᵀ * M * A'.map star).det ≠ 0`. Rewrite using `[hA', Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one]`. Conclude with `pow_ne_zero _ (by norm_num)`.

Introduce `h0`. Apply `hd` to reduce the goal to its premises. Rewrite using `[Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul]`.
-/
theorem meas_det_of_hasSig {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin m := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin m) (Fin m) ℂ := A.submatrix id e.symm
  have hA' : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply]
  have hd : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [hA', Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg,
      Matrix.det_one, mul_one]
    exact pow_ne_zero _ (by norm_num)
  intro h0
  apply hd
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul]

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `key : (d.A.J.map (d.B.emb w).1).det ≠ 0`. Break down `d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩` into its components or cases. Conclude with `meas_det_of_hasSig (hA.sig w)`. Establish `h` using `meas_det_of_hasSig (hA.sig w)`.

Rewrite `h` using `[Matrix.det_smul]`. Introduce `h0; exact h (by rw [h0, mul_zero])`. Introduce `h0`. Apply `key` to reduce the goal to its premises. Establish `hm` using `RingHom.map_det (d.B.emb w).1 d.A.J`.

Rewrite `hm` using `[RingHom.mapMatrix_apply, h0, map_zero]`. Conclude with `hm.symm`.
-/
theorem meas_detA (d : SD σ) : d.A.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have key : (d.A.J.map (d.B.emb w).1).det ≠ 0 := by
    rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact meas_det_of_hasSig (hA.sig w)
    · have h := meas_det_of_hasSig (hA.sig w)
      rw [Matrix.det_smul] at h
      intro h0; exact h (by rw [h0, mul_zero])
  intro h0
  apply key
  have hm := RingHom.map_det (d.B.emb w).1 d.A.J
  rw [RingHom.mapMatrix_apply, h0, map_zero] at hm
  exact hm.symm

/- English proof (translation)
Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Jd, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]`. Conclude with `hh j i`. Rewrite using `[Jd, Matrix.det_transpose, Matrix.det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ hη) (meas_detA d)`.
-/
theorem meas_hermND' (d : SD σ) {η : E} (hη : η ≠ 0) (hh : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (Jd d η) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Jd, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    exact hh j i
  · rw [Jd, Matrix.det_transpose, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hη) (meas_detA d)

end PositivityTheory.SiegelWeilFormula.KWhit

end
