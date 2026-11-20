import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SDarb
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.MapCAMul
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.AdelicCoordinatesEvalZeroFormMemAdmissible

set_option linter.unusedSectionVars false

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {m n : ℕ}

def BfE (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) : LinearMap.BilinForm F (Matrix (Fin m) (Fin n) E) :=
  LinearMap.mk₂ F (fun x z => Algebra.trace F E (xᵀ * J * z.map σ).trace)
    (fun x x' z => by simp [Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add])
    (fun c x z => by simp [Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul])
    (fun x z z' => by simp [Matrix.map_add _ (map_add σ), Matrix.mul_add, Matrix.trace_add])
    (fun c x z => by
      have : (c • z).map σ = c • z.map σ := by ext i j; exact σ.toLinearMap.map_smul c (z i j)
      simp [this, Matrix.mul_smul, Matrix.trace_smul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem BfE_apply (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (x z : Matrix (Fin m) (Fin n) E) :
    BfE σ J x z = Algebra.trace F E (xᵀ * J * z.map σ).trace := rfl

/- English proof (translation)
Establish `hdet : IsUnit J.det` using `isUnit_iff_ne_zero.mpr hJ`. Establish `hdetT : IsUnit Jᵀ.det`. Rewrite using `[Matrix.det_transpose]`. Conclude with `hdet`. Establish `htr1 : Algebra.trace F E 1 ≠ 0`.

Rewrite using `[← map_one (algebraMap F E), Algebra.trace_algebraMap]`. Simplify using `only [nsmul_eq_mul, mul_one, ne_eq, Nat.cast_eq_zero]`. Conclude with `Module.finrank_pos.ne'`. Use `⟨fun x hx => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Establish `hy : Jᵀ * x ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Establish `h2` using `congrArg (fun M => (Jᵀ)⁻¹ * M) h0`. Simplify `h2` using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetT]`.

Choose the witnesses or unpack the hypotheses as in `⟨b0, j0, hb⟩ : ∃ b j, (Jᵀ * x) b j ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hy (Matrix.ext h)`. Establish `h1` using `hx ((Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹).map σ)`.

Establish `hσσ : ((Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹).map σ).map σ = Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹`. Use extensionality with `a b`. Simplify using `only [Matrix.map_apply]`. Conclude with `hσ _`. Establish `hswap : (xᵀ * J) j0 b0 = (Jᵀ * x) b0 j0`.

Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Establish `hv : (xᵀ * J * Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹).trace = 1`. Rewrite using `[Matrix.trace_mul_single, hswap, op_smul_eq_mul, mul_inv_cancel₀ hb]`. Rewrite `h1` using `[BfE_apply, hσσ, hv]`.

Conclude with `htr1 h1`. Assume the negation of the conclusion as `hne`. Establish `hw : J * z.map σ ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises.

Establish `hz0 : z.map σ = 0`. Establish `h2` using `congrArg (fun M => J⁻¹ * M) h0`. Simplify `h2` using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet]`. Use extensionality with `a b`. Use `congrFun (congrFun hz0 a) b` as an intermediate fact.

Simplify using `only [Matrix.map_apply, Matrix.zero_apply] at this`. Rewrite using `[Matrix.zero_apply, ← hσ (z a b), this, map_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨a0, b0, hb⟩ : ∃ a b, (J * z.map σ) a b ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hw (Matrix.ext h)`. Establish `h1` using `hz (Matrix.single a0 b0 ((J * z.map σ) a0 b0)⁻¹)`. Establish `hv : ((Matrix.single a0 b0 ((J * z.map σ) a0 b0)⁻¹)ᵀ * J * z.map σ).trace = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.transpose_single, Matrix.trace_single_mul]`. Simplify using `[inv_mul_cancel₀ hb, mul_inv_cancel₀ hb]`.

Rewrite `h1` using `[BfE_apply, hv]`. Conclude with `htr1 h1`.
-/
theorem BfE_nondeg [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (J : Matrix (Fin m) (Fin m) E)
    (hJ : J.det ≠ 0) : (BfE (n := n) σ J).Nondegenerate := by
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ
  have hdetT : IsUnit Jᵀ.det := by
    rw [Matrix.det_transpose]
    exact hdet
  have htr1 : Algebra.trace F E 1 ≠ 0 := by
    rw [← map_one (algebraMap F E), Algebra.trace_algebraMap]
    simp only [nsmul_eq_mul, mul_one, ne_eq, Nat.cast_eq_zero]
    exact Module.finrank_pos.ne'
  refine ⟨fun x hx => ?_, fun z hz => ?_⟩
  · by_contra hne
    have hy : Jᵀ * x ≠ 0 := by
      intro h0
      apply hne
      have h2 := congrArg (fun M => (Jᵀ)⁻¹ * M) h0
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetT] using h2
    obtain ⟨b0, j0, hb⟩ : ∃ b j, (Jᵀ * x) b j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hy (Matrix.ext h)
    have h1 := hx ((Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹).map σ)
    have hσσ : ((Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹).map σ).map σ =
        Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹ := by
      ext a b
      simp only [Matrix.map_apply]
      exact hσ _
    have hswap : (xᵀ * J) j0 b0 = (Jᵀ * x) b0 j0 := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hv : (xᵀ * J * Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹).trace = 1 := by
      rw [Matrix.trace_mul_single, hswap, op_smul_eq_mul, mul_inv_cancel₀ hb]
    rw [BfE_apply, hσσ, hv] at h1
    exact htr1 h1
  · by_contra hne
    have hw : J * z.map σ ≠ 0 := by
      intro h0
      apply hne
      have hz0 : z.map σ = 0 := by
        have h2 := congrArg (fun M => J⁻¹ * M) h0
        simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet] using h2
      ext a b
      have := congrFun (congrFun hz0 a) b
      simp only [Matrix.map_apply, Matrix.zero_apply] at this
      rw [Matrix.zero_apply, ← hσ (z a b), this, map_zero]
    obtain ⟨a0, b0, hb⟩ : ∃ a b, (J * z.map σ) a b ≠ 0 := by
      by_contra h
      push_neg at h
      exact hw (Matrix.ext h)
    have h1 := hz (Matrix.single a0 b0 ((J * z.map σ) a0 b0)⁻¹)
    have hv : ((Matrix.single a0 b0 ((J * z.map σ) a0 b0)⁻¹)ᵀ * J * z.map σ).trace = 1 := by
      rw [Matrix.mul_assoc, Matrix.transpose_single, Matrix.trace_single_mul]
      simp [inv_mul_cancel₀ hb, mul_inv_cancel₀ hb]
    rw [BfE_apply, hv] at h1
    exact htr1 h1

end PositivityTheory.SiegelWeilFormula.Ldexa
