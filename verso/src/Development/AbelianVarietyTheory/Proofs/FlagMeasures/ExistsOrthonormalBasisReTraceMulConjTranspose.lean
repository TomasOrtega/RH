import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

noncomputable def matrixEntriesEuclideanReal (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] PiLp 2 (fun _ : Fin n × Fin n => ℂ) where
  toFun X := WithLp.toLp 2 (fun p => X p.1 p.2)
  invFun v := Matrix.of fun i j => v.ofLp (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `inner ℝ (WithLp.toLp 2 (fun p : Fin n × Fin n => Y p.1 p.2)) (WithLp.toLp 2 (fun p : Fin n × Fin n => X p.1 p.2)) = _`. Rewrite using `[PiLp.inner_apply]`. Simplify using `only [WithLp.ofLp_toLp, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[Complex.inner, mul_comm]`.
-/
theorem inner_matrixEntriesEuclideanReal (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    inner ℝ (matrixEntriesEuclideanReal n Y) (matrixEntriesEuclideanReal n X)
      = ((X * Yᴴ).trace).re := by
  change inner ℝ (WithLp.toLp 2 (fun p : Fin n × Fin n => Y p.1 p.2))
      (WithLp.toLp 2 (fun p : Fin n × Fin n => X p.1 p.2)) = _
  rw [PiLp.inner_apply]
  simp only [WithLp.ofLp_toLp, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.inner, mul_comm]

/- English proof (translation)
Use `set e := matrixEntriesEuclideanReal n`. Use `set V : Submodule ℝ (PiLp 2 (fun _ : Fin n × Fin n => ℂ)) := U.map e.toLinearMap`. Set `b` to `stdOrthonormalBasis ℝ V`. Use `⟨Module.finrank ℝ V, fun i => e.symm (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ)), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i k`.

Establish `h` using `inner_matrixEntriesEuclideanReal n (e.symm (b i)) (e.symm (b k))`. Simplify using `only [e, LinearEquiv.apply_symm_apply] at h`. Rewrite using `[← h, ← Submodule.coe_inner, orthonormal_iff_ite.mp b.orthonormal k i]`. Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hik, Ne.symm hik]`. Establish `hb : LinearIndependent ℝ (fun i => (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ)))` using `b.orthonormal.linearIndependent.map' V.subtype (Submodule.ker_subtype V)`. Conclude with `hb.map' e.symm.toLinearMap e.symm.ker`. Use `symm`.

Establish `hrange : Set.range (fun i => e.symm (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ))) = e.symm.toLinearMap '' (V.subtype '' Set.range b)`. Use extensionality with `x`. Simplify using `[Set.mem_image, Set.mem_range]`. Establish `hspan : Submodule.span ℝ (Set.range b) = ⊤`. Simplify `b.toBasis.span_eq` using `[OrthonormalBasis.coe_toBasis]`.

Rewrite using `[hrange, Submodule.span_image, Submodule.span_image, hspan, Submodule.map_subtype_top]`. Use extensionality with `x`. Simplify using `[V]`.
-/
theorem exists_orthonormal_basis_re_trace_mul_conjTranspose (n : ℕ)
    (U : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ),
      (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ LinearIndependent ℝ E ∧
        U = Submodule.span ℝ (Set.range E) := by
  classical
  set e := matrixEntriesEuclideanReal n
  set V : Submodule ℝ (PiLp 2 (fun _ : Fin n × Fin n => ℂ)) := U.map e.toLinearMap
  let b := stdOrthonormalBasis ℝ V
  refine ⟨Module.finrank ℝ V, fun i => e.symm (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ)), ?_, ?_, ?_⟩
  · intro i k
    have h := inner_matrixEntriesEuclideanReal n (e.symm (b i)) (e.symm (b k))
    simp only [e, LinearEquiv.apply_symm_apply] at h
    rw [← h, ← Submodule.coe_inner, orthonormal_iff_ite.mp b.orthonormal k i]
    by_cases hik : i = k
    · subst hik; simp
    · simp [hik, Ne.symm hik]
  · have hb : LinearIndependent ℝ (fun i => (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ))) :=
      b.orthonormal.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
    exact hb.map' e.symm.toLinearMap e.symm.ker
  · symm
    have hrange : Set.range (fun i => e.symm (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ)))
        = e.symm.toLinearMap '' (V.subtype '' Set.range b) := by
      ext x; simp [Set.mem_image, Set.mem_range]
    have hspan : Submodule.span ℝ (Set.range b) = ⊤ := by
      simpa [OrthonormalBasis.coe_toBasis] using b.toBasis.span_eq
    rw [hrange, Submodule.span_image, Submodule.span_image, hspan, Submodule.map_subtype_top]
    ext x
    simp [V]

end GlobalTheory
