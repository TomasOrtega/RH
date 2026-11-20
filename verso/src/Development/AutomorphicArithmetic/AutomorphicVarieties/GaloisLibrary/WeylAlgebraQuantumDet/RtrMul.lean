import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop

open Matrix UpperTheory.V.Weyl

/- English proof (translation)
Introduce `n`. Prove the components needed by the constructor for the conclusion. Introduce `f`. Establish `e : (rtr (1 : Matrix (Fin n) (Fin n) ℂ) : Pol n →ₐ[ℂ] Pol n) = AlgHom.id ℂ (Pol n)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises.

Introduce and unpack `⟨i, j⟩`. Simplify using `[rtr, Matrix.one_apply, mul_ite, Finset.sum_ite_eq']`. Rewrite using `[e]`. Both sides reduce to the same expression. Introduce `g h f`.

Establish `e : (rtr (g * h) : Pol n →ₐ[ℂ] Pol n) = (rtr g).comp (rtr h)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨i, j⟩`. Rewrite using `[AlgHom.comp_apply]`. Simplify using `only [rtr, MvPolynomial.aeval_X, map_sum]`.

Establish `hx : ∀ x, (MvPolynomial.aeval (fun ij : Fin n × Fin n => ∑ k, MvPolynomial.X (ij.1, k) * MvPolynomial.C (g k ij.2)) : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (MvPolynomial.X (i, x) * MvPolynomial.C (h x j)) = ∑ k, MvPolynomial.X (i, k) * MvPolynomial. …`. Introduce `x`. Rewrite using `[map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Finset.sum_mul]`. Simplify using `only [mul_assoc, ← map_mul]`. Simplify using `only [hx, Matrix.mul_apply, map_sum, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Weyl.rtrMul :
    ∀ (n : ℕ), (∀ f : Pol n, rtr 1 f = f) ∧ ∀ (g h : Matrix (Fin n) (Fin n) ℂ) (f : Pol n), rtr (g * h) f = rtr g (rtr h f) := by
  intro n
  constructor
  · intro f
    have e : (rtr (1 : Matrix (Fin n) (Fin n) ℂ) : Pol n →ₐ[ℂ] Pol n) = AlgHom.id ℂ (Pol n) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      simp [rtr, Matrix.one_apply, mul_ite, Finset.sum_ite_eq']
    rw [e]
    rfl
  · intro g h f
    have e : (rtr (g * h) : Pol n →ₐ[ℂ] Pol n) = (rtr g).comp (rtr h) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      rw [AlgHom.comp_apply]
      simp only [rtr, MvPolynomial.aeval_X, map_sum]
      have hx : ∀ x, (MvPolynomial.aeval (fun ij : Fin n × Fin n => ∑ k, MvPolynomial.X (ij.1, k) *
          MvPolynomial.C (g k ij.2)) : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ)
          (MvPolynomial.X (i, x) * MvPolynomial.C (h x j)) =
          ∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (g k x * h x j) := by
        intro x
        rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Finset.sum_mul]
        simp only [mul_assoc, ← map_mul]
      simp only [hx, Matrix.mul_apply, map_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [e]
    rfl
