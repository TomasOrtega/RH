import Formalism.MahlerMeasure.StatementD
import Formalism.SmithDeterminants.TruncationChainBoundNonnegExponents

namespace Formalism.GM

open Matrix

/- English proof (translation)
Introduce `p _ n M`. Set `y : (Fin n → ℤ_[p]) →ₗ[ℤ_[p]] (Fin n → ℤ_[p])` to `Matrix.toLin' M`. Take `⟨S⟩` from `Formalism.A.smithExists ℤ_[p] (Fin n → ℤ_[p]) y`. Establish `hfr : Module.finrank ℤ_[p] (Fin n → ℤ_[p]) = n` using `Module.finrank_fin_fun ℤ_[p]`. Set `e : Fin (Module.finrank ℤ_[p] (Fin n → ℤ_[p])) ≃ Fin n` to `finCongr hfr`.

Set `b` to `S.b.reindex e`. Set `b'` to `S.b'.reindex e`. Set `a : Fin n → ℤ_[p]` to `S.a ∘ e.symm`. Establish `hy : ∀ j, M.mulVec (b j) = a j • b' j`. Introduce `j`.

Use `S.hy (e.symm j)` as an intermediate fact. Simplify `this` using `[b, b', a, y, Matrix.toLin'_apply]`. Set `std` to `Pi.basisFun ℤ_[p] (Fin n)`. Set `Q` to `std.toMatrix b`. Set `P` to `std.toMatrix b'`.

Set `V` to `b.toMatrix std`. Establish `hQV : Q * V = 1` using `Module.Basis.toMatrix_mul_toMatrix_flip std b`. Establish `hPW : P * (b'.toMatrix std) = 1` using `Module.Basis.toMatrix_mul_toMatrix_flip std b'`. Establish `hMQ : M * Q = P * Matrix.diagonal a`. Use extensionality with `i j`.

Establish `h1` using `congrFun (hy j) i`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1`. Rewrite using `[Matrix.mul_diagonal, Matrix.mul_apply]`. Simplify using `only [Q, P, std, Module.Basis.toMatrix_apply, Pi.basisFun_repr]`. Rewrite using `[h1]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨P, V, a, Matrix.isUnit_det_of_right_inverse hPW, Matrix.isUnit_det_of_left_inverse hQV, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem smith_form_p_adic_integers : SmithZp := by
  intro p _ n M
  classical
  let y : (Fin n → ℤ_[p]) →ₗ[ℤ_[p]] (Fin n → ℤ_[p]) := Matrix.toLin' M
  obtain ⟨S⟩ := Formalism.A.smithExists ℤ_[p] (Fin n → ℤ_[p]) y
  have hfr : Module.finrank ℤ_[p] (Fin n → ℤ_[p]) = n := Module.finrank_fin_fun ℤ_[p]
  let e : Fin (Module.finrank ℤ_[p] (Fin n → ℤ_[p])) ≃ Fin n := finCongr hfr
  let b := S.b.reindex e
  let b' := S.b'.reindex e
  let a : Fin n → ℤ_[p] := S.a ∘ e.symm
  have hy : ∀ j, M.mulVec (b j) = a j • b' j := by
    intro j
    have := S.hy (e.symm j)
    simpa [b, b', a, y, Matrix.toLin'_apply] using this
  let std := Pi.basisFun ℤ_[p] (Fin n)
  let Q := std.toMatrix b
  let P := std.toMatrix b'
  let V := b.toMatrix std
  have hQV : Q * V = 1 := Module.Basis.toMatrix_mul_toMatrix_flip std b
  have hPW : P * (b'.toMatrix std) = 1 := Module.Basis.toMatrix_mul_toMatrix_flip std b'
  have hMQ : M * Q = P * Matrix.diagonal a := by
    ext i j
    have h1 := congrFun (hy j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Q, P, std, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [h1]; ring
  refine ⟨P, V, a, Matrix.isUnit_det_of_right_inverse hPW, Matrix.isUnit_det_of_left_inverse hQV, ?_⟩
  calc M = M * (Q * V) := by rw [hQV, Matrix.mul_one]
    _ = (M * Q) * V := by rw [Matrix.mul_assoc]
    _ = P * Matrix.diagonal a * V := by rw [hMQ]

end Formalism.GM
