import Mathlib
open scoped TensorProduct

namespace GlobalTheory

open MvPolynomial in

/- English proof (translation)
Take `⟨x₀, hx₀⟩` from `hx`. Set `b` to `Module.Free.chooseBasis B A`. Set `M : Matrix (Module.Free.ChooseBasisIndex B A) (Module.Free.ChooseBasisIndex B A) (MvPolynomial (Fin d) B)` to `Matrix.of fun j l => ∑ i, X i * C (Algebra.leftMulMatrix b (y i) j l)`. Establish `heval : ∀ x : Fin d → B, eval x M.det = Algebra.norm B (∑ i, x i • y i)`. Introduce `x`.

Rewrite using `[Algebra.norm_eq_matrix_det b, RingHom.map_det]`. Use `congr 1`. Use extensionality with `j l`. Simplify using `[M, map_sum, Matrix.sum_apply, mul_comm]`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `hinf : ∀ _ : Fin d, (Set.range (algebraMap k B)).Infinite` using `fun _ => Set.infinite_range_of_injective (algebraMap k B).injective`. Establish `hQ : M.det = 0`. Use `funext_set (fun _ => Set.range (algebraMap k B)) hinf fun x hx => ?_` and prove the remaining obligations. Use `choose a ha using fun i => hx i (Set.mem_univ i)`.

Rewrite using `[heval, map_zero, ← hcon a]`. Simplify using `[ha]`. Conclude with `hx₀ (by rw [← heval, hQ, map_zero])`.
-/
theorem exists_field_combination_norm_ne_zero {k B A : Type} [Field k] [Infinite k] [CommRing B]
    [IsDomain B] [Algebra k B] [CommRing A] [Algebra B A] [Module.Free B A] [Module.Finite B A]
    {d : ℕ} (y : Fin d → A) (hx : ∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0) :
    ∃ a : Fin d → k, Algebra.norm B (∑ i, algebraMap k B (a i) • y i) ≠ 0 := by
  classical
  obtain ⟨x₀, hx₀⟩ := hx
  let b := Module.Free.chooseBasis B A
  let M : Matrix (Module.Free.ChooseBasisIndex B A) (Module.Free.ChooseBasisIndex B A)
      (MvPolynomial (Fin d) B) :=
    Matrix.of fun j l => ∑ i, X i * C (Algebra.leftMulMatrix b (y i) j l)
  have heval : ∀ x : Fin d → B, eval x M.det = Algebra.norm B (∑ i, x i • y i) := by
    intro x
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det]
    congr 1
    ext j l
    simp [M, map_sum, Matrix.sum_apply, mul_comm]
  by_contra hcon
  push_neg at hcon
  have hinf : ∀ _ : Fin d, (Set.range (algebraMap k B)).Infinite := fun _ =>
    Set.infinite_range_of_injective (algebraMap k B).injective
  have hQ : M.det = 0 := by
    refine funext_set (fun _ => Set.range (algebraMap k B)) hinf fun x hx => ?_
    choose a ha using fun i => hx i (Set.mem_univ i)
    rw [heval, map_zero, ← hcon a]
    simp [ha]
  exact hx₀ (by rw [← heval, hQ, map_zero])

end GlobalTheory
