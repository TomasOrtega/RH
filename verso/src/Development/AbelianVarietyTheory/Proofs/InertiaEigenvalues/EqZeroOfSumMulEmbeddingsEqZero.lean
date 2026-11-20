import Mathlib

namespace GlobalTheory

open Module in

/- English proof (translation)
Set `b` to `Module.finBasis F L`. Set `ε : Fin (Module.finrank F L) ≃ (L →ₐ[F] Ω)` to `Fintype.equivOfCardEq (by rw [AlgHom.card F L Ω, Fintype.card_fin])`. Set `E` to `Algebra.embeddingsMatrixReindex F Ω b ε`. Establish `hE : E.det ≠ 0`. Introduce `h0`.

Establish `h1` using `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two F Ω b ε`. Rewrite `h1` using `[show (Algebra.embeddingsMatrixReindex F Ω b ε).det = 0 from h0]`. Simplify using `only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h1`. Conclude with `Algebra.discr_not_zero_of_basis F b ((map_eq_zero _).mp h1)`. Establish `hEa : ∀ i k, E i k = ε k (b i)`.

Introduce `i k`. Simplify using `[E, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]`. Set `v : Fin (Module.finrank F L) → Ω` to `fun i => ∑ t, (b.repr (a t) i) • e t`. Establish `hv : Matrix.vecMul v E = 0`. Use function extensionality and compare the values at `k`.

Rewrite using `[Matrix.vecMul, dotProduct]`. Simplify using `only [Pi.zero_apply, hEa, v]`. Establish `hk` using `h (ε k)`. Rewrite using `[← hk]`. Repeatedly rewrite using `[Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Use `conv_rhs => rw [← b.sum_repr (a t), map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, Algebra.smul_def, Algebra.smul_def]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hv0 : v = 0` using `Matrix.eq_zero_of_vecMul_eq_zero hE hv`. Establish `hc : ∀ t i, b.repr (a t) i = 0`. Introduce `t i`. Use `congrFun hv0 i` as an intermediate fact.

Conclude with `(Fintype.linearIndependent_iff.mp he) (fun t => b.repr (a t) i) this t`. Use function extensionality and compare the values at `t`. Rewrite using `[Pi.zero_apply, ← b.sum_repr (a t)]`. Simplify using `[hc]`.
-/
theorem eq_zero_of_sum_mul_embeddings_eq_zero (F Ω L : Type) [Field F] [CharZero F] [Field Ω]
    [IsAlgClosed Ω] [Algebra F Ω] [Field L] [Algebra F L] [FiniteDimensional F L] (m : ℕ)
    (e : Fin m → Ω) (he : LinearIndependent F e) (_halg : ∀ t, IsAlgebraic F (e t))
    (a : Fin m → L) (h : ∀ σ : L →ₐ[F] Ω, ∑ t, e t * σ (a t) = 0) : a = 0 := by
  classical
  let b := Module.finBasis F L
  let ε : Fin (Module.finrank F L) ≃ (L →ₐ[F] Ω) :=
    Fintype.equivOfCardEq (by rw [AlgHom.card F L Ω, Fintype.card_fin])
  let E := Algebra.embeddingsMatrixReindex F Ω b ε
  have hE : E.det ≠ 0 := by
    intro h0
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two F Ω b ε
    rw [show (Algebra.embeddingsMatrixReindex F Ω b ε).det = 0 from h0] at h1
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h1
    exact Algebra.discr_not_zero_of_basis F b ((map_eq_zero _).mp h1)
  have hEa : ∀ i k, E i k = ε k (b i) := by
    intro i k
    simp [E, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
  let v : Fin (Module.finrank F L) → Ω := fun i => ∑ t, (b.repr (a t) i) • e t
  have hv : Matrix.vecMul v E = 0 := by
    funext k
    rw [Matrix.vecMul, dotProduct]
    simp only [Pi.zero_apply, hEa, v]
    have hk := h (ε k)
    rw [← hk]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    conv_rhs => rw [← b.sum_repr (a t), map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, Algebra.smul_def, Algebra.smul_def]
    ring
  have hv0 : v = 0 := Matrix.eq_zero_of_vecMul_eq_zero hE hv
  have hc : ∀ t i, b.repr (a t) i = 0 := by
    intro t i
    have := congrFun hv0 i
    exact (Fintype.linearIndependent_iff.mp he) (fun t => b.repr (a t) i) this t
  funext t
  rw [Pi.zero_apply, ← b.sum_repr (a t)]
  simp [hc]

end GlobalTheory
