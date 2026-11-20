import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory.RegEigen

/- English proof (translation)
Introduce `C _ O _ _ R Λ _ _ _ n b φ τ hτ`. Use `set ψ : R →+* C := (algebraMap O C).comp φ with hψ`. Set `f : (Fin n → C) → Λ → C` to `fun w x => ∑ i, ψ (b.repr x i) * w i`. Establish `f_add : ∀ w x y, f w (x + y) = f w x + f w y`. Introduce `w x y`.

Simplify using `[f, map_add, add_mul, Finset.sum_add_distrib]`. Establish `f_smul : ∀ w (r : R) x, f w (r • x) = ψ r * f w x`. Introduce `w r x`. Simplify using `[f, map_mul, Finset.mul_sum, mul_assoc]`. Establish `f_basis : ∀ w j, f w (b j) = w j`.

Introduce `w j`. Simplify using `[f, Finsupp.single_apply]`. Establish `f_sum : ∀ w (g : Fin n → Λ), f w (∑ i, g i) = ∑ i, f w (g i)`. Introduce `w g`. Conclude with `map_sum (AddMonoidHom.mk' (f w) (f_add w)) g Finset.univ`.

Establish `mem : ∀ w, w ∈ eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ ↔ ∀ a i, f w (a * b i) = algebraMap O C (τ a) * w i`. Introduce `w`. Simplify using `only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, funext_iff]`. Use `forall_congr' fun a => forall_congr' fun i => ?_` and prove the remaining obligations. Simplify using `[f, Matrix.mulVec, dotProduct, Algebra.leftMulMatrix_eq_repr_mul, hψ]`.

Establish `hτ' : ∀ r, τ (algebraMap R Λ r) = φ r` using `fun r => by rw [← hτ]; rfl`. Use `set w0 : Fin n → C := fun i => algebraMap O C (τ (b i)) with hw0`. Establish `f_w0 : ∀ x, f w0 x = algebraMap O C (τ x)`. Introduce `x`. Use `conv_rhs => rw [← b.sum_repr x]`.

Simplify using `[f, hw0, map_sum, Algebra.smul_def, hτ', hψ]`. Establish `f_mul : ∀ w, (∀ a i, f w (a * b i) = algebraMap O C (τ a) * w i) → ∀ a x, f w (a * x) = algebraMap O C (τ a) * f w x`. Introduce `w h a x`. Use `conv_lhs => rw [← b.sum_repr x, Finset.mul_sum]`. Rewrite using `[f_sum]`.

Repeatedly rewrite using `[mul_smul_comm, f_smul, h a]`. Simplify using `only [f, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `cmHalfIntegralGenerator_mem_algebraicClosure : w0 ∈ eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ`.

Rewrite using `[mem]`. Introduce `a i`. Rewrite using `[f_w0]`. Simplify using `[hw0]`. Establish `w0_ne : w0 ≠ 0`.

Introduce `h0`. Use `f_w0 1` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `[f] at this`. Establish `heq : eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ = Submodule.span C {w0}`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `w hw`. Rewrite using `[Submodule.mem_span_singleton]`. Use `⟨f w 1, funext fun i => ?_⟩` and prove the remaining obligations. Establish `h` using `f_mul w ((mem w).1 hw) (b i) 1`.

Rewrite `h` using `[mul_one, f_basis]`. Simplify using `[hw0, h, mul_comm]`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Conclude with `cmHalfIntegralGenerator_mem_algebraicClosure`. Rewrite using `[heq, finrank_span_singleton w0_ne]`.
-/
theorem eig_leftMulMatrix_finrank : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (R Λ : Type) [CommRing R] [CommRing Λ] [Algebra R Λ] (n : ℕ) (b : Module.Basis (Fin n) R Λ) (φ : R →+* O) (τ : Λ →+* O), τ.comp (algebraMap R Λ) = φ → Module.finrank C (eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ) = 1 := by
  intro C _ O _ _ R Λ _ _ _ n b φ τ hτ
  set ψ : R →+* C := (algebraMap O C).comp φ with hψ
  let f : (Fin n → C) → Λ → C := fun w x => ∑ i, ψ (b.repr x i) * w i
  have f_add : ∀ w x y, f w (x + y) = f w x + f w y := by
    intro w x y; simp [f, map_add, add_mul, Finset.sum_add_distrib]
  have f_smul : ∀ w (r : R) x, f w (r • x) = ψ r * f w x := by
    intro w r x; simp [f, map_mul, Finset.mul_sum, mul_assoc]
  have f_basis : ∀ w j, f w (b j) = w j := by
    intro w j; simp [f, Finsupp.single_apply]
  have f_sum : ∀ w (g : Fin n → Λ), f w (∑ i, g i) = ∑ i, f w (g i) := by
    intro w g
    exact map_sum (AddMonoidHom.mk' (f w) (f_add w)) g Finset.univ
  have mem : ∀ w, w ∈ eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ ↔
      ∀ a i, f w (a * b i) = algebraMap O C (τ a) * w i := by
    intro w
    simp only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, funext_iff]
    refine forall_congr' fun a => forall_congr' fun i => ?_
    simp [f, Matrix.mulVec, dotProduct, Algebra.leftMulMatrix_eq_repr_mul, hψ]
  have hτ' : ∀ r, τ (algebraMap R Λ r) = φ r := fun r => by rw [← hτ]; rfl
  set w0 : Fin n → C := fun i => algebraMap O C (τ (b i)) with hw0
  have f_w0 : ∀ x, f w0 x = algebraMap O C (τ x) := by
    intro x
    conv_rhs => rw [← b.sum_repr x]
    simp [f, hw0, map_sum, Algebra.smul_def, hτ', hψ]
  have f_mul : ∀ w, (∀ a i, f w (a * b i) = algebraMap O C (τ a) * w i) →
      ∀ a x, f w (a * x) = algebraMap O C (τ a) * f w x := by
    intro w h a x
    conv_lhs => rw [← b.sum_repr x, Finset.mul_sum]
    rw [f_sum]
    simp_rw [mul_smul_comm, f_smul, h a]
    simp only [f, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have cmHalfIntegralGenerator_mem_algebraicClosure : w0 ∈ eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ := by
    rw [mem]; intro a i; rw [f_w0]; simp [hw0]
  have w0_ne : w0 ≠ 0 := by
    intro h0
    have := f_w0 1
    rw [h0] at this
    simp [f] at this
  have heq : eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ = Submodule.span C {w0} := by
    apply le_antisymm
    · intro w hw
      rw [Submodule.mem_span_singleton]
      refine ⟨f w 1, funext fun i => ?_⟩
      have h := f_mul w ((mem w).1 hw) (b i) 1
      rw [mul_one, f_basis] at h
      simp [hw0, h, mul_comm]
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact cmHalfIntegralGenerator_mem_algebraicClosure
  rw [heq, finrank_span_singleton w0_ne]

end GlobalTheory.RegEigen
