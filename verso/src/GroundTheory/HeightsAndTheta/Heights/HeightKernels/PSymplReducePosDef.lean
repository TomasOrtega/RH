import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplReducePosDef

/- English proof (translation)
Simplify using `[Fintype.sum_sum_type, Fin.sum_univ_succ, symplCons]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_mul_symplCons {n : ℕ} (c : ℝ) (x : Fin n ⊕ Fin n → ℝ)
    (F : Fin (n + 1) ⊕ Fin (n + 1) → ℝ) :
    ∑ p, F p * symplCons c 0 x p =
      F (Sum.inl 0) * c + ∑ q, F (Sum.map Fin.succ Fin.succ q) * x q := by
  simp [Fintype.sum_sum_type, Fin.sum_univ_succ, symplCons]
  ring

end PSymplReducePosDef

open PSymplReducePosDef in

/- English proof (translation)
Introduce `n H hH`. Establish `hsymm : ∀ i j, H j i = H i j` using `fun i j => by`. Simplify using `using hH.isHermitian.apply i j`. Establish `hpos : 0 < H (Sum.inl 0) (Sum.inl 0)` using `hH.diag_pos`. Use `Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_` and prove the remaining obligations.

Use `Matrix.IsHermitian.ext fun a b => ?_` and prove the remaining obligations. Simplify using `only [symplReduce, star_trivial]`. Rewrite using `[hsymm (Sum.map Fin.succ Fin.succ a), hsymm (Sum.map Fin.succ Fin.succ a) (Sum.inl 0), hsymm (Sum.inl 0) (Sum.map Fin.succ Fin.succ b)]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x hx`.

Simplify using `only [star_trivial]`. Use `set h := H (Sum.inl 0) (Sum.inl 0) with hh`. Use `set S := ∑ b, H (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) * x b with hS`. Use `set Q := ∑ a, (∑ b, H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) * x b) * x a with hQ`. Establish `hT : ∑ a, x a * H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) = S`.

Rewrite using `[hS]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hsymm]`. Expand and normalize the polynomial expressions, which then agree. Establish `hy : symplCons (-(S / h)) 0 x ≠ 0`.

Introduce `hz`. Apply `hx` to reduce the goal to its premises. Use function extensionality and compare the values at `q`. Use `congrFun hz (Sum.map Fin.succ Fin.succ q)` as an intermediate fact. Apply the tactic sequence `cases q <;> simpa [symplCons] using this`.

Establish `h1` using `hH.dotProduct_mulVec_pos hy`. Simplify using `only [star_trivial] at h1`. Establish `hL : symplCons (-(S / h)) 0 x ⬝ᵥ (H *ᵥ symplCons (-(S / h)) 0 x) = (h * (-(S / h)) + S) * (-(S / h)) + (-(S / h)) * S + Q`. Rewrite using `[dotProduct_comm]`. Simplify using `only [dotProduct, mulVec, sum_mul_symplCons]`.

Rewrite using `[← hh, ← hS]`. Simplify using `only [add_mul, Finset.sum_add_distrib]`. Rewrite using `[← hQ]`. Establish `hc : ∑ q, H (Sum.map Fin.succ Fin.succ q) (Sum.inl 0) * (-(S / h)) * x q = (-(S / h)) * S`. Rewrite using `[← hT, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hRa : ∀ a, ∑ b, (H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) - H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) * H (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) / h) * x b = ∑ b, H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) * x b - H (Sum.map Fin.succ F …`.

Introduce `a`. Rewrite using `[hS, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hR : x ⬝ᵥ (symplReduce H *ᵥ x) = Q - S / h * S`.

Simplify using `only [dotProduct, mulVec, symplReduce]`. Rewrite using `[← hh]`. Simplify using `only [hRa, mul_sub, Finset.sum_sub_distrib]`. Rewrite using `[hQ, ← hT, Finset.sum_div, Finset.sum_mul]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hne : h ≠ 0` using `hpos.ne'`.

Establish `key : symplCons (-(S / h)) 0 x ⬝ᵥ (H *ᵥ symplCons (-(S / h)) 0 x) = x ⬝ᵥ (symplReduce H *ᵥ x)`. Rewrite using `[hL, hR]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← key]`.

Conclude with `h1`.
-/
theorem SymplReducePosDef.proof : SymplReducePosDef.Statement := by
  intro n H hH
  have hsymm : ∀ i j, H j i = H i j := fun i j => by
    simpa using hH.isHermitian.apply i j
  have hpos : 0 < H (Sum.inl 0) (Sum.inl 0) := hH.diag_pos
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · refine Matrix.IsHermitian.ext fun a b => ?_
    simp only [symplReduce, star_trivial]
    rw [hsymm (Sum.map Fin.succ Fin.succ a), hsymm (Sum.map Fin.succ Fin.succ a) (Sum.inl 0),
      hsymm (Sum.inl 0) (Sum.map Fin.succ Fin.succ b)]
    ring
  · intro x hx
    simp only [star_trivial]
    set h := H (Sum.inl 0) (Sum.inl 0) with hh
    set S := ∑ b, H (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) * x b with hS
    set Q := ∑ a, (∑ b, H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) * x b) * x a
      with hQ
    have hT : ∑ a, x a * H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) = S := by
      rw [hS]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hsymm]; ring
    have hy : symplCons (-(S / h)) 0 x ≠ 0 := by
      intro hz
      apply hx
      funext q
      have := congrFun hz (Sum.map Fin.succ Fin.succ q)
      cases q <;> simpa [symplCons] using this
    have h1 := hH.dotProduct_mulVec_pos hy
    simp only [star_trivial] at h1
    have hL : symplCons (-(S / h)) 0 x ⬝ᵥ (H *ᵥ symplCons (-(S / h)) 0 x) =
        (h * (-(S / h)) + S) * (-(S / h)) + (-(S / h)) * S + Q := by
      rw [dotProduct_comm]
      simp only [dotProduct, mulVec, sum_mul_symplCons]
      rw [← hh, ← hS]
      simp only [add_mul, Finset.sum_add_distrib]
      rw [← hQ]
      have hc : ∑ q, H (Sum.map Fin.succ Fin.succ q) (Sum.inl 0) * (-(S / h)) * x q =
          (-(S / h)) * S := by
        rw [← hT, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
      rw [hc]
      ring
    have hRa : ∀ a, ∑ b, (H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) -
        H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) * H (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) /
          h) * x b =
        ∑ b, H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) * x b -
          H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) / h * S := by
      intro a
      rw [hS, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    have hR : x ⬝ᵥ (symplReduce H *ᵥ x) = Q - S / h * S := by
      simp only [dotProduct, mulVec, symplReduce]
      rw [← hh]
      simp only [hRa, mul_sub, Finset.sum_sub_distrib]
      rw [hQ, ← hT, Finset.sum_div, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun a _ => ?_
        ring
      · refine Finset.sum_congr rfl fun a _ => ?_
        ring
    have hne : h ≠ 0 := hpos.ne'
    have key : symplCons (-(S / h)) 0 x ⬝ᵥ (H *ᵥ symplCons (-(S / h)) 0 x) =
        x ⬝ᵥ (symplReduce H *ᵥ x) := by
      rw [hL, hR]
      field_simp
      ring
    rw [← key]
    exact h1

end GroundTheory.Heights₂.Heights
