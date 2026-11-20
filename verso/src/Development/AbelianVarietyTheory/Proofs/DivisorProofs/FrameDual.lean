import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
open ReciprocityTheory.PGsh GlobalTheory.FGDepth

namespace GlobalTheory.FrameDual

open Matrix Finset

variable {C : Type} [Field C]

def intSubring (v : AddValuation C (WithTop ℝ)) : Subring C where
  carrier := {x | IsIntV v x}
  zero_mem' := by simp [IsIntV]
  one_mem' := by simp [IsIntV]
  add_mem' := by
    intro x y hx hy
    exact le_trans (le_min hx hy) (v.map_add x y)
  mul_mem' := by
    intro x y hx hy
    show 0 ≤ v (x * y)
    rw [v.map_mul]; exact add_nonneg hx hy
  neg_mem' := by
    intro x hx
    show 0 ≤ v (-x)
    rw [v.map_neg]; exact hx

/- English proof (translation)
Set `M' : Matrix (Fin n) (Fin n) (intSubring v)` to `Matrix.of fun a b => ⟨M a b, hM a b⟩`. Establish `hMM : (intSubring v).subtype.mapMatrix M' = M`. Use extensionality with `a b`. Both sides reduce to the same expression. Use `RingHom.map_adjugate (intSubring v).subtype M'` as an intermediate fact.

Rewrite `this` using `[hMM]`. Rewrite using `[← this]`. Conclude with `(M'.adjugate a b).2`.
-/
theorem adjugate_int (v : AddValuation C (WithTop ℝ)) {n : ℕ} (M : Matrix (Fin n) (Fin n) C)
    (hM : ∀ a b, IsIntV v (M a b)) (a b : Fin n) : IsIntV v (M.adjugate a b) := by
  let M' : Matrix (Fin n) (Fin n) (intSubring v) := Matrix.of fun a b => ⟨M a b, hM a b⟩
  have hMM : (intSubring v).subtype.mapMatrix M' = M := by
    ext a b; rfl
  have := RingHom.map_adjugate (intSubring v).subtype M'
  rw [hMM] at this
  rw [← this]
  exact (M'.adjugate a b).2

/- English proof (translation)
Take `⟨hint, r, hr⟩` from `hu`. Use `set M : Matrix (Fin i) (Fin i) C := Matrix.of fun a b => u a (r b) with hMdef`. Establish `hdet0 : M.det ≠ 0`. Introduce `h`. Rewrite `hr` using `[h, v.map_zero]`.

Conclude with `WithTop.top_ne_coe hr`. Establish `hdetU : IsUnit M.det` using `isUnit_iff_ne_zero.mpr hdet0`. Establish `hinvdet : IsIntV v (M.det)⁻¹` using `by show 0 ≤ v (M.det)⁻¹`. Rewrite using `[v.map_inv, hr, neg_zero]`. Establish `hNint : ∀ a b, IsIntV v (M⁻¹ a b)`.

Introduce `a b`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]`. Conclude with `(intSubring v).mul_mem hinvdet (adjugate_int v M (fun a b => hint _ _) a b)`. Use `⟨fun a e => ∑ b, if r b = e then M⁻¹ b a else 0, ?_, ?_⟩` and prove the remaining obligations. Introduce `a e`.

Conclude with `(intSubring v).sum_mem fun b _ => by split_ifs`. Conclude with `hNint b a`. Conclude with `(intSubring v).zero_mem`. Introduce `a a'`. Establish `hMN` using `Matrix.mul_nonsing_inv M hdetU`.

Establish `h1` using `congrFun (congrFun hMN a') a`. Rewrite `h1` using `[Matrix.mul_apply, Matrix.one_apply]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[h, mul_comm]`. Rewrite using `[zero_mul]`. Use `_ = ∑ b, ∑ e, if r b = e then u a' (r b) * M⁻¹ b a else 0 := Finset.sum_comm`.

Use `_ = ∑ b, M a' b * M⁻¹ b a := by`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_ite_eq]`. Simplify using `[hMdef]`. Use `_ = if a = a' then 1 else 0 := by`.

Rewrite using `[h1]`. Conclude with `if_congr eq_comm rfl rfl`.
-/
theorem frameDual (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (i d : ℕ)
    (u : Fin i → Fin d → C) (hu : IsSatFrame v u) :
    ∃ l : Fin i → Fin d → C, (∀ a e, IsIntV v (l a e)) ∧
      ∀ a a', ∑ e, l a e * u a' e = if a = a' then 1 else 0 := by
  obtain ⟨hint, r, hr⟩ := hu
  set M : Matrix (Fin i) (Fin i) C := Matrix.of fun a b => u a (r b) with hMdef
  have hdet0 : M.det ≠ 0 := by
    intro h; rw [h, v.map_zero] at hr; exact WithTop.top_ne_coe hr
  have hdetU : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet0
  have hinvdet : IsIntV v (M.det)⁻¹ := by
    show 0 ≤ v (M.det)⁻¹
    rw [v.map_inv, hr, neg_zero]
  have hNint : ∀ a b, IsIntV v (M⁻¹ a b) := by
    intro a b
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    exact (intSubring v).mul_mem hinvdet (adjugate_int v M (fun a b => hint _ _) a b)
  refine ⟨fun a e => ∑ b, if r b = e then M⁻¹ b a else 0, ?_, ?_⟩
  · intro a e
    exact (intSubring v).sum_mem fun b _ => by
      split_ifs
      · exact hNint b a
      · exact (intSubring v).zero_mem
  · intro a a'
    have hMN := Matrix.mul_nonsing_inv M hdetU
    have h1 := congrFun (congrFun hMN a') a
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    calc ∑ e, (∑ b, if r b = e then M⁻¹ b a else 0) * u a' e
        = ∑ e, ∑ b, if r b = e then u a' (r b) * M⁻¹ b a else 0 := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          split_ifs with h
          · rw [h, mul_comm]
          · rw [zero_mul]
      _ = ∑ b, ∑ e, if r b = e then u a' (r b) * M⁻¹ b a else 0 := Finset.sum_comm
      _ = ∑ b, M a' b * M⁻¹ b a := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_ite_eq]; simp [hMdef]
      _ = if a = a' then 1 else 0 := by
          rw [h1]; exact if_congr eq_comm rfl rfl

end GlobalTheory.FrameDual
