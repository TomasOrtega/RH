import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.PerpVecPerpSt

namespace PI.UnitaryGroupMassFormula.FormPartialDerivatives

open ReciprocityTheory.ChartRestriction.G.TB

/- English proof (translation)
Apply the tactic sequence `have hentry : ∀ a', hMat h e e' a' c = h (e' a') (e c) := fun _ => rfl`. Establish `key : ∀ a, ∑ a', (hMat h e e').adjugate a a' * h (e' a') (e c) = if a = c then (hMat h e e').det else 0`. Introduce `a`. Establish `hk` using `congrFun (congrFun (Matrix.adjugate_mul (hMat h e e')) a) c`. Rewrite `hk` using `[Matrix.mul_apply]`.

Simplify using `only [hentry] at hk`. Rewrite using `[hk, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [perpVec, map_sub, map_smul, map_sum, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]`. Establish `hsum : ∑ a, ∑ a', (hMat h e e').adjugate a a' * h g (e a) * h (e' a') (e c) = (hMat h e e').det * h g (e c)`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a' _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Use `_ = (hMat h e e').det * h g (e c) := by`. Simplify using `only [key, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem perpVec_perp (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) (c : Fin p) :
    h (perpVec h e e' g) (e c) = 0 := by
  have hentry : ∀ a', hMat h e e' a' c = h (e' a') (e c) := fun _ => rfl
  have key : ∀ a, ∑ a', (hMat h e e').adjugate a a' * h (e' a') (e c) =
      if a = c then (hMat h e e').det else 0 := by
    intro a
    have hk := congrFun (congrFun (Matrix.adjugate_mul (hMat h e e')) a) c
    rw [Matrix.mul_apply] at hk
    simp only [hentry] at hk
    rw [hk, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  simp only [perpVec, map_sub, map_smul, map_sum, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul]
  have hsum : ∑ a, ∑ a', (hMat h e e').adjugate a a' * h g (e a) * h (e' a') (e c) =
      (hMat h e e').det * h g (e c) := by
    calc ∑ a, ∑ a', (hMat h e e').adjugate a a' * h g (e a) * h (e' a') (e c)
        = ∑ a, h g (e a) * ∑ a', (hMat h e e').adjugate a a' * h (e' a') (e c) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a' _ => ?_
          ring
      _ = (hMat h e e').det * h g (e c) := by
          simp only [key, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
  rw [hsum]
  ring

/- English proof (translation)
Set `MO : Matrix (Fin p) (Fin p) O` to `Matrix.of fun a' a => ⟨h (e' a') (e a), hL _ (he' a') _ (he a)⟩`. Establish `hMap : hMat h e e' = O.subtype.mapMatrix MO`. Use extensionality with `a' a`. Both sides reduce to the same expression. Establish `hdet : (hMat h e e').det ∈ O`.

Rewrite using `[hMap, ← RingHom.map_det]`. Conclude with `(MO.det).2`. Establish `hadj : ∀ a a', (hMat h e e').adjugate a a' ∈ O`. Introduce `a a'`. Rewrite using `[hMap, ← RingHom.map_adjugate]`.

Conclude with `(MO.adjugate a a').2`. Establish `hs : ∀ r ∈ O, ∀ v ∈ L, r • v ∈ L`. Introduce `r hr v hv`. Conclude with `L.smul_mem (⟨r, hr⟩ : O) hv`. Unfold `perpVec`.

Use `L.sub_mem (hs _ hdet _ hg) (L.sum_mem fun a _ => L.sum_mem fun a' _ => ?_)` and prove the remaining obligations. Conclude with `hs _ (O.mul_mem (hadj a a') (hL _ hg _ (he a))) _ (he' a')`.
-/
theorem perpVec_int (R : Type) [CommRing R] (O : Subring R) (V : Type) [AddCommGroup V] [Module R V]
    (p : ℕ) (h : V →ₗ[R] (V → R)) (L : Submodule O V)
    (hL : ∀ u ∈ L, ∀ v ∈ L, h u v ∈ O) (e e' : Fin p → V) (g : V)
    (he : ∀ a, e a ∈ L) (he' : ∀ a, e' a ∈ L) (hg : g ∈ L) : perpVec h e e' g ∈ L := by
  let MO : Matrix (Fin p) (Fin p) O := Matrix.of fun a' a => ⟨h (e' a') (e a), hL _ (he' a') _ (he a)⟩
  have hMap : hMat h e e' = O.subtype.mapMatrix MO := by
    ext a' a
    rfl
  have hdet : (hMat h e e').det ∈ O := by
    rw [hMap, ← RingHom.map_det]
    exact (MO.det).2
  have hadj : ∀ a a', (hMat h e e').adjugate a a' ∈ O := by
    intro a a'
    rw [hMap, ← RingHom.map_adjugate]
    exact (MO.adjugate a a').2
  have hs : ∀ r ∈ O, ∀ v ∈ L, r • v ∈ L := by
    intro r hr v hv
    exact L.smul_mem (⟨r, hr⟩ : O) hv
  unfold perpVec
  refine L.sub_mem (hs _ hdet _ hg) (L.sum_mem fun a _ => L.sum_mem fun a' _ => ?_)
  exact hs _ (O.mul_mem (hadj a a') (hL _ hg _ (he a))) _ (he' a')

/- English proof (translation)
Simplify using `[perpVec, hg]`.
-/
theorem perpVec_of_perp (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) (hg : ∀ a, h g (e a) = 0) :
    perpVec h e e' g = (hMat h e e').det • g := by
  simp [perpVec, hg]

end PI.UnitaryGroupMassFormula.FormPartialDerivatives
