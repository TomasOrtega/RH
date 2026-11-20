import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointsIntegralAlmostAll
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPow
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TraceGram

/- English proof (translation)
Use `set L := AlgebraicClosure K`. Use `set f : K →+* L := algebraMap K L`. Use `set M : Matrix (Fin n) (Fin n) L := g.map f`. Establish `hMc : M.charpoly = g.charpoly.map f` using `Matrix.charpoly_map g f`. Establish `hnd : M.charpoly.roots.Nodup`.

Rewrite using `[hMc]`. Conclude with `nodup_roots (hg.map)`. Establish `hcard : M.charpoly.roots.toFinset.card = n`. Rewrite using `[Multiset.toFinset_card_of_nodup hnd, GlobalTheory.CharpolyPow.card_roots_charpoly]`. Use `set s := M.charpoly.roots.toFinset`.

Set `e : Fin n ≃ s` to `(Fin.castOrderIso hcard.symm).toEquiv.trans s.equivFin.symm`. Set `v : Fin n → L` to `fun i => (e i : L)`. Establish `hv : Function.Injective v` using `fun a b h => e.injective (Subtype.ext h)`. Establish `hsum : ∀ φ : L → L, (M.charpoly.roots.map φ).sum = ∑ i, φ (v i)`. Introduce `φ`.

Establish `: M.charpoly.roots = s.val`. Simplify using `[s, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]`. Rewrite using `[this, ← Finset.sum_eq_multiset_sum, ← Finset.sum_coe_sort s]`. Conclude with `(Fintype.sum_equiv e _ _ (fun _ => rfl)).symm`. Establish `htr : ∀ m : ℕ, f (g ^ m).trace = ∑ i, v i ^ m`.

Introduce `m`. Establish `h1 : f (g ^ m).trace = (M ^ m).trace`. Establish `hp : M ^ m = (g ^ m).map f` using `by simp [M, Matrix.map_pow]`. Rewrite using `[hp]`. Simplify using `[Matrix.trace, Matrix.map_apply, map_sum]`.

Rewrite using `[h1, Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow, hsum]`. Establish `hG : (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).map f = (vandermonde v)ᵀ * vandermonde v`. Use extensionality with `i j`. Rewrite using `[vandermonde_transpose_mul_vandermonde, Matrix.map_apply, Matrix.of_apply, htr]`. Introduce `h0`.

Establish `hd` using `RingHom.map_det f (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace)`. Rewrite `hd` using `[h0, map_zero]`. Establish `h2 : ((vandermonde v)ᵀ * vandermonde v).det = 0`. Rewrite using `[← hG]`. Conclude with `hd.symm`.

Rewrite `h2` using `[det_mul, det_transpose, mul_self_eq_zero]`. Conclude with `det_vandermonde_ne_zero_iff.mpr hv h2`.
-/
theorem det_trace_pow_gram_ne_zero {K : Type} [Field K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (hg : g.charpoly.Separable) :
    (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det ≠ 0 := by
  set L := AlgebraicClosure K
  set f : K →+* L := algebraMap K L
  set M : Matrix (Fin n) (Fin n) L := g.map f
  have hMc : M.charpoly = g.charpoly.map f := Matrix.charpoly_map g f
  have hnd : M.charpoly.roots.Nodup := by
    rw [hMc]; exact nodup_roots (hg.map)
  have hcard : M.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, GlobalTheory.CharpolyPow.card_roots_charpoly]
  set s := M.charpoly.roots.toFinset
  let e : Fin n ≃ s := (Fin.castOrderIso hcard.symm).toEquiv.trans s.equivFin.symm
  let v : Fin n → L := fun i => (e i : L)
  have hv : Function.Injective v := fun a b h => e.injective (Subtype.ext h)
  have hsum : ∀ φ : L → L, (M.charpoly.roots.map φ).sum = ∑ i, φ (v i) := by
    intro φ
    have : M.charpoly.roots = s.val := by
      simp [s, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
    rw [this, ← Finset.sum_eq_multiset_sum, ← Finset.sum_coe_sort s]
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
  have htr : ∀ m : ℕ, f (g ^ m).trace = ∑ i, v i ^ m := by
    intro m
    have h1 : f (g ^ m).trace = (M ^ m).trace := by
      have hp : M ^ m = (g ^ m).map f := by simp [M, Matrix.map_pow]
      rw [hp]; simp [Matrix.trace, Matrix.map_apply, map_sum]
    rw [h1, Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow, hsum]
  have hG : (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).map f
      = (vandermonde v)ᵀ * vandermonde v := by
    ext i j
    rw [vandermonde_transpose_mul_vandermonde, Matrix.map_apply, Matrix.of_apply, htr]
  intro h0
  have hd := RingHom.map_det f (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace)
  rw [h0, map_zero] at hd
  have h2 : ((vandermonde v)ᵀ * vandermonde v).det = 0 := by
    rw [← hG]; exact hd.symm
  rw [det_mul, det_transpose, mul_self_eq_zero] at h2
  exact det_vandermonde_ne_zero_iff.mpr hv h2

end GlobalTheory.TraceGram
