import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

open GlobalTheory.Poinc Matrix

namespace GlobalTheory.Poinc

open Matrix in
/- English proof (translation)
Use `⟨∏ v, (q v).den, Finset.prod_pos fun v _ => (q v).den_pos, fun u => (q u).num * ∏ v ∈ Finset.univ.erase u, ((q v).den : ℤ), fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.mul_prod_erase Finset.univ (fun v => (q v).den) (Finset.mem_univ u)]`. Use `push_cast`. Rewrite using `[← Rat.mul_den_eq_num (q u)]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma exists_nat_mul_rat_eq_int' {s : ℕ} (q : Fin s → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ n : Fin s → ℤ, ∀ u, (N : ℚ) * q u = n u := by
  refine ⟨∏ v, (q v).den, Finset.prod_pos fun v _ => (q v).den_pos,
    fun u => (q u).num * ∏ v ∈ Finset.univ.erase u, ((q v).den : ℤ), fun u => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun v => (q v).den) (Finset.mem_univ u)]
  push_cast
  rw [← Rat.mul_den_eq_num (q u)]
  ring

open Matrix in
/- English proof (translation)
Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma bilinForm_sum_zsmul_eq_sum_mul {s : ℕ} {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X) (y : Fin s → X) (n : Fin s → ℤ) :
    β (∑ u, n u • y u) (∑ v, n v • y v) = ∑ u, ∑ v, n u * n v * β (y u) (y v) := by
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

open Matrix in
/- English proof (translation)
Establish `hdense : DenseRange (Pi.map fun _ : Fin s => (Rat.cast : ℚ → ℝ))` using `DenseRange.piMap fun _ => Rat.denseRange_cast`. Use `hdense.induction_on (p := fun c : Fin s → ℝ => 0 ≤ ∑ u, ∑ v, c u * c v * ((β (y u) (y v) : ℤ) : ℝ)) c (isClosed_le continuous_const (by fun_prop)) fun q => ?_` and prove the remaining obligations. Take `⟨N, hN, n, hn⟩` from `exists_nat_mul_rat_eq_int' q`. Establish `hnR : ∀ u, (N : ℝ) * (q u : ℝ) = (n u : ℝ)` using `fun u => by exact_mod_cast hn u`. Establish `hNpos : (0 : ℝ) < (N : ℝ) ^ 2` using `by positivity`.

Establish `key : (N : ℝ) ^ 2 * ∑ u, ∑ v, (q u : ℝ) * (q v : ℝ) * ((β (y u) (y v) : ℤ) : ℝ) = ((β (∑ u, n u • y u) (∑ v, n v • y v) : ℤ) : ℝ)`. Rewrite using `[bilinForm_sum_zsmul_eq_sum_mul]`. Use `push_cast`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← hnR u, ← hnR v]`. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : (0 : ℝ) ≤ ((β (∑ u, n u • y u) (∑ v, n v • y v) : ℤ) : ℝ)`.

Conclude with `hpos _` after adjusting the coercions. Rewrite `h0` using `[← key]`. Conclude with `(mul_nonneg_iff_of_pos_left hNpos).mp h0`.
-/
private lemma gram_quadratic_real_nonneg {s : ℕ} {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X) (hpos : ∀ x, 0 ≤ β x x) (y : Fin s → X) (c : Fin s → ℝ) :
    0 ≤ ∑ u, ∑ v, c u * c v * ((β (y u) (y v) : ℤ) : ℝ) := by
  have hdense : DenseRange (Pi.map fun _ : Fin s => (Rat.cast : ℚ → ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hdense.induction_on (p := fun c : Fin s → ℝ =>
    0 ≤ ∑ u, ∑ v, c u * c v * ((β (y u) (y v) : ℤ) : ℝ)) c
    (isClosed_le continuous_const (by fun_prop)) fun q => ?_
  obtain ⟨N, hN, n, hn⟩ := exists_nat_mul_rat_eq_int' q
  have hnR : ∀ u, (N : ℝ) * (q u : ℝ) = (n u : ℝ) := fun u => by exact_mod_cast hn u
  have hNpos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have key : (N : ℝ) ^ 2 * ∑ u, ∑ v, (q u : ℝ) * (q v : ℝ) * ((β (y u) (y v) : ℤ) : ℝ) =
      ((β (∑ u, n u • y u) (∑ v, n v • y v) : ℤ) : ℝ) := by
    rw [bilinForm_sum_zsmul_eq_sum_mul]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← hnR u, ← hnR v]
    ring
  have h0 : (0 : ℝ) ≤ ((β (∑ u, n u • y u) (∑ v, n v • y v) : ℤ) : ℝ) := by
    exact_mod_cast hpos _
  rw [← key] at h0
  exact (mul_nonneg_iff_of_pos_left hNpos).mp h0

open Matrix in

/- English proof (translation)
Introduce `s W hW X _ β hsymm hpos y`. Unfold `_root_.GlobalTheory.Poinc.PosW at hW`. Unfold `_root_.GlobalTheory.Poinc.qW`. Take `⟨m, v, hv⟩` from `Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hW.posSemidef`. Use `set S : ℤ := ∑ u, ∑ w, W u w * β (y u) (y w) with hS`.

Establish `hswap : ∑ u, ∑ w, W w u * β (y u) (y w) = S`. Rewrite using `[hS, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[hsymm]`. Establish `htwo : ((2 * S : ℤ) : ℝ) = ∑ u, ∑ w, ((W + W.transpose).map (Int.cast : ℤ → ℝ)) u w * ((β (y u) (y w) : ℤ) : ℝ)`.

Establish `: (2 * S : ℤ) = ∑ u, ∑ w, (W u w + W w u) * β (y u) (y w)`. Simplify using `only [add_mul, Finset.sum_add_distrib, hswap, hS]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use `push_cast`.

Simplify using `[Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply]`. Establish `hnonneg : (0 : ℝ) ≤ ∑ u, ∑ w, ((W + W.transpose).map (Int.cast : ℤ → ℝ)) u w * ((β (y u) (y w) : ℤ) : ℝ)`. Rewrite using `[hv]`. Establish `e : ∀ u w, (∑ i, vecMulVec (v i) (star (v i))) u w * ((β (y u) (y w) : ℤ) : ℝ) = ∑ i, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ)`. Introduce `u w`.

Simplify using `[Matrix.sum_apply, Matrix.vecMulVec_apply, Finset.sum_mul]`. Repeatedly rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hnonneg` using `[← htwo]`. Establish `: (0 : ℝ) ≤ (S : ℝ)` using `by push_cast at hnonneg; linarith`.

Conclude with `this` after adjusting the coercions.
-/
theorem _root_.GlobalTheory.Poinc.qW_nonneg_of_posW : ∀ {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ),
    _root_.GlobalTheory.Poinc.PosW W → ∀ {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ x, 0 ≤ β x x) →
    ∀ y : Fin s → X, 0 ≤ _root_.GlobalTheory.Poinc.qW W β y := by
  intro s W hW X _ β hsymm hpos y
  unfold _root_.GlobalTheory.Poinc.PosW at hW
  unfold _root_.GlobalTheory.Poinc.qW
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hW.posSemidef
  set S : ℤ := ∑ u, ∑ w, W u w * β (y u) (y w) with hS
  have hswap : ∑ u, ∑ w, W w u * β (y u) (y w) = S := by
    rw [hS, Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
    rw [hsymm]
  have htwo : ((2 * S : ℤ) : ℝ) = ∑ u, ∑ w,
      ((W + W.transpose).map (Int.cast : ℤ → ℝ)) u w * ((β (y u) (y w) : ℤ) : ℝ) := by
    have : (2 * S : ℤ) = ∑ u, ∑ w, (W u w + W w u) * β (y u) (y w) := by
      simp only [add_mul, Finset.sum_add_distrib, hswap, hS]
      ring
    rw [this]
    push_cast
    simp [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply]
  have hnonneg : (0 : ℝ) ≤ ∑ u, ∑ w,
      ((W + W.transpose).map (Int.cast : ℤ → ℝ)) u w * ((β (y u) (y w) : ℤ) : ℝ) := by
    rw [hv]
    have e : ∀ u w, (∑ i, vecMulVec (v i) (star (v i))) u w * ((β (y u) (y w) : ℤ) : ℝ) =
        ∑ i, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) := by
      intro u w
      simp [Matrix.sum_apply, Matrix.vecMulVec_apply, Finset.sum_mul]
    simp_rw [e]
    calc (0 : ℝ) ≤ ∑ i, ∑ u, ∑ w, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) :=
          Finset.sum_nonneg fun i _ => gram_quadratic_real_nonneg β hpos y (v i)
      _ = ∑ u, ∑ i, ∑ w, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) := Finset.sum_comm
      _ = ∑ u, ∑ w, ∑ i, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) :=
          Finset.sum_congr rfl fun u _ => Finset.sum_comm
  rw [← htwo] at hnonneg
  have : (0 : ℝ) ≤ (S : ℝ) := by push_cast at hnonneg; linarith
  exact_mod_cast this

end GlobalTheory.Poinc
