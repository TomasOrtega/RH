import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

namespace GlobalTheory.Nef.OrdCalc

variable {k F : Type} [Field k] [Field F] [Algebra k F]

/- English proof (translation)
The claim follows from `(map_ne_zero v.1).2 hx`.
-/
theorem vne (v : Place k F) {x : F} (hx : x ≠ 0) : v.1 x ≠ 0 := (map_ne_zero v.1).2 hx

/- English proof (translation)
Unfold `ord`. Rewrite using `[map_mul, WithZero.log_mul (vne v hx) (vne v hy)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ord_mul (v : Place k F) (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    ord v (x * y) = ord v x + ord v y := by
  unfold ord
  rw [map_mul, WithZero.log_mul (vne v hx) (vne v hy)]; ring

/- English proof (translation)
Unfold `ord`. Rewrite using `[map_zpow₀, WithZero.log_zpow]`. Simplify using `[smul_eq_mul]`.
-/
theorem ord_zpow (v : Place k F) (x : F) (m : ℤ) : ord v (x ^ m) = m * ord v x := by
  unfold ord
  rw [map_zpow₀, WithZero.log_zpow]; simp [smul_eq_mul]

/- English proof (translation)
Unfold `ord`. Rewrite using `[← WithZero.log_le_log (vne v hx) one_ne_zero, WithZero.log_one, neg_nonneg]`.
-/
theorem le_one_iff (v : Place k F) (x : F) (hx : x ≠ 0) : v.1 x ≤ 1 ↔ 0 ≤ ord v x := by
  unfold ord
  rw [← WithZero.log_le_log (vne v hx) one_ne_zero, WithZero.log_one, neg_nonneg]

/- English proof (translation)
Unfold `ord`. Rewrite using `[← WithZero.log_le_log (vne v hx) (vne v hy), neg_le_neg_iff]`.
-/
theorem le_iff (v : Place k F) (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    v.1 x ≤ v.1 y ↔ ord v y ≤ ord v x := by
  unfold ord
  rw [← WithZero.log_le_log (vne v hx) (vne v hy), neg_le_neg_iff]

/- English proof (translation)
Establish `h1` using `WithZero.log_le_log (vne v hx) (one_ne_zero (α := WithZero (Multiplicative ℤ)))`. Establish `h2` using `WithZero.log_le_log (one_ne_zero (α := WithZero (Multiplicative ℤ))) (vne v hx)`. Rewrite `h1`, `h2` using `[WithZero.log_one]`. Unfold `ord`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite using `[h, WithZero.log_one]`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `le_antisymm (h1.1 (by omega)) (h2.1 (by omega))`.
-/
theorem eq_one_iff (v : Place k F) (x : F) (hx : x ≠ 0) : v.1 x = 1 ↔ ord v x = 0 := by
  have h1 := WithZero.log_le_log (vne v hx) (one_ne_zero (α := WithZero (Multiplicative ℤ)))
  have h2 := WithZero.log_le_log (one_ne_zero (α := WithZero (Multiplicative ℤ))) (vne v hx)
  rw [WithZero.log_one] at h1 h2
  unfold ord
  constructor
  · intro h; rw [h, WithZero.log_one]; simp
  · intro h
    exact le_antisymm (h1.1 (by omega)) (h2.1 (by omega))

/- English proof (translation)
Take `⟨π, hπ⟩` from `v.2.1 (WithZero.exp (-1 : ℤ))`. Use `⟨π, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hπ` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero hπ.symm`.

Unfold `ord`. Rewrite using `[hπ, WithZero.log_exp]`. Simplify using the standard rewrite rules.
-/
theorem exists_unif (v : Place k F) : ∃ π : F, π ≠ 0 ∧ ord v π = 1 := by
  obtain ⟨π, hπ⟩ := v.2.1 (WithZero.exp (-1 : ℤ))
  refine ⟨π, ?_, ?_⟩
  · rintro rfl; rw [map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
  · unfold ord; rw [hπ, WithZero.log_exp]; simp

/- English proof (translation)
Take `⟨i0, hi0⟩` from `Function.ne_iff.1 hx`. Take `⟨i, -, hi⟩` from `Finset.exists_mem_eq_sup Finset.univ ⟨i0, Finset.mem_univ _⟩ (fun i => v.1 (x i))`. Establish `hle : ∀ j, v.1 (x j) ≤ v.1 (x i)` using `fun j => by`. Rewrite using `[← hi]`. Conclude with `Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ j)`.

Use `⟨i, ?_, hi, ?_, hle⟩` and prove the remaining obligations. Introduce `h0`. Use `hle i0` as an intermediate fact. Rewrite `this` using `[h0, map_zero, le_zero_iff, map_eq_zero]`. Conclude with `hi0 this`.

Unfold `ordVec ord nrm`. Rewrite using `[hi]`.
-/
theorem nrm_max (v : Place k F) (n : ℕ) (x : Fin n → F) (hx : x ≠ 0) :
    ∃ i, x i ≠ 0 ∧ nrm v x = v.1 (x i) ∧ ordVec v x = ord v (x i) ∧ ∀ j, v.1 (x j) ≤ v.1 (x i) := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hx
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨i0, Finset.mem_univ _⟩ (fun i => v.1 (x i))
  have hle : ∀ j, v.1 (x j) ≤ v.1 (x i) := fun j => by
    rw [← hi]; exact Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ j)
  refine ⟨i, ?_, hi, ?_, hle⟩
  · intro h0
    have := hle i0
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi0 this
  · unfold ordVec ord nrm; rw [hi]

/- English proof (translation)
Unfold `nrm`. Apply `le_antisymm` to reduce the goal to its premises. Apply `Finset.sup_le` to reduce the goal to its premises. Introduce `i _`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul]`.

Conclude with `mul_le_mul' le_rfl (Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ i))`. Break down `isEmpty_or_nonempty (Fin n) with h | h` into its components or cases. Simplify using `[Finset.univ_eq_empty]`. Take `⟨i, -, hi⟩` from `Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i => v.1 (x i))`. Rewrite using `[hi]`.

Combine the equalities or inequalities in the displayed calculation. Use `_ ≤ _ := Finset.le_sup (f := fun i => v.1 ((c • x) i)) (Finset.mem_univ i)`.
-/
theorem nrm_smul (v : Place k F) (n : ℕ) (x : Fin n → F) (c : F) :
    nrm v (c • x) = v.1 c * nrm v x := by
  unfold nrm
  apply le_antisymm
  · apply Finset.sup_le; intro i _
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_mul' le_rfl (Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ i))
  · rcases isEmpty_or_nonempty (Fin n) with h | h
    · simp [Finset.univ_eq_empty]
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i => v.1 (x i))
      rw [hi]
      calc v.1 c * v.1 (x i) = v.1 ((c • x) i) := by simp
      _ ≤ _ := Finset.le_sup (f := fun i => v.1 ((c • x) i)) (Finset.mem_univ i)

/- English proof (translation)
Unfold `nrm`. Apply `Finset.sup_le` to reduce the goal to its premises. Introduce `i _`. Simplify using `only [Matrix.mulVec, dotProduct]`. Apply `Valuation.map_sum_le` to reduce the goal to its premises.

Introduce `j _`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `_ = _ := one_mul _`.
-/
theorem nrm_mulVec_le (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) : nrm v (u.mulVec x) ≤ nrm v x := by
  unfold nrm
  apply Finset.sup_le; intro i _
  simp only [Matrix.mulVec, dotProduct]
  apply Valuation.map_sum_le
  intro j _
  rw [map_mul]
  calc v.1 (u i j) * v.1 (x j) ≤ 1 * Finset.univ.sup (fun i => v.1 (x i)) :=
        mul_le_mul' (hu i j) (Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ j))
  _ = _ := one_mul _

/- English proof (translation)
Introduce `i j`. Simplify using `only [Matrix.mul_apply]`. Apply `Valuation.map_sum_le` to reduce the goal to its premises. Introduce `l _`. Rewrite using `[map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Use `_ = 1 := one_mul _`.
-/
theorem mul_int (v : Place k F) (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) (hu' : ∀ i j, v.1 (u' i j) ≤ 1) : ∀ i j, v.1 ((u * u') i j) ≤ 1 := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Valuation.map_sum_le
  intro l _
  rw [map_mul]
  calc v.1 (u i l) * v.1 (u' l j) ≤ 1 * 1 := mul_le_mul' (hu i l) (hu' l j)
  _ = 1 := one_mul _

/- English proof (translation)
Set `M : Matrix (Fin n) (Fin n) v.O` to `fun i j => ⟨u i j, (Valuation.mem_valuationSubring_iff _ _).2 (hu i j)⟩`. Establish `hM : M.map v.O.subtype = u` using `by ext i j; rfl`. Prove the components needed by the constructor for the conclusion. Establish `e : u.det = ((M.det : v.O) : F)`. Rewrite using `[← hM]`.

Conclude with `(RingHom.map_det v.O.subtype M).symm`. Rewrite using `[e]`. Conclude with `(Valuation.mem_valuationSubring_iff _ _).1 (M.det).2`. Introduce `i j`. Establish `e : u.adjugate i j = ((M.adjugate i j : v.O) : F)`.

Rewrite using `[← hM]`. Use `congrFun (congrFun (RingHom.map_adjugate v.O.subtype M) i) j` as an intermediate fact. Conclude with `this.symm`. Rewrite using `[e]`. Conclude with `(Valuation.mem_valuationSubring_iff _ _).1 (M.adjugate i j).2`.
-/
theorem det_adj_int (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) : v.1 u.det ≤ 1 ∧ ∀ i j, v.1 (u.adjugate i j) ≤ 1 := by
  let M : Matrix (Fin n) (Fin n) v.O := fun i j => ⟨u i j, (Valuation.mem_valuationSubring_iff _ _).2 (hu i j)⟩
  have hM : M.map v.O.subtype = u := by ext i j; rfl
  constructor
  · have e : u.det = ((M.det : v.O) : F) := by
      rw [← hM]; exact (RingHom.map_det v.O.subtype M).symm
    rw [e]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (M.det).2
  · intro i j
    have e : u.adjugate i j = ((M.adjugate i j : v.O) : F) := by
      rw [← hM]
      have := congrFun (congrFun (RingHom.map_adjugate v.O.subtype M) i) j
      exact this.symm
    rw [e]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (M.adjugate i j).2

/- English proof (translation)
Use `⟨⟨mul_int v n u u' hu.1 hu'.1, by rw [Matrix.det_mul, map_mul, hu.2, hu'.2, one_mul]⟩, ?_⟩` and prove the remaining obligations. Establish `hd : u.det ≠ 0` using `fun h => by have := hu.2; rw [h, map_zero] at this; exact zero_ne_one this`. Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hu.2, inv_one, one_mul]`. Conclude with `(det_adj_int v n u hu.1).2 i j`.

Rewrite using `[Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, hu.2, inv_one]`.
-/
theorem unimod_mul_inv (v : Place k F) (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F)
    (hu : Unimod v u) (hu' : Unimod v u') : Unimod v (u * u') ∧ Unimod v u⁻¹ := by
  refine ⟨⟨mul_int v n u u' hu.1 hu'.1, by rw [Matrix.det_mul, map_mul, hu.2, hu'.2, one_mul]⟩, ?_⟩
  have hd : u.det ≠ 0 := fun h => by have := hu.2; rw [h, map_zero] at this; exact zero_ne_one this
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hu.2, inv_one, one_mul]
    exact (det_adj_int v n u hu.1).2 i j
  · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, hu.2, inv_one]

/- English proof (translation)
Establish `hd : IsUnit u.det` using `isUnit_iff_ne_zero.2 (fun h => by`. Use `hu.2` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `zero_ne_one this)`. Apply `le_antisymm (nrm_mulVec_le v n u x hu.1)` to reduce the goal to its premises.

Establish `h` using `nrm_mulVec_le v n u⁻¹ (u.mulVec x) (unimod_mul_inv v n u u hu hu).2.1`. Rewrite `h` using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul u hd, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem nrm_unimod (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (hu : Unimod v u) : nrm v (u.mulVec x) = nrm v x := by
  have hd : IsUnit u.det := isUnit_iff_ne_zero.2 (fun h => by
    have := hu.2; rw [h, map_zero] at this; exact zero_ne_one this)
  apply le_antisymm (nrm_mulVec_le v n u x hu.1)
  have h := nrm_mulVec_le v n u⁻¹ (u.mulVec x) (unimod_mul_inv v n u u hu hu).2.1
  rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul u hd, Matrix.one_mulVec] at h

end GlobalTheory.Nef.OrdCalc

open GlobalTheory.Nef.OrdCalc in
/- English proof (translation)
Introduce `k F _ _ _ v`. Conclude with `⟨fun x y hx hy => ord_mul v x y hx hy, fun x _ m => ord_zpow v x m, fun x hx => le_one_iff v x hx, fun x hx => eq_one_iff v x hx, fun x y hx hy => le_iff v x y hx hy, exists_unif v, fun n x hx => nrm_max v n x hx, fun n x c => nrm_smul v n x c, fun n u x hu => nrm_unimod v n u x …`.
-/
theorem GlobalTheory.Nef.ord_calculus : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ v : Place k F, (∀ x y : F, x ≠ 0 → y ≠ 0 → ord v (x * y) = ord v x + ord v y) ∧ (∀ x : F, x ≠ 0 → ∀ m : ℤ, ord v (x ^ m) = m * ord v x) ∧ (∀ x : F, x ≠ 0 → (v.1 x ≤ 1 ↔ 0 ≤ ord v x)) ∧ (∀ x : F, x ≠ 0 → (v.1 x = 1 ↔ ord v x = 0)) ∧ (∀ x y : F, x ≠ 0 → y ≠ 0 → (v.1 x ≤ v.1 y ↔ ord v y ≤ ord v x)) ∧ (∃ π : F, π ≠ 0 ∧ ord v π = 1) ∧ (∀ (n : ℕ) (x : Fin n → F), x ≠ 0 → ∃ i, x i ≠ 0 ∧ nrm v x = v.1 (x i) ∧ ordVec v x = ord v (x i) ∧ ∀ j, v.1 (x j) ≤ v.1 (x i)) ∧ (∀ (n : ℕ) (x : Fin n → F) (c : F), nrm v (c • x) = v.1 c * nrm v x) ∧ (∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F), Unimod v u → nrm v (u.mulVec x) = nrm v x) ∧ (∀ (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F), Unimod v u → Unimod v u' → Unimod v (u * u') ∧ Unimod v u⁻¹) := by
  intro k F _ _ _ v
  exact ⟨fun x y hx hy => ord_mul v x y hx hy, fun x _ m => ord_zpow v x m,
    fun x hx => le_one_iff v x hx, fun x hx => eq_one_iff v x hx, fun x y hx hy => le_iff v x y hx hy,
    exists_unif v, fun n x hx => nrm_max v n x hx, fun n x c => nrm_smul v n x c,
    fun n u x hu => nrm_unimod v n u x hu, fun n u u' hu hu' => unimod_mul_inv v n u u' hu hu'⟩
