import ReciprocityTheory.DualLattices.ValuationDetEqOfSpanEq
import ReciprocityTheory.DualLattices.IsUnitDetOfSpanEq
import ReciprocityTheory.DualLattices.VIntCastLtOneOfDvd

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.Up.U3

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {X : Type} [Fintype X] [DecidableEq X]

/- English proof (translation)
Establish `hcol : ∀ j, ∃ w ∈ intFun (C` using `C) R X, (fun x => B x j) = B' *ᵥ w := fun j => (mem_spanCols_iff B' _).1 (hle (Submodule.subset_span ⟨j, rfl⟩))`. Use `choose w hw hBw using hcol`. Establish `hBP : B = B' * Matrix.of fun x j => w j x`. Use extensionality with `x j`. Use `congrFun (hBw j) x` as an intermediate fact.

Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Establish `hle1 : v (Matrix.of fun x j => w j x).det ≤ 1` using `valuation_det_le_one v hv _ fun x j => hw j x`. Rewrite using `[hBP, Matrix.det_mul, map_mul]`. Conclude with `mul_le_of_le_one_right' hle1`.
-/
theorem vdet_le_of_span_le (hv : v.Integers R) {B B' : Matrix X X C}
    (hle : Submodule.span R (Set.range fun j x => B x j) ≤
      Submodule.span R (Set.range fun j x => B' x j)) : v B.det ≤ v B'.det := by
  have hcol : ∀ j, ∃ w ∈ intFun (C := C) R X, (fun x => B x j) = B' *ᵥ w := fun j =>
    (mem_spanCols_iff B' _).1 (hle (Submodule.subset_span ⟨j, rfl⟩))
  choose w hw hBw using hcol
  have hBP : B = B' * Matrix.of fun x j => w j x := by
    ext x j
    have := congrFun (hBw j) x
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hle1 : v (Matrix.of fun x j => w j x).det ≤ 1 :=
    valuation_det_le_one v hv _ fun x j => hw j x
  rw [hBP, Matrix.det_mul, map_mul]
  exact mul_le_of_le_one_right' hle1

/- English proof (translation)
Use `le_antisymm hle ?_` and prove the remaining obligations. Establish `hcol : ∀ j, ∃ w ∈ intFun (C` using `C) R X, (fun x => B x j) = B' *ᵥ w := fun j => (mem_spanCols_iff B' _).1 (hle (Submodule.subset_span ⟨j, rfl⟩))`. Use `choose w hw hBw using hcol`. Use `choose r hr using hw`. Use `set W0 : Matrix X X R := Matrix.of fun x j => r j x with hW0`.

Establish `hBW : B = B' * W0.map (algebraMap R C)`. Use extensionality with `x j`. Rewrite using `[show B x j = (B' *ᵥ w j) x from congrFun (hBw j) x]`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, W0, hr]`. Establish `hne : v B'.det ≠ 0` using `(Valuation.ne_zero_iff v).2 hB'.ne_zero`.

Establish `hW1 : v (algebraMap R C W0.det) = 1`. Establish `h` using `hdet`. Rewrite `h` using `[hBW, Matrix.det_mul, map_mul, det_map_algebraMap]`. Conclude with `mul_left_cancel₀ hne (h.trans (mul_one _).symm)`. Establish `hU : IsUnit W0.det` using `hv.isUnit_of_one' hW1`.

Establish `hB'eq : B' = B * (W0⁻¹).map (algebraMap R C)`. Rewrite using `[hBW, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv W0 hU, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Rewrite using `[SetLike.mem_coe, mem_spanCols_iff]`.

Use `⟨fun k => algebraMap R C (W0⁻¹ k j), fun k => ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Use `conv_lhs => rw [hB'eq]`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`.
-/
theorem span_eq_of_vdet_eq (hv : v.Integers R) {B B' : Matrix X X C} (hB' : IsUnit B'.det)
    (hle : Submodule.span R (Set.range fun j x => B x j) ≤
      Submodule.span R (Set.range fun j x => B' x j)) (hdet : v B.det = v B'.det) :
    Submodule.span R (Set.range fun j x => B x j) =
      Submodule.span R (Set.range fun j x => B' x j) := by
  refine le_antisymm hle ?_
  have hcol : ∀ j, ∃ w ∈ intFun (C := C) R X, (fun x => B x j) = B' *ᵥ w := fun j =>
    (mem_spanCols_iff B' _).1 (hle (Submodule.subset_span ⟨j, rfl⟩))
  choose w hw hBw using hcol
  choose r hr using hw
  set W0 : Matrix X X R := Matrix.of fun x j => r j x with hW0
  have hBW : B = B' * W0.map (algebraMap R C) := by
    ext x j
    rw [show B x j = (B' *ᵥ w j) x from congrFun (hBw j) x]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, W0, hr]
  have hne : v B'.det ≠ 0 := (Valuation.ne_zero_iff v).2 hB'.ne_zero
  have hW1 : v (algebraMap R C W0.det) = 1 := by
    have h := hdet
    rw [hBW, Matrix.det_mul, map_mul, det_map_algebraMap] at h
    exact mul_left_cancel₀ hne (h.trans (mul_one _).symm)
  have hU : IsUnit W0.det := hv.isUnit_of_one' hW1
  have hB'eq : B' = B * (W0⁻¹).map (algebraMap R C) := by
    rw [hBW, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv W0 hU,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, mem_spanCols_iff]
  refine ⟨fun k => algebraMap R C (W0⁻¹ k j), fun k => ⟨_, rfl⟩, ?_⟩
  ext x
  conv_lhs => rw [hB'eq]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

variable {p : ℕ} [hp : Fact p.Prime]

def finZ (p : ℕ) [NeZero p] : Fin p ≃ ZMod p where
  toFun i := ((i : ℕ) : ZMod p)
  invFun a := ⟨a.val, a.val_lt⟩
  left_inv i := Fin.ext (ZMod.val_cast_of_lt i.2)
  right_inv a := ZMod.natCast_zmod_val a

/- English proof (translation)
The claim follows from `ZMod.val_cast_of_lt i.2`.
-/
theorem finZ_val [NeZero p] (i : Fin p) : (finZ p i).val = i := ZMod.val_cast_of_lt i.2

/- English proof (translation)
Rewrite using `[← Finset.sum_range_id, Finset.sum_range (fun i => i)]`. Conclude with `(Fintype.sum_equiv (finZ p) (fun i : Fin p => (i : ℕ)) (fun j => j.val) (fun i => (finZ_val i).symm)).symm`.
-/
theorem sum_val [NeZero p] : ∑ j : ZMod p, j.val = p * (p - 1) / 2 := by
  rw [← Finset.sum_range_id, Finset.sum_range (fun i => i)]
  exact (Fintype.sum_equiv (finZ p) (fun i : Fin p => (i : ℕ)) (fun j => j.val)
    (fun i => (finZ_val i).symm)).symm

/- English proof (translation)
Rewrite using `[← Matrix.det_submatrix_equiv_self (finZ p)]`. Establish `e : (Matrix.of fun a j : ZMod p => ω a ^ j.val).submatrix (finZ p) (finZ p) = Matrix.vandermonde (ω ∘ finZ p)`. Use extensionality with `i j`. Simplify using `[Matrix.vandermonde, finZ_val]`. Rewrite using `[e, Matrix.det_vandermonde, map_prod]`.

Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_prod]`. Use `Finset.prod_eq_one fun j hj => ?_` and prove the remaining obligations. Conclude with `hω _ _ fun h => (ne_of_gt (Finset.mem_Ioi.1 hj)) ((finZ p).injective h)`.
-/
theorem vdet_vandermonde [NeZero p] (ω : ZMod p → C)
    (hω : ∀ a b, a ≠ b → v (ω a - ω b) = 1) :
    v (Matrix.of fun a j : ZMod p => ω a ^ j.val).det = 1 := by
  rw [← Matrix.det_submatrix_equiv_self (finZ p)]
  have e : (Matrix.of fun a j : ZMod p => ω a ^ j.val).submatrix (finZ p) (finZ p) =
      Matrix.vandermonde (ω ∘ finZ p) := by
    ext i j
    simp [Matrix.vandermonde, finZ_val]
  rw [e, Matrix.det_vandermonde, map_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [map_prod]
  refine Finset.prod_eq_one fun j hj => ?_
  exact hω _ _ fun h => (ne_of_gt (Finset.mem_Ioi.1 hj)) ((finZ p).injective h)

/- English proof (translation)
Establish `e : (Matrix.of fun a j : ZMod p => (c * ω a) ^ j.val) = Matrix.of fun a j => c ^ j.val * (Matrix.of fun a j : ZMod p => ω a ^ j.val) a j`. Use extensionality with `a j`. Simplify using `[mul_pow]`. Rewrite using `[e, Matrix.det_mul_row, map_mul, vdet_vandermonde ω hω, mul_one, map_prod]`. Repeatedly rewrite using `[map_pow]`.

Rewrite using `[Finset.prod_pow_eq_pow_sum, sum_val]`.
-/
theorem vdet_pow [NeZero p] (ω : ZMod p → C) (hω : ∀ a b, a ≠ b → v (ω a - ω b) = 1) (c : C) :
    v (Matrix.of fun a j : ZMod p => (c * ω a) ^ j.val).det = v c ^ (p * (p - 1) / 2) := by
  have e : (Matrix.of fun a j : ZMod p => (c * ω a) ^ j.val) =
      Matrix.of fun a j => c ^ j.val * (Matrix.of fun a j : ZMod p => ω a ^ j.val) a j := by
    ext a j
    simp [mul_pow]
  rw [e, Matrix.det_mul_row, map_mul, vdet_vandermonde ω hω, mul_one, map_prod]
  simp_rw [map_pow]
  rw [Finset.prod_pow_eq_pow_sum, sum_val]

end ReciprocityTheory.PGsh.Up.U3
