import ReciprocityTheory.DualLattices.TensorSpan

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X : Type} [Fintype X] [DecidableEq X]

/- English proof (translation)
Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`. Use `⟨fun j => algebraMap R C (c j), fun j => ⟨c j, rfl⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]`. Introduce and unpack `⟨w, hw, rfl⟩ choose c hc using hw`. Use `⟨c, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, hc, mul_comm]`.
-/
theorem mem_spanCols_iff (B : Matrix X X C) (f : X → C) :
    f ∈ Submodule.span R (Set.range fun j x => B x j) ↔ ∃ w ∈ intFun (C := C) R X, f = B *ᵥ w := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun j => algebraMap R C (c j), fun j => ⟨c j, rfl⟩, ?_⟩
    ext x
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]
  · rintro ⟨w, hw, rfl⟩
    choose c hc using hw
    refine ⟨c, ?_⟩
    ext x
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, hc, mul_comm]

/- English proof (translation)
Rewrite using `[mem_spanCols_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec]` and apply the resulting hypothesis. Introduce `h`.

Conclude with `⟨_, h, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]⟩`.
-/
theorem mem_spanCols_iff_inv (B : Matrix X X C) (hB : IsUnit B.det) (f : X → C) :
    f ∈ Submodule.span R (Set.range fun j x => B x j) ↔ B⁻¹ *ᵥ f ∈ intFun (C := C) R X := by
  rw [mem_spanCols_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec]
  · intro h
    exact ⟨_, h, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h j`. Take `⟨r, hr⟩` from `h _ (Submodule.subset_span ⟨j, rfl⟩)`. Conclude with `⟨r, by rw [hr]; simp [Matrix.vecMul, dotProduct]⟩`. Introduce `h f hf`.

Take `⟨w, hw, rfl⟩` from `(mem_spanCols_iff B f).1 hf`. Use `choose r hr using h`. Use `choose s hs using hw`. Use `⟨∑ j, r j * s j, ?_⟩` and prove the remaining obligations. Simplify using `only [map_sum, map_mul, hr, hs, Matrix.vecMul, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mem_dualLat_spanCols_iff (B : Matrix X X C) (u : X → C) :
    u ∈ dualLat (Submodule.span R (Set.range fun j x => B x j)) ↔ u ᵥ* B ∈ intFun (C := C) R X := by
  constructor
  · intro h j
    obtain ⟨r, hr⟩ := h _ (Submodule.subset_span ⟨j, rfl⟩)
    exact ⟨r, by rw [hr]; simp [Matrix.vecMul, dotProduct]⟩
  · intro h f hf
    obtain ⟨w, hw, rfl⟩ := (mem_spanCols_iff B f).1 hf
    choose r hr using h
    choose s hs using hw
    refine ⟨∑ j, r j * s j, ?_⟩
    simp only [map_sum, map_mul, hr, hs, Matrix.vecMul, dotProduct, Matrix.mulVec,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/- English proof (translation)
Establish `hBT : IsUnit (B⁻¹)ᵀ.det`. Rewrite using `[Matrix.det_transpose]`. Conclude with `Matrix.isUnit_nonsing_inv_det _ hB`. Use extensionality with `u`. Rewrite using `[mem_dualLat_spanCols_iff, mem_spanCols_iff_inv _ hBT, ← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hB, Matrix.mulVec_transpose]`.
-/
theorem dualLat_spanCols (B : Matrix X X C) (hB : IsUnit B.det) :
    dualLat (Submodule.span R (Set.range fun j x => B x j)) =
      Submodule.span R (Set.range fun j x => (B⁻¹)ᵀ x j) := by
  have hBT : IsUnit (B⁻¹)ᵀ.det := by
    rw [Matrix.det_transpose]
    exact Matrix.isUnit_nonsing_inv_det _ hB
  ext u
  rw [mem_dualLat_spanCols_iff, mem_spanCols_iff_inv _ hBT, ← Matrix.transpose_nonsing_inv,
    Matrix.nonsing_inv_nonsing_inv _ hB, Matrix.mulVec_transpose]

/- English proof (translation)
Establish `hBT : IsUnit (B⁻¹)ᵀ.det`. Rewrite using `[Matrix.det_transpose]`. Conclude with `Matrix.isUnit_nonsing_inv_det _ hB`. Rewrite using `[dualLat_spanCols B hB, dualLat_spanCols _ hBT, ← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hB, Matrix.transpose_transpose]`.
-/
theorem dualLat_dualLat_spanCols (B : Matrix X X C) (hB : IsUnit B.det) :
    dualLat (dualLat (Submodule.span R (Set.range fun j x => B x j))) =
      Submodule.span R (Set.range fun j x => B x j) := by
  have hBT : IsUnit (B⁻¹)ᵀ.det := by
    rw [Matrix.det_transpose]
    exact Matrix.isUnit_nonsing_inv_det _ hB
  rw [dualLat_spanCols B hB, dualLat_spanCols _ hBT, ← Matrix.transpose_nonsing_inv,
    Matrix.nonsing_inv_nonsing_inv _ hB, Matrix.transpose_transpose]

/- English proof (translation)
Use `choose r hr using hP`. Establish `: P = (Matrix.of r).map (algebraMap R C)` using `by ext x j; simp [hr]`. Rewrite using `[this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `hv.map_le_one _`.
-/
theorem valuation_det_le_one (v : Valuation C NNReal) (hv : v.Integers R) (P : Matrix X X C)
    (hP : ∀ x j, ∃ r : R, algebraMap R C r = P x j) : v P.det ≤ 1 := by
  choose r hr using hP
  have : P = (Matrix.of r).map (algebraMap R C) := by ext x j; simp [hr]
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact hv.map_le_one _

/- English proof (translation)
Establish `key : ∀ (B B' : Matrix X X C), Submodule.span R (Set.range fun j x => B x j) ≤ Submodule.span R (Set.range fun j x => B' x j) → v B.det ≤ v B'.det`. Introduce `B B' hle`. Establish `hcol : ∀ j, ∃ w ∈ intFun (C` using `C) R X, (fun x => B x j) = B' *ᵥ w := fun j => (mem_spanCols_iff B' _).1 (hle (Submodule.subset_span ⟨j, rfl⟩))`. Use `choose w hw hBw using hcol`. Establish `hBP : B = B' * Matrix.of fun x j => w j x`.

Use extensionality with `x j`. Use `congrFun (hBw j) x` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Establish `hle1 : v (Matrix.of fun x j => w j x).det ≤ 1` using `valuation_det_le_one v hv _ fun x j => hw j x`. Rewrite using `[hBP, Matrix.det_mul, map_mul]`.

Conclude with `mul_le_of_le_one_right' hle1`. Conclude with `le_antisymm (key B B' h.le) (key B' B h.ge)`.
-/
theorem valuation_det_eq_of_span_eq (v : Valuation C NNReal) (hv : v.Integers R)
    (B B' : Matrix X X C)
    (h : Submodule.span R (Set.range fun j x => B x j) =
      Submodule.span R (Set.range fun j x => B' x j)) : v B.det = v B'.det := by
  have key : ∀ (B B' : Matrix X X C),
      Submodule.span R (Set.range fun j x => B x j) ≤
        Submodule.span R (Set.range fun j x => B' x j) → v B.det ≤ v B'.det := by
    intro B B' hle
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
  exact le_antisymm (key B B' h.le) (key B' B h.ge)

end ReciprocityTheory.PGsh.L2
