import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.HasSmithOfOne

namespace KStar.Selmer

open Matrix Module

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {n : Type*} [Fintype n] [DecidableEq n]

/- English proof (translation)
Establish `hU' : IsUnit U` using `(Matrix.isUnit_iff_isUnit_det U).2 hU`. Establish `hV' : IsUnit V` using `(Matrix.isUnit_iff_isUnit_det V).2 hV`. Establish `hb : Function.Bijective U.mulVecLin` using `⟨Matrix.mulVec_injective_of_isUnit hU', Matrix.mulVec_surjective_iff_isUnit.2 hU'⟩`. Establish `hs : LinearMap.range V.mulVecLin = ⊤` using `LinearMap.range_eq_top.2 (Matrix.mulVec_surjective_iff_isUnit.2 hV')`. Use `symm`.

Use `LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ (LinearEquiv.ofBijective U.mulVecLin hb) ?_)` and prove the remaining obligations. Rewrite using `[Matrix.mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ hs, Matrix.mulVecLin_mul, LinearMap.range_comp]`. Both sides reduce to the same expression.
-/
private theorem lengthDet_unit_mul {R : Type*} [CommRing R] (U A V : Matrix n n R)
    (hU : IsUnit U.det) (hV : IsUnit V.det) :
    Module.length R (H2 (U * A * V)) = Module.length R (H2 A) := by
  have hU' : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).2 hU
  have hV' : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).2 hV
  have hb : Function.Bijective U.mulVecLin :=
    ⟨Matrix.mulVec_injective_of_isUnit hU', Matrix.mulVec_surjective_iff_isUnit.2 hU'⟩
  have hs : LinearMap.range V.mulVecLin = ⊤ :=
    LinearMap.range_eq_top.2 (Matrix.mulVec_surjective_iff_isUnit.2 hV')
  symm
  refine LinearEquiv.length_eq
    (Submodule.Quotient.equiv _ _ (LinearEquiv.ofBijective U.mulVecLin hb) ?_)
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ hs, Matrix.mulVecLin_mul,
    LinearMap.range_comp]
  rfl

/- English proof (translation)
Establish `h : LinearMap.range (diagonal d).mulVecLin = Submodule.pi Set.univ (fun i => (Ideal.span {d i} : Submodule R R))`. Use extensionality with `x`. Simplify using `only [LinearMap.mem_range, Matrix.mulVecLin_apply, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩ i`.

Conclude with `⟨y i, by rw [Matrix.mulVec_diagonal, mul_comm]⟩`. Introduce `hx choose y hy using hx`. Conclude with `⟨y, funext fun i => by rw [Matrix.mulVec_diagonal, mul_comm, hy]⟩`. Rewrite using `[((Submodule.quotEquivOfEq _ _ h).trans (Submodule.quotientPi _)).length_eq, Module.length_pi_of_fintype]`. Both sides reduce to the same expression.
-/
private theorem lengthDet_diagonal {R : Type*} [CommRing R] (d : n → R) :
    Module.length R (H2 (diagonal d)) = ∑ i, Ring.ord R (d i) := by
  have h : LinearMap.range (diagonal d).mulVecLin =
      Submodule.pi Set.univ (fun i => (Ideal.span {d i} : Submodule R R)) := by
    ext x
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, Submodule.mem_pi, Set.mem_univ,
      true_imp_iff, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩ i
      exact ⟨y i, by rw [Matrix.mulVec_diagonal, mul_comm]⟩
    · intro hx
      choose y hy using hx
      exact ⟨y, funext fun i => by rw [Matrix.mulVec_diagonal, mul_comm, hy]⟩
  rw [((Submodule.quotEquivOfEq _ _ h).trans (Submodule.quotientPi _)).length_eq,
    Module.length_pi_of_fintype]
  rfl

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, IsDiscreteValuationRing.addVal_mul, ih]`.
-/
private theorem lengthDet_addVal_prod {ι : Type*} (s : Finset ι) (d : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, d i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal O (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, IsDiscreteValuationRing.addVal_mul, ih]

/- English proof (translation)
Set `e : n ≃ Fin (Fintype.card n)` to `Fintype.equivFin n`. Take `⟨U, V, d, hU, hV, h, -⟩` from `exists_smith _ (Φ.submatrix e.symm e.symm)`. Establish `hΦ : Φ = U.submatrix e e * diagonal (d ∘ e) * V.submatrix e e`. Rewrite using `[← Matrix.submatrix_diagonal_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← h]`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Establish `hU' : IsUnit (U.submatrix e e).det` using `by rwa [Matrix.det_submatrix_equiv_self]`. Establish `hV' : IsUnit (V.submatrix e e).det` using `by rwa [Matrix.det_submatrix_equiv_self]`. Rewrite using `[hΦ, lengthDet_unit_mul _ _ _ hU' hV', lengthDet_diagonal, Matrix.det_mul, Matrix.det_mul, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.2 hU', IsDiscreteValuationRing.addVal_eq_zero_iff.2 hV', zero_add, add_zer …`. Conclude with `Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal _`.
-/
theorem length_cokernel_eq_addVal_det (Φ : Matrix n n O) :
    Module.length O (H2 Φ) = IsDiscreteValuationRing.addVal O Φ.det := by
  let e : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  obtain ⟨U, V, d, hU, hV, h, -⟩ := exists_smith _ (Φ.submatrix e.symm e.symm)
  have hΦ : Φ = U.submatrix e e * diagonal (d ∘ e) * V.submatrix e e := by
    rw [← Matrix.submatrix_diagonal_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, ← h]
    ext i j
    simp
  have hU' : IsUnit (U.submatrix e e).det := by rwa [Matrix.det_submatrix_equiv_self]
  have hV' : IsUnit (V.submatrix e e).det := by rwa [Matrix.det_submatrix_equiv_self]
  rw [hΦ, lengthDet_unit_mul _ _ _ hU' hV', lengthDet_diagonal, Matrix.det_mul, Matrix.det_mul,
    IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_eq_zero_iff.2 hU',
    IsDiscreteValuationRing.addVal_eq_zero_iff.2 hV', zero_add, add_zero, Matrix.det_diagonal,
    lengthDet_addVal_prod]
  exact Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal _

/- English proof (translation)
Rewrite using `[specLength, length_cokernel_eq_addVal_det, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem specLength_eq_addVal {Λ : Type*} [CommRing Λ] (ψ : Λ →+* O) (Φ : Matrix n n Λ) :
    specLength ψ Φ = IsDiscreteValuationRing.addVal O (ψ Φ.det) := by
  rw [specLength, length_cokernel_eq_addVal_det, RingHom.map_det]
  rfl

end KStar.Selmer
