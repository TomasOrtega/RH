import Mathlib

universe u_1 u_2

namespace GlobalTheory.LengthQuotientValuationDet

open Module IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, AddValuation.map_mul, ih]`.
-/
theorem addVal_prod {ι : Type*} (s : Finset ι) (f : ι → R) :
    addVal R (∏ i ∈ s, f i) = ∑ i ∈ s, addVal R (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, AddValuation.map_mul, ih]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `exists_irreducible R`. Take `⟨n, u, rfl⟩` from `eq_unit_mul_pow_irreducible hx hϖ`. Rewrite using `[Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq, length_quotient_pow_maximalIdeal, addVal_def' u hϖ]`.
-/
theorem length_quotient_span_singleton {x : R} (hx : x ≠ 0) :
    Module.length R (R ⧸ Ideal.span ({x} : Set R)) = addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq, length_quotient_pow_maximalIdeal, addVal_def' u hϖ]

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis R M`. Establish `h : Module.finrank R N = Module.finrank R M` using `e.symm.finrank_eq`. Set `a` to `Submodule.smithNormalFormCoeffs b h`. Set `b'` to `Submodule.smithNormalFormTopBasis b h`. Set `ab` to `Submodule.smithNormalFormBotBasis b h`.

Establish `ab_eq` using `Submodule.smithNormalFormBotBasis_def b h`. Set `e' : M ≃ₗ[R] N` to `b'.equiv ab (Equiv.refl _)`. Set `f : M →ₗ[R] M` to `N.subtype ∘ₗ (e' : M →ₗ[R] N)`. Establish `hassoc : Associated (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N))) (LinearMap.det f)` using `LinearMap.associated_det_comp_equiv _ _ _`. Rewrite using `[(addVal_eq_iff_associated _ _).mpr hassoc]`.

Establish `ha : ∀ i, f (b' i) = a i • b' i`. Introduce `i`. Express the relevant statement in the definitionally equal form `((b'.equiv ab (Equiv.refl _)) (b' i) : M) = _`. Rewrite using `[b'.equiv_apply, Equiv.refl_apply]`. Conclude with `ab_eq i`.

Establish `hdet : LinearMap.det f = ∏ i, a i`. Rewrite using `[← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]`. Use `congr 1`. Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq, Finsupp.single_eq_same]`. Rewrite using `[Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]`. Rewrite using `[hdet, addVal_prod, (N.quotientEquivPiSpan b h).length_eq, Module.length_pi_of_fintype]`.

Conclude with `Finset.sum_congr rfl fun i _ => length_quotient_span_singleton (Submodule.smithNormalFormCoeffs_ne_zero b h i)`.
-/
theorem length_quotient_eq_addVal_det {R : Type u_1} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type u_2} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (N : Submodule R M) (e : M ≃ₗ[R] N) :
    Module.length R (M ⧸ N) =
      (addVal R : R → ℕ∞) (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N))) := by
  classical
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R N = Module.finrank R M := e.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[R] M := N.subtype ∘ₗ (e' : M →ₗ[R] N)
  have hassoc : Associated (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N))) (LinearMap.det f) :=
    LinearMap.associated_det_comp_equiv _ _ _
  rw [(addVal_eq_iff_associated _ _).mpr hassoc]
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    change ((b'.equiv ab (Equiv.refl _)) (b' i) : M) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdet : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  rw [hdet, addVal_prod, (N.quotientEquivPiSpan b h).length_eq, Module.length_pi_of_fintype]
  exact Finset.sum_congr rfl fun i _ =>
    length_quotient_span_singleton (Submodule.smithNormalFormCoeffs_ne_zero b h i)

end GlobalTheory.LengthQuotientValuationDet
