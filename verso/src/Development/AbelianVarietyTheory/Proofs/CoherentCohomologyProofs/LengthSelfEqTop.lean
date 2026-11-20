import Mathlib

universe u_1 u_2 u_3 u_4

namespace GlobalTheory.LengthQuotientSpanValuation

open Module

section

variable {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/- English proof (translation)
The claim follows from `Ring.ord_eq_addVal x`.
-/
lemma length_quot_span (x : R) :
    Module.length R (R ⧸ Ideal.span {x}) = IsDiscreteValuationRing.addVal R x :=
  Ring.ord_eq_addVal x

/- English proof (translation)
Rewrite using `[← Ring.ord_zero, Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_zero]`.
-/
lemma length_self_eq_top : Module.length R R = ⊤ := by
  rw [← Ring.ord_zero, Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_zero]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj, IsDiscreteValuationRing.addVal_mul, ih]`.
-/
lemma addVal_prod {ι : Type*} (s : Finset ι) (a : ι → R) :
    IsDiscreteValuationRing.addVal R (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, IsDiscreteValuationRing.addVal_mul, ih]

end

/- English proof (translation)
Use `set A := LinearMap.toMatrix b' b f with hA`. Distinguish the cases in `hf : Function.Injective f`. Use `set N := LinearMap.range f with hN`. Set `e₀ : M' ≃ₗ[R] N` to `LinearEquiv.ofInjective f hf`. Establish `h : Module.finrank R N = Module.finrank R M`.

Rewrite using `[← e₀.finrank_eq, Module.finrank_eq_card_basis b', Module.finrank_eq_card_basis b]`. Set `a` to `Submodule.smithNormalFormCoeffs b h`. Set `bT` to `Submodule.smithNormalFormTopBasis b h`. Set `bB` to `Submodule.smithNormalFormBotBasis b h`. Establish `ab_eq` using `Submodule.smithNormalFormBotBasis_def b h`.

Establish `hlen : Module.length R (M ⧸ N) = IsDiscreteValuationRing.addVal R (∏ i, a i)`. Rewrite using `[(Submodule.quotientEquivPiSpan N b h).length_eq, Module.length_pi_of_fintype, addVal_prod]`. Conclude with `Finset.sum_congr rfl fun i _ => length_quot_span _`. Rewrite using `[hlen, IsDiscreteValuationRing.addVal_eq_iff_associated]`. Set `φ : M' ≃ₗ[R] M` to `b'.equiv b (Equiv.refl ι)`.

Establish `hdetA : A.det = LinearMap.det (N.subtype ∘ₗ ((φ.symm.trans e₀ : M ≃ₗ[R] N) : M →ₗ[R] N))`. Rewrite using `[← LinearMap.det_toMatrix b]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[hA, LinearMap.toMatrix_apply, φ, e₀]`.

Both sides reduce to the same expression. Set `e' : M ≃ₗ[R] N` to `bT.equiv bB (Equiv.refl ι)`. Establish `hg : ∀ i, (N.subtype ∘ₗ (e' : M →ₗ[R] N)) (bT i) = a i • bT i`. Introduce `i`. Simplify using `[e', Basis.equiv_apply, bB, bT, a, ab_eq]`.

Establish `hdiag : LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N)) = ∏ i, a i`. Rewrite using `[← LinearMap.det_toMatrix bT, ← Matrix.det_diagonal]`. Use `congr 1`. Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply, hg, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]`. Rewrite using `[hdetA, ← hdiag]`.

Conclude with `LinearMap.associated_det_comp_equiv _ _ _`. Establish `hdet : A.det = 0`. Rewrite using `[← Matrix.exists_mulVec_eq_zero_iff]`. Choose the witnesses or unpack the hypotheses as in `⟨x, y, hxy, hne⟩ : ∃ x y, f x = f y ∧ x ≠ y := by`. Simplify `hf` using `[Function.Injective]`.

Use `⟨b'.repr (x - y), ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← sub_eq_zero]`. Apply `b'.repr.injective` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Conclude with `Finsupp.ext fun i => by simpa using congrFun h i`. Rewrite using `[hA, LinearMap.toMatrix_mulVec_repr, map_sub, hxy, sub_self, map_zero]`. Both sides reduce to the same expression. Rewrite using `[hdet, IsDiscreteValuationRing.addVal_zero]`.

Take `⟨w, hw0, hw⟩` from `Matrix.exists_vecMul_eq_zero_iff.mpr hdet`. Set `φ : M →ₗ[R] R` to `∑ i, w i • b.coord i`. Establish `hφ : ∀ x, φ x = ∑ i, w i * b.repr x i`. Introduce `x`. Simplify using `[φ]`.

Establish `hle : LinearMap.range f ≤ LinearMap.ker φ`. Rewrite using `[LinearMap.range_le_ker_iff]`. Use `b'.ext fun j => ?_` and prove the remaining obligations. Use `congrFun hw j` as an intermediate fact. Simplify using `only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this`.

Rewrite using `[LinearMap.comp_apply, hφ, LinearMap.zero_apply, ← this]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hA, LinearMap.toMatrix_apply]`. Set `ψ` to `(LinearMap.range f).liftQ φ hle`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, w i ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hw0 (funext h)`. Establish `hmem : (R ∙ w i) ≤ LinearMap.range ψ`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`.

Use `⟨Submodule.Quotient.mk (b i), ?_⟩` and prove the remaining obligations. Simplify using `[ψ, hφ, Finsupp.single_apply]`. Establish `h1 : Module.length R (R ∙ w i) = ⊤`. Rewrite using `[← (LinearEquiv.toSpanNonzeroSingleton R R (w i) hi).length_eq, length_self_eq_top]`. Establish `h2 : Module.length R (R ∙ w i) ≤ Module.length R (LinearMap.range ψ)` using `Module.length_le_of_injective (Submodule.inclusion hmem) (Submodule.inclusion_injective hmem)`.

Establish `h3 : Module.length R (LinearMap.range ψ) ≤ Module.length R (M ⧸ LinearMap.range f)` using `Module.length_le_of_surjective ψ.rangeRestrict (LinearMap.surjective_rangeRestrict ψ)`. Rewrite using `[← top_le_iff, ← h1]`. Conclude with `h2.trans h3`.
-/
theorem main {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {M : Type u_2} [AddCommGroup M] [Module R M] {ι : Type u_3} [Fintype ι] [DecidableEq ι]
    {M' : Type u_4} [AddCommGroup M'] [Module R M'] (b' : Module.Basis ι R M')
    (b : Module.Basis ι R M) (f : M' →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) =
      (IsDiscreteValuationRing.addVal R : R → ℕ∞)
        (Matrix.det ((LinearMap.toMatrix b' b : (M' →ₗ[R] M) → Matrix ι ι R) f)) := by
  set A := LinearMap.toMatrix b' b f with hA
  by_cases hf : Function.Injective f
  · set N := LinearMap.range f with hN
    let e₀ : M' ≃ₗ[R] N := LinearEquiv.ofInjective f hf
    have h : Module.finrank R N = Module.finrank R M := by
      rw [← e₀.finrank_eq, Module.finrank_eq_card_basis b', Module.finrank_eq_card_basis b]
    let a := Submodule.smithNormalFormCoeffs b h
    let bT := Submodule.smithNormalFormTopBasis b h
    let bB := Submodule.smithNormalFormBotBasis b h
    have ab_eq := Submodule.smithNormalFormBotBasis_def b h

    have hlen : Module.length R (M ⧸ N) = IsDiscreteValuationRing.addVal R (∏ i, a i) := by
      rw [(Submodule.quotientEquivPiSpan N b h).length_eq, Module.length_pi_of_fintype,
        addVal_prod]
      exact Finset.sum_congr rfl fun i _ => length_quot_span _
    rw [hlen, IsDiscreteValuationRing.addVal_eq_iff_associated]

    let φ : M' ≃ₗ[R] M := b'.equiv b (Equiv.refl ι)
    have hdetA : A.det = LinearMap.det (N.subtype ∘ₗ ((φ.symm.trans e₀ : M ≃ₗ[R] N) : M →ₗ[R] N)) := by
      rw [← LinearMap.det_toMatrix b]
      congr 1
      ext i j
      simp [hA, LinearMap.toMatrix_apply, φ, e₀]
      rfl
    let e' : M ≃ₗ[R] N := bT.equiv bB (Equiv.refl ι)
    have hg : ∀ i, (N.subtype ∘ₗ (e' : M →ₗ[R] N)) (bT i) = a i • bT i := by
      intro i
      simp [e', Basis.equiv_apply, bB, bT, a, ab_eq]
    have hdiag : LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N)) = ∏ i, a i := by
      rw [← LinearMap.det_toMatrix bT, ← Matrix.det_diagonal]
      congr 1
      ext i j
      rw [LinearMap.toMatrix_apply, hg, map_smul, Basis.repr_self, Finsupp.smul_single,
        smul_eq_mul, mul_one]
      by_cases hij : i = j
      · subst hij; simp
      · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
    rw [hdetA, ← hdiag]
    exact LinearMap.associated_det_comp_equiv _ _ _
  · have hdet : A.det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      obtain ⟨x, y, hxy, hne⟩ : ∃ x y, f x = f y ∧ x ≠ y := by
        simpa [Function.Injective] using hf
      refine ⟨b'.repr (x - y), ?_, ?_⟩
      · intro h
        apply hne
        rw [← sub_eq_zero]
        apply b'.repr.injective
        rw [map_zero]
        exact Finsupp.ext fun i => by simpa using congrFun h i
      · rw [hA, LinearMap.toMatrix_mulVec_repr, map_sub, hxy, sub_self, map_zero]
        rfl
    rw [hdet, IsDiscreteValuationRing.addVal_zero]
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    let φ : M →ₗ[R] R := ∑ i, w i • b.coord i
    have hφ : ∀ x, φ x = ∑ i, w i * b.repr x i := by
      intro x
      simp [φ]
    have hle : LinearMap.range f ≤ LinearMap.ker φ := by
      rw [LinearMap.range_le_ker_iff]
      refine b'.ext fun j => ?_
      have := congrFun hw j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
      rw [LinearMap.comp_apply, hφ, LinearMap.zero_apply, ← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hA, LinearMap.toMatrix_apply]
    let ψ := (LinearMap.range f).liftQ φ hle
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hw0 (funext h)
    have hmem : (R ∙ w i) ≤ LinearMap.range ψ := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      refine ⟨Submodule.Quotient.mk (b i), ?_⟩
      simp [ψ, hφ, Finsupp.single_apply]
    have h1 : Module.length R (R ∙ w i) = ⊤ := by
      rw [← (LinearEquiv.toSpanNonzeroSingleton R R (w i) hi).length_eq, length_self_eq_top]
    have h2 : Module.length R (R ∙ w i) ≤ Module.length R (LinearMap.range ψ) :=
      Module.length_le_of_injective (Submodule.inclusion hmem) (Submodule.inclusion_injective hmem)
    have h3 : Module.length R (LinearMap.range ψ) ≤ Module.length R (M ⧸ LinearMap.range f) :=
      Module.length_le_of_surjective ψ.rangeRestrict (LinearMap.surjective_rangeRestrict ψ)
    rw [← top_le_iff, ← h1]
    exact h2.trans h3

end GlobalTheory.LengthQuotientSpanValuation
