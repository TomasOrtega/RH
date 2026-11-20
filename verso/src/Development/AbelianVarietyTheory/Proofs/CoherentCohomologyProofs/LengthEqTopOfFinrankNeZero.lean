import Mathlib

universe u_1 u_2

namespace GlobalTheory.LengthCokernelFinrank

open Module Submodule IsDiscreteValuationRing

variable {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/- English proof (translation)
Establish `h0 : Module.length R (R ⧸ Ideal.span {(0 : R)}) = ⊤`. Establish `h` using `Ring.ord_eq_addVal (0 : R)`. Rewrite `h` using `[addVal_zero]`. Conclude with `h`. Establish `hle` using `Module.length_le_of_surjective (Submodule.mkQ (Ideal.span {(0 : R)})) (Submodule.mkQ_surjective _)`.

Rewrite `hle` using `[h0]`. Conclude with `top_le_iff.mp hle`.
-/
theorem length_self_eq_top : Module.length R R = ⊤ := by
  have h0 : Module.length R (R ⧸ Ideal.span {(0 : R)}) = ⊤ := by
    have h := Ring.ord_eq_addVal (0 : R)
    rw [addVal_zero] at h
    exact h
  have hle := Module.length_le_of_surjective (Submodule.mkQ (Ideal.span {(0 : R)}))
    (Submodule.mkQ_surjective _)
  rw [h0] at hle
  exact top_le_iff.mp hle

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, addVal_mul, ih]`.
-/
theorem addVal_prod {ι : Type*} (s : Finset ι) (a : ι → R) :
    addVal R (∏ i ∈ s, a i) = ∑ i ∈ s, addVal R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, addVal_mul, ih]

variable {M : Type u_2} [AddCommGroup M] [Module R M]

/- English proof (translation)
Establish `hnt : ¬ Module.IsTorsion R M` using `fun ht => h (Module.finrank_eq_zero_iff_isTorsion.mpr ht)`. Establish `hx : ∃ x : M, ∀ a : R, a • x = 0 → a = 0`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Apply `hnt` to reduce the goal to its premises.

Introduce `x`. Take `⟨a, ha, ha0⟩` from `hc x`. Conclude with `⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha0⟩, ha⟩`. Take `⟨x, hx⟩` from `hx`. Establish `hinj : Function.Injective (LinearMap.toSpanSingleton R M x)`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Conclude with `hx a (by simpa using ha)`. Establish `hle` using `Module.length_le_of_injective _ hinj`. Rewrite `hle` using `[length_self_eq_top]`.

Conclude with `top_le_iff.mp hle`.
-/
theorem length_eq_top_of_finrank_ne_zero [Module.Finite R M] (h : finrank R M ≠ 0) :
    Module.length R M = ⊤ := by
  have hnt : ¬ Module.IsTorsion R M := fun ht => h (Module.finrank_eq_zero_iff_isTorsion.mpr ht)
  have hx : ∃ x : M, ∀ a : R, a • x = 0 → a = 0 := by
    by_contra hc
    push Not at hc
    apply hnt
    intro x
    obtain ⟨a, ha, ha0⟩ := hc x
    exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha0⟩, ha⟩
  obtain ⟨x, hx⟩ := hx
  have hinj : Function.Injective (LinearMap.toSpanSingleton R M x) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    exact hx a (by simpa using ha)
  have hle := Module.length_le_of_injective _ hinj
  rw [length_self_eq_top] at hle
  exact top_le_iff.mp hle

/- English proof (translation)
Distinguish the cases in `hk : LinearMap.ker f = ⊥`. Establish `hinj : Function.Injective f` using `LinearMap.ker_eq_bot.mp hk set N := LinearMap.range f with hN`. Set `e : M ≃ₗ[R] N` to `LinearEquiv.ofInjective f hinj`. Set `b` to `Module.Free.chooseBasis R M`. Establish `h : finrank R N = finrank R M` using `e.symm.finrank_eq`.

Set `a` to `smithNormalFormCoeffs b h`. Set `b'` to `smithNormalFormTopBasis b h`. Set `ab` to `smithNormalFormBotBasis b h`. Set `e' : M ≃ₗ[R] N` to `b'.equiv ab (Equiv.refl _)`. Set `g : M →ₗ[R] M` to `N.subtype ∘ₗ (e' : M →ₗ[R] N)`.

Establish `hf : f = N.subtype ∘ₗ (e : M →ₗ[R] N)`. Use extensionality with `x`. Both sides reduce to the same expression. Establish `hassoc : Associated (LinearMap.det f) (LinearMap.det g)`. Use `LinearMap.associated_det_comp_equiv N.subtype e e'` as an intermediate fact.

Rewrite `this` using `[← hf]`. Then use the resulting hypothesis. Establish `hg : ∀ i, g (b' i) = a i • b' i`. Introduce `i`. Establish `: e' (b' i) = ab i` using `by simp [e']`. Express the relevant statement in the definitionally equal form `((e' (b' i) : N) : M) = _`.

Rewrite using `[this]`. Conclude with `smithNormalFormBotBasis_def b h i`. Establish `hmat : LinearMap.toMatrix b' b' g = Matrix.diagonal a`. Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply, hg, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Matrix.diagonal_apply, Finsupp.single_apply]`.

Distinguish the cases in `hij : i = j`. Simplify using `[hij]`. Simplify using `[hij, Ne.symm hij]`. Establish `hdet : LinearMap.det g = ∏ i, a i`. Rewrite using `[← LinearMap.det_toMatrix b', hmat, Matrix.det_diagonal]`.

Rewrite using `[(addVal_eq_iff_associated _ _).mpr hassoc, hdet, addVal_prod, (quotientEquivPiSpan N b h).length_eq, Module.length_pi_of_fintype]`. Conclude with `Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal (a i)`. Rewrite using `[LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk, addVal_zero]`. Apply `length_eq_top_of_finrank_ne_zero` to reduce the goal to its premises. Introduce `h0`.

Establish `h1` using `Submodule.finrank_quotient_add_finrank (LinearMap.range f)`. Establish `h2` using `Submodule.finrank_quotient_add_finrank (LinearMap.ker f)`. Rewrite `h2` using `[(LinearMap.quotKerEquivRange f).finrank_eq]`. Establish `h3 : finrank R (LinearMap.ker f) = 0` using `by omega`. Conclude with `hk (Submodule.finrank_eq_zero.mp h3)`.
-/
theorem length_coker_eq_addVal_det [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by
  classical
  by_cases hk : LinearMap.ker f = ⊥
  · have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hk
    set N := LinearMap.range f with hN
    let e : M ≃ₗ[R] N := LinearEquiv.ofInjective f hinj
    let b := Module.Free.chooseBasis R M
    have h : finrank R N = finrank R M := e.symm.finrank_eq
    let a := smithNormalFormCoeffs b h
    let b' := smithNormalFormTopBasis b h
    let ab := smithNormalFormBotBasis b h
    let e' : M ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
    let g : M →ₗ[R] M := N.subtype ∘ₗ (e' : M →ₗ[R] N)
    have hf : f = N.subtype ∘ₗ (e : M →ₗ[R] N) := by
      ext x
      rfl
    have hassoc : Associated (LinearMap.det f) (LinearMap.det g) := by
      have := LinearMap.associated_det_comp_equiv N.subtype e e'
      rwa [← hf] at this
    have hg : ∀ i, g (b' i) = a i • b' i := by
      intro i
      have : e' (b' i) = ab i := by simp [e']
      change ((e' (b' i) : N) : M) = _
      rw [this]
      exact smithNormalFormBotBasis_def b h i
    have hmat : LinearMap.toMatrix b' b' g = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply, hg, map_smul, Basis.repr_self, Finsupp.smul_single,
        smul_eq_mul, mul_one, Matrix.diagonal_apply, Finsupp.single_apply]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, Ne.symm hij]
    have hdet : LinearMap.det g = ∏ i, a i := by
      rw [← LinearMap.det_toMatrix b', hmat, Matrix.det_diagonal]
    rw [(addVal_eq_iff_associated _ _).mpr hassoc, hdet, addVal_prod,
      (quotientEquivPiSpan N b h).length_eq, Module.length_pi_of_fintype]
    exact Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal (a i)
  · rw [LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk, addVal_zero]
    apply length_eq_top_of_finrank_ne_zero
    intro h0
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
    have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
    rw [(LinearMap.quotKerEquivRange f).finrank_eq] at h2
    have h3 : finrank R (LinearMap.ker f) = 0 := by omega
    exact hk (Submodule.finrank_eq_zero.mp h3)

end GlobalTheory.LengthCokernelFinrank
