import Formalism.JumpKernelCokernel.Statement

namespace Formalism.KernelCokernelLengths.DeterminantLengthLemmas

open Module

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.sum_insert hi, Ring.ord_mul' O (mem_nonZeroDivisors_of_ne_zero (ha i)), ih]`.
-/
theorem ord_prod {O : Type} [CommRing O] [IsDomain O] {ι : Type} (s : Finset ι) (a : ι → O)
    (ha : ∀ i, a i ≠ 0) :
    Ring.ord O (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord O (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' O (mem_nonZeroDivisors_of_ne_zero (ha i)), ih]

end Formalism.KernelCokernelLengths.DeterminantLengthLemmas

open Module in
/- English proof (translation)
Introduce `O _ _ _ M _ _ _ _ d hdet`. Establish `hinj : Function.Injective d`. Rewrite using `[← LinearMap.ker_eq_bot]`. Assume the negation of the conclusion as `hk`. Conclude with `hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)`.

Set `e : M ≃ₗ[O] LinearMap.range d` to `LinearEquiv.ofInjective d hinj`. Establish `h : finrank O (LinearMap.range d) = finrank O M` using `e.finrank_eq.symm`. Set `b` to `Free.chooseBasis O M`. Set `a` to `Submodule.smithNormalFormCoeffs b h`. Set `b'` to `Submodule.smithNormalFormTopBasis b h`.

Set `ab` to `Submodule.smithNormalFormBotBasis b h`. Establish `hab : ∀ i, (ab i : M) = a i • b' i` using `Submodule.smithNormalFormBotBasis_def b h`. Establish `ha : ∀ i, a i ≠ 0` using `Submodule.smithNormalFormCoeffs_ne_zero b h`. Establish `hL : Module.length O (M ⧸ LinearMap.range d) = ∑ i, Ring.ord O (a i)`. Rewrite using `[((LinearMap.range d).quotientEquivPiSpan b h).length_eq, Module.length_pi_of_fintype]`.

Both sides reduce to the same expression. Set `u : M ≃ₗ[O] LinearMap.range d` to `b'.equiv ab (Equiv.refl _)`. Set `D : M →ₗ[O] M` to `(LinearMap.range d).subtype ∘ₗ u.toLinearMap`. Establish `hD : LinearMap.det D = ∏ i, a i`. Rewrite using `[← LinearMap.det_toMatrix b']`.

Establish `: LinearMap.toMatrix b' b' D = Matrix.diagonal a`. Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply]`. Simplify using `only [D, u, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Basis.equiv_apply, Equiv.refl_apply, Submodule.coe_subtype, hab, map_smul, Basis.repr_self, Finsupp.smul_apply, smul_eq_mul, Matrix.diagonal_apply, Finsupp.single_apply]`. Distinguish the cases in `hij : j = i`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij, Ne.symm hij]`. Rewrite using `[this, Matrix.det_diagonal]`. Establish `hd : d = D ∘ₗ (e.trans u.symm).toLinearMap`.

Use extensionality with `x`. Simplify using `[D, e]`. Establish `hdet' : LinearMap.det d = (∏ i, a i) * LinearMap.det (e.trans u.symm).toLinearMap`. Rewrite using `[congrArg LinearMap.det hd, LinearMap.det_comp, hD]`. Rewrite using `[hL]`.

Express the relevant statement in the definitionally equal form `_ = Ring.ord O (LinearMap.det d)`. Rewrite using `[hdet', Ring.ord_mul_of_isUnit_right (LinearEquiv.isUnit_det' _), Formalism.KernelCokernelLengths.DeterminantLengthLemmas.ord_prod _ _ ha]`.
-/
theorem Formalism.KernelCokernelLengths.determinant_length_formula : Formalism.KernelCokernelLengths.DetLen := by
  intro O _ _ _ M _ _ _ _ d hdet
  classical
  have hinj : Function.Injective d := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  let e : M ≃ₗ[O] LinearMap.range d := LinearEquiv.ofInjective d hinj
  have h : finrank O (LinearMap.range d) = finrank O M := e.finrank_eq.symm
  let b := Free.chooseBasis O M
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have hab : ∀ i, (ab i : M) = a i • b' i := Submodule.smithNormalFormBotBasis_def b h
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b h

  have hL : Module.length O (M ⧸ LinearMap.range d) = ∑ i, Ring.ord O (a i) := by
    rw [((LinearMap.range d).quotientEquivPiSpan b h).length_eq,
      Module.length_pi_of_fintype]
    rfl

  let u : M ≃ₗ[O] LinearMap.range d := b'.equiv ab (Equiv.refl _)
  let D : M →ₗ[O] M := (LinearMap.range d).subtype ∘ₗ u.toLinearMap
  have hD : LinearMap.det D = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b']
    have : LinearMap.toMatrix b' b' D = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply]
      simp only [D, u, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        Basis.equiv_apply, Equiv.refl_apply, Submodule.coe_subtype, hab, map_smul,
        Basis.repr_self, Finsupp.smul_apply, smul_eq_mul, Matrix.diagonal_apply,
        Finsupp.single_apply]
      by_cases hij : j = i
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    rw [this, Matrix.det_diagonal]
  have hd : d = D ∘ₗ (e.trans u.symm).toLinearMap := by
    ext x
    simp [D, e]
  have hdet' : LinearMap.det d = (∏ i, a i) * LinearMap.det (e.trans u.symm).toLinearMap := by
    rw [congrArg LinearMap.det hd, LinearMap.det_comp, hD]
  rw [hL]
  change _ = Ring.ord O (LinearMap.det d)
  rw [hdet', Ring.ord_mul_of_isUnit_right (LinearEquiv.isUnit_det' _),
    Formalism.KernelCokernelLengths.DeterminantLengthLemmas.ord_prod _ _ ha]
