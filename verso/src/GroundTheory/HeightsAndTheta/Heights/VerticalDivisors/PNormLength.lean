import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open Module

noncomputable section

section NormLength

variable {R B : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing B]
  [Algebra R B] [Module.Free R B] [Module.Finite R B]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj, Ring.ord_mul, ih fun i hi => ha i (by simp [hi])]`. Conclude with `mem_nonZeroDivisors_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun i hi => ha i (by simp [hi]))`.
-/
theorem ord_prod {ι : Type*} (s : Finset ι) (a : ι → R) (ha : ∀ i ∈ s, a i ≠ 0) :
    Ring.ord R (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Ring.ord_mul, ih fun i hi => ha i (by simp [hi])]
    exact mem_nonZeroDivisors_of_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun i hi => ha i (by simp [hi]))

/- English proof (translation)
Set `bs` to `Module.Free.chooseBasis R B`. Set `ι` to `Module.Free.ChooseBasisIndex R B`. Set `N : Submodule R B` to `(Ideal.span {b}).restrictScalars R`. Set `m : B →ₗ[R] B` to `Algebra.lmul R B b`. Establish `hm : Function.Injective m` using `hb`.

Establish `hrange : LinearMap.range m = N`. Use extensionality with `x`. Simplify using `only [LinearMap.mem_range, Submodule.restrictScalars_mem, Ideal.mem_span_singleton', N, m]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `⟨y, mul_comm y b⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨y, mul_comm b y⟩`. Set `φ : B ≃ₗ[R] N` to `(LinearEquiv.ofInjective m hm).trans (LinearEquiv.ofEq _ _ hrange)`. Establish `h : Module.finrank R N = Module.finrank R B` using `φ.finrank_eq.symm`.

Set `a` to `Submodule.smithNormalFormCoeffs bs h`. Set `b'` to `Submodule.smithNormalFormTopBasis bs h`. Set `ab` to `Submodule.smithNormalFormBotBasis bs h`. Establish `ab_eq : ∀ i, (ab i : B) = a i • b' i` using `Submodule.smithNormalFormBotBasis_def bs h`. Establish `ha : ∀ i, a i ≠ 0` using `Submodule.smithNormalFormCoeffs_ne_zero bs h`.

Establish `hlen : Module.length R (B ⧸ Ideal.span {b}) = ∑ i, Ring.ord R (a i)`. Rewrite using `[← (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {b})).length_eq, (Submodule.quotientEquivPiSpan N bs h).length_eq, Module.length_pi_of_fintype]`. Both sides reduce to the same expression. Set `E : B ≃ₗ[R] N` to `b'.equiv ab (Equiv.refl ι)`. Set `D : B →ₗ[R] B` to `N.subtype ∘ₗ E.toLinearMap`.

Set `u : B ≃ₗ[R] B` to `φ.trans E.symm`. Establish `hmDu : m = D ∘ₗ u.toLinearMap`. Use extensionality with `x`. Simplify using `[D, u, φ]`. Establish `hDb : ∀ j, D (b' j) = a j • b' j` using `fun j => by`.

Simplify using `only [D, E, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe, Basis.equiv_apply]`. Conclude with `ab_eq j`. Establish `hD : LinearMap.toMatrix b' b' D = Matrix.diagonal a`. Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply, Matrix.diagonal_apply, hDb, map_smul, Basis.repr_self]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij]`. Establish `hdet : Algebra.norm R b = (∏ i, a i) * LinearMap.det (u : B →ₗ[R] B)`.

Rewrite using `[Algebra.norm_apply, show Algebra.lmul R B b = m from rfl, hmDu, LinearMap.det_comp, ← LinearMap.det_toMatrix b' D, hD, Matrix.det_diagonal]`. Rewrite using `[hdet, Ring.ord_mul_of_isUnit_right (LinearEquiv.isUnit_det' u), ord_prod _ _ fun i _ => ha i, hlen]`.
-/
theorem ord_norm_eq_length {b : B} (hb : Function.Injective (fun x : B => b * x)) :
    Ring.ord R (Algebra.norm R b) = Module.length R (B ⧸ Ideal.span {b}) := by
  classical
  let bs := Module.Free.chooseBasis R B
  let ι := Module.Free.ChooseBasisIndex R B
  let N : Submodule R B := (Ideal.span {b}).restrictScalars R
  let m : B →ₗ[R] B := Algebra.lmul R B b
  have hm : Function.Injective m := hb
  have hrange : LinearMap.range m = N := by
    ext x
    simp only [LinearMap.mem_range, Submodule.restrictScalars_mem, Ideal.mem_span_singleton', N, m]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm y b⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm b y⟩
  let φ : B ≃ₗ[R] N := (LinearEquiv.ofInjective m hm).trans (LinearEquiv.ofEq _ _ hrange)
  have h : Module.finrank R N = Module.finrank R B := φ.finrank_eq.symm
  let a := Submodule.smithNormalFormCoeffs bs h
  let b' := Submodule.smithNormalFormTopBasis bs h
  let ab := Submodule.smithNormalFormBotBasis bs h
  have ab_eq : ∀ i, (ab i : B) = a i • b' i := Submodule.smithNormalFormBotBasis_def bs h
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero bs h

  have hlen : Module.length R (B ⧸ Ideal.span {b}) = ∑ i, Ring.ord R (a i) := by
    rw [← (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {b})).length_eq,
      (Submodule.quotientEquivPiSpan N bs h).length_eq, Module.length_pi_of_fintype]
    rfl

  let E : B ≃ₗ[R] N := b'.equiv ab (Equiv.refl ι)
  let D : B →ₗ[R] B := N.subtype ∘ₗ E.toLinearMap
  let u : B ≃ₗ[R] B := φ.trans E.symm
  have hmDu : m = D ∘ₗ u.toLinearMap := by
    ext x
    simp [D, u, φ]
  have hDb : ∀ j, D (b' j) = a j • b' j := fun j => by
    simp only [D, E, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearEquiv.coe_coe, Basis.equiv_apply]
    exact ab_eq j
  have hD : LinearMap.toMatrix b' b' D = Matrix.diagonal a := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply, hDb, map_smul, Basis.repr_self]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have hdet : Algebra.norm R b = (∏ i, a i) * LinearMap.det (u : B →ₗ[R] B) := by
    rw [Algebra.norm_apply, show Algebra.lmul R B b = m from rfl, hmDu, LinearMap.det_comp,
      ← LinearMap.det_toMatrix b' D, hD, Matrix.det_diagonal]
  rw [hdet, Ring.ord_mul_of_isUnit_right (LinearEquiv.isUnit_det' u), ord_prod _ _ fun i _ => ha i,
    hlen]

end NormLength

/- English proof (translation)
Introduce `R B _ _ _ _ _ _ _ b hb`. Conclude with `ord_norm_eq_length hb`.
-/
theorem NormLength.proof : NormLength.Statement := by
  intro R B _ _ _ _ _ _ _ b hb
  exact ord_norm_eq_length hb

end

end GroundTheory.Heights₂.Heights.Vertical
