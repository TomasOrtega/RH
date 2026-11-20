import Development.EtaleCohomology.EtaleSheaves.StrictLocalStalks

open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.ULAStalkPf

/- English proof (translation)
Introduce `A B b`. Set `_ : Algebra A B` to `b.hom.toAlgebra`. Set `_ : Algebra (Polynomial A) (Polynomial B)` to `(Polynomial.mapRingHom b.hom).toAlgebra`. Establish `_ : IsScalarTower A (Polynomial A) (Polynomial B)` using `IsScalarTower.of_algebraMap_eq (fun a => by`. Express the relevant statement in the definitionally equal form `Polynomial.C (b.hom a) = Polynomial.map b.hom (Polynomial.C a)`.

Rewrite using `[Polynomial.map_C])`. Establish `hP : Algebra.IsPushout A B (Polynomial A) (Polynomial B)`. Use `⟨IsBaseChange.of_equiv (polyEquivTensor' A B).symm.toLinearEquiv (fun p => ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(polyEquivTensor A B).symm (1 ⊗ₜ p) = Polynomial.map b.hom p`. Rewrite using `[polyEquivTensor_symm_apply_tmul_eq_smul, one_smul]`.

Both sides reduce to the same expression. Conclude with `CommRingCat.isPushout_iff_isPushout.mpr hP.symm`.
-/
theorem polyPO : PolyPO := by
  intro A B b
  let _ : Algebra A B := b.hom.toAlgebra
  let _ : Algebra (Polynomial A) (Polynomial B) := (Polynomial.mapRingHom b.hom).toAlgebra
  have _ : IsScalarTower A (Polynomial A) (Polynomial B) := IsScalarTower.of_algebraMap_eq (fun a => by
    change Polynomial.C (b.hom a) = Polynomial.map b.hom (Polynomial.C a)
    rw [Polynomial.map_C])
  have hP : Algebra.IsPushout A B (Polynomial A) (Polynomial B) := by
    refine ⟨IsBaseChange.of_equiv (polyEquivTensor' A B).symm.toLinearEquiv (fun p => ?_)⟩
    change (polyEquivTensor A B).symm (1 ⊗ₜ p) = Polynomial.map b.hom p
    rw [polyEquivTensor_symm_apply_tmul_eq_smul, one_smul]; rfl
  exact CommRingCat.isPushout_iff_isPushout.mpr hP.symm

end LateralTheory.E.ULAStalkPf
