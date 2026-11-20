import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OrdBasic

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

/- English proof (translation)
Introduce `T K M _ _ _ _ _ _ _`. Use `haveI hp : (RingHom.ker (algebraMap T K)).IsPrime := RingHom.ker_isPrime _`. Use `set p : Ideal T := RingHom.ker (algebraMap T K) with hpdef`. Set `P : PrimeSpectrum T` to `⟨p, hp⟩`. Establish `hP : P ∈ Module.support T M`.

Rewrite using `[Module.support_eq_zeroLocus, (Module.annihilator_eq_bot).mpr inferInstance]`. Simplify using the standard rewrite rules. Establish `hV : Nontrivial (p.ResidueField ⊗[T] M)` using `(Module.mem_support_iff_nontrivial_residueField_tensorProduct P).mp hP`. Set `f : p.ResidueField →+* K` to `Ideal.ResidueField.lift p (algebraMap T K) le_rfl (by`. Introduce `x hx`.

Establish `hx' : algebraMap T K x ≠ 0` using `fun h => hx ((RingHom.mem_ker).mpr h)`. Conclude with `(isUnit_iff_ne_zero.mpr hx'))`. Use `letI : Algebra p.ResidueField K := f.toAlgebra`. Use `haveI : IsScalarTower T p.ResidueField K := IsScalarTower.of_algebraMap_eq fun r => (Ideal.ResidueField.lift_algebraMap p (algebraMap T K) le_rfl _ r).symm`. Set `e` to `AlgebraTensorModule.cancelBaseChange T p.ResidueField K K M`.

Use `haveI : Nontrivial (K ⊗[p.ResidueField] (p.ResidueField ⊗[T] M)) := TensorProduct.nontrivial_of_linearMap_injective_of_flat_right p.ResidueField K (p.ResidueField ⊗[T] M) (Algebra.linearMap p.ResidueField K) (algebraMap p.ResidueField K).injective`. Conclude with `e.symm.nontrivial`.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.fibreNe :
    ∀ {T K M : Type*} [CommRing T] [Field K] [Algebra T K] [AddCommGroup M] [Module T M] [Module.Finite T M] [FaithfulSMul T M], Nontrivial (K ⊗[T] M) := by
  intro T K M _ _ _ _ _ _ _
  classical
  haveI hp : (RingHom.ker (algebraMap T K)).IsPrime := RingHom.ker_isPrime _
  set p : Ideal T := RingHom.ker (algebraMap T K) with hpdef
  let P : PrimeSpectrum T := ⟨p, hp⟩
  have hP : P ∈ Module.support T M := by
    rw [Module.support_eq_zeroLocus, (Module.annihilator_eq_bot).mpr inferInstance]
    simp
  have hV : Nontrivial (p.ResidueField ⊗[T] M) :=
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct P).mp hP
  let f : p.ResidueField →+* K := Ideal.ResidueField.lift p (algebraMap T K) le_rfl (by
    intro x hx
    have hx' : algebraMap T K x ≠ 0 := fun h => hx ((RingHom.mem_ker).mpr h)
    exact (isUnit_iff_ne_zero.mpr hx'))
  letI : Algebra p.ResidueField K := f.toAlgebra
  haveI : IsScalarTower T p.ResidueField K := IsScalarTower.of_algebraMap_eq fun r =>
    (Ideal.ResidueField.lift_algebraMap p (algebraMap T K) le_rfl _ r).symm
  let e := AlgebraTensorModule.cancelBaseChange T p.ResidueField K K M
  haveI : Nontrivial (K ⊗[p.ResidueField] (p.ResidueField ⊗[T] M)) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_right p.ResidueField
      K (p.ResidueField ⊗[T] M) (Algebra.linearMap p.ResidueField K)
      (algebraMap p.ResidueField K).injective
  exact e.symm.nontrivial
