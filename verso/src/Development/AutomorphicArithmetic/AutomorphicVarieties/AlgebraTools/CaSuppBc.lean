import Mathlib

open IsLocalRing

/- English proof (translation)
Introduce `R B _ _ _ M _ _ _ Q`. Set `p` to `PrimeSpectrum.comap (algebraMap R B) Q`. Set `φ` to `Ideal.ResidueField.mapₐ p.asIdeal Q.asIdeal (Algebra.ofId R B) rfl`. Use `letI : Algebra p.asIdeal.ResidueField Q.asIdeal.ResidueField := φ.toRingHom.toAlgebra`. Use `haveI : IsScalarTower R p.asIdeal.ResidueField Q.asIdeal.ResidueField := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm`.

Rewrite using `[Module.mem_support_iff_nontrivial_residueField_tensorProduct, Module.mem_support_iff_nontrivial_residueField_tensorProduct, (TensorProduct.AlgebraTensorModule.cancelBaseChange R B Q.asIdeal.ResidueField Q.asIdeal.ResidueField M).nontrivial_congr, ← (TensorProduct.AlgebraTensorMo …`. Conclude with `Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right _ _`.
-/
theorem UpperTheory.V.AlgebraTools.mem_support_baseChange :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
      (Q : PrimeSpectrum B), Q ∈ Module.support B (TensorProduct R B M) ↔
        PrimeSpectrum.comap (algebraMap R B) Q ∈ Module.support R M := by
  intro R B _ _ _ M _ _ _ Q
  let p := PrimeSpectrum.comap (algebraMap R B) Q
  let φ := Ideal.ResidueField.mapₐ p.asIdeal Q.asIdeal (Algebra.ofId R B) rfl
  letI : Algebra p.asIdeal.ResidueField Q.asIdeal.ResidueField := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R p.asIdeal.ResidueField Q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R B Q.asIdeal.ResidueField
      Q.asIdeal.ResidueField M).nontrivial_congr,
    ← (TensorProduct.AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField
      Q.asIdeal.ResidueField Q.asIdeal.ResidueField M).nontrivial_congr]
  exact Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right _ _
