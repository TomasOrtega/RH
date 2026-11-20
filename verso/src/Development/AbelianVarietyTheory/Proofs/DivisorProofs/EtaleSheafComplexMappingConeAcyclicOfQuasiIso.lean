import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]`. Establish `hu : HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ) ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map u)`. Rewrite using `[HomotopyCategory.quotient_map_mem_quasiIso_iff]`. Conclude with `(inferInstance : QuasiIso u)`. Rewrite `hu` using `[HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]`.

Conclude with `((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished _ (HomotopyCategory.mappingCone_triangleh_distinguished u)).1 hu`.
-/
theorem mappingCone_acyclic_of_quasiIso {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {K L : CochainComplex 𝒜 ℤ} (u : K ⟶ L) [QuasiIso u] :
    (CochainComplex.mappingCone u).Acyclic := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  have hu : HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map u) := by
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (inferInstance : QuasiIso u)
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at hu
  exact ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished u)).1 hu

/- English proof (translation)
Introduce `_ _ _ _ u _` and use `mappingCone_acyclic_of_quasiIso u`.
-/
theorem EtC.mappingCone_acyclic :
    ∀ (R : Type) [CommRing R] {C J : Cx R} (u : C ⟶ J) [QuasiIso u], (mappingCone u).Acyclic :=
  fun _ _ _ _ u _ => mappingCone_acyclic_of_quasiIso u

end GlobalTheory
