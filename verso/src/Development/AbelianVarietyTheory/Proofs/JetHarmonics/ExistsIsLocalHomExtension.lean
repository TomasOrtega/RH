import Mathlib

namespace GlobalTheory.LocalHomExtension

/- English proof (translation)
Set `: Algebra A B` to `φ.toAlgebra`. Set `: Algebra A O` to `ι.toAlgebra`. Set `: Algebra A C` to `((algebraMap O C).comp ι).toAlgebra`. Establish `: IsScalarTower A O C` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: Module.IsTorsionFree A B` using `Module.isTorsionFree_iff_algebraMap_injective.mpr hφ`.

Establish `: Module.IsTorsionFree A C` using `Module.isTorsionFree_iff_algebraMap_injective.mpr hι`. Establish `: Algebra.IsIntegral A B` using `⟨hint⟩`. Set `f : B →ₐ[A] C` to `IsAlgClosed.lift`. Establish `hO : ∀ b : B, ∃ o : O, algebraMap O C o = f b` using `fun b => by`. Establish `h1 : IsIntegral A (f b)` using `(Algebra.IsIntegral.isIntegral b).map f`.

Conclude with `hv.exists_of_le_one (hv.mem_of_integral h1.tower_top)`. Use `choose g hg using hO`. Establish `inj` using `hv.hom_inj`. Set `ι' : B →+* O` to `{ toFun := g map_one' := inj (by rw [hg, map_one, map_one]) map_mul' := fun x y => inj (by rw [hg, map_mul, map_mul, hg, hg]) map_zero' := inj (by rw [hg, map_zero, map_zero]) map_add' := fun x y => inj (by rw [hg, map_add, map_add, hg, hg]) }`. Establish `hcomp : ι'.comp φ = ι`.

Use extensionality with `a`. Apply `inj` to reduce the goal to its premises. Use `show algebraMap O C (g (φ a)) = algebraMap O C (ι a)`. Rewrite using `[hg]`. Conclude with `f.commutes a`.

Use `⟨ι', ?_, hcomp⟩` and prove the remaining obligations. Establish `hA : (IsLocalRing.maximalIdeal O).comap ι = IsLocalRing.maximalIdeal A` using `((IsLocalRing.local_hom_TFAE ι).out 0 4).mp (inferInstance : IsLocalHom ι)`. Establish `hp : (((IsLocalRing.maximalIdeal O).comap ι').comap (algebraMap A B)).IsMaximal`. Rewrite using `[Ideal.comap_comap, show ι'.comp (algebraMap A B) = ι from hcomp, hA]`. Conclude with `IsLocalRing.maximalIdeal.isMaximal A`.

Establish `hpm` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap ((IsLocalRing.maximalIdeal O).comap ι') hp`. Conclude with `((IsLocalRing.local_hom_TFAE ι').out 0 4).mpr (IsLocalRing.eq_maximalIdeal hpm)`.
-/
theorem exists_isLocalHom_extension {A B O C : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing O] [IsLocalRing O] [Field C]
    [IsAlgClosed C] [Algebra O C] (v : Valuation C NNReal) (hv : Valuation.Integers v O)
    (φ : A →+* B) (hφ : Function.Injective φ) (hint : φ.IsIntegral)
    (ι : A →+* O) [IsLocalHom ι]
    (hι : Function.Injective ((algebraMap O C).comp ι)) :
    ∃ ι' : B →+* O, IsLocalHom ι' ∧ ι'.comp φ = ι := by
  let : Algebra A B := φ.toAlgebra
  let : Algebra A O := ι.toAlgebra
  let : Algebra A C := ((algebraMap O C).comp ι).toAlgebra
  have : IsScalarTower A O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hφ
  have : Module.IsTorsionFree A C := Module.isTorsionFree_iff_algebraMap_injective.mpr hι
  have : Algebra.IsIntegral A B := ⟨hint⟩

  let f : B →ₐ[A] C := IsAlgClosed.lift

  have hO : ∀ b : B, ∃ o : O, algebraMap O C o = f b := fun b => by
    have h1 : IsIntegral A (f b) := (Algebra.IsIntegral.isIntegral b).map f
    exact hv.exists_of_le_one (hv.mem_of_integral h1.tower_top)
  choose g hg using hO
  have inj := hv.hom_inj
  let ι' : B →+* O :=
    { toFun := g
      map_one' := inj (by rw [hg, map_one, map_one])
      map_mul' := fun x y => inj (by rw [hg, map_mul, map_mul, hg, hg])
      map_zero' := inj (by rw [hg, map_zero, map_zero])
      map_add' := fun x y => inj (by rw [hg, map_add, map_add, hg, hg]) }
  have hcomp : ι'.comp φ = ι := by
    ext a
    apply inj
    show algebraMap O C (g (φ a)) = algebraMap O C (ι a)
    rw [hg]
    exact f.commutes a
  refine ⟨ι', ?_, hcomp⟩

  have hA : (IsLocalRing.maximalIdeal O).comap ι = IsLocalRing.maximalIdeal A :=
    ((IsLocalRing.local_hom_TFAE ι).out 0 4).mp (inferInstance : IsLocalHom ι)
  have hp : (((IsLocalRing.maximalIdeal O).comap ι').comap (algebraMap A B)).IsMaximal := by
    rw [Ideal.comap_comap, show ι'.comp (algebraMap A B) = ι from hcomp, hA]
    exact IsLocalRing.maximalIdeal.isMaximal A
  have hpm := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap ((IsLocalRing.maximalIdeal O).comap ι') hp
  exact ((IsLocalRing.local_hom_TFAE ι').out 0 4).mpr (IsLocalRing.eq_maximalIdeal hpm)

end GlobalTheory.LocalHomExtension
