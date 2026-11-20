import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.LinearAlgebra.Dimension.Basic

noncomputable section

open CategoryTheory

namespace UpperTheory.V.Lit.Dr

/- English proof (translation)
Introduce `Γ M Ω Z _ _ _ _ _ _ _ ρM ρΩ ρZ ι π hι hπ hinj hsurj hex hΩ n`. Set `f : Rep.of ρM ⟶ Rep.of ρΩ` to `Rep.ofHom ⟨ι, fun γ => by ext m; exact hι γ m⟩`. Set `g : Rep.of ρΩ ⟶ Rep.of ρZ` to `Rep.ofHom ⟨π, fun γ => by ext x; exact hπ γ x⟩`. Establish `hfg : f ≫ g = 0`. Use extensionality with `m`.

Conclude with `hex.apply_apply_eq_zero m`. Set `X : ShortComplex (Rep ℂ Γ)` to `ShortComplex.mk f g hfg`. Establish `hX : X.ShortExact` using `{ exact := (forget₂ (Rep ℂ Γ) (ModuleCat ℂ)).reflects_exact_of_faithful _ <| (ShortComplex.moduleCat_exact_iff _).2 fun x hx => (hex x).1 hx mono_f := (Rep.mono_iff_injective _).2 hinj epi_g := (Rep.epi_iff_surjective _).2 hsurj }`. Establish `hz : Limits.IsZero (groupCohomology X.X₂ (n + 1))` using `by haveI := hΩ n`. Conclude with `ModuleCat.isZero_of_subsingleton _`.

Establish `hmono` using `groupCohomology.mono_δ_of_isZero hX (n + 1) hz`. Establish `hinjδ` using `(ModuleCat.mono_iff_injective _).1 hmono`. Conclude with `LinearMap.rank_le_of_injective _ hinjδ`.
-/
theorem shiftUp : ShiftUp := by
  intro Γ M Ω Z _ _ _ _ _ _ _ ρM ρΩ ρZ ι π hι hπ hinj hsurj hex hΩ n
  let f : Rep.of ρM ⟶ Rep.of ρΩ := Rep.ofHom ⟨ι, fun γ => by ext m; exact hι γ m⟩
  let g : Rep.of ρΩ ⟶ Rep.of ρZ := Rep.ofHom ⟨π, fun γ => by ext x; exact hπ γ x⟩
  have hfg : f ≫ g = 0 := by
    ext m
    exact hex.apply_apply_eq_zero m
  let X : ShortComplex (Rep ℂ Γ) := ShortComplex.mk f g hfg
  have hX : X.ShortExact :=
    { exact := (forget₂ (Rep ℂ Γ) (ModuleCat ℂ)).reflects_exact_of_faithful _ <|
        (ShortComplex.moduleCat_exact_iff _).2 fun x hx => (hex x).1 hx
      mono_f := (Rep.mono_iff_injective _).2 hinj
      epi_g := (Rep.epi_iff_surjective _).2 hsurj }
  have hz : Limits.IsZero (groupCohomology X.X₂ (n + 1)) := by
    haveI := hΩ n
    exact ModuleCat.isZero_of_subsingleton _
  have hmono := groupCohomology.mono_δ_of_isZero hX (n + 1) hz
  have hinjδ := (ModuleCat.mono_iff_injective _).1 hmono
  exact LinearMap.rank_le_of_injective _ hinjδ

end UpperTheory.V.Lit.Dr
