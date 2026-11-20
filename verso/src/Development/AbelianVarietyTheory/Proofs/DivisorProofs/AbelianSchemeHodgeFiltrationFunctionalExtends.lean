import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamComparisonBijectiveCupSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjectiveStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

/- English proof (translation)
Set `f : FirstDeRham s →ₗ[R] HO1 s` to `(toHO1 s).comp (cmp1 s)`. Establish `hf : Function.Surjective f` using `hsurj.comp h1`. Take `⟨σ, hσ⟩` from `Module.projective_lifting_property f LinearMap.id hf`. Establish `hker : ∀ c : FirstDeRham s, f c = 0 ↔ c ∈ F1 s` using `fun c ↦ by`. Express the relevant statement in the definitionally equal form `toHO1 s (cmp1 s c) = 0 ↔ toH1O s c = 0`.

Rewrite using `[structureSheaf_comparison_comm]`. Conclude with `⟨fun h ↦ hO (h.trans (map_zero _).symm), fun h ↦ by rw [h, map_zero]⟩`. Set `p : FirstDeRham s →ₗ[R] F1 s` to `LinearMap.codRestrict (F1 s) (LinearMap.id - σ.comp f) fun c ↦ by`. Rewrite using `[← hker]`. Establish `: f (σ (f c)) = f c` using `LinearMap.congr_fun hσ (f c)`.

Simplify using `[this]`. Use `⟨ψ.comp p, fun c ↦ ?_⟩` and prove the remaining obligations. Establish `hc : f c = 0` using `(hker c).2 c.2`. Establish `: p c = c` using `Subtype.ext (by simp [p, hc])`. Simplify using `[this]`.
-/
theorem exists_extend_hodgeFiltration_functional_split {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (hO : Function.Injective (cmpO s)) (h1 : Function.Surjective (cmp1 s))
    (hsurj : Function.Surjective (toHO1 s)) [Module.Projective R (HO1 s)]
    (ψ : F1 s →ₗ[R] R) : ∃ H : FirstDeRham s →ₗ[R] R, ∀ c : F1 s, H c = ψ c := by
  let f : FirstDeRham s →ₗ[R] HO1 s := (toHO1 s).comp (cmp1 s)
  have hf : Function.Surjective f := hsurj.comp h1
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hker : ∀ c : FirstDeRham s, f c = 0 ↔ c ∈ F1 s := fun c ↦ by
    change toHO1 s (cmp1 s c) = 0 ↔ toH1O s c = 0
    rw [structureSheaf_comparison_comm]
    exact ⟨fun h ↦ hO (h.trans (map_zero _).symm), fun h ↦ by rw [h, map_zero]⟩
  let p : FirstDeRham s →ₗ[R] F1 s := LinearMap.codRestrict (F1 s) (LinearMap.id - σ.comp f) fun c ↦ by
    rw [← hker]
    have : f (σ (f c)) = f c := LinearMap.congr_fun hσ (f c)
    simp [this]
  refine ⟨ψ.comp p, fun c ↦ ?_⟩
  have hc : f c = 0 := (hker c).2 c.2
  have : p c = c := Subtype.ext (by simp [p, hc])
  simp [this]

end GlobalTheory.CechDR

namespace GlobalTheory.AbelianExtend

open GlobalTheory.CechDR

/- English proof (translation)
Introduce `hC hH R _ A _ g hab hdim ψ`. Take `⟨-, -, -, ⟨-, hproj, -⟩, ⟨-, -, hsurj⟩, -⟩` from `hH R A g hab hdim`. Use `haveI := hab.smooth`. Use `haveI := hab.proper`. Establish `hsm : Smooth (A.hom ≫ 𝟙 (Sp R))` using `by rw [Category.comp_id]; infer_instance`.

Establish `hsep : IsSeparated (A.hom ≫ 𝟙 (Sp R))` using `by rw [Category.comp_id]; infer_instance`. Establish `hqc : QuasiCompact (A.hom ≫ 𝟙 (Sp R))` using `by rw [Category.comp_id]; infer_instance`. Establish `h1` using `(GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth hC R A.left (A.hom ≫ 𝟙 (Sp R)) hsm hsep hqc).1.2`. Establish `hO` using `GlobalTheory.T.structure_sheaf_comparison_injective R A.left (A.hom ≫ 𝟙 (Sp R))`. Establish `hs' : Function.Surjective (toHO1 (A.hom ≫ 𝟙 (Sp R)))` using `by rw [Category.comp_id]; exact hsurj`.

Use `haveI : Module.Projective R (HO1 (A.hom ≫ 𝟙 (Sp R))) := by rw [Category.comp_id]; exact hproj`. Conclude with `GlobalTheory.CechDR.exists_extend_hodgeFiltration_functional_split _ hO h1 hs' ψ`.
-/
theorem abelianScheme_hodgeFiltration_functional_extends' : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ ψ : F1 (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R, ∃ H : FirstDeRham (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R,
      ∀ c : F1 (A.hom ≫ 𝟙 (Sp R)), H c = ψ c := by
  intro hC hH R _ A _ g hab hdim ψ
  obtain ⟨-, -, -, ⟨-, hproj, -⟩, ⟨-, -, hsurj⟩, -⟩ := hH R A g hab hdim
  haveI := hab.smooth
  haveI := hab.proper
  have hsm : Smooth (A.hom ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; infer_instance
  have hsep : IsSeparated (A.hom ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; infer_instance
  have hqc : QuasiCompact (A.hom ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; infer_instance
  have h1 := (GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth hC R A.left (A.hom ≫ 𝟙 (Sp R)) hsm hsep hqc).1.2
  have hO := GlobalTheory.T.structure_sheaf_comparison_injective R A.left (A.hom ≫ 𝟙 (Sp R))
  have hs' : Function.Surjective (toHO1 (A.hom ≫ 𝟙 (Sp R))) := by rw [Category.comp_id]; exact hsurj
  haveI : Module.Projective R (HO1 (A.hom ≫ 𝟙 (Sp R))) := by rw [Category.comp_id]; exact hproj
  exact GlobalTheory.CechDR.exists_extend_hodgeFiltration_functional_split _ hO h1 hs' ψ

end GlobalTheory.AbelianExtend
