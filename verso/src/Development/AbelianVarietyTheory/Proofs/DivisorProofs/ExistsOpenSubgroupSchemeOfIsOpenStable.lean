import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory.OpenSubgroup

/- English proof (translation)
Introduce `S G _ Z hZ h1 hmul hinv`. Set `U : G.left.Opens` to `⟨Z, hZ⟩`. Set `G₀ : Over S` to `Over.mk (U.ι ≫ G.hom)`. Set `j : G₀ ⟶ G` to `Over.homMk U.ι rfl`. Establish `hjo : IsOpenImmersion j.left` using `inferInstanceAs (IsOpenImmersion U.ι)`.

Establish `hr : Set.range j.left = Z` using `U.range_ι`. Establish `: Mono j` using `Over.mono_of_mono_left j`. Establish `lift : ∀ (X : Over S) (φ : X ⟶ G), Set.range φ.left ⊆ Z → ∃ ψ : X ⟶ G₀, ψ ≫ j = φ`. Introduce `X φ hsub`. Establish `hsub' : Set.range φ.left ⊆ Set.range j.left` using `hr ▸ hsub`.

Use `⟨Over.homMk (IsOpenImmersion.lift j.left φ.left hsub') ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← j.w, IsOpenImmersion.lift_fac_assoc, φ.w]`. Conclude with `Over.OverMorphism.ext (IsOpenImmersion.lift_fac j.left φ.left hsub')`. Establish `inZ : ∀ x : G₀.left, j.left x ∈ Z` using `fun x => hr ▸ Set.mem_range_self x`. Take `⟨e, he⟩` from `lift (𝟙_ _) η[G] (by`.

Introduce and unpack `_ ⟨s, rfl⟩`. Conclude with `h1 s)`. Take `⟨m, hm⟩` from `lift (G₀ ⊗ G₀) ((j ⊗ₘ j) ≫ μ[G]) (by`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[Over.comp_left, Scheme.Hom.comp_apply]`.

Apply `hmul` to reduce the goal to its premises. Rewrite using `[← Scheme.Hom.comp_apply, ← Over.comp_left, tensorHom_fst, Over.comp_left, Scheme.Hom.comp_apply]`. Conclude with `inZ _`. Rewrite using `[← Scheme.Hom.comp_apply, ← Over.comp_left, tensorHom_snd, Over.comp_left, Scheme.Hom.comp_apply]`. Conclude with `inZ _)`.

Take `⟨i, hi⟩` from `lift G₀ (j ≫ ι[G]) (by`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[Over.comp_left, Scheme.Hom.comp_apply]`. Conclude with `hinv _ (inZ x))`. Take `⟨Gs, hG⟩` from `exists_grpObj_of_mono_of_fac j e m i he hm hi`.

Conclude with `⟨G₀, Gs, j, hG, hjo, hr⟩`.
-/
theorem exists_open_subgroup : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (Z : Set G.left), IsOpen Z → (∀ s : S, (η[G]).left s ∈ Z) → (∀ w : (G ⊗ G).left, (fst G G).left w ∈ Z → (snd G G).left w ∈ Z → (μ[G]).left w ∈ Z) → (∀ y ∈ Z, (ι[G]).left y ∈ Z) → ∃ (G₀ : Over S) (_ : GrpObj G₀) (j : G₀ ⟶ G), IsMonHom j ∧ IsOpenImmersion j.left ∧ Set.range j.left = Z := by
  intro S G _ Z hZ h1 hmul hinv
  let U : G.left.Opens := ⟨Z, hZ⟩
  let G₀ : Over S := Over.mk (U.ι ≫ G.hom)
  let j : G₀ ⟶ G := Over.homMk U.ι rfl
  have hjo : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion U.ι)
  have hr : Set.range j.left = Z := U.range_ι
  have : Mono j := Over.mono_of_mono_left j
  have lift : ∀ (X : Over S) (φ : X ⟶ G), Set.range φ.left ⊆ Z → ∃ ψ : X ⟶ G₀, ψ ≫ j = φ := by
    intro X φ hsub
    have hsub' : Set.range φ.left ⊆ Set.range j.left := hr ▸ hsub
    refine ⟨Over.homMk (IsOpenImmersion.lift j.left φ.left hsub') ?_, ?_⟩
    · rw [← j.w, IsOpenImmersion.lift_fac_assoc, φ.w]
    · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac j.left φ.left hsub')
  have inZ : ∀ x : G₀.left, j.left x ∈ Z := fun x => hr ▸ Set.mem_range_self x
  obtain ⟨e, he⟩ := lift (𝟙_ _) η[G] (by
    rintro _ ⟨s, rfl⟩
    exact h1 s)
  obtain ⟨m, hm⟩ := lift (G₀ ⊗ G₀) ((j ⊗ₘ j) ≫ μ[G]) (by
    rintro _ ⟨w, rfl⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    apply hmul
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, tensorHom_fst, Over.comp_left,
        Scheme.Hom.comp_apply]
      exact inZ _
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, tensorHom_snd, Over.comp_left,
        Scheme.Hom.comp_apply]
      exact inZ _)
  obtain ⟨i, hi⟩ := lift G₀ (j ≫ ι[G]) (by
    rintro _ ⟨x, rfl⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact hinv _ (inZ x))
  obtain ⟨Gs, hG⟩ := exists_grpObj_of_mono_of_fac j e m i he hm hi
  exact ⟨G₀, Gs, j, hG, hjo, hr⟩

end GlobalTheory.OpenSubgroup
