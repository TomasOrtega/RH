import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalOfZariskiSheafOpenChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallOfSeparatedPresheafOpenChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartsRepresentedFunctorOpenCoverStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

/- English proof (translation)
Introduce `F hsep hglue Ix U x hinj hopen hcov`. Use `haveI hs : FunctorToTypes.Small.{0} F := GlobalTheory.T.small_of_separated_presheaf_open_charts F hsep Ix U x hopen hcov`. Set `G : Scheme.{0}ᵒᵖ ⥤ Type` to `FunctorToTypes.shrink.{0} F`. Set `e : ∀ T : Scheme.{0}, F.obj (op T) ≃ G.obj (op T)` to `fun T => equivShrink.{0} (F.obj (op T))`. Establish `he : ∀ {Y T : Scheme.{0}} (a : Y ⟶ T) (y : G.obj (op T)), G.map a.op y = e Y (F.map a.op ((e T).symm y))` using `fun a y => rfl`.

Establish `he' : ∀ {Y T : Scheme.{0}} (a : Y ⟶ T) (y : F.obj (op T)), G.map a.op (e T y) = e Y (F.map a.op y)` using `fun a y => by`. Rewrite using `[he, Equiv.symm_apply_apply]`. Establish `key` using `GlobalTheory.T.exists_universal_of_zariskiSheaf_openCharts G ?_ ?_ Ix U (fun i => e _ (x i)) ?_ ?_ ?_`. Take `⟨B, x₀, hx⟩` from `key`. Take `⟨x₁, rfl⟩` from `(e B).surjective x₀`.

Establish `hx' : ∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₁ = y`. Introduce `T y`. Establish `h` using `hx T (e T y)`. Simplify `h` using `only [he', Equiv.apply_eq_iff_eq]`. Conclude with `⟨B, x₁, hx', GlobalTheory.T.charts_representedFunctor_openCover F Ix U x hinj hopen hcov B x₁ hx'⟩`.

Introduce `T y y' h`. Take `⟨y, rfl⟩` from `(e T).surjective y`. Take `⟨y', rfl⟩` from `(e T).surjective y'`. Simplify using `only [he', Equiv.apply_eq_iff_eq] at h`. Rewrite using `[hsep T y y' h]`.

Introduce `T J Z z y hz hc h`. Take `⟨y₀, hy₀⟩` from `hglue T J Z z (fun i => (e _).symm (y i)) hz hc (fun i k Y a b hab => by`. Establish `h1` using `h i k Y a b hab`. Rewrite `h1` using `[he, he]`. Conclude with `(e Y).injective h1)`.

Use `⟨e T y₀, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[he', hy₀, Equiv.apply_symm_apply]`. Introduce `i Y u u' h`. Rewrite `h` using `[he', he']`. Conclude with `hinj i Y u u' ((e Y).injective h)`.

Introduce `i T y`. Take `⟨y, rfl⟩` from `(e T).surjective y`. Simplify using `only [he', Equiv.apply_eq_iff_eq]`. Conclude with `hopen i T y`. Introduce `T y p`.

Take `⟨y, rfl⟩` from `(e T).surjective y`. Simplify using `only [he', Equiv.apply_eq_iff_eq]`. Conclude with `hcov T y p`.
-/
theorem exists_represent_of_charts_large : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type 1), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Scheme.{0}) (J : Type) (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i)) → (∀ p : T, ∃ i, p ∈ Set.range (z i)) → (∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → ∀ (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Scheme.{0}) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∃ (B : Scheme.{0}) (x₀ : F.obj (op B)), (∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) ∧ ∃ j : ∀ i, U i ⟶ B, (∀ i, IsOpenImmersion (j i)) ∧ (∀ p : B, ∃ i, p ∈ Set.range (j i)) ∧ ∀ i, F.map (j i).op x₀ = x i := by
  intro F hsep hglue Ix U x hinj hopen hcov
  haveI hs : FunctorToTypes.Small.{0} F := GlobalTheory.T.small_of_separated_presheaf_open_charts F hsep Ix U x hopen hcov
  let G : Scheme.{0}ᵒᵖ ⥤ Type := FunctorToTypes.shrink.{0} F
  let e : ∀ T : Scheme.{0}, F.obj (op T) ≃ G.obj (op T) := fun T => equivShrink.{0} (F.obj (op T))
  have he : ∀ {Y T : Scheme.{0}} (a : Y ⟶ T) (y : G.obj (op T)),
      G.map a.op y = e Y (F.map a.op ((e T).symm y)) := fun a y => rfl
  have he' : ∀ {Y T : Scheme.{0}} (a : Y ⟶ T) (y : F.obj (op T)),
      G.map a.op (e T y) = e Y (F.map a.op y) := fun a y => by
    rw [he, Equiv.symm_apply_apply]
  have key := GlobalTheory.T.exists_universal_of_zariskiSheaf_openCharts G ?_ ?_ Ix U (fun i => e _ (x i)) ?_ ?_ ?_
  · obtain ⟨B, x₀, hx⟩ := key
    obtain ⟨x₁, rfl⟩ := (e B).surjective x₀
    have hx' : ∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₁ = y := by
      intro T y
      have h := hx T (e T y)
      simpa only [he', Equiv.apply_eq_iff_eq] using h
    exact ⟨B, x₁, hx', GlobalTheory.T.charts_representedFunctor_openCover F Ix U x hinj hopen hcov B x₁ hx'⟩
  · intro T y y' h
    obtain ⟨y, rfl⟩ := (e T).surjective y
    obtain ⟨y', rfl⟩ := (e T).surjective y'
    simp only [he', Equiv.apply_eq_iff_eq] at h
    rw [hsep T y y' h]
  · intro T J Z z y hz hc h
    obtain ⟨y₀, hy₀⟩ := hglue T J Z z (fun i => (e _).symm (y i)) hz hc (fun i k Y a b hab => by
      have h1 := h i k Y a b hab
      rw [he, he] at h1
      exact (e Y).injective h1)
    refine ⟨e T y₀, fun i => ?_⟩
    rw [he', hy₀, Equiv.apply_symm_apply]
  · intro i Y u u' h
    rw [he', he'] at h
    exact hinj i Y u u' ((e Y).injective h)
  · intro i T y
    obtain ⟨y, rfl⟩ := (e T).surjective y
    simp only [he', Equiv.apply_eq_iff_eq]
    exact hopen i T y
  · intro T y p
    obtain ⟨y, rfl⟩ := (e T).surjective y
    simp only [he', Equiv.apply_eq_iff_eq]
    exact hcov T y p

end GlobalTheory.PicGlue
