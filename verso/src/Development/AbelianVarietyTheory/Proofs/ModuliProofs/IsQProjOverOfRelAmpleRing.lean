import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasisOnAny
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmplifyingFrames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.Models.InhabZOn

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in

/- English proof (translation)
Use `haveI : Smooth t.G.hom := t.semi.smooth`. Use `haveI : GeometricallyIntegral t.G.hom := _root_.GlobalTheory.geometricallyIntegral_of_isSemiAbelian (h := t.semi) _`. Set `e : S ⟶ t.G.left` to `(η[t.G]).left`. Establish `he : e ≫ t.G.hom = 𝟙 S` using `Over.w (η[t.G])`. Establish `hes : ∀ s, t.G.hom (e s) = s` using `fun s => by`.

Rewrite using `[← Scheme.Hom.comp_apply, he]`. Both sides reduce to the same expression. Establish `hfib : ∀ s : S, _root_.IsPreconnected (t.G.hom ⁻¹' {s})` using `fun s => by`. Rewrite using `[← Scheme.Hom.range_fiberι]`. Conclude with `isPreconnected_range (Scheme.Hom.continuous _)`.

Establish `hsec : _root_.IsPreconnected (Set.range e)` using `isPreconnected_range (Scheme.Hom.continuous _)`. Take `⟨s₀⟩` from `(inferInstance : Nonempty S)`. Use `haveI : PreconnectedSpace t.G.left := by`. Use `⟨isPreconnected_of_forall (e s₀) fun x _ => ?_⟩` and prove the remaining obligations. Use `⟨Set.range e ∪ t.G.hom ⁻¹' {t.G.hom x}, Set.subset_univ _, Or.inl ⟨s₀, rfl⟩, Or.inr rfl, ?_⟩` and prove the remaining obligations.

Conclude with `hsec.union (e (t.G.hom x)) ⟨_, rfl⟩ (hes _) (hfib _)`. Conclude with `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_dim_of_preconnected t.G.hom (e s₀)`.
-/
theorem _root_.GlobalTheory.Models.InhabZOn.exists_dim_triple {E : Type} [Field E] [NumberField E]
    [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {S : Scheme.{0}}
    [ConnectedSpace S] (t : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.SAB H S) : ∃ d, SmoothOfRelativeDimension d t.G.hom := by
  haveI : Smooth t.G.hom := t.semi.smooth
  haveI : GeometricallyIntegral t.G.hom :=
    _root_.GlobalTheory.geometricallyIntegral_of_isSemiAbelian (h := t.semi) _
  let e : S ⟶ t.G.left := (η[t.G]).left
  have he : e ≫ t.G.hom = 𝟙 S := Over.w (η[t.G])
  have hes : ∀ s, t.G.hom (e s) = s := fun s => by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have hfib : ∀ s : S, _root_.IsPreconnected (t.G.hom ⁻¹' {s}) := fun s => by
    rw [← Scheme.Hom.range_fiberι]
    exact isPreconnected_range (Scheme.Hom.continuous _)
  have hsec : _root_.IsPreconnected (Set.range e) :=
    isPreconnected_range (Scheme.Hom.continuous _)
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  haveI : PreconnectedSpace t.G.left := by
    refine ⟨isPreconnected_of_forall (e s₀) fun x _ => ?_⟩
    refine ⟨Set.range e ∪ t.G.hom ⁻¹' {t.G.hom x}, Set.subset_univ _, Or.inl ⟨s₀, rfl⟩,
      Or.inr rfl, ?_⟩
    exact hsec.union (e (t.G.hom x)) ⟨_, rfl⟩ (hes _) (hfib _)
  exact _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_dim_of_preconnected t.G.hom (e s₀)

end GlobalTheory.Models.InhabZOn

end
