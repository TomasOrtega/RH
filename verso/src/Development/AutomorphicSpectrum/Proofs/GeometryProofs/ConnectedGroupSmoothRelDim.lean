import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.CompanionTheory.Ggeo

/- English proof (translation)
Introduce `X _ G _ hs hc`. Use `haveI : Smooth G.hom := hs`. Take `⟨d, W, hxW, hW⟩ : ∃ (d : G.left → ℕ) (W : G.left → G.left.Opens), (∀ x, x ∈ W x) ∧ ∀ x, SmoothOfRelativeDimension (d x) ((W x).ι ≫ G.hom)` from `by choose d W hxW hW using fun x => ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom x`. Conclude with `⟨d, W, hxW, hW⟩`. Establish `hres : ∀ (x : G.left) (V : G.left.Opens), V ≤ W x → SmoothOfRelativeDimension (d x) (V.ι ≫ G.hom)`.

Introduce `x V hV`. Establish `h` using `HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension (d x)) (G.left.homOfLE hV) ((W x).ι ≫ G.hom) (hW x)`. Rewrite `h` using `[← Category.assoc, Scheme.homOfLE_ι]`. Then use the resulting hypothesis. Establish `hd : IsLocallyConstant d`. Rewrite using `[IsLocallyConstant.iff_exists_open]`.

Introduce `x`. Use `⟨W x, (W x).isOpen, hxW x, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1` using `hres x (W x ⊓ W y) inf_le_left`. Establish `h2` using `hres y (W x ⊓ W y) inf_le_right`. Conclude with `ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h2 h1 ⟨y, hy, hxW y⟩`.

Set `e : X ⟶ G.left` to `(η[G]).left`. Establish `hcomp : e ≫ G.hom = 𝟙 X` using `Over.w (η[G])`. Establish `he : ∀ s : X, G.hom (e s) = s`. Introduce `s`. Establish `h` using `congrArg (fun g : X ⟶ X => g s) hcomp`.

Simplify using `using h`. Establish `hfib : ∀ s : X, _root_.IsPreconnected (G.hom ⁻¹' {s})`. Introduce `s`. Rewrite using `[← Scheme.Hom.range_fiberι]`. Conclude with `isPreconnected_range (Scheme.Hom.continuous _)`.

Take `⟨s₀⟩ : Nonempty X` from `inferInstance`. Establish `hconst : ∀ x, d x = d (e s₀)`. Introduce `x`. Establish `h1 : d x = d (e (G.hom x))` using `hd.apply_eq_of_isPreconnected (hfib (G.hom x)) rfl (he (G.hom x))`. Establish `h2 : d (e (G.hom x)) = d (e s₀)` using `(hd.comp_continuous (Scheme.Hom.continuous e)).apply_eq_of_isPreconnected isPreconnected_univ trivial trivial`.

Conclude with `h1.trans h2`. Use `⟨d (e s₀), ?_⟩` and prove the remaining obligations. Use `haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (d (e s₀))) := HasRingHomProperty.instIsZariskiLocalAtSource`. Conclude with `IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (d (e s₀))) W (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩) (fun x => by rw [← hconst x]; exact hW x)`.
-/
theorem exists_smoothOfRelativeDimension_of_geometricallyConnected :
    ∀ (X : Scheme.{0}) [ConnectedSpace X] (G : Over X) [GrpObj G], Smooth G.hom →
      GeometricallyConnected G.hom → ∃ g : ℕ, SmoothOfRelativeDimension g G.hom := by
  intro X _ G _ hs hc
  haveI : Smooth G.hom := hs
  obtain ⟨d, W, hxW, hW⟩ : ∃ (d : G.left → ℕ) (W : G.left → G.left.Opens), (∀ x, x ∈ W x) ∧
      ∀ x, SmoothOfRelativeDimension (d x) ((W x).ι ≫ G.hom) := by
    choose d W hxW hW using fun x => ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom x
    exact ⟨d, W, hxW, hW⟩
  have hres : ∀ (x : G.left) (V : G.left.Opens), V ≤ W x →
      SmoothOfRelativeDimension (d x) (V.ι ≫ G.hom) := by
    intro x V hV
    have h := HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension (d x))
      (G.left.homOfLE hV) ((W x).ι ≫ G.hom) (hW x)
    rwa [← Category.assoc, Scheme.homOfLE_ι] at h
  have hd : IsLocallyConstant d := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨W x, (W x).isOpen, hxW x, fun y hy => ?_⟩
    have h1 := hres x (W x ⊓ W y) inf_le_left
    have h2 := hres y (W x ⊓ W y) inf_le_right
    exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h2 h1 ⟨y, hy, hxW y⟩
  let e : X ⟶ G.left := (η[G]).left
  have hcomp : e ≫ G.hom = 𝟙 X := Over.w (η[G])
  have he : ∀ s : X, G.hom (e s) = s := by
    intro s
    have h := congrArg (fun g : X ⟶ X => g s) hcomp
    simpa using h
  have hfib : ∀ s : X, _root_.IsPreconnected (G.hom ⁻¹' {s}) := by
    intro s
    rw [← Scheme.Hom.range_fiberι]
    exact isPreconnected_range (Scheme.Hom.continuous _)
  obtain ⟨s₀⟩ : Nonempty X := inferInstance
  have hconst : ∀ x, d x = d (e s₀) := by
    intro x
    have h1 : d x = d (e (G.hom x)) :=
      hd.apply_eq_of_isPreconnected (hfib (G.hom x)) rfl (he (G.hom x))
    have h2 : d (e (G.hom x)) = d (e s₀) :=
      (hd.comp_continuous (Scheme.Hom.continuous e)).apply_eq_of_isPreconnected
        isPreconnected_univ trivial trivial
    exact h1.trans h2
  refine ⟨d (e s₀), ?_⟩
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (d (e s₀))) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (d (e s₀))) W
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩)
    (fun x => by rw [← hconst x]; exact hW x)

end GlobalTheory.CompanionTheory.Ggeo
