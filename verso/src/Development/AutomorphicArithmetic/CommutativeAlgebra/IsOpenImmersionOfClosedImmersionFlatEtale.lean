import Mathlib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

/- English proof (translation)
Introduce `V X T v p hp hv hf hl`. Establish `hv' : FormallyUnramified v` using `inferInstance`. Establish `hu : FormallyUnramified (v ≫ p)` using `MorphismProperty.comp_mem @FormallyUnramified v p hv' inferInstance`. Establish `he : Etale (v ≫ p)` using `Etale.of_formallyUnramified_of_flat (v ≫ p)`. Establish `hev : Etale v` using `Etale.of_comp v p`.

Conclude with `IsOpenImmersion.of_flat_of_mono v`.
-/
theorem UpperTheory.isOpenImmersion_of_closedImmersion_flat_etale :
    ∀ {V X T : Scheme.{0}} (v : V ⟶ X) (p : X ⟶ T), Etale p → IsClosedImmersion v → Flat (v ≫ p) → LocallyOfFinitePresentation (v ≫ p) → IsOpenImmersion v := by
  intro V X T v p hp hv hf hl
  have hv' : FormallyUnramified v := inferInstance
  have hu : FormallyUnramified (v ≫ p) :=
    MorphismProperty.comp_mem @FormallyUnramified v p hv' inferInstance
  have he : Etale (v ≫ p) := Etale.of_formallyUnramified_of_flat (v ≫ p)
  have hev : Etale v := Etale.of_comp v p
  exact IsOpenImmersion.of_flat_of_mono v
