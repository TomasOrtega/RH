import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

noncomputable section

variable {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Simplify using the standard rewrite rules.

Both sides reduce to the same expression.
-/
theorem isPushout_app_of_isPullback (H : IsPullback fst snd f g) [IsAffine Y] [IsAffine Z]
    {V : X.Opens} (hV : IsAffineOpen V) :
    IsPushout (f.appLE ⊤ V le_top) g.appTop (fst.app V) (snd.appLE ⊤ (fst ⁻¹ᵁ V) le_top) := by
  have : IsAffine V.toScheme := hV
  have hP := (isPullback_morphismRestrict fst V).paste_vert H
  have hA := isPushout_appTop_of_isPullback hP
  refine hA.of_iso (Iso.refl _) (Scheme.Opens.topIso V) (Iso.refl _)
    (Scheme.Opens.topIso (fst ⁻¹ᵁ V)) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Scheme.Hom.comp_appTop, Scheme.Opens.topIso_hom,
      Scheme.Opens.ι_appTop, Scheme.Hom.appLE]
    erw [Category.assoc, ← Functor.map_comp]
    rfl
  · simp
  · simp only [Scheme.Opens.topIso_hom, morphismRestrict_appTop]
    erw [Category.assoc, ← Functor.map_comp, ← Scheme.Hom.naturality]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Scheme.Hom.comp_appTop, Scheme.Opens.topIso_hom,
      Scheme.Opens.ι_appTop, Scheme.Hom.appLE]
    erw [Category.assoc, ← Functor.map_comp]
    rfl

end

end GroundTheory.Arith.SchemeCoh
