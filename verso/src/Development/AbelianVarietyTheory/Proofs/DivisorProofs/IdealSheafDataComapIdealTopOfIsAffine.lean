import Mathlib
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Establish `hle : J.comap f ≤ Scheme.IdealSheafData.ofIdealTop (Ideal.map f.appTop.hom (J.ideal ⟨⊤, isAffineOpen_top Y⟩))`. Rewrite using `[← Scheme.IdealSheafData.le_map_iff_comap_le]`. Apply `Scheme.IdealSheafData.le_of_isAffine` to reduce the goal to its premises. Rewrite using `[Scheme.IdealSheafData.ideal_map_of_isAffineHom]`.

Introduce `j hj`. Rewrite using `[Ideal.mem_comap, Scheme.IdealSheafData.ofIdealTop_ideal]`. Establish `h1 : (X.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ (⊤ : Y.Opens) ≤ ⊤)).op) = 𝟙 _` using `X.presheaf.map_id _`. Rewrite using `[h1]`. Use `erw [CommRingCat.hom_id, Ideal.map_id]`.

Conclude with `Ideal.mem_map_of_mem _ hj`. Use `hle ⟨⊤, isAffineOpen_top X⟩` as an intermediate fact. Simplify using `using this`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `j hj`.

Rewrite using `[Ideal.mem_comap, Scheme.IdealSheafData.comap, Scheme.Hom.ker_apply, RingHom.mem_ker]`. Establish `hj' : J.subschemeι.appTop.hom j = 0`. Use `hj` as an intermediate fact. Rewrite `this` using `[← J.ker_subschemeι, Scheme.Hom.ker_apply, RingHom.mem_ker]`. Conclude with `this`.

Establish `hc` using `congrArg (fun g => g.hom j) (congrArg Scheme.Hom.appTop (pullback.condition (f := f) (g := J.subschemeι)))`. Simplify using `only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at hc`. Express the relevant statement in the definitionally equal form `(pullback.fst f J.subschemeι).appTop.hom (f.appTop.hom j) = 0`. Rewrite using `[hc, hj', map_zero]`.
-/
theorem IdealSheafData.ideal_comap_top_of_isAffine (X Y : Scheme.{0}) [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (J : Y.IdealSheafData) :
    (J.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      Ideal.map f.appTop.hom (J.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  apply le_antisymm
  · have hle : J.comap f ≤ Scheme.IdealSheafData.ofIdealTop
        (Ideal.map f.appTop.hom (J.ideal ⟨⊤, isAffineOpen_top Y⟩)) := by
      rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
      apply Scheme.IdealSheafData.le_of_isAffine
      rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]
      intro j hj
      rw [Ideal.mem_comap, Scheme.IdealSheafData.ofIdealTop_ideal]
      have h1 : (X.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ (⊤ : Y.Opens) ≤ ⊤)).op) = 𝟙 _ :=
        X.presheaf.map_id _
      rw [h1]
      erw [CommRingCat.hom_id, Ideal.map_id]
      exact Ideal.mem_map_of_mem _ hj
    have := hle ⟨⊤, isAffineOpen_top X⟩
    simpa using this
  · rw [Ideal.map_le_iff_le_comap]
    intro j hj
    rw [Ideal.mem_comap, Scheme.IdealSheafData.comap, Scheme.Hom.ker_apply, RingHom.mem_ker]
    have hj' : J.subschemeι.appTop.hom j = 0 := by
      have := hj
      rw [← J.ker_subschemeι, Scheme.Hom.ker_apply, RingHom.mem_ker] at this
      exact this
    have hc := congrArg (fun g => g.hom j)
      (congrArg Scheme.Hom.appTop (pullback.condition (f := f) (g := J.subschemeι)))
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at hc
    change (pullback.fst f J.subschemeι).appTop.hom (f.appTop.hom j) = 0
    rw [hc, hj', map_zero]

/- English proof (translation)
Introduce `X Y _ _ f J` and use `IdealSheafData.ideal_comap_top_of_isAffine X Y f J`.
-/
example : ∀ (X Y : Scheme.{0}) [IsAffine X] [IsAffine Y] (f : X ⟶ Y) (J : Y.IdealSheafData), (J.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.map f.appTop.hom (J.ideal ⟨⊤, isAffineOpen_top Y⟩) :=
  fun X Y _ _ f J => IdealSheafData.ideal_comap_top_of_isAffine X Y f J

end GlobalTheory
