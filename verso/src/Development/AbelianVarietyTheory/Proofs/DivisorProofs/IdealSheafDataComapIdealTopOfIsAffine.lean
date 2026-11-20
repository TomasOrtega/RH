import Mathlib
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
example : ∀ (X Y : Scheme.{0}) [IsAffine X] [IsAffine Y] (f : X ⟶ Y) (J : Y.IdealSheafData), (J.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.map f.appTop.hom (J.ideal ⟨⊤, isAffineOpen_top Y⟩) :=
  fun X Y _ _ f J => IdealSheafData.ideal_comap_top_of_isAffine X Y f J

end GlobalTheory
