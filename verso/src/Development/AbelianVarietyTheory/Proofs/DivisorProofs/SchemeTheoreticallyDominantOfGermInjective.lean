import Mathlib
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine
    (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens)
    (h : ∀ (U : X.Opens) (V : T.Opens), IsAffineOpen U → IsAffineOpen V → U ≤ p ⁻¹ᵁ V →
      ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) → b = 0) :
    IsSchemeTheoreticallyDominant W.ι := by
  rw [isSchemeTheoreticallyDominant_iff]
  let h𝒰 := X.isBasis_affineOpens.isOpenCover_mem_and_le
    (T.isBasis_affineOpens.isOpenCover.comap p.base.hom)
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U ↦ ⟨_, by exact U.2.1⟩) h𝒰 ?_
  rintro ⟨⟨U, ⟨V, hV⟩⟩, hU, hUV : U ≤ p ⁻¹ᵁ V⟩
  simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, ← le_bot_iff]
  intro b hb
  have hb' : W.ι.app U b = 0 := W.ι.ideal_ker_le ⟨U, hU⟩ hb
  refine h U V hU hV hUV b fun x hx hxW ↦ ?_
  have h1 := Scheme.Hom.germ_stalkMap_apply W.ι U ⟨x, hxW⟩ hx b
  rw [hb', map_zero] at h1
  let y : W.toScheme := ⟨x, hxW⟩
  have hiso : IsIso (W.ι.stalkMap y) := inferInstance
  have hinj : Function.Injective (W.ι.stalkMap y) :=
    (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap y)).1
  exact hinj (h1.trans (map_zero _).symm)

end GlobalTheory
