import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

/- English proof (translation)
Introduce `ι _ _ n P D Ω _ y x' E hR hA`. Take `⟨Q, hQ⟩` from `hPrime ι n P D`. Take `⟨_, _, _, hd⟩` from `hA`. Rewrite using `[← hR.ext_eq]`. Use `⟨inferInstance, hQ ▸ Q.isMultiProjPrime, hQ ▸ Q.isHorizontal, ?_⟩` and prove the remaining obligations.

Rewrite `hd` using `[← hR.ideal_eq]`. Express the relevant statement in the definitionally equal form `ringKrullDim (MvPolynomial (Coord D.extSizes) ℤ ⧸ D.extIdeal) = _`. Rewrite using `[hDim ι n P D]`. Express the relevant statement in the definitionally equal form `ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ P.ideal) + 1 = _`. Express the relevant statement in the definitionally equal form `ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ P.ideal) = _ at hd`.

Rewrite using `[hd, Fintype.card_option]`. Use `norm_cast`.
-/
theorem YPlusArithVar.proof (hPrime : ChartPrimality.Statement) (hDim : ExtensionDimension.Statement) :
    YPlusArithVar.Statement := by
  intro ι _ _ n P D Ω _ y x' E hR hA
  obtain ⟨Q, hQ⟩ := hPrime ι n P D
  obtain ⟨_, _, _, hd⟩ := hA
  rw [← hR.ext_eq]
  refine ⟨inferInstance, hQ ▸ Q.isMultiProjPrime, hQ ▸ Q.isHorizontal, ?_⟩
  rw [← hR.ideal_eq] at hd
  change ringKrullDim (MvPolynomial (Coord D.extSizes) ℤ ⧸ D.extIdeal) = _
  rw [hDim ι n P D]
  change ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ P.ideal) + 1 = _
  change ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ P.ideal) = _ at hd
  rw [hd, Fintype.card_option]
  norm_cast

end GroundTheory.Heights₂.Heights
