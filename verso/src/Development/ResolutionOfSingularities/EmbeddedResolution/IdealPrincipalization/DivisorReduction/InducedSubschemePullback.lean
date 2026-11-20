import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

/- English proof (authored)
The first projection from the fiber product has kernel equal to the pulled-back ideal. This is the defining ideal of the new closed subscheme. The kernel containment required for factorization through its inclusion therefore holds by equality, giving the stated lift.
-/
private theorem exists_lift_pullback_subschemeι_comap {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) :
    ∃ ψ : Limits.pullback h D.subschemeι ⟶ D'.subscheme,
      ψ ≫ D'.subschemeι = Limits.pullback.fst h D.subschemeι := by
  have hle : D'.subschemeι.ker ≤ (Limits.pullback.fst h D.subschemeι).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hD]
    exact le_rfl
  exact ⟨AlgebraicGeometry.IsClosedImmersion.lift D'.subschemeι
      (Limits.pullback.fst h D.subschemeι) hle, by simp⟩

/- English proof (authored)
The square commutes by construction, so the new closed subscheme maps to the categorical fiber product. Conversely, the first projection of the fiber product factors through that closed subscheme, giving a reverse map. One composite is the identity by cancellation of the new closed immersion. The other is the identity because its composites with both fiber-product projections agree with those of the identity. For the second projection this follows from commutativity and cancellation of the original closed immersion. Thus the given square identifies with the pullback square.
-/
theorem isPullback_subschemeMapOfComap (X Y : Scheme.{u}) (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) :
    IsPullback (subschemeMapOfComap h D D' hD) D'.subschemeι D.subschemeι h := by
  have hcomm : subschemeMapOfComap h D D' hD ≫ D.subschemeι = D'.subschemeι ≫ h :=
    subschemeMapOfComap_comp h D D' hD
  obtain ⟨ψ, hψ⟩ := exists_lift_pullback_subschemeι_comap h D D' hD
  have h1 : Limits.pullback.lift D'.subschemeι (subschemeMapOfComap h D D' hD) hcomm.symm ≫ ψ = 𝟙 _ := by
    rw [← cancel_mono D'.subschemeι, Category.assoc, hψ, Category.id_comp]
    exact Limits.pullback.lift_fst _ _ _
  have h2 : ψ ≫ Limits.pullback.lift D'.subschemeι (subschemeMapOfComap h D D' hD) hcomm.symm = 𝟙 _ := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, Category.id_comp]
      exact hψ
    · rw [Category.assoc, Limits.pullback.lift_snd, Category.id_comp,
        ← cancel_mono D.subschemeι, Category.assoc, hcomm, ← Category.assoc, hψ]
      exact Limits.pullback.condition
  refine (IsPullback.of_iso_pullback ⟨hcomm.symm⟩
    { hom := Limits.pullback.lift D'.subschemeι (subschemeMapOfComap h D D' hD) hcomm.symm
      inv := ψ
      hom_inv_id := h1
      inv_hom_id := h2 } ?_ ?_).flip
  · exact Limits.pullback.lift_fst _ _ _
  · exact Limits.pullback.lift_snd _ _ _

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
