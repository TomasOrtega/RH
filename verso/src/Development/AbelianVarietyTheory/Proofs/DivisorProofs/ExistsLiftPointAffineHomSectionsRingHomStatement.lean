import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftPointAffineHomSectionsRingHom
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AffinePointLift.exists_lift` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLiftPointAffineHomSectionsRingHom.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.exists_lift_point_affineHom_sections_ringHom : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsAffineHom π], ∀ (U : Z.affineOpens) (V V' : Type) [CommRing V]
    [IsLocalRing V] [CommRing V'] [IsLocalRing V'] (ξ : Sp V ⟶ Z) (hξ : ⊤ ≤ ξ ⁻¹ᵁ U.1) (f : V →+* V')
    (ρ : Γ(Y, π ⁻¹ᵁ U.1) →+* V'),
    ρ.comp (π.app U.1).hom = f.comp (ξ.appLE U.1 ⊤ hξ ≫ (Scheme.ΓSpecIso (.of V)).hom).hom →
    ∃ ψ : Sp V' ⟶ Y, ψ ≫ π = spMap f ≫ ξ ∧
      ∀ I : Y.IdealSheafData, idlAlong I ψ = (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩).map ρ := by
  first | exact @GlobalTheory.AffinePointLift.exists_lift | exact GlobalTheory.AffinePointLift.exists_lift | (intros; apply GlobalTheory.AffinePointLift.exists_lift <;> assumption)
