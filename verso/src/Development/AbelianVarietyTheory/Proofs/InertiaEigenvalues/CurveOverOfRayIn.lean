import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverFormsMulComponentFunction
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesMemOfContainsRayField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldOfRay
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwistRat.Field

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem curveOver_of_rayIn : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ (N : ℕ), 3 ≤ N →
    ∀ (Fc : IntermediateField ℚ ℂ) (σ : Fc →+* ℂ), RayIn D N σ.fieldRange → GlobalTheory.CompRat.CurveOver Q.H Fc N := by
  intro _ D Q hP N hN Fc σ hray
  obtain ⟨L, _, _, _, _, hL, j, -, hjv⟩ := hray

  have hC : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap D.host.K L) N :=
    GlobalTheory.FieldSize.RayNorm.containsRayField_of_ray N hL.1 fun I hI hc => (hL.2.2 I hI hc).1

  let S : IntermediateField ℚ ℂ := σ.toRatAlgHom.fieldRange
  let e : Fc ≃ₐ[ℚ] S := AlgEquiv.ofInjectiveField σ.toRatAlgHom
  have hS : ∀ x, j x ∈ S := fun x => by
    obtain ⟨y, hy⟩ := hjv x
    exact ⟨y, hy⟩
  let j' : L →+* S := j.codRestrict S hS
  let ψ : L →+* ℂ := (algebraMap Fc ℂ).comp (((e.symm : S ≃+* Fc) : S →+* Fc).comp j')
  have hψ : ψ.toRatAlgHom.fieldRange ≤ Fc := by
    rintro _ ⟨x, rfl⟩
    exact (e.symm (j' x)).2

  have hsq : ∃ a : D.host.K, a ^ 2 = -(Q.H.d : D.host.K) := by
    refine ⟨⟨D.host.sqrtMinusD, Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D⟩, ?_⟩
    rw [hP.1]
    apply Subtype.ext
    have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqrtMinusD_sq
    simpa using hb
  obtain ⟨hW, hrt⟩ := GlobalTheory.FieldSize.WeberTransport.weberIn_of_containsRayField D.host.E Q.H D.host.K L
    (algebraMap D.host.K L) ψ (Formalism.L2.Pj.LPb.finrank_K D) hsq N hN hC
  refine (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn D.host.E Q.H Fc N (by omega)).1 (hψ hrt) fun Λ hΛ => ?_
  obtain ⟨h1, h2⟩ := hW Λ hΛ
  exact ⟨hψ h1, fun s hs => hψ (h2 s hs)⟩

end GlobalTheory.TwistRat.Field
