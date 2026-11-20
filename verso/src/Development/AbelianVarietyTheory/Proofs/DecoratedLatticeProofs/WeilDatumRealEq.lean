import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdeleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsStdIsVacVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeLeRealSymplecticPairingSum
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealEqWeil

/- English proof (translation)
Introduce `D ψ S T χS χT χS' χT' om om' hW hW' hS hT a ha b hb f hf`. Take `⟨θ, hθ⟩` from `GlobalTheory.DualPairCompare.exists_infFam D`. Establish `eS : ∀ τ, HasInfExp D (χS' * χS⁻¹) τ ((0 : ℤ) : ℚ)` using `fun τ => by`. Take `⟨e, h1, h2⟩` from `hS τ`. Simplify using `using GlobalTheory.Chain.hasInfExp_div h2 h1`.

Establish `eT : ∀ τ, HasInfExp D (χT' * χT⁻¹) τ ((0 : ℤ) : ℚ)` using `fun τ => by`. Take `⟨e, h1, h2⟩` from `hT τ`. Simplify using `using GlobalTheory.Chain.hasInfExp_div h2 h1`. Take `⟨om'', hW'', hmv⟩` from `GlobalTheory.WeilChange.exists_weilDatum_twist D ψ hW.std S T χS χT (χS' * χS⁻¹) (χT' * χT⁻¹) om hW (GlobalTheory.WeilVacChar.hecke_mul_inv hW'.hecS hW.hecS) (GlobalTheory.WeilVacChar.hecke_mul_inv hW'.hecT hW.hecT) (GlobalTheory.WeilVacChar.resEta_mul_inv hW'.resS hW.resS) (Glob …`. Rewrite `hW''` using `[GlobalTheory.WeilVacChar.mul_mul_inv_cancel, GlobalTheory.WeilVacChar.mul_mul_inv_cancel]`.

Take `⟨x, hx, hxv⟩` from `GlobalTheory.OneMapRef.RealMove.exists_root hθ S (GlobalTheory.RealPairBound.gramAt_det_ne D S) a ha`. Take `⟨y, hy, hyv⟩` from `GlobalTheory.OneMapRef.RealMove.exists_root hθ T (GlobalTheory.RealPairBound.gramAt_det_ne D T) b hb`. Establish `x1 : (χT' * χT⁻¹) x = 1`. Apply `Circle.coe_injective` to reduce the goal to its premises. Rewrite using `[hxv _ (fun _ => 0) eT]`.

Simplify using the standard rewrite rules. Establish `y1 : (χS' * χS⁻¹) y = 1`. Apply `Circle.coe_injective` to reduce the goal to its premises. Rewrite using `[hyv _ (fun _ => 0) eS]`. Simplify using the standard rewrite rules.

Establish `h1` using `hmv a b x y hx hy`. Rewrite `h1` using `[x1, y1, inv_one, one_mul, Circle.coe_one, one_smul]`. Rewrite using `[← h1]`. Conclude with `GlobalTheory.WeilUniq.weilDatum_unique D ψ hW.std S T χS' χT' om'' om' hW'' hW' (a, b) f hf`.
-/
theorem weilDatum_realEq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om om' : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om' → (∀ τ, ∃ e : ℚ, HasInfExp D χS τ e ∧ HasInfExp D χS' τ e) → (∀ τ, ∃ e : ℚ, HasInfExp D χT τ e ∧ HasInfExp D χT' τ e) → ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ f, IsThetaFunO ψ S T f → om (a, b) f = om' (a, b) f := by
  intro D ψ S T χS χT χS' χT' om om' hW hW' hS hT a ha b hb f hf
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D

  have eS : ∀ τ, HasInfExp D (χS' * χS⁻¹) τ ((0 : ℤ) : ℚ) := fun τ => by
    obtain ⟨e, h1, h2⟩ := hS τ
    simpa using GlobalTheory.Chain.hasInfExp_div h2 h1
  have eT : ∀ τ, HasInfExp D (χT' * χT⁻¹) τ ((0 : ℤ) : ℚ) := fun τ => by
    obtain ⟨e, h1, h2⟩ := hT τ
    simpa using GlobalTheory.Chain.hasInfExp_div h2 h1
  obtain ⟨om'', hW'', hmv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ hW.std S T χS χT (χS' * χS⁻¹) (χT' * χT⁻¹) om hW
    (GlobalTheory.WeilVacChar.hecke_mul_inv hW'.hecS hW.hecS) (GlobalTheory.WeilVacChar.hecke_mul_inv hW'.hecT hW.hecT)
    (GlobalTheory.WeilVacChar.resEta_mul_inv hW'.resS hW.resS) (GlobalTheory.WeilVacChar.resEta_mul_inv hW'.resT hW.resT)
  rw [GlobalTheory.WeilVacChar.mul_mul_inv_cancel, GlobalTheory.WeilVacChar.mul_mul_inv_cancel] at hW''
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ S (GlobalTheory.RealPairBound.gramAt_det_ne D S) a ha
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ T (GlobalTheory.RealPairBound.gramAt_det_ne D T) b hb
  have x1 : (χT' * χT⁻¹) x = 1 := by
    apply Circle.coe_injective
    rw [hxv _ (fun _ => 0) eT]
    simp
  have y1 : (χS' * χS⁻¹) y = 1 := by
    apply Circle.coe_injective
    rw [hyv _ (fun _ => 0) eS]
    simp
  have h1 := hmv a b x y hx hy
  rw [x1, y1, inv_one, one_mul, Circle.coe_one, one_smul] at h1
  rw [← h1]
  exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hW.std S T χS' χT' om'' om' hW'' hW' (a, b) f hf

end GlobalTheory.RealEqWeil
