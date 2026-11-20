import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

open NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open GlobalTheory.CuspRep Formalism.L2.Host

namespace GlobalTheory.ConjDualTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {m : ℕ}

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem opTriv_thetaOp (o : Op E m) : opTriv (thetaOp o) = opTriv o := by
  cases o <;> rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem act_mulChi_oneFn (ψ : HChar E) (o : Op E m) :
    act o (mulChi m ψ (oneFn E m)) = (((opMul ψ o : ℂˣ) : ℂ) * opTriv o + opAdd ψ o) • mulChi m ψ (oneFn E m) := by
  rw [act_mulChi, act_oneFn, smul_smul, ← add_smul, map_smul]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pull_oneFn : GlobalTheory.ThetaPull.pull E m (oneFn E m) = oneFn E m := Subtype.ext rfl

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem scalar_thetaOp (χ : HChar E) (o : Op E m) :
    ((opMul χ (thetaOp o) : ℂˣ) : ℂ) * opTriv o + opAdd χ (thetaOp o) =
      ((opMul (GlobalTheory.ThetaPull.thetaChar χ) o : ℂˣ) : ℂ) * opTriv o + opAdd (GlobalTheory.ThetaPull.thetaChar χ) o := by
  have h1 := GlobalTheory.ThetaPull.act_pull o (mulChi m χ (oneFn E m))
  simp only [act_mulChi_oneFn, map_smul, GlobalTheory.ThetaPull.pull_mulChi, pull_oneFn, opTriv_thetaOp] at h1
  have hF : mulChi m (GlobalTheory.ThetaPull.thetaChar χ) (oneFn E m) ≠ 0 :=
    (LinearEquiv.map_ne_zero_iff _).2 oneFn_ne_zero
  exact (smul_left_injective ℂ hF h1).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Treat this case separately.
-/
theorem isConjDualBy_twist_thetaChar : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {m : ℕ} {π : GlobalTheory.CuspRep.CuspSub E m}, π.IsCsd → ∀ χ : Formalism.L2.Host.HChar E, GlobalTheory.GalOfCusp.IsConjDualBy (π.twist χ) (χ * (GlobalTheory.ThetaPull.thetaChar χ)⁻¹) := by
  intro E _ _ _ m π hπ χ
  refine GlobalTheory.GalOfCusp.isConjDualBy_twist hπ fun o => ?_
  have e : χ * (χ * (GlobalTheory.ThetaPull.thetaChar χ)⁻¹)⁻¹ = GlobalTheory.ThetaPull.thetaChar χ := by
    rw [mul_inv_rev, inv_inv, mul_comm (GlobalTheory.ThetaPull.thetaChar χ), ← mul_assoc, mul_inv_cancel, one_mul]
  rw [e]
  have h := scalar_thetaOp χ o
  cases o with
  | fin k => exact ⟨Units.ext (by simpa [opTriv, opAdd, thetaOp] using h), rfl⟩
  | cpt k => exact ⟨Units.ext (by simpa [opTriv, opAdd, thetaOp] using h), rfl⟩
  | lie X => exact ⟨rfl, by simpa [opTriv, opMul, thetaOp] using h⟩

end GlobalTheory.ConjDualTwist

end
