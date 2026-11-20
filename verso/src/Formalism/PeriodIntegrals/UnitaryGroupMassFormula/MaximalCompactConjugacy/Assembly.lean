import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
import Formalism.PeriodIntegrals.AdBridgeSteps

noncomputable section

namespace PI.BridgeMaxCptWork

open NumberField IsDedekindDomain Matrix
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem conj_unitary_iff {n : ℕ} (P θ : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) :
    ((P⁻¹ * θ * P)ᴴ * (P⁻¹ * θ * P) = 1) ↔
      θᴴ * ((P⁻¹)ᴴ * P⁻¹) * θ = (P⁻¹)ᴴ * P⁻¹ := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPi : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have hPi' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have hH : Pᴴ * (P⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hPi, Matrix.conjTranspose_one]
  have hH' : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hPi', Matrix.conjTranspose_one]
  have e1 : (P⁻¹ * θ * P)ᴴ * (P⁻¹ * θ * P) = Pᴴ * (θᴴ * ((P⁻¹)ᴴ * P⁻¹) * θ) * P := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e1]
  constructor
  · intro h
    calc θᴴ * ((P⁻¹)ᴴ * P⁻¹) * θ
        = (P⁻¹)ᴴ * Pᴴ * (θᴴ * ((P⁻¹)ᴴ * P⁻¹) * θ) * (P * P⁻¹) := by
          rw [hH', hPi', Matrix.one_mul, Matrix.mul_one]
      _ = (P⁻¹)ᴴ * (Pᴴ * (θᴴ * ((P⁻¹)ᴴ * P⁻¹) * θ) * P) * P⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * P⁻¹ := by rw [h, Matrix.mul_one]
  · intro h
    rw [h, ← Matrix.mul_assoc, hH, Matrix.one_mul, hPi]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem kinf_iff (hR : PI.AdBridgeSteps.RealK) (I : AutInst) (e : I.GA ≃ₜ* HAd I)
    (hb : IsBridge I e) (x : I.GA) : (∀ v, x.1 v ∈ KinfV I v) ↔ e x ∈ KinfHA I := by
  have key : ∀ v, (x.1 v ∈ KinfV I v ↔
      ((hmat I (e x)).map (thetaV I v))ᴴ * majV I v * (hmat I (e x)).map (thetaV I v) =
        majV I v) := by
    intro v
    have hu : uMat (x.1 v) = (I.P v)⁻¹ * (hmat I (e x)).map (thetaV I v) * I.P v := (hb x).1 v
    have hP : IsUnit (I.P v) := by
      by_contra hP
      have h0 : (I.P v)⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _
        (fun h => hP ((Matrix.isUnit_iff_isUnit_det _).mpr h))
      have hU : IsUnit (uMat (x.1 v)) := Units.isUnit _
      rw [hu, h0, zero_mul, zero_mul] at hU
      haveI : Subsingleton (Matrix (Fin I.n) (Fin I.n) ℂ) :=
        subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hU)
      exact hP (by rw [Subsingleton.elim (I.P v) 1]; exact isUnit_one)
    have hk : Formalism.REAL.inUJ (I.ε v) (uMat (x.1 v)) := (x.1 v).2
    have h1 := hR I.n (I.ε v) (uMat (x.1 v)) hk
    calc x.1 v ∈ KinfV I v ↔ (uMat (x.1 v))ᴴ * uMat (x.1 v) = 1 := h1.symm
      _ ↔ _ := by rw [hu]; exact conj_unitary_iff _ _ hP
  show (∀ v, x.1 v ∈ KinfV I v) ↔ ∀ v, ((hmat I (e x)).map (thetaV I v))ᴴ * majV I v *
    (hmat I (e x)).map (thetaV I v) = majV I v
  exact forall_congr' key

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem kf_iff (hF : PI.AdBridgeSteps.FinK) (I : AutInst) (e : I.GA ≃ₜ* HAd I)
    (hb : IsBridge I e) (x : I.GA) : x.2 ∈ I.Kset ↔ e x ∈ KfHA I := by
  have h := hF I (e x)
  rw [← (hb x).2] at h
  exact h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mem_KGA_iff (hR : PI.AdBridgeSteps.RealK) (hF : PI.AdBridgeSteps.FinK) (I : AutInst)
    (e : I.GA ≃ₜ* HAd I) (hb : IsBridge I e) (x : I.GA) : x ∈ KGA I ↔ e x ∈ KHA I := by
  show ((∀ v, x.1 v ∈ KinfV I v) ∧ x.2 ∈ I.Kset) ↔ (e x ∈ KinfHA I ∧ e x ∈ KfHA I)
  exact and_congr (kinf_iff hR I e hb x) (kf_iff hF I e hb x)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem bridgeMaxCpt_of (hR : PI.AdBridgeSteps.RealK) (hF : PI.AdBridgeSteps.FinK) :
    ∀ I : AutInst, AdBridgeK I := by
  intro I e hb
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_KGA_iff hR hF I e hb x).1 hx
  · intro hy
    refine ⟨e.symm y, (mem_KGA_iff hR hF I e hb _).2 ?_, by simp⟩
    simpa using hy

end PI.BridgeMaxCptWork
