import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
import Formalism.PeriodIntegrals.AdBridgeSteps

noncomputable section

namespace PI.BridgeMaxCptWork

open NumberField IsDedekindDomain Matrix
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

/- English proof (translation)
Establish `hd : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).mp hP`. Establish `hPi : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P hd`. Establish `hPi' : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P hd`. Establish `hH : Pᴴ * (P⁻¹)ᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul, hPi, Matrix.conjTranspose_one]`.

Establish `hH' : (P⁻¹)ᴴ * Pᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul, hPi', Matrix.conjTranspose_one]`. Establish `e1 : (P⁻¹ * θ * P)ᴴ * (P⁻¹ * θ * P) = Pᴴ * (θᴴ * ((P⁻¹)ᴴ * P⁻¹) * θ) * P`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[e1]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hH', hPi', Matrix.one_mul, Matrix.mul_one]`. Use `_ = (P⁻¹)ᴴ * (Pᴴ * (θᴴ * ((P⁻¹)ᴴ * P⁻¹) * θ) * P) * P⁻¹ := by`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = (P⁻¹)ᴴ * P⁻¹ := by rw [h, Matrix.mul_one]`. Introduce `h`. Rewrite using `[h, ← Matrix.mul_assoc, hH, Matrix.one_mul, hPi]`.
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
Establish `key : ∀ v, (x.1 v ∈ KinfV I v ↔ ((hmat I (e x)).map (thetaV I v))ᴴ * majV I v * (hmat I (e x)).map (thetaV I v) = majV I v)`. Introduce `v`. Establish `hu : uMat (x.1 v) = (I.P v)⁻¹ * (hmat I (e x)).map (thetaV I v) * I.P v` using `(hb x).1 v`. Establish `hP : IsUnit (I.P v)`. Assume the negation of the conclusion as `hP`.

Establish `h0 : (I.P v)⁻¹ = 0` using `Matrix.nonsing_inv_apply_not_isUnit _ (fun h => hP ((Matrix.isUnit_iff_isUnit_det _).mpr h))`. Establish `hU : IsUnit (uMat (x.1 v))` using `Units.isUnit _`. Rewrite `hU` using `[hu, h0, zero_mul, zero_mul]`. Use `haveI : Subsingleton (Matrix (Fin I.n) (Fin I.n) ℂ) := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hU)`. Conclude with `hP (by rw [Subsingleton.elim (I.P v) 1]; exact isUnit_one)`.

Establish `hk : Formalism.REAL.inUJ (I.ε v) (uMat (x.1 v))` using `(x.1 v).2`. Establish `h1` using `hR I.n (I.ε v) (uMat (x.1 v)) hk`. Combine the equalities or inequalities in the displayed calculation. Use `show (∀ v, x.1 v ∈ KinfV I v) ↔ ∀ v, ((hmat I (e x)).map (thetaV I v))ᴴ * majV I v * (hmat I (e x)).map (thetaV I v) = majV I v`. Conclude with `forall_congr' key`.
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
Establish `h` using `hF I (e x)`. Rewrite `h` using `[← (hb x).2]`. Conclude with `h`.
-/
theorem kf_iff (hF : PI.AdBridgeSteps.FinK) (I : AutInst) (e : I.GA ≃ₜ* HAd I)
    (hb : IsBridge I e) (x : I.GA) : x.2 ∈ I.Kset ↔ e x ∈ KfHA I := by
  have h := hF I (e x)
  rw [← (hb x).2] at h
  exact h

/- English proof (translation)
Use `show ((∀ v, x.1 v ∈ KinfV I v) ∧ x.2 ∈ I.Kset) ↔ (e x ∈ KinfHA I ∧ e x ∈ KfHA I)`. Conclude with `and_congr (kinf_iff hR I e hb x) (kf_iff hF I e hb x)`.
-/
theorem mem_KGA_iff (hR : PI.AdBridgeSteps.RealK) (hF : PI.AdBridgeSteps.FinK) (I : AutInst)
    (e : I.GA ≃ₜ* HAd I) (hb : IsBridge I e) (x : I.GA) : x ∈ KGA I ↔ e x ∈ KHA I := by
  show ((∀ v, x.1 v ∈ KinfV I v) ∧ x.2 ∈ I.Kset) ↔ (e x ∈ KinfHA I ∧ e x ∈ KfHA I)
  exact and_congr (kinf_iff hR I e hb x) (kf_iff hF I e hb x)

/- English proof (translation)
Introduce `I e hb`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `(mem_KGA_iff hR hF I e hb x).1 hx`.

Introduce `hy`. Use `⟨e.symm y, (mem_KGA_iff hR hF I e hb _).2 ?_, by simp⟩` and prove the remaining obligations. Simplify using `using hy`.
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
