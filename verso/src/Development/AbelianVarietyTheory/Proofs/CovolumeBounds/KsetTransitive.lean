import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FrameIsotropicOrthonormal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MaximalCompactSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsUnitaryOfGramEq
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsQr
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi

/- English proof (translation)
Establish `hinj : Function.Injective A.mulVec`. Introduce `x y hxy`. Establish `h2` using `congrArg L.mulVec hxy`. Simplify `h2` using `[Matrix.mulVec_mulVec, h]`. Establish `hp : (Aᴴ * A).PosDef` using `Matrix.PosDef.conjTranspose_mul_self A hinj`.

Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit`.
-/
theorem isUnit_det_gram_of_leftInverse {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (L : Matrix (Fin m) (Fin n) ℂ)
    (h : L * A = 1) : IsUnit (Aᴴ * A).det := by
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have h2 := congrArg L.mulVec hxy
    simpa [Matrix.mulVec_mulVec, h] using h2
  have hp : (Aᴴ * A).PosDef := Matrix.PosDef.conjTranspose_mul_self A hinj
  exact (Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit

/- English proof (translation)
Use `set P : Matrix (Fin n) (Fin n) ℂ := (2⁻¹ : ℂ) • (1 + H) with hP`. Establish `hPh : Pᴴ = P`. Simplify using `[hP, conjTranspose_smul, conjTranspose_add, hH]`. Establish `hPP : P * P = P`. Simplify using `only [hP, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, one_mul, mul_one, hHH]`.

Use `module`. Establish `hHP : H = (2 : ℂ) • P - 1`. Simplify using `only [hP]`. Use `module`. Establish `hG : Aᴴ * P * A = Bᴴ * P * B`.

Simplify using `only [hP, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1, h2]`. Use `clear_value P`. Establish `hQh : (1 - P)ᴴ = 1 - P` using `by simp [hPh]`. Establish `hQQ : (1 - P) * (1 - P) = 1 - P`. Simplify using `only [mul_sub, sub_mul, one_mul, mul_one, hPP, sub_self, sub_zero]`.

Establish `hG' : Aᴴ * (1 - P) * A = Bᴴ * (1 - P) * B`. Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, hG]`. Establish `key : ∀ E : Matrix (Fin n) (Fin n) ℂ, Eᴴ = E → E * E = E → Aᴴ * E * A = Bᴴ * E * B → ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * E = E * U ∧ U * (1 - E) = 1 - E ∧ U * (E * A) = E * B`. Introduce `E hE hEE hg`. Establish `e : ∀ C : Matrix (Fin n) (Fin m) ℂ, (E * C)ᴴ * (E * C) = Cᴴ * E * C`.

Introduce `C`. Rewrite using `[conjTranspose_mul, hE, Matrix.mul_assoc, ← Matrix.mul_assoc E E, hEE, Matrix.mul_assoc]`. Use `GlobalTheory.UnitaryExtension.exists_unitary_of_gram_eq n m E (E * A) (E * B) hE hEE ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← Matrix.mul_assoc, hEE]`. Rewrite using `[← Matrix.mul_assoc, hEE]`.

Rewrite using `[e, e, hg]`. Take `⟨U, hU1, hU2, hU3, hU4⟩` from `key P hPh hPP hG`. Take `⟨V, hV1, hV2, hV3, hV4⟩` from `key (1 - P) hQh hQQ hG'`. Rewrite `hV3` using `[sub_sub_cancel]`. Establish `hV5 : V * P = P * V`.

Use `hV2` as an intermediate fact. Simplify using `only [mul_sub, sub_mul, one_mul, mul_one] at this`. Conclude with `sub_right_injective this`. Use `⟨U * V, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU1, Matrix.one_mul, hV1]`.

Establish `: U * V * P = P * (U * V)`. Rewrite using `[mul_assoc, hV5, ← mul_assoc, hU2, mul_assoc]`. Rewrite using `[hHP]`. Simplify using `only [mul_sub, sub_mul, one_mul, mul_one, mul_smul_comm, smul_mul_assoc, this]`. Establish `hA : A = P * A + (1 - P) * A`.

Rewrite using `[← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]`. Establish `hB : B = P * B + (1 - P) * B`. Rewrite using `[← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_add, hV4, ← Matrix.mul_assoc V P, hV3]`.

Use `_ = P * B + (1 - P) * B := by`. Rewrite using `[Matrix.mul_add, hU4, ← Matrix.mul_assoc U (1 - P), hU3]`. Use `_ = B := hB.symm`.
-/
theorem Iwasawa.exists_unitary_comm {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (A B : Matrix (Fin n) (Fin m) ℂ) (h1 : Aᴴ * A = Bᴴ * B) (h2 : Aᴴ * H * A = Bᴴ * H * B) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * H = H * U ∧ U * A = B := by
  set P : Matrix (Fin n) (Fin n) ℂ := (2⁻¹ : ℂ) • (1 + H) with hP
  have hPh : Pᴴ = P := by
    simp [hP, conjTranspose_smul, conjTranspose_add, hH]
  have hPP : P * P = P := by
    simp only [hP, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, one_mul, mul_one, hHH]
    module
  have hHP : H = (2 : ℂ) • P - 1 := by
    simp only [hP]
    module
  have hG : Aᴴ * P * A = Bᴴ * P * B := by
    simp only [hP, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1, h2]
  clear_value P
  have hQh : (1 - P)ᴴ = 1 - P := by simp [hPh]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    simp only [mul_sub, sub_mul, one_mul, mul_one, hPP, sub_self, sub_zero]
  have hG' : Aᴴ * (1 - P) * A = Bᴴ * (1 - P) * B := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, hG]
  have key : ∀ E : Matrix (Fin n) (Fin n) ℂ, Eᴴ = E → E * E = E → Aᴴ * E * A = Bᴴ * E * B →
      ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * E = E * U ∧ U * (1 - E) = 1 - E ∧ U * (E * A) = E * B := by
    intro E hE hEE hg
    have e : ∀ C : Matrix (Fin n) (Fin m) ℂ, (E * C)ᴴ * (E * C) = Cᴴ * E * C := by
      intro C
      rw [conjTranspose_mul, hE, Matrix.mul_assoc, ← Matrix.mul_assoc E E, hEE, Matrix.mul_assoc]
    refine GlobalTheory.UnitaryExtension.exists_unitary_of_gram_eq n m E (E * A) (E * B) hE hEE ?_ ?_ ?_
    · rw [← Matrix.mul_assoc, hEE]
    · rw [← Matrix.mul_assoc, hEE]
    · rw [e, e, hg]
  obtain ⟨U, hU1, hU2, hU3, hU4⟩ := key P hPh hPP hG
  obtain ⟨V, hV1, hV2, hV3, hV4⟩ := key (1 - P) hQh hQQ hG'
  rw [sub_sub_cancel] at hV3
  have hV5 : V * P = P * V := by
    have := hV2
    simp only [mul_sub, sub_mul, one_mul, mul_one] at this
    exact sub_right_injective this
  refine ⟨U * V, ?_, ?_, ?_⟩
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU1, Matrix.one_mul, hV1]
  · have : U * V * P = P * (U * V) := by
      rw [mul_assoc, hV5, ← mul_assoc, hU2, mul_assoc]
    rw [hHP]
    simp only [mul_sub, sub_mul, one_mul, mul_one, mul_smul_comm, smul_mul_assoc, this]
  · have hA : A = P * A + (1 - P) * A := by
      rw [← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
    have hB : B = P * B + (1 - P) * B := by
      rw [← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
    calc U * V * A = U * (V * (P * A + (1 - P) * A)) := by rw [← hA, Matrix.mul_assoc]
      _ = U * (P * A + (1 - P) * B) := by
        rw [Matrix.mul_add, hV4, ← Matrix.mul_assoc V P, hV3]
      _ = P * B + (1 - P) * B := by
        rw [Matrix.mul_add, hU4, ← Matrix.mul_assoc U (1 - P), hU3]
      _ = B := hB.symm

/- English proof (translation)
Introduce `k r m A B h1 h2`. Establish `hF` using `Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r`. Take `⟨U, hU1, hU2, hU3⟩` from `Iwasawa.exists_unitary_comm (Hpk k r) hF.1 hF.2.1 A B h1 h2`. Use `⟨U, ⟨?_, hU1⟩, hU3⟩` and prove the remaining obligations. Use `show Uᴴ * Hpk k r * U = Hpk k r`.

Rewrite using `[Matrix.mul_assoc, ← hU2, ← Matrix.mul_assoc, hU1, Matrix.one_mul]`.
-/
theorem Iwasawa.kset_transitive : ∀ (k r m : ℕ) (A B : Matrix (Fin (2 * r + k + 1)) (Fin m) ℂ),
    Aᴴ * A = Bᴴ * B → Aᴴ * Hpk k r * A = Bᴴ * Hpk k r * B → ∃ κ ∈ Kset k r, κ * A = B := by
  intro k r m A B h1 h2
  have hF := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  obtain ⟨U, hU1, hU2, hU3⟩ := Iwasawa.exists_unitary_comm (Hpk k r) hF.1 hF.2.1 A B h1 h2
  refine ⟨U, ⟨?_, hU1⟩, hU3⟩
  show Uᴴ * Hpk k r * U = Hpk k r
  rw [Matrix.mul_assoc, ← hU2, ← Matrix.mul_assoc, hU1, Matrix.one_mul]

/- English proof (translation)
Introduce `k r hk g hg`. Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Take `⟨hF1, hF0⟩` from `FrameOrth.frame_orthonormal_isotropic k r hk`. Take `⟨-, -, hH, hK, -⟩` from `KGroup.kset_facts k r`. Establish `hHH : (Hpk k r)ᴴ * Hpk k r = 1` using `hH.2`.

Establish `hL : ((frame k r)ᴴ * (Hpk k r)ᴴ * gᴴ * Hpk k r) * (g * frame k r) = 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hg', hHH, Matrix.mul_one, hF1]`. Take `⟨Q, u, hQ, hu, hud, hA⟩` from `GlobalTheory.QRDecomp.exists_qr _ _ (g * frame k r) (isUnit_det_gram_of_leftInverse _ _ hL)`.

Establish `hQA : Q = g * frame k r * u⁻¹`. Rewrite using `[hA, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hud, Matrix.mul_one]`. Establish `hQ0 : Qᴴ * Hpk k r * Q = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hQA]`.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = 0 := by rw [hg', hF0, Matrix.mul_zero, Matrix.zero_mul]`. Take `⟨κ, hκ, hκF⟩` from `Iwasawa.kset_transitive k r (r + 1) (frame k r) Q (by rw [hF1, hQ]) (by rw [hF0, hQ0])`. Establish `hκ1 : κᴴ * κ = 1` using `hκ.2`. Establish `hκ2 : κ * κᴴ = 1` using `mul_eq_one_comm.1 hκ1`.

Establish `hκs : κᴴᴴ * Hpk k r * κᴴ = Hpk k r` using `(hK κ hκ).1.1`. Use `⟨κ, hκ, κᴴ * g, ⟨?_, u, hu, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show (κᴴ * g)ᴴ * Hpk k r * (κᴴ * g) = Hpk k r`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = Hpk k r := by rw [hκs, hg']`. Rewrite using `[Matrix.mul_assoc, hA, ← hκF, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hκ1, Matrix.one_mul]`. Rewrite using `[← Matrix.mul_assoc, hκ2, Matrix.one_mul]`.
-/
theorem iwasawa : ∀ k r : ℕ, 1 ≤ k → ∀ g ∈ GV k r, ∃ κ ∈ Kset k r, ∃ p ∈ Pset k r, g = κ * p := by
  intro k r hk g hg
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  obtain ⟨hF1, hF0⟩ := FrameOrth.frame_orthonormal_isotropic k r hk
  obtain ⟨-, -, hH, hK, -⟩ := KGroup.kset_facts k r
  have hHH : (Hpk k r)ᴴ * Hpk k r = 1 := hH.2
  have hL : ((frame k r)ᴴ * (Hpk k r)ᴴ * gᴴ * Hpk k r) * (g * frame k r) = 1 := by
    calc ((frame k r)ᴴ * (Hpk k r)ᴴ * gᴴ * Hpk k r) * (g * frame k r)
        = (frame k r)ᴴ * ((Hpk k r)ᴴ * (gᴴ * Hpk k r * g)) * frame k r := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hHH, Matrix.mul_one, hF1]
  obtain ⟨Q, u, hQ, hu, hud, hA⟩ := GlobalTheory.QRDecomp.exists_qr _ _ (g * frame k r)
    (isUnit_det_gram_of_leftInverse _ _ hL)
  have hQA : Q = g * frame k r * u⁻¹ := by
    rw [hA, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hud, Matrix.mul_one]
  have hQ0 : Qᴴ * Hpk k r * Q = 0 := by
    calc Qᴴ * Hpk k r * Q
        = (u⁻¹)ᴴ * ((frame k r)ᴴ * (gᴴ * Hpk k r * g) * frame k r) * u⁻¹ := by
          rw [hQA]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hg', hF0, Matrix.mul_zero, Matrix.zero_mul]
  obtain ⟨κ, hκ, hκF⟩ := Iwasawa.kset_transitive k r (r + 1) (frame k r) Q (by rw [hF1, hQ]) (by rw [hF0, hQ0])
  have hκ1 : κᴴ * κ = 1 := hκ.2
  have hκ2 : κ * κᴴ = 1 := mul_eq_one_comm.1 hκ1
  have hκs : κᴴᴴ * Hpk k r * κᴴ = Hpk k r := (hK κ hκ).1.1
  refine ⟨κ, hκ, κᴴ * g, ⟨?_, u, hu, ?_⟩, ?_⟩
  · show (κᴴ * g)ᴴ * Hpk k r * (κᴴ * g) = Hpk k r
    calc (κᴴ * g)ᴴ * Hpk k r * (κᴴ * g) = gᴴ * (κᴴᴴ * Hpk k r * κᴴ) * g := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [hκs, hg']
  · rw [Matrix.mul_assoc, hA, ← hκF, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hκ1, Matrix.one_mul]
  · rw [← Matrix.mul_assoc, hκ2, Matrix.one_mul]

end GlobalTheory.HCXi
