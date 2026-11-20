import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPolyRadialCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThtFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDtrSIo

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

namespace FS

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} {ζ : ℂ}

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem stabilizer_fixes_first_vector (hz : inWb k r z) (hT : 0 < Tz k r z) {p : Q.Mx k r × Q.Mx k r}
    (hp : p ∈ NF.Stab k r z z' μsec ζ) :
    p.1 *ᵥ SSn.nu0 k r z z' μsec ζ = SSn.nu0 k r z z' μsec ζ := by
  obtain ⟨ha, hb, hab⟩ := hp
  have e : p.1 *ᵥ (NF.muZ k r μsec ζ *ᵥ z') = NF.muZ k r μsec ζ *ᵥ z' := by
    conv_rhs => rw [← hab, ← Matrix.mulVec_mulVec, hb.2.2, ← Matrix.mulVec_mulVec]
  unfold SSn.nu0 SSn.unitH
  rw [Matrix.mulVec_smul, ← TF.prWv_uw hz hT ha, e]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem nu0'_fix (hz' : inWb k r z') (hT' : 0 < Tz k r z') {p : Q.Mx k r × Q.Mx k r}
    (hp : p ∈ NF.Stab k r z z' μsec ζ) :
    p.2⁻¹ *ᵥ SSn.nu0' k r z z' μsec ζ = SSn.nu0' k r z z' μsec ζ := by
  obtain ⟨ha, hb, hab⟩ := hp
  have hai := P.LieBracketMultiplication.uw_inv ha
  have hbi := P.LieBracketMultiplication.uw_inv hb
  have h1 : (NF.muZ k r μsec ζ)⁻¹ = p.2⁻¹ * ((NF.muZ k r μsec ζ)⁻¹ * p.1⁻¹) := by
    conv_lhs => rw [← hab, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have e : p.2⁻¹ *ᵥ ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) = (NF.muZ k r μsec ζ)⁻¹ *ᵥ z := by
    conv_rhs => rw [h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hai.2.2]
  unfold SSn.nu0' SSn.unitH
  rw [Matrix.mulVec_smul, ← TF.prWv_uw hz' hT' hbi, e]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nu0'_fix' (hz' : inWb k r z') (hT' : 0 < Tz k r z') {p : Q.Mx k r × Q.Mx k r}
    (hp : p ∈ NF.Stab k r z z' μsec ζ) :
    p.2 *ᵥ SSn.nu0' k r z z' μsec ζ = SSn.nu0' k r z z' μsec ζ := by
  conv_lhs => rw [← nu0'_fix hz' hT' hp, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hp.2.1.1), Matrix.one_mulVec]

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem stabilizer_fixes_section_embedding (hz' : inWb k r z') (hT' : 0 < Tz k r z') {p : Q.Mx k r × Q.Mx k r}
    (hp : p ∈ NF.Stab k r z z' μsec ζ) :
    p.1 * SSn.io0 k r z z' μsec ζ * p.2 = SSn.io0 k r z z' μsec ζ := by
  have hν := nu0'_fix' hz' hT' hp
  obtain ⟨ha, hb, hab⟩ := hp
  have key : ∀ v : Fin (2 * r + k + 1) → ℂ,
      (p.1 * SSn.io0 k r z z' μsec ζ * p.2) *ᵥ v = SSn.io0 k r z z' μsec ζ *ᵥ v := by
    intro v
    have hh : herm (Hpk k r) (p.2 *ᵥ SSn.prWv k r z' v) (SSn.nu0' k r z z' μsec ζ) =
        herm (Hpk k r) (SSn.prWv k r z' v) (SSn.nu0' k r z z' μsec ζ) := by
      calc herm (Hpk k r) (p.2 *ᵥ SSn.prWv k r z' v) (SSn.nu0' k r z z' μsec ζ)
          = herm (Hpk k r) (p.2 *ᵥ SSn.prWv k r z' v) (p.2 *ᵥ SSn.nu0' k r z z' μsec ζ) := by rw [hν]
        _ = _ := P.Qx2.herm_uh hb.1 _ _
    have hk : SSn.prWv k r z' (p.2 *ᵥ v) -
          herm (Hpk k r) (SSn.prWv k r z' (p.2 *ᵥ v)) (SSn.nu0' k r z z' μsec ζ) • SSn.nu0' k r z z' μsec ζ =
        p.2 *ᵥ (SSn.prWv k r z' v -
          herm (Hpk k r) (SSn.prWv k r z' v) (SSn.nu0' k r z z' μsec ζ) • SSn.nu0' k r z z' μsec ζ) := by
      rw [TF.prWv_uw hz' hT' hb, Matrix.mulVec_sub, Matrix.mulVec_smul, hν, hh]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, MC.DT.ioMulVec, MC.DT.ioMulVec, hk, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hab]
  exact Matrix.ext_of_mulVec_single fun i => key _

end FS

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem fibre_stability_holds : FibStable := by
  intro Wp Wq _ _ _ _ _ _ P Bs hPl hk Pr hPr Bw Bw' hBw hBw' ζ hζ Xf hX ρ
  obtain ⟨hOK, hz, hz', hTe, hTe', hty, hty'⟩ := hPl
  have hT : 0 < Tz P.k P.r Bs.z := Bs.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := Bs.T'_pos
  have hR : Qr.IsRepW P.k P.r Bs.z Bs.π := ⟨hty.2.1, hty.2.2.1⟩
  have hR' : Qr.IsRepW P.k P.r Bs.z' Bs.π' := ⟨hty'.2.1, hty'.2.2.1⟩
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · have hx := hX p hp
    have e1 := hPr.2.1 p.1 hp.1 ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
    rw [FS.stabilizer_fixes_first_vector hz hT hp] at e1
    conv_rhs => rw [e1, ← hx]
    ext x
    simp only [ContinuousLinearMap.comp_apply, TF.rep_inv_cancel hR hp.1]
  · have hbi := Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv hp.2.1
    have hbb : (p.2⁻¹)⁻¹ = p.2 := Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hp.2.1.1)
    have e := TF.tht_eqv hz hT hR hz' hT' hR' hBw hBw' hp.1 hbi (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
      (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf
    rw [hbb, FS.stabilizer_fixes_first_vector hz hT hp, FS.nu0'_fix hz' hT' hp, FS.stabilizer_fixes_section_embedding hz' hT' hp, hX p hp] at e
    exact e.symm

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
