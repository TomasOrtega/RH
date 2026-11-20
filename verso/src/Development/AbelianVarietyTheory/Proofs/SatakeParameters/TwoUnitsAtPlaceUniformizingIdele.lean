import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterUniformizingIdeleMemCoeffFieldStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteNormalisingCharPowValuesInCoeffFieldStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLambdaCharacterNormOneIdeleEqPPowStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SystemWeightsEqShiftedCharacterExponentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersCharOnNormOneIdelesMulUnramifiedClassValueStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiAlgUnitInert
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiAMemRange
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.VEqKZeroOfNormOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplAlgLocAt
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.TwoUnits

/- English proof (translation)
Rewrite using `[mem_algebraicClosure_iff']`. Conclude with `(Algebra.IsIntegral.isIntegral z).map D.what₂.embLL.toRatAlgHom`.
-/
theorem embLL_mem (D : D7) (z : D.what₂.LL) : D.what₂.embLL z ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral z).map D.what₂.embLL.toRatAlgHom

/- English proof (translation)
Rewrite using `[Formalism.L2.Ker.lamC_of_mem lam (zpow_mem hx n), Formalism.L2.Ker.lamC_of_mem lam hx, ← map_zpow₀]`. Use `congr 1`.
-/
theorem lamC_zpow {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (n : ℤ) :
    TaylorLogMetric.lamC lam (x ^ n) = TaylorLogMetric.lamC lam x ^ n := by
  rw [Formalism.L2.Ker.lamC_of_mem lam (zpow_mem hx n), Formalism.L2.Ker.lamC_of_mem lam hx, ← map_zpow₀]
  congr 1

/- English proof (translation)
Rewrite using `[Formalism.L2.Ker.lamC_of_mem lam (inv_mem hx), Formalism.L2.Ker.lamC_of_mem lam hx, ← map_inv₀]`. Both sides reduce to the same expression.
-/
theorem lamC_inv {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam x⁻¹ = (TaylorLogMetric.lamC lam x)⁻¹ := by
  rw [Formalism.L2.Ker.lamC_of_mem lam (inv_mem hx), Formalism.L2.Ker.lamC_of_mem lam hx, ← map_inv₀]
  rfl

end GlobalTheory.TwV.Xc.TwoUnits

open GlobalTheory.TwV.Xc.TwoUnits in
set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS hKIn hPos v π hπ j hj hcj hcj1`. Establish `hπU : π ∈ U1 (sigD D)` using `hπ.1`. Take `⟨rm, hrm⟩` from `GlobalTheory.T.stepCharacter_uniformizingIdele_mem_coeffField S hD hS hKIn v π hπ j hj`. Take `⟨ra, hra⟩` from `GlobalTheory.T.kernelSite_normalisingCharPow_values_in_coeffField S hD hS j hj.le hcj π hπU`. Take `⟨rb, hrb⟩` from `GlobalTheory.T.kernelSite_normalisingCharPow_values_in_coeffField S hD hS (j + 1) hj hcj1 π hπU`.

Establish `hfill` using `GlobalTheory.T.systemWeights_eq_shifted_character_exponents S hD hS j hj hcj1`. Establish `hnorm` using `GlobalTheory.T.norm_lambdaCharacter_normOne_idele_eq_p_pow S hD hS hPos j hj hfill π hπU`. Establish `hord : ∀ v' : (sysS H X std).Pl, ordA (A0 J) v' π = if v' = v then 1 else 0`. Introduce `v'`. Use `split_ifs with h`.

Substitute `h` using the available equality. Conclude with `hπ.2.2`. Conclude with `((GlobalTheory.TwV.Xc.OrdA.ordA_props _ _ _ _ _ (A0 J) (GlobalTheory.TwV.LbB.locInt_locAt _) hS.1 v').2.2.2 v (Ne.symm h) π hπ.2.1)`. Establish `hsum : (∑ v' : (sysS H X std).Pl, (sysS H X std).vm v' (j + 1) * ordA (A0 J) v' π) = (sysS H X std).vm v (j + 1)`. Rewrite using `[Finset.sum_eq_single v]`.

Rewrite using `[hord v, if_pos rfl, mul_one]`. Introduce `b _ hb`. Rewrite using `[hord b, if_neg hb, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ v) h`.

Rewrite `hnorm` using `[hsum]`. Take `⟨𝔞, h𝔞, hχ⟩` from `(GlobalTheory.T.charOnNormOneIdeles_mul_unramified_classValue S hD hS).2.2.2 π hπU`. Establish `hcur` using `S.curve`. Establish `hp2 : D.what₂.places.resChar w ≠ 2` using `by have := hcur.1; omega`. Take `⟨hQ, -, hone⟩` from `GlobalTheory.TwV.Xc.chi_alg_unit_inert D _ S.lam t.χ hcur.2.2.2.2.2.2.1 hp2 hcur.2.2.1 𝔞 h𝔞`.

Rewrite `hQ`, `hone` using `[← hχ]`. Establish `hpK : ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖ ≠ 0` using `norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 (Fact.out : (D.what₂.places.resChar w).Prime).ne_zero)`. Establish `hmQ : S.muT (j + 1) π ∈ TaylorLogMetric.Qbar` using `hrm ▸ embLL_mem D rm`. Establish `hK : ∀ r : D.what₂.LL, S.E.iK (ex.cmp.embW u w hg r) = TaylorLogMetric.lamC S.lam (D.what₂.embLL r)` using `fun r => (S.hK r (embLL_mem D r)).trans (Formalism.L2.Ker.lamC_of_mem S.lam (embLL_mem D r)).symm`. Use `⟨((D.what₂.places.resChar w : ℕ) : (sysS H X std).G.Kf) ^ (-((sysS H X std).vm v (j + 1))) * ex.cmp.embW u w hg (rm * ra), ((D.what₂.places.resChar w : ℕ) : (sysS H X std).G.Kf) ^ ((sysS H X std).vm v (j + 1)) * ex.cmp.embW u w hg (rm⁻¹ * rb⁻¹), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Apply `GlobalTheory.UnitK.vEqK_zero_of_norm_one _ _ S.E.toCEmb show ‖S.E.iK _‖ = 1` to reduce the goal to its premises. Rewrite using `[map_mul, map_zpow₀, map_natCast, hK, map_mul, hrm, hra, Formalism.L2.Ker.lamC_mul S.lam hmQ (zpow_mem hQ _), lamC_zpow S.lam hQ, norm_mul, norm_mul, norm_zpow, norm_zpow, hnorm, hone, one_zpow, mul_one, ← zpow_add₀ hpK, neg_add_cancel, zpow_zero]`. Apply `GlobalTheory.UnitK.vEqK_zero_of_norm_one _ _ S.E.toCEmb show ‖S.E.iK _‖ = 1` to reduce the goal to its premises. Rewrite using `[map_mul, map_zpow₀, map_natCast, hK, map_mul, map_inv₀, map_inv₀, hrm, hrb, Formalism.L2.Ker.lamC_mul S.lam (inv_mem hmQ) (inv_mem (zpow_mem hQ _)), lamC_inv S.lam hmQ, lamC_inv S.lam (zpow_mem hQ _), lamC_zpow S.lam hQ, norm_mul, norm_mul, norm_inv, norm_inv, norm_zpow, norm_zp …`. Use `show S.E.iK _ = _`.

Rewrite using `[map_mul, map_zpow₀, map_natCast, hK, map_mul, hrm, hra]`. Use `show S.E.iK _ = _`. Rewrite using `[map_mul, map_zpow₀, map_natCast, hK, map_mul, map_inv₀, map_inv₀, hrm, hrb, zpow_neg (chiI J π)]`.
-/
theorem GlobalTheory.TwV.Xc.two_units : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => KIn t → S.Pos → ∀ v π, IsUnifAt J v π → ∀ j < D.R.m, (sysS H X std).Lv.comp j → (sysS H X std).Lv.comp (j + 1) → ∃ a b : (sysS H X std).G.Kf, (sysS H X std).vEqK a 0 ∧ (sysS H X std).vEqK b 0 ∧ S.E.iK a = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (-((sysS H X std).vm v (j + 1))) * TaylorLogMetric.lamC S.lam (S.muT (j + 1) π * chiI J π ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) ∧ S.E.iK b = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ ((sysS H X std).vm v (j + 1)) * TaylorLogMetric.lamC S.lam ((S.muT (j + 1) π)⁻¹ * chiI J π ^ (-((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS hKIn hPos v π hπ j hj hcj hcj1
  have hπU : π ∈ U1 (sigD D) := hπ.1
  obtain ⟨rm, hrm⟩ := GlobalTheory.T.stepCharacter_uniformizingIdele_mem_coeffField S hD hS hKIn v π hπ j hj
  obtain ⟨ra, hra⟩ := GlobalTheory.T.kernelSite_normalisingCharPow_values_in_coeffField S hD hS j hj.le hcj π hπU
  obtain ⟨rb, hrb⟩ := GlobalTheory.T.kernelSite_normalisingCharPow_values_in_coeffField S hD hS (j + 1) hj hcj1 π hπU
  have hfill := GlobalTheory.T.systemWeights_eq_shifted_character_exponents S hD hS j hj hcj1
  have hnorm := GlobalTheory.T.norm_lambdaCharacter_normOne_idele_eq_p_pow S hD hS hPos j hj hfill π hπU
  have hord : ∀ v' : (sysS H X std).Pl, ordA (A0 J) v' π = if v' = v then 1 else 0 := by
    intro v'
    split_ifs with h
    · subst h; exact hπ.2.2
    · exact ((GlobalTheory.TwV.Xc.OrdA.ordA_props _ _ _ _ _ (A0 J) (GlobalTheory.TwV.LbB.locInt_locAt _) hS.1 v').2.2.2 v (Ne.symm h) π hπ.2.1)
  have hsum : (∑ v' : (sysS H X std).Pl, (sysS H X std).vm v' (j + 1) * ordA (A0 J) v' π) = (sysS H X std).vm v (j + 1) := by
    rw [Finset.sum_eq_single v]
    · rw [hord v, if_pos rfl, mul_one]
    · intro b _ hb; rw [hord b, if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ v) h
  rw [hsum] at hnorm
  obtain ⟨𝔞, h𝔞, hχ⟩ := (GlobalTheory.T.charOnNormOneIdeles_mul_unramified_classValue S hD hS).2.2.2 π hπU
  have hcur := S.curve
  have hp2 : D.what₂.places.resChar w ≠ 2 := by have := hcur.1; omega
  obtain ⟨hQ, -, hone⟩ := GlobalTheory.TwV.Xc.chi_alg_unit_inert D _ S.lam t.χ hcur.2.2.2.2.2.2.1 hp2 hcur.2.2.1 𝔞 h𝔞
  rw [← hχ] at hQ hone
  have hpK : ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖ ≠ 0 :=
    norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 (Fact.out : (D.what₂.places.resChar w).Prime).ne_zero)
  have hmQ : S.muT (j + 1) π ∈ TaylorLogMetric.Qbar := hrm ▸ embLL_mem D rm
  have hK : ∀ r : D.what₂.LL, S.E.iK (ex.cmp.embW u w hg r) = TaylorLogMetric.lamC S.lam (D.what₂.embLL r) := fun r =>
    (S.hK r (embLL_mem D r)).trans (Formalism.L2.Ker.lamC_of_mem S.lam (embLL_mem D r)).symm
  refine ⟨((D.what₂.places.resChar w : ℕ) : (sysS H X std).G.Kf) ^ (-((sysS H X std).vm v (j + 1))) * ex.cmp.embW u w hg (rm * ra),
    ((D.what₂.places.resChar w : ℕ) : (sysS H X std).G.Kf) ^ ((sysS H X std).vm v (j + 1)) * ex.cmp.embW u w hg (rm⁻¹ * rb⁻¹), ?_, ?_, ?_, ?_⟩
  · apply GlobalTheory.UnitK.vEqK_zero_of_norm_one _ _ S.E.toCEmb
    show ‖S.E.iK _‖ = 1
    rw [map_mul, map_zpow₀, map_natCast, hK, map_mul, hrm, hra, Formalism.L2.Ker.lamC_mul S.lam hmQ (zpow_mem hQ _), lamC_zpow S.lam hQ,
      norm_mul, norm_mul, norm_zpow, norm_zpow, hnorm, hone, one_zpow, mul_one, ← zpow_add₀ hpK, neg_add_cancel, zpow_zero]
  · apply GlobalTheory.UnitK.vEqK_zero_of_norm_one _ _ S.E.toCEmb
    show ‖S.E.iK _‖ = 1
    rw [map_mul, map_zpow₀, map_natCast, hK, map_mul, map_inv₀, map_inv₀, hrm, hrb, Formalism.L2.Ker.lamC_mul S.lam (inv_mem hmQ) (inv_mem (zpow_mem hQ _)),
      lamC_inv S.lam hmQ, lamC_inv S.lam (zpow_mem hQ _), lamC_zpow S.lam hQ,
      norm_mul, norm_mul, norm_inv, norm_inv, norm_zpow, norm_zpow, hnorm, hone, one_zpow, inv_one, mul_one, mul_inv_cancel₀ (zpow_ne_zero _ hpK)]
  · show S.E.iK _ = _
    rw [map_mul, map_zpow₀, map_natCast, hK, map_mul, hrm, hra]
  · show S.E.iK _ = _
    rw [map_mul, map_zpow₀, map_natCast, hK, map_mul, map_inv₀, map_inv₀, hrm, hrb, zpow_neg (chiI J π)]

end
