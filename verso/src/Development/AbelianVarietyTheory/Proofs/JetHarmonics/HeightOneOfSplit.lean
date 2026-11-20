import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSmallInPrimePow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupPadicMulIntegralVanishingOrderStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUnitCoeffMulSeriesLeNormStatement

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

/- English proof (translation)
Unfold `zc`. Conclude with `(PadicComplex.norm_extends' (p := q) (a : ℚ_[q])).trans (PadicInt.norm_def).symm`.
-/
private theorem norm_zc_eq {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  exact (PadicComplex.norm_extends' (p := q) (a : ℚ_[q])).trans (PadicInt.norm_def).symm

/- English proof (translation)
Simplify using `[zc]`.
-/
private theorem zc_natCast_eq {q : ℕ} [Fact q.Prime] (n : ℕ) : zc (n : ℤ_[q]) = (n : ℂ_[q]) := by
  simp [zc]

/- English proof (translation)
Introduce `d q _ M F hd hd16 hs hOK hM hF`. Use `set U : ℂ_[q]⟦X⟧ := PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u) with hUdef`. Establish `flow` using `uw_elliptic_flow q M hM`. Establish `hU0 : constantCoeff U = 0`. Rewrite using `[hUdef, ← coeff_zero_eq_constantCoeff_apply, coeff_map, tay, coeff_mk]`.

Simplify using `[flow.2.2.2.2.1]`. Take `⟨ℓ, hchart, hℓX⟩` from `Basic.exists_chart M hM`. Establish `hℓ0 : constantCoeff ℓ = 0` using `hchart.2.1`. Establish `hUℓ : U.subst ℓ = X` using `hℓX`. Take `⟨P1, P2, P3⟩` from `GlobalTheory.T.formalGroup_padicMul_integral_vanishingOrder q F U ℓ hU0 hℓ0 hUℓ hF`.

Use `⟨ℓ, hℓ0, hUℓ, ?_, ?_⟩` and prove the remaining obligations. Establish `hle : ‖coeff q (U.subst (C (q : ℂ_[q]) * ℓ))‖ ≤ 1`. Use `P1 (q : ℤ_[q])` as an intermediate fact. Rewrite `this` using `[zc_natCast_eq]`. Conclude with `this q`.

Use `le_antisymm hle (not_lt.1 fun hlt => ?_)` and prove the remaining obligations. Establish `P3'` using `P3 hlt`. Use `set k : ℕ := d + 3 with hk`. Take `⟨β, N, hβ, hβ0, hβn, hN, hNle⟩` from `exists_small_in_prime_pow d q M.ι hd hd16 hs k`. Establish `ar` using `okArith d q M.ι hd hd16 hs`.

Take `⟨a, ha⟩` from `(ar.2.1 β hβ).1`. Establish `hanorm : ‖a‖ ≤ (q : ℝ) ^ (-(k : ℤ))`. Rewrite using `[← norm_zc_eq, ← ha]`. Conclude with `hβn`. Establish `hlat : ∀ l ∈ M.L.lattice, β * l ∈ M.L.lattice`.

Introduce `l hl`. Rewrite `hl`, the goal using `[hOK]`. Conclude with `(ar.1.2.2 β l hβ hl).2.1`. Establish `hu0 : AnalyticAt ℂ M.u 0` using `(flow.2.2.2.2.2.2.2.2 0 (Or.inl ((hOK 0).2 ⟨0, 0, by simp⟩))).1`. Establish `hhat : hat M.ι ℓ (fun z => M.u (β * z)) = U.subst (C (zc a) * ℓ)`.

Rewrite using `[(TaylorRead.hat_laws q M.ι ℓ hℓ0).2.2.2.2.2.1 M.u β hu0, ← ha]`. Both sides reduce to the same expression. Establish `hbd : Bd 1 (hat M.ι ℓ (fun z => M.u (β * z)))`. Rewrite using `[hhat]`. Conclude with `P1 a`.

Take `⟨n, hnN, hn1⟩` from `GlobalTheory.T.exists_unit_coeff_mul_series_le_norm q M ℓ β N hchart hβ0 hlat hN hbd`. Establish `hnlt : n < (2 * q) ^ k`. Establish `hq : 0 < q ^ k` using `pow_pos (Fact.out : q.Prime).pos k`. Establish `h2 : d + 3 < 2 ^ k` using `Nat.lt_two_pow_self`. Combine the equalities or inequalities in the displayed calculation.

Use `P3' k a hanorm n hnlt` as an intermediate fact. Rewrite `this` using `[← hhat, hn1]`. Conclude with `lt_irrefl _ this`. Introduce `k hk`. Break down `Nat.eq_zero_or_pos k with rfl | hkpos` into its components or cases.

Establish `hc : constantCoeff (C (q : ℂ_[q]) * ℓ) = 0` using `by simp [hℓ0]`. Rewrite using `[coeff_zero_eq_constantCoeff_apply, TaylorRead.constantCoeff_subst_of hc, hU0, norm_zero]`. Conclude with `one_pos`. Conclude with `P2 k (Nat.not_dvd_of_pos_of_lt hkpos hk)`.
-/
theorem height_one_of_split : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (F : FormalGroup 𝓞_ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.Ok → MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)), PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u))] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) → ∃ ℓ : ℂ_[q]⟦X⟧, constantCoeff ℓ = 0 ∧ PowerSeries.subst ℓ (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) = X ∧ ‖coeff q (PowerSeries.subst (C (q : ℂ_[q]) * ℓ) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)))‖ = 1 ∧ ∀ k < q, ‖coeff k (PowerSeries.subst (C (q : ℂ_[q]) * ℓ) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)))‖ < 1 := by
  intro d q _ M F hd hd16 hs hOK hM hF
  set U : ℂ_[q]⟦X⟧ := PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u) with hUdef
  have flow := uw_elliptic_flow q M hM
  have hU0 : constantCoeff U = 0 := by
    rw [hUdef, ← coeff_zero_eq_constantCoeff_apply, coeff_map, tay, coeff_mk]
    simp [flow.2.2.2.2.1]

  obtain ⟨ℓ, hchart, hℓX⟩ := Basic.exists_chart M hM
  have hℓ0 : constantCoeff ℓ = 0 := hchart.2.1
  have hUℓ : U.subst ℓ = X := hℓX
  obtain ⟨P1, P2, P3⟩ := GlobalTheory.T.formalGroup_padicMul_integral_vanishingOrder q F U ℓ hU0 hℓ0 hUℓ hF
  refine ⟨ℓ, hℓ0, hUℓ, ?_, ?_⟩
  ·

    have hle : ‖coeff q (U.subst (C (q : ℂ_[q]) * ℓ))‖ ≤ 1 := by
      have := P1 (q : ℤ_[q])
      rw [zc_natCast_eq] at this
      exact this q
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    have P3' := P3 hlt
    set k : ℕ := d + 3 with hk
    obtain ⟨β, N, hβ, hβ0, hβn, hN, hNle⟩ := exists_small_in_prime_pow d q M.ι hd hd16 hs k
    have ar := okArith d q M.ι hd hd16 hs
    obtain ⟨a, ha⟩ := (ar.2.1 β hβ).1
    have hanorm : ‖a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) := by
      rw [← norm_zc_eq, ← ha]
      exact hβn
    have hlat : ∀ l ∈ M.L.lattice, β * l ∈ M.L.lattice := by
      intro l hl
      rw [hOK] at hl ⊢
      exact (ar.1.2.2 β l hβ hl).2.1
    have hu0 : AnalyticAt ℂ M.u 0 := (flow.2.2.2.2.2.2.2.2 0 (Or.inl ((hOK 0).2 ⟨0, 0, by simp⟩))).1
    have hhat : hat M.ι ℓ (fun z => M.u (β * z)) = U.subst (C (zc a) * ℓ) := by
      rw [(TaylorRead.hat_laws q M.ι ℓ hℓ0).2.2.2.2.2.1 M.u β hu0, ← ha]
      rfl
    have hbd : Bd 1 (hat M.ι ℓ (fun z => M.u (β * z))) := by
      rw [hhat]
      exact P1 a
    obtain ⟨n, hnN, hn1⟩ := GlobalTheory.T.exists_unit_coeff_mul_series_le_norm q M ℓ β N hchart hβ0 hlat hN hbd
    have hnlt : n < (2 * q) ^ k := by
      have hq : 0 < q ^ k := pow_pos (Fact.out : q.Prime).pos k
      have h2 : d + 3 < 2 ^ k := Nat.lt_two_pow_self
      calc n ≤ N := hnN
        _ ≤ (d + 3) * q ^ k := hNle
        _ < 2 ^ k * q ^ k := Nat.mul_lt_mul_of_pos_right h2 hq
        _ = (2 * q) ^ k := (mul_pow 2 q k).symm
    have := P3' k a hanorm n hnlt
    rw [← hhat, hn1] at this
    exact lt_irrefl _ this
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hc : constantCoeff (C (q : ℂ_[q]) * ℓ) = 0 := by simp [hℓ0]
      rw [coeff_zero_eq_constantCoeff_apply, TaylorRead.constantCoeff_subst_of hc, hU0, norm_zero]
      exact one_pos
    · exact P2 k (Nat.not_dvd_of_pos_of_lt hkpos hk)

end GlobalTheory.MomOne
