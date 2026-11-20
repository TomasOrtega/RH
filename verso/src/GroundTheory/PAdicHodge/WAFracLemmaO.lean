import Mathlib
import GroundTheory.PAdicHodge.WAFracBridge
import GroundTheory.PAdicHodge.WAFracOrbit
import GroundTheory.PAdicHodge.WAFracNorm
import GroundTheory.PAdicHodge.AnnNormAcrisToAnnPosBig
import GroundTheory.PAdicHodge.WAFracAnnPt
import GroundTheory.PAdicHodge.FundamentalSeqSurj
import GroundTheory.PAdicHodge.BCrisPlusInvariants
import GroundTheory.PAdicHodge.FontaineLemmaInvariants
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WAFrac

open _root_.WittVector WittTilt WAEval TeichLift PhiGamma ACris WABridge WAPeriodT

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p

/- English proof (translation)
The claim follows from `radA_lt_inv_p.le`.
-/
theorem radA_le_inv_p : radA p ≤ (p : ℝ)⁻¹ := radA_lt_inv_p.le

/- English proof (translation)
Establish `h` using `congrArg (bcrisToAnn hσ) (natCast_mul_pInv (p := p))`. Rewrite `h` using `[map_mul, map_natCast, map_one]`. Rewrite using `[mul_comm]`. Conclude with `h`.
-/
theorem bcrisToAnn_pInv_mul {ρ0 : Set.Ioo (0 : ℝ) 1} {σ0 : Set.Ioc (0 : ℝ) ρ0} (hσ : (p : ℝ)⁻¹ ≤ σ0) :
    bcrisToAnn hσ (pInv p) * (p : (𝓣).Ann ρ0 σ0) = 1 := by
  have h := congrArg (bcrisToAnn hσ) (natCast_mul_pInv (p := p))
  rw [map_mul, map_natCast, map_one] at h
  rw [mul_comm]; exact h

set_option maxHeartbeats 3200000 in

/- English proof (translation)
Take `⟨hext, b, j₀, s, c, t, hι, hφ, ht, hc, hb, happ⟩` from `exists_bCrisPlus_approx_single k y hy`. Use `⟨hext, b, hφ, hι, fun ρ0 σ0 hσ h0 ρ' hρ' z hz => ?_⟩` and prove the remaining obligations. Take `⟨z₂, hz₂⟩` from `hext (radTwo p)`. Establish `hres : (𝓣).res hρ' z = (𝓣).res h0 z₂` using `(𝓣).ofRad_injective ρ0 (by rw [(𝓣).ofRad_res, (𝓣).ofRad_res, hz, hz₂])`. Use `set Z : (𝓣).Ann ρ0 σ0 := (𝓣).toAnn ρ0 σ0 ((𝓣).res hρ' z) with hZ`.

Establish `hcZ : (p : (𝓣).Ann ρ0 σ0) ^ j₀ * Z = acrisToAnn hσ c`. Use `eq_acrisToAnn hσ fun N => ⟨t N, ?_, fun r => ?_⟩` and prove the remaining obligations. Take `⟨d, hd⟩` from `hc N`. Rewrite using `[hd]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`.

Rewrite using `[ht N, map_mul, map_pow, map_natCast, ← mul_sub, (𝓣).annNorm_mul, (𝓣).annNorm_pow, annNorm_awayToAnn_natCast_p]`. Establish `hr0 : (0 : ℝ) ≤ r` using `(rad_pos' r).le`. Establish `hr1 : (r : ℝ) ^ j₀ ≤ 1` using `pow_le_one₀ hr0 (rad_lt_one' r).le`. Use `(mul_le_of_le_one_left ((𝓣).annNorm_nonneg _ _) hr1).trans ?_` and prove the remaining obligations. Rewrite using `[hZ, awayToAnn_eq_toAnn, ← map_sub, (𝓣).annNorm_toAnn, hres]`.

Establish `hrT : (r : ℝ) ≤ radTwo p` using `r.2.2.trans h0`. Establish `hrA : radA p ≤ (r : ℝ)` using `radA_le_inv_p.trans (hσ.trans r.2.1)`. Establish `e1 : (𝓣).res h0 z₂ - awayToExt p ρ0 (s N) = (𝓣).res h0 ((𝓣).res (le_refl _) z₂ - awayToExt p (radTwo p) (s N))`. Rewrite using `[map_sub, (𝓣).res_res, res_awayToExt]`. Rewrite using `[e1, (𝓣).extNorm_res]`.

Use `(happ N (radTwo p) le_rfl z₂ hz₂ ⟨r, (rad_pos' r), hrT⟩ hrA).trans ?_` and prove the remaining obligations. Conclude with `pow_le_pow_left₀ (radA_pos (p := p)).le (radA_le_inv_p.trans (hσ.trans σ0.2.2)) N`. Rewrite using `[hb, map_mul, map_pow, bcrisToAnn_algebraMap, ← hcZ]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_bCrisPlus_ann (k : ℕ) (y : (𝓣).RobbaTilde)
    (hy : (frob ℂ_[p] p).tildeFrob y = (p : (𝓣).RobbaTilde) ^ (k + 1) * y) :
    (∀ ρ : Set.Ioo (0 : ℝ) 1, ∃ z : (𝓣).RobbaExt ρ, (𝓣).ofRad ρ z = y) ∧
    ∃ b : BCrisPlus ℂ_[p] p, phiPlus ℂ_[p] p b = (p : BCrisPlus ℂ_[p] p) ^ (k + 1) * b ∧
      (∀ (ρ : Set.Ioo (0 : ℝ) 1) (hρ : (p : ℝ)⁻¹ < ρ) (z : (𝓣).RobbaExt ρ),
        (𝓣).ofRad ρ z = y → iotaPlus ℂ_[p] p b = iota p hρ z) ∧
      ∀ (ρ0 : Set.Ioo (0 : ℝ) 1) (σ0 : Set.Ioc (0 : ℝ) ρ0) (hσ : (p : ℝ)⁻¹ ≤ σ0)
        (_ : (ρ0 : ℝ) ≤ radTwo p) (ρ' : Set.Ioo (0 : ℝ) 1) (hρ' : (ρ0 : ℝ) ≤ ρ') (z : (𝓣).RobbaExt ρ'),
        (𝓣).ofRad ρ' z = y → bcrisToAnn hσ b = (𝓣).toAnn ρ0 σ0 ((𝓣).res hρ' z) := by
  obtain ⟨hext, b, j₀, s, c, t, hι, hφ, ht, hc, hb, happ⟩ := exists_bCrisPlus_approx_single k y hy
  refine ⟨hext, b, hφ, hι, fun ρ0 σ0 hσ h0 ρ' hρ' z hz => ?_⟩
  obtain ⟨z₂, hz₂⟩ := hext (radTwo p)
  have hres : (𝓣).res hρ' z = (𝓣).res h0 z₂ :=
    (𝓣).ofRad_injective ρ0 (by rw [(𝓣).ofRad_res, (𝓣).ofRad_res, hz, hz₂])
  set Z : (𝓣).Ann ρ0 σ0 := (𝓣).toAnn ρ0 σ0 ((𝓣).res hρ' z) with hZ

  have hcZ : (p : (𝓣).Ann ρ0 σ0) ^ j₀ * Z = acrisToAnn hσ c := by
    refine eq_acrisToAnn hσ fun N => ⟨t N, ?_, fun r => ?_⟩
    · obtain ⟨d, hd⟩ := hc N
      rw [hd]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · rw [ht N, map_mul, map_pow, map_natCast, ← mul_sub, (𝓣).annNorm_mul, (𝓣).annNorm_pow,
        annNorm_awayToAnn_natCast_p]
      have hr0 : (0 : ℝ) ≤ r := (rad_pos' r).le
      have hr1 : (r : ℝ) ^ j₀ ≤ 1 := pow_le_one₀ hr0 (rad_lt_one' r).le
      refine (mul_le_of_le_one_left ((𝓣).annNorm_nonneg _ _) hr1).trans ?_
      rw [hZ, awayToAnn_eq_toAnn, ← map_sub, (𝓣).annNorm_toAnn, hres]
      have hrT : (r : ℝ) ≤ radTwo p := r.2.2.trans h0
      have hrA : radA p ≤ (r : ℝ) := radA_le_inv_p.trans (hσ.trans r.2.1)
      have e1 : (𝓣).res h0 z₂ - awayToExt p ρ0 (s N) =
          (𝓣).res h0 ((𝓣).res (le_refl _) z₂ - awayToExt p (radTwo p) (s N)) := by
        rw [map_sub, (𝓣).res_res, res_awayToExt]
      rw [e1, (𝓣).extNorm_res]
      refine (happ N (radTwo p) le_rfl z₂ hz₂ ⟨r, (rad_pos' r), hrT⟩ hrA).trans ?_
      exact pow_le_pow_left₀ (radA_pos (p := p)).le (radA_le_inv_p.trans (hσ.trans σ0.2.2)) N
  rw [hb, map_mul, map_pow, bcrisToAnn_algebraMap, ← hcZ]
  calc (p : (𝓣).Ann ρ0 σ0) ^ j₀ * Z * bcrisToAnn hσ (pInv p) ^ j₀
      = Z * (bcrisToAnn hσ (pInv p) * (p : (𝓣).Ann ρ0 σ0)) ^ j₀ := by ring
    _ = Z := by rw [bcrisToAnn_pInv_mul, one_pow, mul_one]

section T

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

include hε hζ in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Establish `hy : (frob ℂ_[p] p).tildeFrob (tTilde p ε) = (p : (𝓣).RobbaTilde) ^ (0 + 1) * tTilde p ε`. Rewrite using `[zero_add, pow_one]`. Conclude with `tildeFrob_tTilde hε hζ`. Take `⟨-, b, -, hι, hann⟩` from `exists_bCrisPlus_ann 0 (tTilde p ε) hy`. Establish `hbt : b = periodTPlus hε`.

Apply `iotaPlus_injective (K := ℂ_[p]) (p := p)` to reduce the goal to its premises. Rewrite using `[hι (rhoMid p) inv_p_lt_rhoMid (tTildeExt p ε (rhoMid p)) (ofRad_tTildeExt hε hζ (rhoMid p)), iotaPlus_periodTPlus, ← iotaTildeFun_ofRad inv_p_lt_rhoMid, ofRad_tTildeExt hε hζ, iotaTildeFun_tTilde hε hζ]`. Rewrite using `[← hbt]`. Conclude with `hann ρ0 σ0 hσ h0 ρ' hρ' w hw`.
-/
theorem bcrisToAnn_periodTPlus {ρ0 : Set.Ioo (0 : ℝ) 1} {σ0 : Set.Ioc (0 : ℝ) ρ0} (hσ : (p : ℝ)⁻¹ ≤ σ0)
    (h0 : (ρ0 : ℝ) ≤ radTwo p) {ρ' : Set.Ioo (0 : ℝ) 1} (hρ' : (ρ0 : ℝ) ≤ ρ') (w : (𝓣).RobbaExt ρ')
    (hw : (𝓣).ofRad ρ' w = tTilde p ε) :
    bcrisToAnn hσ (periodTPlus hε) = (𝓣).toAnn ρ0 σ0 ((𝓣).res hρ' w) := by
  have hy : (frob ℂ_[p] p).tildeFrob (tTilde p ε) = (p : (𝓣).RobbaTilde) ^ (0 + 1) * tTilde p ε := by
    rw [zero_add, pow_one]; exact tildeFrob_tTilde hε hζ
  obtain ⟨-, b, -, hι, hann⟩ := exists_bCrisPlus_ann 0 (tTilde p ε) hy
  have hbt : b = periodTPlus hε := by
    apply iotaPlus_injective (K := ℂ_[p]) (p := p)
    rw [hι (rhoMid p) inv_p_lt_rhoMid (tTildeExt p ε (rhoMid p)) (ofRad_tTildeExt hε hζ (rhoMid p)),
      iotaPlus_periodTPlus, ← iotaTildeFun_ofRad inv_p_lt_rhoMid, ofRad_tTildeExt hε hζ,
      iotaTildeFun_tTilde hε hζ]
  rw [← hbt]
  exact hann ρ0 σ0 hσ h0 ρ' hρ' w hw

end T

/- English proof (translation)
Take `⟨u, hu⟩` from `hb.exists_right_inv`. Take `⟨⟨δ, s⟩, hδ⟩` from `IsLocalization.mk'_surjective (Submonoid.powers t) u`. Take `⟨M, hM⟩` from `s.2`. Simplify using `only at hδ`. Use `⟨δ, M, hinj ?_⟩` and prove the remaining obligations.

Establish `hspec` using `IsLocalization.mk'_spec S δ s`. Rewrite using `[map_mul, ← hspec, ← mul_assoc, hδ, hu, one_mul, ← (show t ^ M = (s : R) from hM)]`.
-/
theorem exists_mul_eq_pow_of_isUnit {R S : Type*} [CommRing R] [CommRing S] {t : R} [Algebra R S]
    [IsLocalization.Away t S] (hinj : Function.Injective (algebraMap R S)) {b : R}
    (hb : IsUnit (algebraMap R S b)) : ∃ (δ : R) (M : ℕ), b * δ = t ^ M := by
  obtain ⟨u, hu⟩ := hb.exists_right_inv
  obtain ⟨⟨δ, s⟩, hδ⟩ := IsLocalization.mk'_surjective (Submonoid.powers t) u
  obtain ⟨M, hM⟩ := s.2
  simp only at hδ
  refine ⟨δ, M, hinj ?_⟩
  have hspec := IsLocalization.mk'_spec S δ s
  rw [map_mul, ← hspec, ← mul_assoc, hδ, hu, one_mul, ← (show t ^ M = (s : R) from hM)]

set_option maxHeartbeats 1600000 in
/- English proof (translation)
The claim follows from `(galB_algebraMap hε σ b).trans ((congrArg (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) h).trans (map_mul (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) _ b))`.
-/
theorem galB_algebraMap_eq_of_smul_eq {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
    {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ : Gal(PadicAlgCl p/K)) {b : BCrisPlus ℂ_[p] p}
    {q : ℚ_[p]} (h : σ • b = algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q * b) :
    galB hε σ (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) b) =
      algebraMap ℚ_[p] (BCris hε) q * algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) b :=
  (galB_algebraMap hε σ b).trans ((congrArg (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) h).trans
    (map_mul (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) _ b))

section LemmaO

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)
  {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨w, hw⟩` from `hz`. Apply `iotaPlus_injective (K := ℂ_[p]) (p := p)` to reduce the goal to its premises. Rewrite using `[iotaPlus_gal_smul, map_mul, iotaPlus_algebraMap_padic, hι (rhoMid p) inv_p_lt_rhoMid w hw, ← iota_extMap inv_p_lt_rhoMid σ w]`. Establish `e : (galIso σ).extMap (rhoMid p) w = awayToExt p (rhoMid p) (wittFpbarToAway p (padicToWFrac p q)) * w`. Apply `(𝓣).ofRad_injective (rhoMid p)` to reduce the goal to its premises.

Rewrite using `[← TeichLift.TeichIso.tildeMap_ofRad, hw, hq, map_mul, ← padicToTilde_eq_ofRad, hw]`. Rewrite using `[e, map_mul, iota_awayToExt_padic]`.
-/
theorem galPlus_eq_of_tildeMap {z : (𝓣).RobbaTilde} {b : BCrisPlus ℂ_[p] p}
    (hι : ∀ (ρ : Set.Ioo (0 : ℝ) 1) (hρ : (p : ℝ)⁻¹ < ρ) (w : (𝓣).RobbaExt ρ),
      (𝓣).ofRad ρ w = z → iotaPlus ℂ_[p] p b = iota p hρ w)
    (hz : ∃ w : (𝓣).RobbaExt (rhoMid p), (𝓣).ofRad (rhoMid p) w = z)
    (σ : Gal(PadicAlgCl p/K)) {q : ℚ_[p]} (hq : (galIso σ).tildeMap z = padicToTilde p q * z) :
    σ • b = algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q * b := by
  obtain ⟨w, hw⟩ := hz
  apply iotaPlus_injective (K := ℂ_[p]) (p := p)
  rw [iotaPlus_gal_smul, map_mul, iotaPlus_algebraMap_padic, hι (rhoMid p) inv_p_lt_rhoMid w hw,
    ← iota_extMap inv_p_lt_rhoMid σ w]
  have e : (galIso σ).extMap (rhoMid p) w =
      awayToExt p (rhoMid p) (wittFpbarToAway p (padicToWFrac p q)) * w := by
    apply (𝓣).ofRad_injective (rhoMid p)
    rw [← TeichLift.TeichIso.tildeMap_ofRad, hw, hq, map_mul, ← padicToTilde_eq_ofRad, hw]
  rw [e, map_mul, iota_awayToExt_padic]

include hζ in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε))` using `algebraMap_bCrisPlus_bCris_injective hε hζ`. Establish `hbu` using `isUnit_of_galB_eigen_of_finiteIndex hε hζ H (fun h => hb0 (hinj (by rw [h, map_zero]))) (fun σ hσ => (hbH σ hσ).imp fun q hq => galB_algebraMap_eq_of_smul_eq hε σ hq)`. Conclude with `exists_mul_eq_pow_of_isUnit (R := BCrisPlus ℂ_[p] p) (S := BCris hε) (t := periodTPlus hε) hinj hbu`.
-/
theorem exists_mul_eq_periodTPlus_pow [FiniteDimensional ℚ_[p] K] (H : Subgroup Gal(PadicAlgCl p/K))
    [H.FiniteIndex] {b : BCrisPlus ℂ_[p] p} (hb0 : b ≠ 0)
    (hbH : ∀ σ ∈ H, ∃ q : ℚ_[p], σ • b = algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q * b) :
    ∃ (δ : BCrisPlus ℂ_[p] p) (M : ℕ), b * δ = periodTPlus hε ^ M := by
  have hinj : Function.Injective (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) :=
    algebraMap_bCrisPlus_bCris_injective hε hζ
  have hbu := isUnit_of_galB_eigen_of_finiteIndex hε hζ H
    (fun h => hb0 (hinj (by rw [h, map_zero])))
    (fun σ hσ => (hbH σ hσ).imp fun q hq => galB_algebraMap_eq_of_smul_eq hε σ hq)
  exact exists_mul_eq_pow_of_isUnit (R := BCrisPlus ℂ_[p] p) (S := BCris hε) (t := periodTPlus hε) hinj hbu

include hζ in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Establish `hr0' : 0 < (𝓣).ptRad ξ'` using `(𝓣).ptRad_pos' hξ'`. Set `ρA : Set.Ioo (0 : ℝ) 1` to `⟨(𝓣).ptRad ξ', hr0', (𝓣).ptRad_lt_one' hξ'⟩`. Set `σA : Set.Ioc (0 : ℝ) ρA` to `⟨(𝓣).ptRad ξ', hr0', le_rfl⟩`. Establish `hσA : (p : ℝ)⁻¹ ≤ σA` using `hr0`. Establish `hA : (ρA : ℝ) ≤ radTwo p` using `hr1`.

Establish `hmem : (𝓣).ptRad ξ' ∈ Set.Icc (σA : ℝ) ρA` using `⟨le_rfl, le_rfl⟩`. Establish `hρA : (ρA : ℝ) ≤ ρ` using `hρ.le`. Establish `hev : ∀ x : (𝓣).RobbaExt ρ, (𝓣).annEval hξ' hmem ((𝓣).toAnn ρA σA ((𝓣).res hρA x)) = (𝓣).ptEval hξ' hρ.le x` using `fun x => by`. Rewrite using `[(𝓣).annEval_toAnn, (𝓣).ptEval_res]`. Establish `hb_ev : (𝓣).annEval hξ' hmem (bcrisToAnn hσA b) = 0`.

Rewrite using `[hbz ρA σA hσA hA hρA, hev, hzvan]`. Establish `h1` using `congrArg (fun x => (𝓣).annEval hξ' hmem (bcrisToAnn hσA x)) hδ`. Simplify using `only [map_mul, map_pow, hb_ev, zero_mul] at h1`. Establish `h2 : (𝓣).annEval hξ' hmem (bcrisToAnn hσA (periodTPlus hε)) = 0` using `(pow_eq_zero_iff'.1 h1.symm).1`. Rewrite `h2` using `[bcrisToAnn_periodTPlus hε hζ hσA hA hρA w hw, hev]`.

Conclude with `h2`.
-/
theorem ptEval_tTilde_eq_zero_of_dvd {ξ' : (𝓣).int} (hξ' : (𝓣).IsPrimOne ξ')
    (hr0 : (p : ℝ)⁻¹ ≤ (𝓣).ptRad ξ') (hr1 : (𝓣).ptRad ξ' ≤ radTwo p)
    {b δ : BCrisPlus ℂ_[p] p} {M : ℕ} (hδ : b * δ = periodTPlus hε ^ M)
    (ρ : Set.Ioo (0 : ℝ) 1) (hρ : (𝓣).ptRad ξ' < ρ) {zρ : (𝓣).RobbaExt ρ}
    (hbz : ∀ (ρ0 : Set.Ioo (0 : ℝ) 1) (σ0 : Set.Ioc (0 : ℝ) ρ0) (hσ : (p : ℝ)⁻¹ ≤ σ0),
      (ρ0 : ℝ) ≤ radTwo p → ∀ (hρ' : (ρ0 : ℝ) ≤ ρ), bcrisToAnn hσ b = (𝓣).toAnn ρ0 σ0 ((𝓣).res hρ' zρ))
    (hzvan : (𝓣).ptEval hξ' hρ.le zρ = 0) (w : (𝓣).RobbaExt ρ) (hw : (𝓣).ofRad ρ w = tTilde p ε) :
    (𝓣).ptEval hξ' hρ.le w = 0 := by
  have hr0' : 0 < (𝓣).ptRad ξ' := (𝓣).ptRad_pos' hξ'
  let ρA : Set.Ioo (0 : ℝ) 1 := ⟨(𝓣).ptRad ξ', hr0', (𝓣).ptRad_lt_one' hξ'⟩
  let σA : Set.Ioc (0 : ℝ) ρA := ⟨(𝓣).ptRad ξ', hr0', le_rfl⟩
  have hσA : (p : ℝ)⁻¹ ≤ σA := hr0
  have hA : (ρA : ℝ) ≤ radTwo p := hr1
  have hmem : (𝓣).ptRad ξ' ∈ Set.Icc (σA : ℝ) ρA := ⟨le_rfl, le_rfl⟩
  have hρA : (ρA : ℝ) ≤ ρ := hρ.le
  have hev : ∀ x : (𝓣).RobbaExt ρ, (𝓣).annEval hξ' hmem ((𝓣).toAnn ρA σA ((𝓣).res hρA x)) =
      (𝓣).ptEval hξ' hρ.le x := fun x => by
    rw [(𝓣).annEval_toAnn, (𝓣).ptEval_res]
  have hb_ev : (𝓣).annEval hξ' hmem (bcrisToAnn hσA b) = 0 := by
    rw [hbz ρA σA hσA hA hρA, hev, hzvan]
  have h1 := congrArg (fun x => (𝓣).annEval hξ' hmem (bcrisToAnn hσA x)) hδ
  simp only [map_mul, map_pow, hb_ev, zero_mul] at h1
  have h2 : (𝓣).annEval hξ' hmem (bcrisToAnn hσA (periodTPlus hε)) = 0 :=
    (pow_eq_zero_iff'.1 h1.symm).1
  rw [bcrisToAnn_periodTPlus hε hζ hσA hA hρA w hw, hev] at h2
  exact h2

include hε hζ in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨k, z, hz0, hφz, hHz, hzall, hzvan⟩` from `exists_eigen_vanishing hε hζ H hξ' hfix`. Take `⟨-, b, -, hι, hann⟩` from `exists_bCrisPlus_ann k z hφz`. Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`. Take `⟨w₀, hw₀⟩` from `hzall (rhoMid p)`.

Establish `h` using `hι (rhoMid p) inv_p_lt_rhoMid w₀ hw₀`. Rewrite `h` using `[map_zero]`. Establish `: w₀ = 0` using `iota_injective inv_p_lt_rhoMid (by rw [← h, map_zero])`. Rewrite `hw₀` using `[this, map_zero]`. Conclude with `hz0 hw₀.symm`.

Establish `hbH : ∀ σ ∈ H, ∃ q : ℚ_[p], σ • b = algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q * b` using `fun σ hσ => (hHz σ hσ).imp fun q hq => galPlus_eq_of_tildeMap hι (hzall (rhoMid p)) σ hq.2`. Take `⟨δ, M, hδ⟩` from `exists_mul_eq_periodTPlus_pow hε hζ H hb0 hbH`. Take `⟨zρ, hzρ⟩` from `hzall ρ`. Conclude with `ptEval_tTilde_eq_zero_of_dvd hε hζ hξ' hr0 hr1 hδ ρ hρ (fun ρ0 σ0 hσ h0 hρ' => hann ρ0 σ0 hσ h0 ρ hρ' zρ hzρ) (hzvan ρ hρ zρ hzρ) w hw`.
-/
theorem ptEval_tTilde_eq_zero_of_fixed [FiniteDimensional ℚ_[p] K] (H : Subgroup Gal(PadicAlgCl p/K))
    [H.FiniteIndex] {ξ' : (𝓣).int} (hξ' : (𝓣).IsPrimOne ξ') (hr0 : (p : ℝ)⁻¹ ≤ (𝓣).ptRad ξ')
    (hr1 : (𝓣).ptRad ξ' ≤ radTwo p)
    (hfix : ∀ σ ∈ H, ∃ u : (𝓣).int, IsUnit u ∧ ((galIso σ).ψ ξ' : WC p) = u * ξ')
    (ρ : Set.Ioo (0 : ℝ) 1) (hρ : (𝓣).ptRad ξ' < ρ) (w : (𝓣).RobbaExt ρ)
    (hw : (𝓣).ofRad ρ w = tTilde p ε) :
    (𝓣).ptEval hξ' hρ.le w = 0 := by
  obtain ⟨k, z, hz0, hφz, hHz, hzall, hzvan⟩ := exists_eigen_vanishing hε hζ H hξ' hfix
  obtain ⟨-, b, -, hι, hann⟩ := exists_bCrisPlus_ann k z hφz
  have hb0 : b ≠ 0 := by
    rintro rfl
    obtain ⟨w₀, hw₀⟩ := hzall (rhoMid p)
    have h := hι (rhoMid p) inv_p_lt_rhoMid w₀ hw₀
    rw [map_zero] at h
    have : w₀ = 0 := iota_injective inv_p_lt_rhoMid (by rw [← h, map_zero])
    rw [this, map_zero] at hw₀
    exact hz0 hw₀.symm
  have hbH : ∀ σ ∈ H, ∃ q : ℚ_[p], σ • b = algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q * b := fun σ hσ =>
    (hHz σ hσ).imp fun q hq => galPlus_eq_of_tildeMap hι (hzall (rhoMid p)) σ hq.2
  obtain ⟨δ, M, hδ⟩ := exists_mul_eq_periodTPlus_pow hε hζ H hb0 hbH
  obtain ⟨zρ, hzρ⟩ := hzall ρ
  exact ptEval_tTilde_eq_zero_of_dvd hε hζ hξ' hr0 hr1 hδ ρ hρ
    (fun ρ0 σ0 hσ h0 hρ' => hann ρ0 σ0 hσ h0 ρ hρ' zρ hzρ) (hzvan ρ hρ zρ hzρ) w hw

end LemmaO

end WAFrac

end GroundTheory.PAdicHodge
