import Mathlib
import GroundTheory.PAdicHodge.WABridgeApprox
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WABridge

open _root_.WittVector WittTilt WAEval TeichLift PhiGamma Laurent ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p

variable (p) in

def ainfToBCrisPlus : AInf ℂ_[p] p →+* BCrisPlus ℂ_[p] p :=
  (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p)).comp (algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p))

/- English proof (translation)
Rewrite using `[ainfToBCrisPlus, RingHom.comp_apply, iotaPlus_algebraMap, iota_algebraMap]`. Both sides reduce to the same expression.
-/
theorem iotaPlus_ainfToBCrisPlus (a : AInf ℂ_[p] p) :
    iotaPlus ℂ_[p] p (ainfToBCrisPlus p a) =
      toBDeRhamPlus (normInteger ℂ_[p]) p (algebraMap _ 𝔸 a) := by
  rw [ainfToBCrisPlus, RingHom.comp_apply, iotaPlus_algebraMap, iota_algebraMap]
  rfl

variable (p) in

abbrev pInv : BCrisPlus ℂ_[p] p := IsLocalization.Away.invSelf (p : ACris ℂ_[p] p)

/- English proof (translation)
Establish `h` using `IsLocalization.Away.mul_invSelf (S := BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p)`. Rewrite `h` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem natCast_mul_pInv : (p : BCrisPlus ℂ_[p] p) * pInv p = 1 := by
  have h := IsLocalization.Away.mul_invSelf (S := BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p)
  rwa [map_natCast] at h

/- English proof (translation)
Rewrite using `[← map_natCast (iotaPlus ℂ_[p] p), ← map_mul, mul_comm, natCast_mul_pInv, map_one]`.
-/
theorem iotaPlus_pInv_mul : iotaPlus ℂ_[p] p (pInv p) * (p : 𝔹) = 1 := by
  rw [← map_natCast (iotaPlus ℂ_[p] p), ← map_mul, mul_comm, natCast_mul_pInv, map_one]

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `h0 : algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p) * pInv p = 1` using `IsLocalization.Away.mul_invSelf (p : ACris ℂ_[p] p)`. Establish `hφP : phiPlus ℂ_[p] p (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p)) = algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p)`. Rewrite using `[phiPlus_algebraMap, phi_natCast_p]`. Establish `h1 : phiPlus ℂ_[p] p (pInv p) * algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p) = 1` using `by conv_lhs => rw [← hφP]`. Rewrite using `[← map_mul, mul_comm, h0, map_one]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h0, mul_one]`. Use `_ = pInv p := by rw [← mul_assoc, h1, one_mul]`.
-/
theorem phiPlus_pInv : phiPlus ℂ_[p] p (pInv p) = pInv p := by
  have h0 : algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p) * pInv p = 1 :=
    IsLocalization.Away.mul_invSelf (p : ACris ℂ_[p] p)
  have hφP : phiPlus ℂ_[p] p (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p)) =
      algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p) := by
    rw [phiPlus_algebraMap, phi_natCast_p]
  have h1 : phiPlus ℂ_[p] p (pInv p) *
      algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p) = 1 := by
    conv_lhs => rw [← hφP]
    rw [← map_mul, mul_comm, h0, map_one]
  calc phiPlus ℂ_[p] p (pInv p) = phiPlus ℂ_[p] p (pInv p) *
        (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p) * pInv p) := by
        rw [h0, mul_one]
    _ = pInv p := by rw [← mul_assoc, h1, one_mul]

/- English proof (translation)
Rewrite using `[map_mul, map_pow, iotaPlus_algebraMap, ← h, mul_comm ((p : 𝔹) ^ j) x, mul_assoc, ← mul_pow, mul_comm (p : 𝔹), iotaPlus_pInv_mul, one_pow, mul_one]`.
-/
theorem iotaPlus_div_eq {c : ACris ℂ_[p] p} {j : ℕ} {x : 𝔹}
    (h : (p : 𝔹) ^ j * x = ACris.iota ℂ_[p] p c) :
    iotaPlus ℂ_[p] p (algebraMap _ (BCrisPlus ℂ_[p] p) c * pInv p ^ j) = x := by
  rw [map_mul, map_pow, iotaPlus_algebraMap, ← h, mul_comm ((p : 𝔹) ^ j) x, mul_assoc, ← mul_pow,
    mul_comm (p : 𝔹), iotaPlus_pInv_mul, one_pow, mul_one]

/- English proof (translation)
Establish `e : (p : 𝔸) ^ j = ((pUnit p ^ (j : ℤ) : 𝔸ˣ) : 𝔸)`. Rewrite using `[zpow_natCast, Units.val_pow_eq_pow_val, coe_pUnit, map_natCast]`. Rewrite using `[e, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]`.
-/
theorem pow_mul_pUnit_neg (j : ℕ) :
    (p : 𝔸) ^ j * ((pUnit p ^ (-(j : ℤ)) : 𝔸ˣ) : 𝔸) = 1 := by
  have e : (p : 𝔸) ^ j = ((pUnit p ^ (j : ℤ) : 𝔸ˣ) : 𝔸) := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, coe_pUnit, map_natCast]
  rw [e, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `exists_eq_zpow_mul_of_gn_le hz`. Rewrite using `[← mul_assoc, pow_mul_pUnit_neg, one_mul]`. Conclude with `hc`.
-/
theorem pow_mul_mem_acrisZero {z : 𝔸} {j : ℕ}
    (hz : gn ℂ_[p] p (radA p) z ≤ radA p ^ (-(j : ℤ))) : (p : 𝔸) ^ j * z ∈ ACrisZero ℂ_[p] p := by
  obtain ⟨c, hc, rfl⟩ := exists_eq_zpow_mul_of_gn_le hz
  rw [← mul_assoc, pow_mul_pUnit_neg, one_mul]
  exact hc

/- English proof (translation)
Establish `h : gn ℂ_[p] p (radA p) ((p : 𝔸) ^ j * z) ≤ radA p ^ (N : ℤ)`. Rewrite using `[gn_mul (K := ℂ_[p]) (p := p) radA_pos radA_lt_one, gn_pow (K := ℂ_[p]) (p := p) radA_pos radA_lt_one, gn_radA_natCast_p, zpow_natCast]`. Conclude with `(mul_le_of_le_one_left (gn_nonneg (K := ℂ_[p]) (p := p) radA_pos _) (pow_le_one₀ radA_pos.le radA_lt_one.le)).trans hz`. Take `⟨d, hd, he⟩` from `exists_eq_zpow_mul_of_gn_le h`. Use `⟨d, hd, ?_⟩` and prove the remaining obligations.

Rewrite using `[he, zpow_natCast, Units.val_pow_eq_pow_val, coe_pUnit, map_natCast]`.
-/
theorem exists_pow_mul_eq {z : 𝔸} {j N : ℕ} (hz : gn ℂ_[p] p (radA p) z ≤ radA p ^ N) :
    ∃ d ∈ ACrisZero ℂ_[p] p, (p : 𝔸) ^ j * z = (p : 𝔸) ^ N * d := by
  have h : gn ℂ_[p] p (radA p) ((p : 𝔸) ^ j * z) ≤ radA p ^ (N : ℤ) := by
    rw [gn_mul (K := ℂ_[p]) (p := p) radA_pos radA_lt_one, gn_pow (K := ℂ_[p]) (p := p) radA_pos
      radA_lt_one, gn_radA_natCast_p, zpow_natCast]
    exact (mul_le_of_le_one_left (gn_nonneg (K := ℂ_[p]) (p := p) radA_pos _)
      (pow_le_one₀ radA_pos.le radA_lt_one.le)).trans hz
  obtain ⟨d, hd, he⟩ := exists_eq_zpow_mul_of_gn_le h
  refine ⟨d, hd, ?_⟩
  rw [he, zpow_natCast, Units.val_pow_eq_pow_val, coe_pUnit, map_natCast]

/- English proof (translation)
Rewrite using `[zpow_neg, zpow_natCast, ← inv_pow]`. Conclude with `pow_le_pow_left₀ radA_pos.le radA_lt_inv_p.le N`.
-/
theorem radA_pow_le (N : ℕ) : radA p ^ N ≤ (p : ℝ) ^ (-(N : ℤ)) := by
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  exact pow_le_pow_left₀ radA_pos.le radA_lt_inv_p.le N

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Establish `ha : ∀ i, y i ∈ allRad p` using `mem_allRad_of_tildeFrob_eq (fun i j => (p : (𝓣).RobbaTilde) * ainfTilde p (C i j)) (fun i j => Subring.mul_mem _ (natCast_mem _ p) (ainfTilde_mem_allRad _)) y hy`. Use `⟨fun i ρ => mem_allRad.1 (ha i) ρ, ?_⟩` and prove the remaining obligations. Use `set M : ℝ := 1 + ∑ j, tn (ha j) (radC p) with hMdef`. Establish `hM : 1 ≤ M` using `le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => tn_nonneg _ _)`. Establish `hdec : ∀ i (k : ℕ), tn (ha i) ((frob ℂ_[p] p).rootRadius^[k] (radC p)) ^ (p ^ k) ≤ ((radC p : Set.Ioo (0 : ℝ) 1) : ℝ) ^ k * M`.

Introduce `i k`. Take `⟨j, hj⟩` from `exists_tn_pow_pow_le C hy ha k i ((frob ℂ_[p] p).rootRadius^[k] (radC p))`. Rewrite `hj` using `[iterate_powRadius_rootRadius]`. Establish `e : (((frob ℂ_[p] p).rootRadius^[k] (radC p) : Set.Ioo (0 : ℝ) 1) : ℝ) ^ (k * p ^ k) = ((radC p : Set.Ioo (0 : ℝ) 1) : ℝ) ^ k`. Rewrite using `[mul_comm, pow_mul, pow_iterate_rootRadius]`.

Rewrite `hj` using `[e]`. Use `hj.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (radC p).2.1.le _))` and prove the remaining obligations. Conclude with `(Finset.single_le_sum (f := fun j => tn (ha j) (radC p)) (fun j _ => tn_nonneg _ _) (Finset.mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)`. Use `choose s hs1 hs2 using fun i (N : ℕ) => exists_approx (ha i) hM (hdec i) (pow_pos (radA_pos (p := p)) N)`. Establish `hY : ∀ i, ∃ j₀ : ℕ, max (tn (ha i) ⟨radA p, radA_pos, radA_lt_one⟩) 1 ≤ radA p ^ (-(j₀ : ℤ))`.

Introduce `i`. Use `set Y := max (tn (ha i) ⟨radA p, radA_pos (p := p), radA_lt_one (p := p)⟩) 1`. Establish `hY0 : 0 < Y` using `zero_lt_one.trans_le (le_max_right _ _)`. Take `⟨j₀, hj₀⟩` from `exists_pow_lt_of_lt_one (inv_pos.2 hY0) (radA_lt_one (p := p))`. Use `⟨j₀, ?_⟩` and prove the remaining obligations.

Rewrite using `[zpow_neg, zpow_natCast]`. Conclude with `(le_inv_comm₀ (pow_pos radA_pos j₀) hY0).1 hj₀.le`. Use `choose j₀ hj₀ using hY`. Establish `hmem : ∀ i N, (p : 𝔸) ^ j₀ i * s i N ∈ ACrisZero ℂ_[p] p` using `fun i N => pow_mul_mem_acrisZero ((hs2 i N).trans (hj₀ i))`. Establish `hrA : radA p ≤ ((radTwo p : Set.Ioo (0 : ℝ) 1) : ℝ)` using `radA_lt_radTwo.le`.

Establish `hdiff : ∀ i (N N' : ℕ), N ≤ N' → gn ℂ_[p] p (radA p) (s i N - s i N') ≤ radA p ^ N`. Introduce `i N N' hNN'`. Establish `e1` using `extNorm_awayToExt (radTwo p) ⟨radA p, radA_pos, hrA⟩ (s i N - s i N')`. Establish `e2 : awayToExt p (radTwo p) (s i N - s i N') = (rep (ha i) (radTwo p) - awayToExt p (radTwo p) (s i N')) - (rep (ha i) (radTwo p) - awayToExt p (radTwo p) (s i N))`. Rewrite using `[map_sub]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← e1, e2, sub_eq_add_neg]`. Use `((𝓣).extNorm_add_le _ _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Conclude with `(hs1 i N' _ le_rfl).trans (pow_le_pow_of_le_one radA_pos.le radA_lt_one.le hNN')`. Rewrite using `[(𝓣).extNorm_neg]`.

Conclude with `hs1 i N _ le_rfl`. Establish `hlim : ∀ i, ∃ c : ACris ℂ_[p] p, ∀ N, ∃ d : ACris ℂ_[p] p, c - algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) ⟨_, hmem i N⟩ = (p : ACris ℂ_[p] p) ^ N * d`. Introduce `i`. Use `exists_limit (fun N => ⟨_, hmem i N⟩) fun N N' hNN' => ?_` and prove the remaining obligations. Take `⟨d, hd, he⟩` from `exists_pow_mul_eq (j := j₀ i) (hdiff i N N' hNN')`.

Use `⟨⟨d, hd⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_pow]`. Rewrite using `[← mul_sub, he]`. Simplify using the standard rewrite rules. Use `choose c hc using hlim`.

Establish `hρ₂ : (p : ℝ)⁻¹ < ((radTwo p : Set.Ioo (0 : ℝ) 1) : ℝ)` using `inv_p_lt_radTwo`. Establish `hR0 : ∀ N i, (𝓣).extNorm (radTwo p) (inversePRadius p hρ₂) (rep (ha i) (radTwo p) - awayToExt p (radTwo p) (s i N)) ≤ (p : ℝ) ^ (-(N : ℤ))` using `fun N i => (hs1 i N _ radA_lt_inv_p.le).trans (radA_pow_le N)`. Establish `hι : ∀ i, (p : 𝔹) ^ j₀ i * iota p hρ₂ (rep (ha i) (radTwo p)) = ACris.iota ℂ_[p] p (c i)` using `fun i => pow_mul_iota_eq hρ₂ (j₀ i) (s i) (fun N => hR0 N i) (hmem i) (hc i)`. Use `set σ := (frob ℂ_[p] p).powRadius (radTwo p) with hσ`. Establish `hσρ : ((σ : Set.Ioo (0 : ℝ) 1) : ℝ) = rhoMid p` using `congrArg Subtype.val ((frob ℂ_[p] p).powRadius_rootRadius (rhoMid p))`.

Establish `hρσ : (p : ℝ)⁻¹ < ((σ : Set.Ioo (0 : ℝ) 1) : ℝ)` using `by rw [hσρ]; exact inv_p_lt_rhoMid`. Use `set r' : Set.Ioc (0 : ℝ) (radTwo p) := ⟨((p : ℝ)⁻¹) ^ ((p : ℝ)⁻¹), Real.rpow_pos_of_pos inv_p_pos _, by show ((p : ℝ)⁻¹) ^ ((p : ℝ)⁻¹) ≤ (((frob ℂ_[p] p).rootRadius (rhoMid p) : Set.Ioo (0 : ℝ) 1) : ℝ)`. Rewrite using `[rootRadius_coe]`. Conclude with `Real.rpow_le_rpow inv_p_pos.le inv_p_lt_rhoMid.le (inv_pos.2 (Nat.cast_pos.2 hp.out.pos)).le⟩ with hr'`. Establish `hr'A : radA p ≤ (r' : ℝ)` using `radA_lt_inv_p.le.trans (Real.self_le_rpow_of_le_one inv_p_pos.le inv_p_lt_one.le inv_p_lt_one.le)`.

Establish `hpowRad : (frob ℂ_[p] p).powRad r' = inversePRadius p hρσ`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[TeichLift.TeichFrob.coe_powRad, frob_a, pow_one]`. Conclude with `Real.rpow_inv_natCast_pow inv_p_pos.le hp.out.ne_zero`. Establish `hphiS : ∀ N i, awayToExt p σ (phiAway ℂ_[p] p (s i N)) = (frob ℂ_[p] p).extFrob (radTwo p) (awayToExt p (radTwo p) (s i N))`.

Introduce `N i`. Rewrite using `[awayToExt_eq_ofAll, awayToExt_eq_ofAll, TeichLift.TeichFrob.extFrob_ofAll]`. Conclude with `(𝓣).ofAll_congr _ _ (toB_phiAway _) _`. Establish `hR0' : ∀ N i, (𝓣).extNorm σ (inversePRadius p hρσ) ((frob ℂ_[p] p).extFrob (radTwo p) (rep (ha i) (radTwo p)) - awayToExt p σ (phiAway ℂ_[p] p (s i N))) ≤ (p : ℝ) ^ (-(N : ℤ))`. Introduce `N i`.

Rewrite using `[hphiS, ← map_sub, ← hpowRad, TeichLift.TeichFrob.extNorm_extFrob, frob_a, pow_one]`. Establish `h1` using `hs1 i N r' hr'A`. Establish `h2 : radA p ^ N ≤ 1` using `pow_le_one₀ radA_pos.le radA_lt_one.le`. Use `(pow_le_pow_left₀ ((𝓣).extNorm_nonneg _ _) h1 p).trans ?_` and prove the remaining obligations. Use `(pow_le_of_le_one (pow_nonneg radA_pos.le _) h2 hp.out.ne_zero).trans ?_` and prove the remaining obligations.

Conclude with `radA_pow_le N`. Establish `hmem' : ∀ i N, (p : 𝔸) ^ j₀ i * phiAway ℂ_[p] p (s i N) ∈ ACrisZero ℂ_[p] p`. Introduce `i N`. Establish `e : (p : 𝔸) ^ j₀ i * phiAway ℂ_[p] p (s i N) = phiAway ℂ_[p] p ((p : 𝔸) ^ j₀ i * s i N)`. Rewrite using `[map_mul, map_pow, map_natCast]`.

Rewrite using `[e]`. Conclude with `phiAway_mem (hmem i N)`. Establish `hc' : ∀ i N, ∃ d : ACris ℂ_[p] p, ACris.phi ℂ_[p] p (c i) - algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) ⟨_, hmem' i N⟩ = (p : ACris ℂ_[p] p) ^ N * d`. Introduce `i N`. Take `⟨d, hd⟩` from `hc i N`.

Use `⟨ACris.phi ℂ_[p] p d, ?_⟩` and prove the remaining obligations. Establish `e : algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) ⟨_, hmem' i N⟩ = ACris.phi ℂ_[p] p (algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) ⟨_, hmem i N⟩)`. Rewrite using `[AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply, phi_of]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[coe_phiZero, map_mul, map_pow, map_natCast]`. Rewrite using `[e, ← map_sub, hd, map_mul, map_pow, map_natCast]`. Establish `hιφ : ∀ i, (p : 𝔹) ^ j₀ i * iota p hρσ ((frob ℂ_[p] p).extFrob (radTwo p) (rep (ha i) (radTwo p))) = ACris.iota ℂ_[p] p (ACris.phi ℂ_[p] p (c i))` using `fun i => pow_mul_iota_eq hρσ (j₀ i) (fun N => phiAway ℂ_[p] p (s i N)) (fun N => hR0' N i) (hmem' i) (hc' i)`. Use `⟨fun i => algebraMap _ (BCrisPlus ℂ_[p] p) (c i) * pInv p ^ j₀ i, ?_, ?_⟩` and prove the remaining obligations. Introduce `i ρ hρ z hz`.

Rewrite using `[iotaPlus_div_eq (hι i)]`. Conclude with `iota_eq_of_ofRad_eq hρ₂ hρ (by rw [ofRad_rep, hz])`. Introduce `i`. Apply `iotaPlus_injective` to reduce the goal to its premises. Establish `e1 : phiPlus ℂ_[p] p (algebraMap _ (BCrisPlus ℂ_[p] p) (c i) * pInv p ^ j₀ i) = algebraMap _ (BCrisPlus ℂ_[p] p) (ACris.phi ℂ_[p] p (c i)) * pInv p ^ j₀ i`.

Rewrite using `[map_mul, map_pow, phiPlus_algebraMap, phiPlus_pInv]`. Rewrite using `[e1, iotaPlus_div_eq (hιφ i), extFrob_rep C hy ha i (radTwo p), map_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_natCast, iota_awayToExt, map_mul, map_mul, map_natCast, iotaPlus_ainfToBCrisPlus, iotaPlus_div_eq (hι j)]`. Use `congr 1`.

Conclude with `iota_eq_of_ofRad_eq hρσ hρ₂ (by rw [ofRad_rep, ofRad_rep])`.
-/
theorem exists_bCrisPlus {m : ℕ} (C : Matrix (Fin m) (Fin m) (AInf ℂ_[p] p))
    (y : Fin m → (𝓣).RobbaTilde)
    (hy : ∀ i, (frob ℂ_[p] p).tildeFrob (y i) =
      ∑ j, (p : (𝓣).RobbaTilde) * ainfTilde p (C i j) * y j) :
    (∀ (i : Fin m) (ρ : Set.Ioo (0 : ℝ) 1), ∃ z : (𝓣).RobbaExt ρ, (𝓣).ofRad ρ z = y i) ∧
    ∃ b : Fin m → BCrisPlus ℂ_[p] p,
      (∀ (i : Fin m) (ρ : Set.Ioo (0 : ℝ) 1) (hρ : (p : ℝ)⁻¹ < ρ) (z : (𝓣).RobbaExt ρ),
        (𝓣).ofRad ρ z = y i → iotaPlus ℂ_[p] p (b i) = iota p hρ z) ∧
      ∀ i, phiPlus ℂ_[p] p (b i) = ∑ j, (p : BCrisPlus ℂ_[p] p) * ainfToBCrisPlus p (C i j) * b j := by
  have ha : ∀ i, y i ∈ allRad p :=
    mem_allRad_of_tildeFrob_eq (fun i j => (p : (𝓣).RobbaTilde) * ainfTilde p (C i j))
      (fun i j => Subring.mul_mem _ (natCast_mem _ p) (ainfTilde_mem_allRad _)) y hy
  refine ⟨fun i ρ => mem_allRad.1 (ha i) ρ, ?_⟩

  set M : ℝ := 1 + ∑ j, tn (ha j) (radC p) with hMdef
  have hM : 1 ≤ M := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => tn_nonneg _ _)
  have hdec : ∀ i (k : ℕ), tn (ha i) ((frob ℂ_[p] p).rootRadius^[k] (radC p)) ^ (p ^ k) ≤
      ((radC p : Set.Ioo (0 : ℝ) 1) : ℝ) ^ k * M := by
    intro i k
    obtain ⟨j, hj⟩ := exists_tn_pow_pow_le C hy ha k i ((frob ℂ_[p] p).rootRadius^[k] (radC p))
    rw [iterate_powRadius_rootRadius] at hj
    have e : (((frob ℂ_[p] p).rootRadius^[k] (radC p) : Set.Ioo (0 : ℝ) 1) : ℝ) ^ (k * p ^ k) =
        ((radC p : Set.Ioo (0 : ℝ) 1) : ℝ) ^ k := by
      rw [mul_comm, pow_mul, pow_iterate_rootRadius]
    rw [e] at hj
    refine hj.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (radC p).2.1.le _))
    exact (Finset.single_le_sum (f := fun j => tn (ha j) (radC p)) (fun j _ => tn_nonneg _ _)
      (Finset.mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)

  choose s hs1 hs2 using fun i (N : ℕ) => exists_approx (ha i) hM (hdec i) (pow_pos (radA_pos (p := p)) N)
  have hY : ∀ i, ∃ j₀ : ℕ, max (tn (ha i) ⟨radA p, radA_pos, radA_lt_one⟩) 1 ≤
      radA p ^ (-(j₀ : ℤ)) := by
    intro i
    set Y := max (tn (ha i) ⟨radA p, radA_pos (p := p), radA_lt_one (p := p)⟩) 1
    have hY0 : 0 < Y := zero_lt_one.trans_le (le_max_right _ _)
    obtain ⟨j₀, hj₀⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hY0) (radA_lt_one (p := p))
    refine ⟨j₀, ?_⟩
    rw [zpow_neg, zpow_natCast]
    exact (le_inv_comm₀ (pow_pos radA_pos j₀) hY0).1 hj₀.le
  choose j₀ hj₀ using hY
  have hmem : ∀ i N, (p : 𝔸) ^ j₀ i * s i N ∈ ACrisZero ℂ_[p] p :=
    fun i N => pow_mul_mem_acrisZero ((hs2 i N).trans (hj₀ i))
  have hrA : radA p ≤ ((radTwo p : Set.Ioo (0 : ℝ) 1) : ℝ) := radA_lt_radTwo.le
  have hdiff : ∀ i (N N' : ℕ), N ≤ N' → gn ℂ_[p] p (radA p) (s i N - s i N') ≤ radA p ^ N := by
    intro i N N' hNN'
    have e1 := extNorm_awayToExt (radTwo p) ⟨radA p, radA_pos, hrA⟩ (s i N - s i N')
    have e2 : awayToExt p (radTwo p) (s i N - s i N') =
        (rep (ha i) (radTwo p) - awayToExt p (radTwo p) (s i N')) -
          (rep (ha i) (radTwo p) - awayToExt p (radTwo p) (s i N)) := by
      rw [map_sub]; ring
    rw [← e1, e2, sub_eq_add_neg]
    refine ((𝓣).extNorm_add_le _ _ _).trans (max_le ?_ ?_)
    · exact (hs1 i N' _ le_rfl).trans (pow_le_pow_of_le_one radA_pos.le radA_lt_one.le hNN')
    · rw [(𝓣).extNorm_neg]; exact hs1 i N _ le_rfl

  have hlim : ∀ i, ∃ c : ACris ℂ_[p] p, ∀ N, ∃ d : ACris ℂ_[p] p,
      c - algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) ⟨_, hmem i N⟩ =
        (p : ACris ℂ_[p] p) ^ N * d := by
    intro i
    refine exists_limit (fun N => ⟨_, hmem i N⟩) fun N N' hNN' => ?_
    obtain ⟨d, hd, he⟩ := exists_pow_mul_eq (j := j₀ i) (hdiff i N N' hNN')
    refine ⟨⟨d, hd⟩, Subtype.ext ?_⟩
    simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_pow]
    rw [← mul_sub, he]
    simp
  choose c hc using hlim

  have hρ₂ : (p : ℝ)⁻¹ < ((radTwo p : Set.Ioo (0 : ℝ) 1) : ℝ) := inv_p_lt_radTwo
  have hR0 : ∀ N i, (𝓣).extNorm (radTwo p) (inversePRadius p hρ₂)
      (rep (ha i) (radTwo p) - awayToExt p (radTwo p) (s i N)) ≤ (p : ℝ) ^ (-(N : ℤ)) :=
    fun N i => (hs1 i N _ radA_lt_inv_p.le).trans (radA_pow_le N)
  have hι : ∀ i, (p : 𝔹) ^ j₀ i * iota p hρ₂ (rep (ha i) (radTwo p)) = ACris.iota ℂ_[p] p (c i) :=
    fun i => pow_mul_iota_eq hρ₂ (j₀ i) (s i) (fun N => hR0 N i) (hmem i) (hc i)

  set σ := (frob ℂ_[p] p).powRadius (radTwo p) with hσ
  have hσρ : ((σ : Set.Ioo (0 : ℝ) 1) : ℝ) = rhoMid p :=
    congrArg Subtype.val ((frob ℂ_[p] p).powRadius_rootRadius (rhoMid p))
  have hρσ : (p : ℝ)⁻¹ < ((σ : Set.Ioo (0 : ℝ) 1) : ℝ) := by rw [hσρ]; exact inv_p_lt_rhoMid
  set r' : Set.Ioc (0 : ℝ) (radTwo p) := ⟨((p : ℝ)⁻¹) ^ ((p : ℝ)⁻¹),
    Real.rpow_pos_of_pos inv_p_pos _, by
      show ((p : ℝ)⁻¹) ^ ((p : ℝ)⁻¹) ≤ (((frob ℂ_[p] p).rootRadius (rhoMid p) :
        Set.Ioo (0 : ℝ) 1) : ℝ)
      rw [rootRadius_coe]
      exact Real.rpow_le_rpow inv_p_pos.le inv_p_lt_rhoMid.le (inv_pos.2 (Nat.cast_pos.2
        hp.out.pos)).le⟩ with hr'
  have hr'A : radA p ≤ (r' : ℝ) :=
    radA_lt_inv_p.le.trans (Real.self_le_rpow_of_le_one inv_p_pos.le inv_p_lt_one.le
      inv_p_lt_one.le)
  have hpowRad : (frob ℂ_[p] p).powRad r' = inversePRadius p hρσ := by
    apply Subtype.ext
    rw [TeichLift.TeichFrob.coe_powRad, frob_a, pow_one]
    exact Real.rpow_inv_natCast_pow inv_p_pos.le hp.out.ne_zero
  have hphiS : ∀ N i, awayToExt p σ (phiAway ℂ_[p] p (s i N)) =
      (frob ℂ_[p] p).extFrob (radTwo p) (awayToExt p (radTwo p) (s i N)) := by
    intro N i
    rw [awayToExt_eq_ofAll, awayToExt_eq_ofAll, TeichLift.TeichFrob.extFrob_ofAll]
    exact (𝓣).ofAll_congr _ _ (toB_phiAway _) _
  have hR0' : ∀ N i, (𝓣).extNorm σ (inversePRadius p hρσ)
      ((frob ℂ_[p] p).extFrob (radTwo p) (rep (ha i) (radTwo p)) -
        awayToExt p σ (phiAway ℂ_[p] p (s i N))) ≤ (p : ℝ) ^ (-(N : ℤ)) := by
    intro N i
    rw [hphiS, ← map_sub, ← hpowRad, TeichLift.TeichFrob.extNorm_extFrob, frob_a, pow_one]
    have h1 := hs1 i N r' hr'A
    have h2 : radA p ^ N ≤ 1 := pow_le_one₀ radA_pos.le radA_lt_one.le
    refine (pow_le_pow_left₀ ((𝓣).extNorm_nonneg _ _) h1 p).trans ?_
    refine (pow_le_of_le_one (pow_nonneg radA_pos.le _) h2 hp.out.ne_zero).trans ?_
    exact radA_pow_le N
  have hmem' : ∀ i N, (p : 𝔸) ^ j₀ i * phiAway ℂ_[p] p (s i N) ∈ ACrisZero ℂ_[p] p := by
    intro i N
    have e : (p : 𝔸) ^ j₀ i * phiAway ℂ_[p] p (s i N) = phiAway ℂ_[p] p ((p : 𝔸) ^ j₀ i * s i N) := by
      rw [map_mul, map_pow, map_natCast]
    rw [e]
    exact phiAway_mem (hmem i N)
  have hc' : ∀ i N, ∃ d : ACris ℂ_[p] p,
      ACris.phi ℂ_[p] p (c i) - algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) ⟨_, hmem' i N⟩ =
        (p : ACris ℂ_[p] p) ^ N * d := by
    intro i N
    obtain ⟨d, hd⟩ := hc i N
    refine ⟨ACris.phi ℂ_[p] p d, ?_⟩
    have e : algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) ⟨_, hmem' i N⟩ =
        ACris.phi ℂ_[p] p (algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) ⟨_, hmem i N⟩) := by
      rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, RingHom.id_apply, phi_of]
      congr 1
      apply Subtype.ext
      rw [coe_phiZero, map_mul, map_pow, map_natCast]
    rw [e, ← map_sub, hd, map_mul, map_pow, map_natCast]
  have hιφ : ∀ i, (p : 𝔹) ^ j₀ i *
      iota p hρσ ((frob ℂ_[p] p).extFrob (radTwo p) (rep (ha i) (radTwo p))) =
        ACris.iota ℂ_[p] p (ACris.phi ℂ_[p] p (c i)) :=
    fun i => pow_mul_iota_eq hρσ (j₀ i) (fun N => phiAway ℂ_[p] p (s i N))
      (fun N => hR0' N i) (hmem' i) (hc' i)

  refine ⟨fun i => algebraMap _ (BCrisPlus ℂ_[p] p) (c i) * pInv p ^ j₀ i, ?_, ?_⟩
  · intro i ρ hρ z hz
    rw [iotaPlus_div_eq (hι i)]
    exact iota_eq_of_ofRad_eq hρ₂ hρ (by rw [ofRad_rep, hz])
  · intro i
    apply iotaPlus_injective
    have e1 : phiPlus ℂ_[p] p (algebraMap _ (BCrisPlus ℂ_[p] p) (c i) * pInv p ^ j₀ i) =
        algebraMap _ (BCrisPlus ℂ_[p] p) (ACris.phi ℂ_[p] p (c i)) * pInv p ^ j₀ i := by
      rw [map_mul, map_pow, phiPlus_algebraMap, phiPlus_pInv]
    rw [e1, iotaPlus_div_eq (hιφ i), extFrob_rep C hy ha i (radTwo p), map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, map_natCast, iota_awayToExt, map_mul, map_mul, map_natCast,
      iotaPlus_ainfToBCrisPlus, iotaPlus_div_eq (hι j)]
    congr 1
    exact iota_eq_of_ofRad_eq hρσ hρ₂ (by rw [ofRad_rep, ofRad_rep])

/- English proof (translation)
Take `⟨hext, b, hb, hφ⟩` from `exists_bCrisPlus C y hy`. Use `⟨fun i => ?_, b, fun i => ?_, hφ⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `hext i (rhoMid p)`. Conclude with `⟨rhoMid p, inv_p_lt_rhoMid, z, hz⟩`. Take `⟨z, hz⟩` from `hext i (rhoMid p)`.

Rewrite using `[hb i (rhoMid p) inv_p_lt_rhoMid z hz, ← hz, iotaTildeFun_ofRad]`.
-/
theorem exists_bCrisPlus_iotaTilde {m : ℕ} (C : Matrix (Fin m) (Fin m) (AInf ℂ_[p] p))
    (y : Fin m → (𝓣).RobbaTilde)
    (hy : ∀ i, (frob ℂ_[p] p).tildeFrob (y i) =
      ∑ j, (p : (𝓣).RobbaTilde) * ainfTilde p (C i j) * y j) :
    (∀ i, y i ∈ tildeDom p) ∧ ∃ b : Fin m → BCrisPlus ℂ_[p] p,
      (∀ i, iotaPlus ℂ_[p] p (b i) = iotaTildeFun p (y i)) ∧
      ∀ i, phiPlus ℂ_[p] p (b i) = ∑ j, (p : BCrisPlus ℂ_[p] p) * ainfToBCrisPlus p (C i j) * b j := by
  obtain ⟨hext, b, hb, hφ⟩ := exists_bCrisPlus C y hy
  refine ⟨fun i => ?_, b, fun i => ?_, hφ⟩
  · obtain ⟨z, hz⟩ := hext i (rhoMid p)
    exact ⟨rhoMid p, inv_p_lt_rhoMid, z, hz⟩
  · obtain ⟨z, hz⟩ := hext i (rhoMid p)
    rw [hb i (rhoMid p) inv_p_lt_rhoMid z hz, ← hz, iotaTildeFun_ofRad]

end WABridge

end GroundTheory.PAdicHodge
