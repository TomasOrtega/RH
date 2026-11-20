import Mathlib
import GroundTheory.PAdicHodge.WABridge
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WABridge

open _root_.WittVector WittTilt WAEval TeichLift PhiGamma Laurent ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p

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

Rewrite using `[coe_phiZero, map_mul, map_pow, map_natCast]`. Rewrite using `[e, ← map_sub, hd, map_mul, map_pow, map_natCast]`. Establish `hιφ : ∀ i, (p : 𝔹) ^ j₀ i * iota p hρσ ((frob ℂ_[p] p).extFrob (radTwo p) (rep (ha i) (radTwo p))) = ACris.iota ℂ_[p] p (ACris.phi ℂ_[p] p (c i))` using `fun i => pow_mul_iota_eq hρσ (j₀ i) (fun N => phiAway ℂ_[p] p (s i N)) (fun N => hR0' N i) (hmem' i) (hc' i)`. Use `⟨fun i => algebraMap _ (BCrisPlus ℂ_[p] p) (c i) * pInv p ^ j₀ i, j₀, s, c, fun i N => ⟨_, hmem i N⟩, ?_, ?_, fun i N => rfl, hc, fun i => rfl, ?_⟩` and prove the remaining obligations. Introduce `i ρ hρ z hz`.

Rewrite using `[iotaPlus_div_eq (hι i)]`. Conclude with `iota_eq_of_ofRad_eq hρ₂ hρ (by rw [ofRad_rep, hz])`. Introduce `i`. Apply `iotaPlus_injective` to reduce the goal to its premises. Establish `e1 : phiPlus ℂ_[p] p (algebraMap _ (BCrisPlus ℂ_[p] p) (c i) * pInv p ^ j₀ i) = algebraMap _ (BCrisPlus ℂ_[p] p) (ACris.phi ℂ_[p] p (c i)) * pInv p ^ j₀ i`.

Rewrite using `[map_mul, map_pow, phiPlus_algebraMap, phiPlus_pInv]`. Rewrite using `[e1, iotaPlus_div_eq (hιφ i), extFrob_rep C hy ha i (radTwo p), map_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_natCast, iota_awayToExt, map_mul, map_mul, map_natCast, iotaPlus_ainfToBCrisPlus, iotaPlus_div_eq (hι j)]`. Use `congr 1`.

Conclude with `iota_eq_of_ofRad_eq hρσ hρ₂ (by rw [ofRad_rep, ofRad_rep])`. Introduce `i N ρ' hρ' z hz r hr`. Establish `e : (𝓣).res hρ' z = rep (ha i) (radTwo p)` using `(𝓣).ofRad_injective (radTwo p) (by rw [(𝓣).ofRad_res, hz, ofRad_rep])`. Rewrite using `[e]`. Conclude with `hs1 i N r hr`.
-/
theorem exists_bCrisPlus_approx {m : ℕ} (C : Matrix (Fin m) (Fin m) (AInf ℂ_[p] p))
    (y : Fin m → (𝓣).RobbaTilde)
    (hy : ∀ i, (frob ℂ_[p] p).tildeFrob (y i) =
      ∑ j, (p : (𝓣).RobbaTilde) * ainfTilde p (C i j) * y j) :
    (∀ (i : Fin m) (ρ : Set.Ioo (0 : ℝ) 1), ∃ z : (𝓣).RobbaExt ρ, (𝓣).ofRad ρ z = y i) ∧
    ∃ (b : Fin m → BCrisPlus ℂ_[p] p) (j₀ : Fin m → ℕ) (s : Fin m → ℕ → 𝔸)
      (c : Fin m → ACris ℂ_[p] p) (t : Fin m → ℕ → ACrisZero ℂ_[p] p),
      (∀ (i : Fin m) (ρ : Set.Ioo (0 : ℝ) 1) (hρ : (p : ℝ)⁻¹ < ρ) (z : (𝓣).RobbaExt ρ),
        (𝓣).ofRad ρ z = y i → iotaPlus ℂ_[p] p (b i) = iota p hρ z) ∧
      (∀ i, phiPlus ℂ_[p] p (b i) = ∑ j, (p : BCrisPlus ℂ_[p] p) * ainfToBCrisPlus p (C i j) * b j) ∧
      (∀ i N, ((t i N : ACrisZero ℂ_[p] p) : 𝔸) = (p : 𝔸) ^ j₀ i * s i N) ∧
      (∀ i N, ∃ d : ACris ℂ_[p] p,
        c i - algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) (t i N) = (p : ACris ℂ_[p] p) ^ N * d) ∧
      (∀ i, b i = algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (c i) * pInv p ^ j₀ i) ∧
      (∀ i N (ρ' : Set.Ioo (0 : ℝ) 1) (hρ' : ((radTwo p : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ ρ')
        (z : (𝓣).RobbaExt ρ'), (𝓣).ofRad ρ' z = y i →
        ∀ r : Set.Ioc (0 : ℝ) (radTwo p), radA p ≤ r →
          (𝓣).extNorm (radTwo p) r ((𝓣).res hρ' z - awayToExt p (radTwo p) (s i N)) ≤
            radA p ^ N) := by
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

  refine ⟨fun i => algebraMap _ (BCrisPlus ℂ_[p] p) (c i) * pInv p ^ j₀ i, j₀, s, c,
    fun i N => ⟨_, hmem i N⟩, ?_, ?_, fun i N => rfl, hc, fun i => rfl, ?_⟩
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
  · intro i N ρ' hρ' z hz r hr
    have e : (𝓣).res hρ' z = rep (ha i) (radTwo p) :=
      (𝓣).ofRad_injective (radTwo p) (by rw [(𝓣).ofRad_res, hz, ofRad_rep])
    rw [e]
    exact hs1 i N r hr

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hy' : ∀ i : Fin 1, (frob ℂ_[p] p).tildeFrob ((fun _ => y) i) = ∑ j, (p : (𝓣).RobbaTilde) * ainfTilde p ((fun _ _ => (p : AInf ℂ_[p] p) ^ k : Matrix (Fin 1) (Fin 1) (AInf ℂ_[p] p)) i j) * (fun _ => y) j`. Introduce `i`. Rewrite using `[Fin.sum_univ_one, map_pow, map_natCast, hy]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨hext, b, j₀, s, c, t, hι, hφ, ht, hc, hb, happ⟩` from `exists_bCrisPlus_approx _ _ hy'`.

Use `⟨hext 0, b 0, j₀ 0, s 0, c 0, t 0, hι 0, ?_, ht 0, hc 0, hb 0, happ 0⟩` and prove the remaining obligations. Rewrite using `[hφ 0, Fin.sum_univ_one, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_bCrisPlus_approx_single (k : ℕ) (y : (𝓣).RobbaTilde)
    (hy : (frob ℂ_[p] p).tildeFrob y = (p : (𝓣).RobbaTilde) ^ (k + 1) * y) :
    (∀ ρ : Set.Ioo (0 : ℝ) 1, ∃ z : (𝓣).RobbaExt ρ, (𝓣).ofRad ρ z = y) ∧
    ∃ (b : BCrisPlus ℂ_[p] p) (j₀ : ℕ) (s : ℕ → 𝔸) (c : ACris ℂ_[p] p) (t : ℕ → ACrisZero ℂ_[p] p),
      (∀ (ρ : Set.Ioo (0 : ℝ) 1) (hρ : (p : ℝ)⁻¹ < ρ) (z : (𝓣).RobbaExt ρ),
        (𝓣).ofRad ρ z = y → iotaPlus ℂ_[p] p b = iota p hρ z) ∧
      phiPlus ℂ_[p] p b = (p : BCrisPlus ℂ_[p] p) ^ (k + 1) * b ∧
      (∀ N, ((t N : ACrisZero ℂ_[p] p) : 𝔸) = (p : 𝔸) ^ j₀ * s N) ∧
      (∀ N, ∃ d : ACris ℂ_[p] p,
        c - algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) (t N) = (p : ACris ℂ_[p] p) ^ N * d) ∧
      b = algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) c * pInv p ^ j₀ ∧
      (∀ N (ρ' : Set.Ioo (0 : ℝ) 1) (hρ' : ((radTwo p : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ ρ')
        (z : (𝓣).RobbaExt ρ'), (𝓣).ofRad ρ' z = y →
        ∀ r : Set.Ioc (0 : ℝ) (radTwo p), radA p ≤ r →
          (𝓣).extNorm (radTwo p) r ((𝓣).res hρ' z - awayToExt p (radTwo p) (s N)) ≤ radA p ^ N) := by
  have hy' : ∀ i : Fin 1, (frob ℂ_[p] p).tildeFrob ((fun _ => y) i) =
      ∑ j, (p : (𝓣).RobbaTilde) * ainfTilde p ((fun _ _ => (p : AInf ℂ_[p] p) ^ k :
        Matrix (Fin 1) (Fin 1) (AInf ℂ_[p] p)) i j) * (fun _ => y) j := by
    intro i
    rw [Fin.sum_univ_one, map_pow, map_natCast, hy]
    ring
  obtain ⟨hext, b, j₀, s, c, t, hι, hφ, ht, hc, hb, happ⟩ := exists_bCrisPlus_approx _ _ hy'
  refine ⟨hext 0, b 0, j₀ 0, s 0, c 0, t 0, hι 0, ?_, ht 0, hc 0, hb 0, happ 0⟩
  rw [hφ 0, Fin.sum_univ_one, map_pow, map_natCast]
  ring

end WABridge

end GroundTheory.PAdicHodge
