import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDivisibilityBreuilKisinFactsStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.OEmod

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K)

def ψ : bk.S →+* Cb l := (WittVector.constantCoeff (p := l) (R := Cb l)).comp bk.evW

/- English proof (translation)
Simplify using `[ψ, BK.evW, inclW, WittVector.constantCoeff_apply, WittVector.map_coeff]`.
-/
theorem ψ_apply (s : bk.S) : ψ bk s = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := by
  simp [ψ, BK.evW, inclW, WittVector.constantCoeff_apply, WittVector.map_coeff]

/- English proof (translation)
Rewrite using `[ψ_apply, bk.ev_X, WittVector.teichmuller_coeff_zero]`.
-/
theorem ψ_X : ψ bk X = algebraMap (OCb l) (Cb l) bk.flat := by
  rw [ψ_apply, bk.ev_X, WittVector.teichmuller_coeff_zero]

/- English proof (translation)
The claim follows from `ψ_X bk`.
-/
theorem cc_evW_X : WittVector.constantCoeff (bk.evW X) = algebraMap (OCb l) (Cb l) bk.flat := ψ_X bk

/- English proof (translation)
Rewrite using `[WittVector.constantCoeff_apply, mul_comm]`. Conclude with `WittVector.mul_charP_coeff_zero y`.
-/
theorem cc_l_mul (y : WCb l) : WittVector.constantCoeff ((l : WCb l) * y) = 0 := by
  rw [WittVector.constantCoeff_apply, mul_comm]
  exact WittVector.mul_charP_coeff_zero y

/- English proof (translation)
Simplify using `[BK.evW, bk.ev_X, inclW, WittVector.map_teichmuller]`.
-/
theorem evW_X_eq : bk.evW X = WittVector.teichmuller l (algebraMap (OCb l) (Cb l) bk.flat) := by
  simp [BK.evW, bk.ev_X, inclW, WittVector.map_teichmuller]

/- English proof (translation)
Distinguish the cases in `h0 : x = 0`. Conclude with `h0 ▸ dvd_zero _`. Take `⟨m, b, hb, rfl⟩` from `WittVector.exists_eq_pow_p_mul x h0`. Consider the cases of `m with`. Consider the case `zero => exact absurd (by simpa using WittVector.isUnit_of_coeff_zero_ne_zero b hb) h`.

Consider the case `succ m => exact Dvd.intro _ (by rw [pow_succ', mul_assoc])`.
-/
theorem l_dvd_of_not_isUnit (a : ℕ) [NeZero a] (x : Wq l a) (h : ¬ IsUnit x) : (l : Wq l a) ∣ x := by
  by_cases h0 : x = 0
  · exact h0 ▸ dvd_zero _
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul x h0
  cases m with
  | zero => exact absurd (by simpa using WittVector.isUnit_of_coeff_zero_ne_zero b hb) h
  | succ m => exact Dvd.intro _ (by rw [pow_succ', mul_assoc])

/- English proof (translation)
Establish `hex : ∃ i, IsUnit (coeff i s)`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Establish `hd : ∀ i, (l : Wq l bk.a) ∣ coeff i s` using `fun i => l_dvd_of_not_isUnit bk.a _ (hno i)`. Use `choose c hc using hd`.

Establish `: s = (l : bk.S) * PowerSeries.mk c`. Use extensionality with `i`. Rewrite using `[← map_natCast (C (R := Wq l bk.a)), coeff_C_mul, coeff_mk, hc i]`. Apply `hs` to reduce the goal to its premises. Rewrite using `[this, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]`.

Set `k` to `Nat.find hex`. Establish `hk : IsUnit (coeff k s)` using `Nat.find_spec hex`. Establish `hlt : ∀ i < k, (l : Wq l bk.a) ∣ coeff i s` using `fun i hi => l_dvd_of_not_isUnit bk.a _ (Nat.find_min hex hi)`. Use `choose! c hc using hlt`. Set `s₁ : bk.S` to `PowerSeries.mk fun i => coeff (i + k) s`.

Set `s₂ : bk.S` to `PowerSeries.mk fun i => if i < k then c i else 0`. Establish `hs₁ : IsUnit s₁`. Rewrite using `[isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add]`. Conclude with `hk`. Establish `hsplit : s = X ^ k * s₁ + (l : bk.S) * s₂`.

Use extensionality with `i`. Rewrite using `[map_add, coeff_X_pow_mul', ← map_natCast (C (R := Wq l bk.a)), coeff_C_mul, coeff_mk, coeff_mk]`. Distinguish the cases in `hi : i < k`. Rewrite using `[if_neg (by omega), if_pos hi, zero_add, hc i hi]`. Rewrite using `[if_pos (by omega), if_neg hi, mul_zero, add_zero, Nat.sub_add_cancel (by omega)]`.

Use `⟨k, s₁, hs₁, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [hsplit]`. Rewrite using `[map_add, map_mul, map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]`.
-/
theorem exists_unit (s : bk.S) (hs : ψ bk s ≠ 0) :
    ∃ (k : ℕ) (s₁ : bk.S), IsUnit s₁ ∧ ψ bk s = ψ bk X ^ k * ψ bk s₁ := by
  have hex : ∃ i, IsUnit (coeff i s) := by
    by_contra hno
    push_neg at hno
    have hd : ∀ i, (l : Wq l bk.a) ∣ coeff i s := fun i => l_dvd_of_not_isUnit bk.a _ (hno i)
    choose c hc using hd
    have : s = (l : bk.S) * PowerSeries.mk c := by
      ext i
      rw [← map_natCast (C (R := Wq l bk.a)), coeff_C_mul, coeff_mk, hc i]
    apply hs
    rw [this, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
  classical
  let k := Nat.find hex
  have hk : IsUnit (coeff k s) := Nat.find_spec hex
  have hlt : ∀ i < k, (l : Wq l bk.a) ∣ coeff i s := fun i hi =>
    l_dvd_of_not_isUnit bk.a _ (Nat.find_min hex hi)
  choose! c hc using hlt
  let s₁ : bk.S := PowerSeries.mk fun i => coeff (i + k) s
  let s₂ : bk.S := PowerSeries.mk fun i => if i < k then c i else 0
  have hs₁ : IsUnit s₁ := by
    rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add]
    exact hk
  have hsplit : s = X ^ k * s₁ + (l : bk.S) * s₂ := by
    ext i
    rw [map_add, coeff_X_pow_mul', ← map_natCast (C (R := Wq l bk.a)), coeff_C_mul, coeff_mk, coeff_mk]
    by_cases hi : i < k
    · rw [if_neg (by omega), if_pos hi, zero_add, hc i hi]
    · rw [if_pos (by omega), if_neg hi, mul_zero, add_zero, Nat.sub_add_cancel (by omega)]
  refine ⟨k, s₁, hs₁, ?_⟩
  conv_lhs => rw [hsplit]
  rw [map_add, map_mul, map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]

end GlobalTheory.BSP.OEmod

open GlobalTheory.BSP.OEmod in
/- English proof (translation)
Introduce `l _ K bk`. Establish `hflat : bk.flat ≠ 0` using `(GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk).2.2.2.1`. Establish `hf : algebraMap (OCb l) (Cb l) bk.flat ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 hflat`. Establish `hunit : IsUnit (bk.evW X)`. Rewrite using `[evW_X_eq]`.

Apply `WittVector.isUnit_of_coeff_zero_ne_zero` to reduce the goal to its premises. Rewrite using `[WittVector.teichmuller_coeff_zero]`. Conclude with `hf`. Establish `h1 : ∀ y : Cb l, y ∈ bk.OE.map (WittVector.constantCoeff (p` using `l) (R := Cb l)) ↔ ∃ (m : ℕ) (s : bk.S), algebraMap (OCb l) (Cb l) bk.flat ^ m * y = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := by`. Introduce `y`.

Rewrite using `[Subring.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Take `⟨m, s, z, h⟩` from `hw 1`. Use `⟨m, s, ?_⟩` and prove the remaining obligations.

Use `congrArg (WittVector.constantCoeff (p := l) (R := Cb l)) h` as an intermediate fact. Rewrite `this` using `[map_mul, map_pow, map_add, pow_one, cc_l_mul, add_zero, cc_evW_X]`. Rewrite using `[this, ← ψ_apply]`. Both sides reduce to the same expression. Introduce and unpack `⟨m, s, h⟩`.

Take `⟨u, hu⟩` from `hunit`. Use `⟨(↑(u⁻¹) : WCb l) ^ m * bk.evW s, fun n => ⟨m, s, 0, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_zero, add_zero, ← mul_assoc, ← mul_pow, ← hu, Units.mul_inv, one_pow, one_mul]`. Establish `hc : WittVector.constantCoeff (bk.evW X) * WittVector.constantCoeff ((↑(u⁻¹) : WCb l)) = 1`. Rewrite using `[← map_mul, ← hu, Units.mul_inv, map_one]`.

Rewrite `hc` using `[cc_evW_X]`. Rewrite using `[map_mul, map_pow]`. Establish `hs : WittVector.constantCoeff (bk.evW s) = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0)` using `ψ_apply bk s`. Rewrite using `[hs, ← h, ← mul_assoc, ← mul_pow, mul_comm _ (algebraMap (OCb l) (Cb l) bk.flat), hc, one_pow, one_mul]`. Use `⟨h1, fun s n => ⟨0, s, 0, by simp⟩, hunit, fun w hw n => ?_, fun y hy => ?_⟩` and prove the remaining obligations.

Take `⟨m, s, z, h⟩` from `hw n`. Conclude with `⟨m + 1, s, z, by rw [pow_succ, mul_assoc, h]⟩`. Distinguish the cases in `hy0 : y = 0`. Rewrite using `[hy0, inv_zero]`. Conclude with `Subring.zero_mem _`.

Take `⟨m, s, h⟩` from `(h1 y).1 hy`. Rewrite `h` using `[← ψ_apply]`. Establish `hs : ψ bk s ≠ 0` using `by rw [← h]; exact mul_ne_zero (pow_ne_zero _ hf) hy0`. Take `⟨k, s₁, ⟨t, rfl⟩, hk⟩` from `exists_unit bk s hs`. Rewrite using `[h1]`.

Use `⟨k, ((X : bk.S) ^ m * ↑(t⁻¹) : bk.S), ?_⟩` and prove the remaining obligations. Rewrite using `[← ψ_apply, map_mul, map_pow, ψ_X]`. Rewrite `h` using `[hk, ψ_X]`. Establish `ht : ψ bk ↑t * ψ bk ↑(t⁻¹) = 1` using `by rw [← map_mul, Units.mul_inv, map_one]`. Establish `ht0 : ψ bk ↑t ≠ 0` using `left_ne_zero_of_mul_eq_one ht`.

Establish `hinv : ψ bk ↑(t⁻¹) = (ψ bk ↑t)⁻¹` using `eq_inv_of_mul_eq_one_right ht`. Rewrite using `[hinv]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-h`.
-/
theorem GlobalTheory.BSP.oe_mod_l : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ y : Cb l, y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) ↔ ∃ (m : ℕ) (s : bk.S), algebraMap (OCb l) (Cb l) bk.flat ^ m * y = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0)) ∧ (∀ s : bk.S, bk.evW s ∈ bk.OE) ∧ IsUnit (bk.evW X) ∧ (∀ w : WCb l, bk.evW X * w ∈ bk.OE → w ∈ bk.OE) ∧ ∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), y⁻¹ ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := by
  intro l _ K bk
  have hflat : bk.flat ≠ 0 := (GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk).2.2.2.1
  have hf : algebraMap (OCb l) (Cb l) bk.flat ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 hflat
  have hunit : IsUnit (bk.evW X) := by
    rw [evW_X_eq]
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [WittVector.teichmuller_coeff_zero]
    exact hf
  have h1 : ∀ y : Cb l, y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) ↔ ∃ (m : ℕ) (s : bk.S),
      algebraMap (OCb l) (Cb l) bk.flat ^ m * y = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := by
    intro y
    rw [Subring.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨m, s, z, h⟩ := hw 1
      refine ⟨m, s, ?_⟩
      have := congrArg (WittVector.constantCoeff (p := l) (R := Cb l)) h
      rw [map_mul, map_pow, map_add, pow_one, cc_l_mul, add_zero, cc_evW_X] at this
      rw [this, ← ψ_apply]
      rfl
    · rintro ⟨m, s, h⟩
      obtain ⟨u, hu⟩ := hunit
      refine ⟨(↑(u⁻¹) : WCb l) ^ m * bk.evW s, fun n => ⟨m, s, 0, ?_⟩, ?_⟩
      · rw [mul_zero, add_zero, ← mul_assoc, ← mul_pow, ← hu, Units.mul_inv, one_pow, one_mul]
      · have hc : WittVector.constantCoeff (bk.evW X) * WittVector.constantCoeff ((↑(u⁻¹) : WCb l)) = 1 := by
          rw [← map_mul, ← hu, Units.mul_inv, map_one]
        rw [cc_evW_X] at hc
        rw [map_mul, map_pow]
        have hs : WittVector.constantCoeff (bk.evW s) = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := ψ_apply bk s
        rw [hs, ← h, ← mul_assoc, ← mul_pow, mul_comm _ (algebraMap (OCb l) (Cb l) bk.flat), hc, one_pow, one_mul]
  refine ⟨h1, fun s n => ⟨0, s, 0, by simp⟩, hunit, fun w hw n => ?_, fun y hy => ?_⟩
  · obtain ⟨m, s, z, h⟩ := hw n
    exact ⟨m + 1, s, z, by rw [pow_succ, mul_assoc, h]⟩
  · by_cases hy0 : y = 0
    · rw [hy0, inv_zero]; exact Subring.zero_mem _
    obtain ⟨m, s, h⟩ := (h1 y).1 hy
    rw [← ψ_apply] at h
    have hs : ψ bk s ≠ 0 := by rw [← h]; exact mul_ne_zero (pow_ne_zero _ hf) hy0
    obtain ⟨k, s₁, ⟨t, rfl⟩, hk⟩ := exists_unit bk s hs
    rw [h1]
    refine ⟨k, ((X : bk.S) ^ m * ↑(t⁻¹) : bk.S), ?_⟩
    rw [← ψ_apply, map_mul, map_pow, ψ_X]
    rw [hk, ψ_X] at h
    have ht : ψ bk ↑t * ψ bk ↑(t⁻¹) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have ht0 : ψ bk ↑t ≠ 0 := left_ne_zero_of_mul_eq_one ht
    have hinv : ψ bk ↑(t⁻¹) = (ψ bk ↑t)⁻¹ := eq_inv_of_mul_eq_one_right ht
    rw [hinv]
    field_simp
    linear_combination -h
