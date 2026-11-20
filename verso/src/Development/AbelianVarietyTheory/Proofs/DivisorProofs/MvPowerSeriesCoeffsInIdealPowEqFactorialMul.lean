import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.DPSeries

section SlopeTestRemainingChoices

variable {B : Type} [CommRing B] {τ : Type}

def coeffIdeal (J : Ideal B) (τ : Type) : Ideal (MvPowerSeries τ B) where
  carrier := {f | ∀ α, coeff α f ∈ J}
  add_mem' {a b} ha hb α := by
    rw [map_add]
    exact J.add_mem (ha α) (hb α)
  zero_mem' α := by simp
  smul_mem' c f hf α := by
    classical
    rw [smul_eq_mul, coeff_mul]
    exact J.sum_mem fun x _ => J.mul_mem_left _ (hf _)

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro α _`. Both sides reduce to the same expression. Consider the case `succ n ih`.

Introduce `α hα`. Rewrite using `[pow_succ, pow_succ, coeff_mul, coeff_mul]`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `h1 : x.1 ≤ β` using `le_trans (by rw [← hx]; exact le_self_add) hα`.

Establish `h2 : x.2 ≤ β` using `le_trans (by rw [← hx]; exact le_add_self) hα`. Rewrite using `[ih _ h1, h _ h2]`.
-/
theorem coeff_pow_congr {f g : MvPowerSeries τ B} {β : τ →₀ ℕ}
    (h : ∀ α ≤ β, coeff α f = coeff α g) : ∀ n, ∀ α ≤ β, coeff α (f ^ n) = coeff α (g ^ n) := by
  classical
  intro n
  induction n with
  | zero => intro α _; rfl
  | succ n ih =>
    intro α hα
    rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have h1 : x.1 ≤ β := le_trans (by rw [← hx]; exact le_self_add) hα
    have h2 : x.2 ≤ β := le_trans (by rw [← hx]; exact le_add_self) hα
    rw [ih _ h1, h _ h2]

variable (p : ℕ) (J : Ideal B)

def HasPDiv (f : MvPowerSeries τ B) : Prop :=
  f ∈ coeffIdeal J τ ∧ ∃ y ∈ coeffIdeal J τ, f ^ p = (p : MvPowerSeries τ B) * y

variable {p J}

/- English proof (translation)
Take `⟨ha, ya, hya, hpa⟩` from `ha`. Take `⟨hb, yb, hyb, hpb⟩` from `hb`. Take `⟨r, hr⟩` from `exists_add_pow_prime_eq hp a b`. Use `⟨(coeffIdeal J τ).add_mem ha hb, ya + yb + a * b * r, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(coeffIdeal J τ).add_mem ((coeffIdeal J τ).add_mem hya hyb) ((coeffIdeal J τ).mul_mem_right _ ((coeffIdeal J τ).mul_mem_right _ ha))`.

Rewrite using `[hr, hpa, hpb]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasPDiv_add (hp : p.Prime) {a b : MvPowerSeries τ B} (ha : HasPDiv p J a)
    (hb : HasPDiv p J b) : HasPDiv p J (a + b) := by
  obtain ⟨ha, ya, hya, hpa⟩ := ha
  obtain ⟨hb, yb, hyb, hpb⟩ := hb
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp a b
  refine ⟨(coeffIdeal J τ).add_mem ha hb, ya + yb + a * b * r, ?_, ?_⟩
  · exact (coeffIdeal J τ).add_mem ((coeffIdeal J τ).add_mem hya hyb)
      ((coeffIdeal J τ).mul_mem_right _ ((coeffIdeal J τ).mul_mem_right _ ha))
  · rw [hr, hpa, hpb]; ring

/- English proof (translation)
Take `⟨y, hy, hcy⟩` from `hJ c hc`. Use `⟨fun γ => ?_, monomial (p • α) y, fun γ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_monomial]`. Use `split_ifs`. Conclude with `hc`.

Conclude with `J.zero_mem`. Rewrite using `[coeff_monomial]`. Use `split_ifs`. Conclude with `hy`. Conclude with `J.zero_mem`.

Rewrite using `[monomial_pow, hcy]`. Use extensionality with `γ`. Rewrite using `[coeff_monomial, ← map_natCast (C (σ := τ) (R := B)) p, coeff_C_mul, coeff_monomial]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem hasPDiv_monomial (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (α : τ →₀ ℕ) {c : B}
    (hc : c ∈ J) : HasPDiv p J (monomial α c) := by
  classical
  obtain ⟨y, hy, hcy⟩ := hJ c hc
  refine ⟨fun γ => ?_, monomial (p • α) y, fun γ => ?_, ?_⟩
  · rw [coeff_monomial]; split_ifs
    · exact hc
    · exact J.zero_mem
  · rw [coeff_monomial]; split_ifs
    · exact hy
    · exact J.zero_mem
  · rw [monomial_pow, hcy]
    ext γ
    rw [coeff_monomial, ← map_natCast (C (σ := τ) (R := B)) p, coeff_C_mul, coeff_monomial]
    split_ifs <;> simp

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use `⟨by simpa using (coeffIdeal J τ).zero_mem, 0, (coeffIdeal J τ).zero_mem, ?_⟩` and prove the remaining obligations. Simplify using `[hp.ne_zero]`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.sum_insert ha]`. Conclude with `hasPDiv_add hp (hasPDiv_monomial hJ a (hc a)) ih`.
-/
theorem hasPDiv_sum (hp : p.Prime) (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y)
    (c : (τ →₀ ℕ) → B) (hc : ∀ α, c α ∈ J) (s : Finset (τ →₀ ℕ)) :
    HasPDiv p J (∑ α ∈ s, monomial α (c α)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using (coeffIdeal J τ).zero_mem, 0, (coeffIdeal J τ).zero_mem, ?_⟩
    simp [hp.ne_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hasPDiv_add hp (hasPDiv_monomial hJ a (hc a)) ih

/- English proof (translation)
Establish `key : ∀ β : τ →₀ ℕ, ∃ c ∈ J, coeff β (w ^ p) = p * c`. Introduce `β`. Use `set w' : MvPowerSeries τ B := ∑ α ∈ Finset.Iic β, monomial α (coeff α w) with hw'`. Establish `hagree : ∀ α ≤ β, coeff α w = coeff α w'`. Introduce `α hα`.

Rewrite using `[hw', map_sum]`. Repeatedly rewrite using `[coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq]`. Simplify using `[Finset.mem_Iic.mpr hα]`. Take `⟨_, y, hy, hpy⟩` from `hasPDiv_sum hp hJ (fun α => coeff α w) hw (Finset.Iic β)`.

Use `⟨coeff β y, hy β, ?_⟩` and prove the remaining obligations. Establish `hpy' : w' ^ p = (p : MvPowerSeries τ B) * y` using `hpy`. Rewrite using `[coeff_pow_congr hagree p β le_rfl, hpy', ← map_natCast (C (σ := τ) (R := B)) p, coeff_C_mul]`. Use `choose c hcJ hc using key`. Set `y : MvPowerSeries τ B` to `fun β => c β`.

Establish `hy : ∀ β, coeff β y = c β` using `fun _ => rfl`. Use `⟨y, fun β => by rw [hy]; exact hcJ β, ?_⟩` and prove the remaining obligations. Use extensionality with `β`. Rewrite using `[hc, ← map_natCast (C (σ := τ) (R := B)) p, coeff_C_mul, hy]`.
-/
theorem pow_prime_eq (hp : p.Prime) (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y)
    {w : MvPowerSeries τ B} (hw : w ∈ coeffIdeal J τ) :
    ∃ y ∈ coeffIdeal J τ, w ^ p = (p : MvPowerSeries τ B) * y := by
  classical
  have key : ∀ β : τ →₀ ℕ, ∃ c ∈ J, coeff β (w ^ p) = p * c := by
    intro β
    set w' : MvPowerSeries τ B := ∑ α ∈ Finset.Iic β, monomial α (coeff α w) with hw'
    have hagree : ∀ α ≤ β, coeff α w = coeff α w' := by
      intro α hα
      rw [hw', map_sum]
      simp_rw [coeff_monomial]
      rw [Finset.sum_ite_eq]
      simp [Finset.mem_Iic.mpr hα]
    obtain ⟨_, y, hy, hpy⟩ := hasPDiv_sum hp hJ (fun α => coeff α w) hw (Finset.Iic β)
    refine ⟨coeff β y, hy β, ?_⟩
    have hpy' : w' ^ p = (p : MvPowerSeries τ B) * y := hpy
    rw [coeff_pow_congr hagree p β le_rfl, hpy',
      ← map_natCast (C (σ := τ) (R := B)) p, coeff_C_mul]
  choose c hcJ hc using key
  let y : MvPowerSeries τ B := fun β => c β
  have hy : ∀ β, coeff β y = c β := fun _ => rfl
  refine ⟨y, fun β => by rw [hy]; exact hcJ β, ?_⟩
  ext β
  rw [hc, ← map_natCast (C (σ := τ) (R := B)) p, coeff_C_mul, hy]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `hn w hw`. Distinguish the cases in `hpn : p ∣ n`.

Take `⟨m, rfl⟩` from `hpn`. Establish `hm : 0 < m` using `Nat.pos_of_ne_zero (by rintro rfl; simp at hn)`. Establish `hmn : m < p * m` using `by nlinarith [hp.two_le]`. Take `⟨z, hz, hwz⟩` from `pow_prime_eq hp hJ hw`. Take `⟨y, hy, hzy⟩` from `ih m hmn hm z hz`.

Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.factorization_factorial_mul hp, pow_mul, hwz, mul_pow, hzy]`. Expand and normalize the polynomial expressions, which then agree. Break down `Nat.lt_or_ge n 2 with h | h` into its components or cases. Establish `h1 : n = 1` using `by omega`.

Substitute `h1` using the available equality. Conclude with `⟨w, hw, by simp⟩`. Take `⟨k, rfl⟩ : ∃ k, n = k + 1` from `⟨n - 1, by omega⟩`. Take `⟨y, hy, hwy⟩` from `ih k (by omega) (by omega) w hw`. Use `⟨w * y, (coeffIdeal J τ).mul_mem_left _ hy, ?_⟩` and prove the remaining obligations.

Establish `hv : (k + 1).factorial.factorization p = k.factorial.factorization p`. Rewrite using `[Nat.factorial_succ, Nat.factorization_mul (Nat.succ_ne_zero k) (Nat.factorial_ne_zero k), Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpn, zero_add]`. Rewrite using `[hv, pow_succ, hwy]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pow_eq_pow_factorization_mul (hp : p.Prime) (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) :
    ∀ n : ℕ, 0 < n → ∀ w ∈ coeffIdeal J τ, ∃ y ∈ coeffIdeal J τ,
      w ^ n = (p : MvPowerSeries τ B) ^ (n.factorial.factorization p) * y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn w hw
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hmn : m < p * m := by nlinarith [hp.two_le]
    obtain ⟨z, hz, hwz⟩ := pow_prime_eq hp hJ hw
    obtain ⟨y, hy, hzy⟩ := ih m hmn hm z hz
    refine ⟨y, hy, ?_⟩
    rw [Nat.factorization_factorial_mul hp, pow_mul, hwz, mul_pow, hzy]
    ring
  · rcases Nat.lt_or_ge n 2 with h | h
    · have h1 : n = 1 := by omega
      subst h1
      exact ⟨w, hw, by simp⟩
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain ⟨y, hy, hwy⟩ := ih k (by omega) (by omega) w hw
      refine ⟨w * y, (coeffIdeal J τ).mul_mem_left _ hy, ?_⟩
      have hv : (k + 1).factorial.factorization p = k.factorial.factorization p := by
        rw [Nat.factorial_succ, Nat.factorization_mul (Nat.succ_ne_zero k)
          (Nat.factorial_ne_zero k), Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hpn, zero_add]
      rw [hv, pow_succ, hwy]; ring

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `p hpf B O Q _ _ _ _ θ hF J hJ τ w hw n hn`. Establish `hp : p.Prime` using `hpf.out`. Take `⟨y, hy, hwy⟩` from `pow_eq_pow_factorization_mul hp hJ n hn w hw`. Take `⟨c, hc_def⟩ : ∃ c, c = ordCompl[p] n.factorial` from `⟨_, rfl⟩`. Establish `hcop : Nat.Coprime c p`.

Rewrite using `[hc_def]`. Conclude with `(Nat.coprime_ordCompl hp (Nat.factorial_ne_zero n)).symm`. Take `⟨u, hu⟩` from `hF.unit_coprime c hcop`. Use `⟨C (↑u⁻¹ : B) * y, (coeffIdeal J τ).mul_mem_left _ hy, ?_⟩` and prove the remaining obligations. Establish `hnat : p ^ (n.factorial.factorization p) * c = n.factorial`.

Rewrite using `[hc_def]`. Conclude with `Nat.ordProj_mul_ordCompl_eq_self _ _`. Establish `hfac : (p : MvPowerSeries τ B) ^ (n.factorial.factorization p) * (c : MvPowerSeries τ B) = (n.factorial : MvPowerSeries τ B)`. Rewrite using `[← Nat.cast_pow, ← Nat.cast_mul, hnat]`. Establish `hcu : (c : MvPowerSeries τ B) * C (↑u⁻¹ : B) = 1`.

Rewrite using `[← map_natCast (C (σ := τ) (R := B)) c, ← hu, ← map_mul, Units.mul_inv, map_one]`. Rewrite using `[hwy, ← hfac]`. Take the linear combination `(-((p : MvPowerSeries τ B) ^ (n.factorial.factorization p) * y)) * hcu`.
-/
theorem pow_eq_factorial_mul : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ J : Ideal B,
    (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (τ : Type) (w : MvPowerSeries τ B),
    (∀ α, coeff α w ∈ J) → ∀ n : ℕ, 0 < n → ∃ y : MvPowerSeries τ B,
    (∀ α, coeff α y ∈ J) ∧ w ^ n = (n.factorial : MvPowerSeries τ B) * y := by
  intro p hpf B O Q _ _ _ _ θ hF J hJ τ w hw n hn
  have hp : p.Prime := hpf.out
  obtain ⟨y, hy, hwy⟩ := pow_eq_pow_factorization_mul hp hJ n hn w hw
  obtain ⟨c, hc_def⟩ : ∃ c, c = ordCompl[p] n.factorial := ⟨_, rfl⟩
  have hcop : Nat.Coprime c p := by
    rw [hc_def]; exact (Nat.coprime_ordCompl hp (Nat.factorial_ne_zero n)).symm
  obtain ⟨u, hu⟩ := hF.unit_coprime c hcop
  refine ⟨C (↑u⁻¹ : B) * y, (coeffIdeal J τ).mul_mem_left _ hy, ?_⟩
  have hnat : p ^ (n.factorial.factorization p) * c = n.factorial := by
    rw [hc_def]; exact Nat.ordProj_mul_ordCompl_eq_self _ _
  have hfac : (p : MvPowerSeries τ B) ^ (n.factorial.factorization p) * (c : MvPowerSeries τ B) =
      (n.factorial : MvPowerSeries τ B) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, hnat]
  have hcu : (c : MvPowerSeries τ B) * C (↑u⁻¹ : B) = 1 := by
    rw [← map_natCast (C (σ := τ) (R := B)) c, ← hu, ← map_mul, Units.mul_inv, map_one]
  rw [hwy, ← hfac]
  linear_combination (-((p : MvPowerSeries τ B) ^ (n.factorial.factorization p) * y)) * hcu

end GlobalTheory.DPSeries
