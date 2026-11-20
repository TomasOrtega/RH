import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.NormOneP
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.NormOneA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.IndBasic

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW.Pair

open PI.KLW

/- English proof (translation)
Establish `h` using `Ind.add_smul_mem hL (Ind.zero_mem_of hL) hb hr`. Rewrite `h` using `[zero_add]`. Then use the resulting hypothesis.
-/
theorem smul_mem' {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ} {ι : Type}
    [Fintype ι] {L : Set (ι → K)} (hL : Unimod K c p L) {b : ι → K} (hb : b ∈ L) {r : K}
    (hr : Rp K p r) : r • b ∈ L := by
  have h := Ind.add_smul_mem hL (Ind.zero_mem_of hL) hb hr
  rwa [zero_add] at h

/- English proof (translation)
Establish `h` using `Ind.add_smul_mem hL ha hb (Ind.rp_one p)`. Rewrite `h` using `[one_smul]`. Then use the resulting hypothesis.
-/
theorem add_mem' {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ} {ι : Type}
    [Fintype ι] {L : Set (ι → K)} (hL : Unimod K c p L) {a b : ι → K} (ha : a ∈ L) (hb : b ∈ L) :
    a + b ∈ L := by
  have h := Ind.add_smul_mem hL ha hb (Ind.rp_one p)
  rwa [one_smul] at h

/- English proof (translation)
Assume the negation of the conclusion as `H`. Use `push_neg at H`. Establish `hp0 : (p : K) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hce : c ε = 1 - ε` using `by linear_combination hsum`. Take `⟨T, hT⟩ : ∃ T, T = ε / p + c ε` from `⟨_, rfl⟩`.

Establish `hTL : ∀ x ∈ L, T • x ∈ L` using `fun x hx => (hL _).2 fun y hy => by`. Rewrite using `[Ind.hf_smul_left]`. Establish `e : T * hf c x y = ε * hf c x y / p + c ε * hf c x y` using `by rw [hT]; ring`. Rewrite using `[e]`. Conclude with `NO.rp_add (H x hx y hy) (NO.rp_mul (NO.rp_c c hε) ((hL x).1 hx y hy))`.

Take `⟨i⟩` from `‹Nonempty ι›`. Take `⟨N, hN0, hNL⟩` from `hS (Pi.single i 1)`. Establish `hTj : ∀ j : ℕ, T ^ j • ((N : K) • Pi.single i (1 : K)) ∈ L`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => rw [pow_zero, one_smul]`. Conclude with `hNL`. Consider the case `succ j ihj => rw [pow_succ', mul_smul]`. Conclude with `hTL _ ihj`. Establish `hvv : hf c ((N : K) • Pi.single i (1 : K)) ((N : K) • Pi.single i (1 : K)) = (N : K) * N`.

Rewrite using `[Ind.hf_smul_left, Ind.hf_smul_right, Ind.hf_single_single, map_natCast, mul_one]`. Establish `hj : ∀ j : ℕ, Rp K p (T ^ j * ((N : K) * N))` using `fun j => by`. Use `(hL _).1 (hTj j) _ hNL` as an intermediate fact. Rewrite `this` using `[Ind.hf_smul_left, hvv]`. Then use the resulting hypothesis. Establish `hcT : c T = c ε / p + ε` using `by rw [hT, map_add, map_div₀, map_natCast, hc]`.

Establish `hjj : ∀ j : ℕ, Rp K p ((T * c T) ^ j * ((N : K) ^ 4))` using `fun j => by`. Establish `h1` using `hj j`. Establish `h2` using `NO.rp_c c (hj j)`. Rewrite `h2` using `[map_mul, map_pow, map_mul, map_natCast]`. Establish `e : (T * c T) ^ j * ((N : K) ^ 4) = (T ^ j * ((N : K) * N)) * (c T ^ j * ((N : K) * N))` using `by ring`.

Rewrite using `[e]`. Conclude with `NO.rp_mul h1 h2`. Take `⟨d, hd⟩ : ∃ d, d = ε * c ε / (p : K) ^ 2` from `⟨_, rfl⟩`. Establish `hdR : Rp K p d` using `hd ▸ hδ`. Take `⟨ρ, hρ⟩ : ∃ ρ, ρ = d + (p : K) ^ 2 * d - p * d - p * d` from `⟨_, rfl⟩`.

Establish `hρR : Rp K p ρ`. Rewrite using `[hρ]`. Establish `hpd : Rp K p ((p : K) * d)` using `NO.rp_mul (NO.rp_natCast p) hdR`. Conclude with `NO.rp_sub (NO.rp_sub (NO.rp_add hdR (NO.rp_mul (NO.rp_pow (NO.rp_natCast p) 2) hdR)) hpd) hpd`. Establish `hTcT : T * c T = (1 + (p : K) * ρ) / p`.

Rewrite using `[hcT, hT, hρ, hd, hce]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨hu0, huinv⟩` from `NO.one_add_p_unit c hc hK hne hp hρR`. Establish `hQ : N ^ 4 ≠ 0` using `pow_ne_zero _ hN0`.

Establish `hpow` using `NO.rp_pow_div (K := K) hp hQ (le_refl (N ^ 4))`. Establish `hA` using `hjj (N ^ 4 + 1)`. Establish `hB` using `NO.rp_pow huinv (N ^ 4 + 1)`. Take `⟨M, hM⟩ : ∃ M, N ^ 4 = M` from `⟨_, rfl⟩`. Rewrite `hpow`, `hA`, `hB` using `[hM]`.

Establish `hMK : (M : K) = (N : K) ^ 4` using `by rw [← hM]; push_cast; ring`. Establish `hN : (N : K) ≠ 0` using `by exact_mod_cast hN0`. Establish `e1 : (1 + (p : K) * ρ) ^ (M + 1) * ((1 + (p : K) * ρ)⁻¹) ^ (M + 1) = 1`. Rewrite using `[← mul_pow, mul_inv_cancel₀ hu0, one_pow]`. Establish `hpM : (p : K) ^ M ≠ 0` using `pow_ne_zero _ hp0`.

Establish `hN4 : (N : K) ^ 4 ≠ 0` using `pow_ne_zero _ hN`. Establish `key : ((T * c T) ^ (M + 1) * (N : K) ^ 4) * ((1 + (p : K) * ρ)⁻¹ ^ (M + 1)) * ((p : K) ^ M / (M : K)) = ((p : K))⁻¹`. Establish `e2 : ((T * c T) ^ (M + 1) * (N : K) ^ 4) * ((1 + (p : K) * ρ)⁻¹ ^ (M + 1)) * ((p : K) ^ M / (M : K)) = ((1 + (p : K) * ρ) ^ (M + 1) * ((1 + (p : K) * ρ)⁻¹) ^ (M + 1)) * ((N : K) ^ 4 / (N : K) ^ 4) * ((p : K) ^ M / ((p : K) ^ M * p))`. Rewrite using `[hTcT, div_pow, hMK]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e2, e1, div_self hN4, div_mul_eq_div_div, div_self hpM, one_mul, one_mul, one_div]`. Apply `NO.not_rp_inv_p (K := K) hp` to reduce the goal to its premises. Rewrite using `[← key]`. Conclude with `NO.rp_mul (NO.rp_mul hA hB) hpow`.
-/
theorem half {K : Type} [Field K] [NumberField K] (c : K →+* K) (hc : ∀ x, c (c x) = x)
    (hK : Module.finrank ℚ K = 2) (hne : ∃ z, c z ≠ z) {p : ℕ} (hp : p.Prime) {ι : Type}
    [Fintype ι] [Nonempty ι] {L : Set (ι → K)} (hL : Unimod K c p L) (hS : Spans K L) {ε : K}
    (hε : Rp K p ε) (hsum : ε + c ε = 1) (hδ : Rp K p (ε * c ε / (p : K) ^ 2)) :
    ∃ x ∈ L, ∃ y ∈ L, ¬ Rp K p (ε * hf c x y / p) := by
  classical
  by_contra H
  push_neg at H
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hce : c ε = 1 - ε := by linear_combination hsum
  obtain ⟨T, hT⟩ : ∃ T, T = ε / p + c ε := ⟨_, rfl⟩
  have hTL : ∀ x ∈ L, T • x ∈ L := fun x hx => (hL _).2 fun y hy => by
    rw [Ind.hf_smul_left]
    have e : T * hf c x y = ε * hf c x y / p + c ε * hf c x y := by rw [hT]; ring
    rw [e]
    exact NO.rp_add (H x hx y hy) (NO.rp_mul (NO.rp_c c hε) ((hL x).1 hx y hy))
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨N, hN0, hNL⟩ := hS (Pi.single i 1)
  have hTj : ∀ j : ℕ, T ^ j • ((N : K) • Pi.single i (1 : K)) ∈ L := by
    intro j
    induction j with
    | zero => rw [pow_zero, one_smul]; exact hNL
    | succ j ihj => rw [pow_succ', mul_smul]; exact hTL _ ihj
  have hvv : hf c ((N : K) • Pi.single i (1 : K)) ((N : K) • Pi.single i (1 : K))
      = (N : K) * N := by
    rw [Ind.hf_smul_left, Ind.hf_smul_right, Ind.hf_single_single, map_natCast, mul_one]
  have hj : ∀ j : ℕ, Rp K p (T ^ j * ((N : K) * N)) := fun j => by
    have := (hL _).1 (hTj j) _ hNL
    rwa [Ind.hf_smul_left, hvv] at this
  have hcT : c T = c ε / p + ε := by rw [hT, map_add, map_div₀, map_natCast, hc]
  have hjj : ∀ j : ℕ, Rp K p ((T * c T) ^ j * ((N : K) ^ 4)) := fun j => by
    have h1 := hj j
    have h2 := NO.rp_c c (hj j)
    rw [map_mul, map_pow, map_mul, map_natCast] at h2
    have e : (T * c T) ^ j * ((N : K) ^ 4)
        = (T ^ j * ((N : K) * N)) * (c T ^ j * ((N : K) * N)) := by ring
    rw [e]
    exact NO.rp_mul h1 h2
  obtain ⟨d, hd⟩ : ∃ d, d = ε * c ε / (p : K) ^ 2 := ⟨_, rfl⟩
  have hdR : Rp K p d := hd ▸ hδ
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = d + (p : K) ^ 2 * d - p * d - p * d := ⟨_, rfl⟩
  have hρR : Rp K p ρ := by
    rw [hρ]
    have hpd : Rp K p ((p : K) * d) := NO.rp_mul (NO.rp_natCast p) hdR
    exact NO.rp_sub (NO.rp_sub (NO.rp_add hdR (NO.rp_mul (NO.rp_pow (NO.rp_natCast p) 2) hdR))
      hpd) hpd
  have hTcT : T * c T = (1 + (p : K) * ρ) / p := by
    rw [hcT, hT, hρ, hd, hce]
    field_simp
    ring
  obtain ⟨hu0, huinv⟩ := NO.one_add_p_unit c hc hK hne hp hρR
  have hQ : N ^ 4 ≠ 0 := pow_ne_zero _ hN0
  have hpow := NO.rp_pow_div (K := K) hp hQ (le_refl (N ^ 4))
  have hA := hjj (N ^ 4 + 1)
  have hB := NO.rp_pow huinv (N ^ 4 + 1)
  obtain ⟨M, hM⟩ : ∃ M, N ^ 4 = M := ⟨_, rfl⟩
  rw [hM] at hpow hA hB
  have hMK : (M : K) = (N : K) ^ 4 := by rw [← hM]; push_cast; ring
  have hN : (N : K) ≠ 0 := by exact_mod_cast hN0
  have e1 : (1 + (p : K) * ρ) ^ (M + 1) * ((1 + (p : K) * ρ)⁻¹) ^ (M + 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hu0, one_pow]
  have hpM : (p : K) ^ M ≠ 0 := pow_ne_zero _ hp0
  have hN4 : (N : K) ^ 4 ≠ 0 := pow_ne_zero _ hN
  have key : ((T * c T) ^ (M + 1) * (N : K) ^ 4) * ((1 + (p : K) * ρ)⁻¹ ^ (M + 1))
      * ((p : K) ^ M / (M : K)) = ((p : K))⁻¹ := by
    have e2 : ((T * c T) ^ (M + 1) * (N : K) ^ 4) * ((1 + (p : K) * ρ)⁻¹ ^ (M + 1))
        * ((p : K) ^ M / (M : K))
        = ((1 + (p : K) * ρ) ^ (M + 1) * ((1 + (p : K) * ρ)⁻¹) ^ (M + 1))
          * ((N : K) ^ 4 / (N : K) ^ 4) * ((p : K) ^ M / ((p : K) ^ M * p)) := by
      rw [hTcT, div_pow, hMK]
      ring
    rw [e2, e1, div_self hN4, div_mul_eq_div_div, div_self hpM, one_mul, one_mul, one_div]
  apply NO.not_rp_inv_p (K := K) hp
  rw [← key]
  exact NO.rp_mul (NO.rp_mul hA hB) hpow

/- English proof (translation)
Take `⟨x', hx', y', hy', hn⟩` from `half c hc hK hne hp hL hS hε hsum hδ`. Establish `hp0 : (p : K) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hce : c ε = 1 - ε` using `by linear_combination hsum`. Take `⟨ρ', hρ'⟩ : ∃ ρ', ρ' = hf c x' y'` from `⟨_, rfl⟩`. Establish `hρR : Rp K p ρ'` using `by rw [hρ']; exact (hL x').1 hx' y' hy'`.

Rewrite `hn` using `[← hρ']`. Take `⟨z, hz⟩ : ∃ z, z = ε * ρ' + c ε` from `⟨_, rfl⟩`. Establish `hzR : Rp K p z` using `by rw [hz]; exact NO.rp_add (NO.rp_mul hε hρR) (NO.rp_c c hε)`. Establish `hcz : c z = c ε * c ρ' + ε` using `by rw [hz, map_add, map_mul, hc]`. Establish `hnz : ¬ Rp K p (z * c z / p)`.

Introduce `h`. Apply `hn` to reduce the goal to its premises. Establish `key : ε * ρ' / p = ε * (z * c z / p) + ((p : K) * (ε * c ε / (p : K) ^ 2)) * (-ε * (ρ' * c ρ' - ρ' - c ρ' + 1) + ρ' - c ρ')`. Rewrite using `[hcz, hz, hce]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Establish `hcρ : Rp K p (c ρ')` using `NO.rp_c c hρR`. Establish `hW : Rp K p (-ε * (ρ' * c ρ' - ρ' - c ρ' + 1) + ρ' - c ρ')` using `NO.rp_sub (NO.rp_add (NO.rp_mul (NO.rp_neg hε) (NO.rp_add (NO.rp_sub (NO.rp_sub (NO.rp_mul hρR hcρ) hρR) hcρ) NO.rp_one)) hρR) hcρ`. Conclude with `NO.rp_add (NO.rp_mul hε h) (NO.rp_mul (NO.rp_mul (NO.rp_natCast p) hδ) hW)`.

Take `⟨hz0, hzi⟩` from `NO.unit_of_norm c hc hK hne hp hzR hnz`. Use `⟨x', hx', c (z⁻¹) • y', smul_mem' hL hy' (NO.rp_c c hzi), z⁻¹ * (ρ' - 1), NO.rp_mul hzi (NO.rp_sub hρR NO.rp_one), ?_⟩` and prove the remaining obligations. Rewrite using `[Ind.hf_smul_right, hc, ← hρ']`. Establish `h1 : ε * (ρ' - z) = ε * c ε * (ρ' - 1)` using `by rw [hz, hce]; ring`. Establish `hzz : z⁻¹ * z = 1` using `inv_mul_cancel₀ hz0`.

Take the linear combination `z⁻¹ * h1 + ε * hzz`.
-/
theorem near_one {K : Type} [Field K] [NumberField K] (c : K →+* K) (hc : ∀ x, c (c x) = x)
    (hK : Module.finrank ℚ K = 2) (hne : ∃ z, c z ≠ z) {p : ℕ} (hp : p.Prime) {ι : Type}
    [Fintype ι] [Nonempty ι] {L : Set (ι → K)} (hL : Unimod K c p L) (hS : Spans K L) {ε : K}
    (hε : Rp K p ε) (hsum : ε + c ε = 1) (hδ : Rp K p (ε * c ε / (p : K) ^ 2)) :
    ∃ x ∈ L, ∃ y ∈ L, ∃ r, Rp K p r ∧ ε * (hf c x y - 1) = ε * c ε * r := by
  obtain ⟨x', hx', y', hy', hn⟩ := half c hc hK hne hp hL hS hε hsum hδ
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hce : c ε = 1 - ε := by linear_combination hsum
  obtain ⟨ρ', hρ'⟩ : ∃ ρ', ρ' = hf c x' y' := ⟨_, rfl⟩
  have hρR : Rp K p ρ' := by rw [hρ']; exact (hL x').1 hx' y' hy'
  rw [← hρ'] at hn
  obtain ⟨z, hz⟩ : ∃ z, z = ε * ρ' + c ε := ⟨_, rfl⟩
  have hzR : Rp K p z := by rw [hz]; exact NO.rp_add (NO.rp_mul hε hρR) (NO.rp_c c hε)
  have hcz : c z = c ε * c ρ' + ε := by rw [hz, map_add, map_mul, hc]
  have hnz : ¬ Rp K p (z * c z / p) := by
    intro h
    apply hn
    have key : ε * ρ' / p = ε * (z * c z / p) + ((p : K) * (ε * c ε / (p : K) ^ 2))
        * (-ε * (ρ' * c ρ' - ρ' - c ρ' + 1) + ρ' - c ρ') := by
      rw [hcz, hz, hce]
      field_simp
      ring
    rw [key]
    have hcρ : Rp K p (c ρ') := NO.rp_c c hρR
    have hW : Rp K p (-ε * (ρ' * c ρ' - ρ' - c ρ' + 1) + ρ' - c ρ') :=
      NO.rp_sub (NO.rp_add (NO.rp_mul (NO.rp_neg hε)
        (NO.rp_add (NO.rp_sub (NO.rp_sub (NO.rp_mul hρR hcρ) hρR) hcρ) NO.rp_one)) hρR) hcρ
    exact NO.rp_add (NO.rp_mul hε h) (NO.rp_mul (NO.rp_mul (NO.rp_natCast p) hδ) hW)
  obtain ⟨hz0, hzi⟩ := NO.unit_of_norm c hc hK hne hp hzR hnz
  refine ⟨x', hx', c (z⁻¹) • y', smul_mem' hL hy' (NO.rp_c c hzi), z⁻¹ * (ρ' - 1),
    NO.rp_mul hzi (NO.rp_sub hρR NO.rp_one), ?_⟩
  rw [Ind.hf_smul_right, hc, ← hρ']
  have h1 : ε * (ρ' - z) = ε * c ε * (ρ' - 1) := by rw [hz, hce]; ring
  have hzz : z⁻¹ * z = 1 := inv_mul_cancel₀ hz0
  linear_combination z⁻¹ * h1 + ε * hzz

/- English proof (translation)
Take `⟨x1, hx1, y1, hy1, r1, hr1, h1⟩` from `near_one c hc hK hne hp hL hS hε hsum hδ`. Establish `hε' : Rp K p (c ε)` using `NO.rp_c c hε`. Establish `hsum' : c ε + c (c ε) = 1` using `by rw [hc, add_comm, hsum]`. Establish `hδ' : Rp K p (c ε * c (c ε) / (p : K) ^ 2)` using `by rw [hc, mul_comm]; exact hδ`. Take `⟨x2, hx2, y2, hy2, r2, hr2, h2⟩` from `near_one c hc hK hne hp hL hS hε' hsum' hδ'`.

Rewrite `h2` using `[hc]`. Establish `hp0 : (p : K) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hxL : ε • x1 + c ε • x2 ∈ L` using `add_mem' hL (smul_mem' hL hx1 hε) (smul_mem' hL hx2 hε')`. Establish `hyL : c ε • y1 + ε • y2 ∈ L` using `add_mem' hL (smul_mem' hL hy1 hε') (smul_mem' hL hy2 hε)`. Establish `hd : (p : K) * ((p : K) * (ε * c ε / (p : K) ^ 2)) = ε * c ε` using `by field_simp`.

Establish `hxy : hf c (ε • x1 + c ε • x2) (c ε • y1 + ε • y2) = 1 + (p : K) * ((p : K) * (ε * c ε / (p : K) ^ 2) * (ε * r1 + hf c x1 y2 + hf c x2 y1 + c ε * r2 - 1 - 1))`. Simplify using `only [Ind.hf_add_left, Ind.hf_add_right, Ind.hf_smul_left, Ind.hf_smul_right, hc]`. Take the linear combination `ε * h1 + c ε * h2 - (ε * r1 + hf c x1 y2 + hf c x2 y1 + c ε * r2 - 1 - 1) * hd + (ε + c ε + 1) * hsum`. Establish `hQ : Rp K p ((p : K) * (ε * c ε / (p : K) ^ 2) * (ε * r1 + hf c x1 y2 + hf c x2 y1 + c ε * r2 - 1 - 1))` using `NO.rp_mul (NO.rp_mul (NO.rp_natCast p) hδ) (NO.rp_sub (NO.rp_sub (NO.rp_add (NO.rp_add (NO.rp_add (NO.rp_mul hε hr1) ((hL x1).1 hx1 y2 hy2)) ((hL x2).1 hx2 y1 hy1)) (NO.rp_mul hε' hr2)) NO.rp_one) NO.rp_one)`. Take `⟨ha0, hai⟩` from `NO.one_add_p_unit c hc hK hne hp hQ`.

Rewrite `ha0`, `hai` using `[← hxy]`. Use `⟨_, hxL, c ((hf c (ε • x1 + c ε • x2) (c ε • y1 + ε • y2))⁻¹) • (c ε • y1 + ε • y2), smul_mem' hL hyL (NO.rp_c c hai), ?_⟩` and prove the remaining obligations. Rewrite using `[Ind.hf_smul_right, hc, inv_mul_cancel₀ ha0]`.
-/
theorem pair_of_eps {K : Type} [Field K] [NumberField K] (c : K →+* K) (hc : ∀ x, c (c x) = x)
    (hK : Module.finrank ℚ K = 2) (hne : ∃ z, c z ≠ z) {p : ℕ} (hp : p.Prime) {ι : Type}
    [Fintype ι] [Nonempty ι] {L : Set (ι → K)} (hL : Unimod K c p L) (hS : Spans K L) {ε : K}
    (hε : Rp K p ε) (hsum : ε + c ε = 1) (hδ : Rp K p (ε * c ε / (p : K) ^ 2)) :
    ∃ x ∈ L, ∃ y ∈ L, hf c x y = 1 := by
  obtain ⟨x1, hx1, y1, hy1, r1, hr1, h1⟩ := near_one c hc hK hne hp hL hS hε hsum hδ
  have hε' : Rp K p (c ε) := NO.rp_c c hε
  have hsum' : c ε + c (c ε) = 1 := by rw [hc, add_comm, hsum]
  have hδ' : Rp K p (c ε * c (c ε) / (p : K) ^ 2) := by rw [hc, mul_comm]; exact hδ
  obtain ⟨x2, hx2, y2, hy2, r2, hr2, h2⟩ := near_one c hc hK hne hp hL hS hε' hsum' hδ'
  rw [hc] at h2
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hxL : ε • x1 + c ε • x2 ∈ L := add_mem' hL (smul_mem' hL hx1 hε) (smul_mem' hL hx2 hε')
  have hyL : c ε • y1 + ε • y2 ∈ L := add_mem' hL (smul_mem' hL hy1 hε') (smul_mem' hL hy2 hε)
  have hd : (p : K) * ((p : K) * (ε * c ε / (p : K) ^ 2)) = ε * c ε := by field_simp
  have hxy : hf c (ε • x1 + c ε • x2) (c ε • y1 + ε • y2) = 1 + (p : K) * ((p : K)
      * (ε * c ε / (p : K) ^ 2) * (ε * r1 + hf c x1 y2 + hf c x2 y1 + c ε * r2 - 1 - 1)) := by
    simp only [Ind.hf_add_left, Ind.hf_add_right, Ind.hf_smul_left, Ind.hf_smul_right, hc]
    linear_combination ε * h1 + c ε * h2
      - (ε * r1 + hf c x1 y2 + hf c x2 y1 + c ε * r2 - 1 - 1) * hd + (ε + c ε + 1) * hsum
  have hQ : Rp K p ((p : K) * (ε * c ε / (p : K) ^ 2)
      * (ε * r1 + hf c x1 y2 + hf c x2 y1 + c ε * r2 - 1 - 1)) :=
    NO.rp_mul (NO.rp_mul (NO.rp_natCast p) hδ)
      (NO.rp_sub (NO.rp_sub (NO.rp_add (NO.rp_add (NO.rp_add (NO.rp_mul hε hr1)
        ((hL x1).1 hx1 y2 hy2)) ((hL x2).1 hx2 y1 hy1)) (NO.rp_mul hε' hr2)) NO.rp_one) NO.rp_one)
  obtain ⟨ha0, hai⟩ := NO.one_add_p_unit c hc hK hne hp hQ
  rw [← hxy] at ha0 hai
  refine ⟨_, hxL, c ((hf c (ε • x1 + c ε • x2) (c ε • y1 + ε • y2))⁻¹) • (c ε • y1 + ε • y2),
    smul_mem' hL hyL (NO.rp_c c hai), ?_⟩
  rw [Ind.hf_smul_right, hc, inv_mul_cancel₀ ha0]

/- English proof (translation)
Take `⟨P, _, _, a, b, hab, ha, hb⟩` from `hs`. Use `⟨(a : K), ?_⟩` and prove the remaining obligations. Rewrite using `[hab]`. Introduce `h`. Conclude with `hb (by rwa [RingOfIntegers.ext h])`.
-/
theorem ne_of_split {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ}
    (hs : SplitK c p) : ∃ z, c z ≠ z := by
  obtain ⟨P, _, _, a, b, hab, ha, hb⟩ := hs
  refine ⟨(a : K), ?_⟩
  rw [hab]
  intro h
  exact hb (by rwa [RingOfIntegers.ext h])

def EpsSplit : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ),
    Module.finrank ℚ K = 2 → (∀ x, c (c x) = x) → p.Prime → SplitK c p →
      ∀ k : ℕ, ∃ ε : K, Rp K p ε ∧ ε + c ε = 1 ∧ Rp K p (ε * c ε / (p : K) ^ k)

/- English proof (translation)
Introduce `K _ _ c p ι _ _ L hK hc hp hs hL hS`. Take `⟨ε, hε, hsum, hδ⟩` from `h K c p hK hc hp hs 2`. Conclude with `pair_of_eps c hc hK (ne_of_split hs) hp hL hS hε hsum hδ`.
-/
theorem pairOne_of (h : EpsSplit) : PairOne := by
  intro K _ _ c p ι _ _ L hK hc hp hs hL hS
  obtain ⟨ε, hε, hsum, hδ⟩ := h K c p hK hc hp hs 2
  exact pair_of_eps c hc hK (ne_of_split hs) hp hL hS hε hsum hδ

/- English proof (translation)
Introduce `K _ _ c p hK hc hp hs k`. Conclude with `NO.eps c hc hK hp hs k`.
-/
theorem epsSplit : EpsSplit := by
  intro K _ _ c p hK hc hp hs k
  exact NO.eps c hc hK hp hs k

end PI.KLW.Pair

namespace PI.KLW

/- English proof (translation)
The claim follows from `Pair.pairOne_of Pair.epsSplit`.
-/
theorem pairOne : PairOne := Pair.pairOne_of Pair.epsSplit

end PI.KLW
