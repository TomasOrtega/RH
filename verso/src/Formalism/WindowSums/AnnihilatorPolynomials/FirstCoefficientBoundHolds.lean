import Formalism.WindowSums.Statement

noncomputable section

namespace Formalism.WindowSums

open PowerSeries

namespace AnnihilatorQuotientResidues

variable {O : Type} [CommRing O]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hc : ∀ n, ∃ z, z * ϖ = PowerSeries.coeff n f`. Introduce `n`. Establish `h1` using `congrArg (PowerSeries.coeff n) h`.

Rewrite `h1` using `[PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_span_singleton'.mp h1`. Use `⟨PowerSeries.mk fun n => Classical.choose (hc n), ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, mul_comm]`.

Conclude with `(Classical.choose_spec (hc n)).symm`. Introduce and unpack `⟨g, rfl⟩`. Rewrite using `[map_mul, PowerSeries.map_C, (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self ϖ), map_zero, zero_mul]`.
-/
lemma map_mk_eq_zero_iff (ϖ : O) (f : PowerSeries O) :
    PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) f = 0 ↔ PowerSeries.C ϖ ∣ f := by
  constructor
  · intro h
    have hc : ∀ n, ∃ z, z * ϖ = PowerSeries.coeff n f := by
      intro n
      have h1 := congrArg (PowerSeries.coeff n) h
      rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem] at h1
      exact Ideal.mem_span_singleton'.mp h1
    refine ⟨PowerSeries.mk fun n => Classical.choose (hc n), ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, mul_comm]
    exact (Classical.choose_spec (hc n)).symm
  · rintro ⟨g, rfl⟩
    rw [map_mul, PowerSeries.map_C,
      (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self ϖ), map_zero, zero_mul]

/- English proof (translation)
The claim follows from `(Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self ϖ)`.
-/
lemma mk_self (ϖ : O) : Ideal.Quotient.mk (Ideal.span {ϖ}) ϖ = 0 :=
  (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self ϖ)

/- English proof (translation)
Rewrite using `[p1, map_add, map_mul, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, mk_self, map_zero, zero_mul, zero_add]`.
-/
lemma residue_map_p1_eq (ℓ : ℕ) (ε u : PowerSeries O) :
    PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O)})) (p1 ℓ ε u) =
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O)})) u * PowerSeries.X ^ ℓ := by
  rw [p1, map_add, map_mul, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, mk_self,
    map_zero, zero_mul, zero_add]

variable [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Introduce `h`. Apply `hℓ.ne_zero` to reduce the goal to its premises. Simplify using `using congrArg PowerSeries.constantCoeff h`.
-/
lemma C_ne_zero {ℓ : ℕ} (hℓ : Irreducible (ℓ : O)) : (PowerSeries.C (ℓ : O)) ≠ 0 := by
  intro h
  apply hℓ.ne_zero
  simpa using congrArg PowerSeries.constantCoeff h

/- English proof (translation)
Establish `: (Ideal.span {(ℓ : O)}).IsPrime` using `(PrincipalIdealRing.isMaximal_of_irreducible hℓ).isPrime`. Introduce `t`. Proceed by induction on `t with`. Consider the case `zero => intro g _`. Simplify using the standard rewrite rules.

Consider the case `succ t ih`. Introduce `g h`. Take `⟨g1, rfl⟩` from `ih g (dvd_trans (pow_dvd_pow _ (Nat.le_succ t)) h)`. Establish `hL` using `C_ne_zero hℓ`. Rewrite `h`, the goal using `[pow_succ]`.

Establish `h2 : PowerSeries.C (ℓ : O) ∣ p1 ℓ ε u ^ y * g1`. Rewrite `h` using `[show p1 ℓ ε u ^ y * (PowerSeries.C (ℓ : O) ^ t * g1) = PowerSeries.C (ℓ : O) ^ t * (p1 ℓ ε u ^ y * g1) by ring]`. Conclude with `(mul_dvd_mul_iff_left (pow_ne_zero t hL)).mp h`. Establish `h3` using `(map_mk_eq_zero_iff _ _).mpr h2`. Rewrite `h3` using `[map_mul, map_pow, residue_map_p1_eq]`.

Establish `h4 : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O)})) g1 = 0`. Break down `mul_eq_zero.mp h3 with h4 | h4` into its components or cases. It suffices to derive a contradiction. Conclude with `pow_ne_zero _ (mul_ne_zero (hu.map _).ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero)) h4`. Conclude with `h4`.

Conclude with `mul_dvd_mul_left _ ((map_mk_eq_zero_iff _ _).mp h4)`.
-/
lemma nzd {ℓ : ℕ} (hℓ : Irreducible (ℓ : O)) (ε u : PowerSeries O) (hu : IsUnit u) (y : ℕ) :
    ∀ (t : ℕ) (g : PowerSeries O), PowerSeries.C (ℓ : O) ^ t ∣ p1 ℓ ε u ^ y * g →
      PowerSeries.C (ℓ : O) ^ t ∣ g := by
  have : (Ideal.span {(ℓ : O)}).IsPrime := (PrincipalIdealRing.isMaximal_of_irreducible hℓ).isPrime
  intro t
  induction t with
  | zero => intro g _; simp
  | succ t ih =>
    intro g h
    obtain ⟨g1, rfl⟩ := ih g (dvd_trans (pow_dvd_pow _ (Nat.le_succ t)) h)
    have hL := C_ne_zero hℓ
    rw [pow_succ] at h ⊢
    have h2 : PowerSeries.C (ℓ : O) ∣ p1 ℓ ε u ^ y * g1 := by
      rw [show p1 ℓ ε u ^ y * (PowerSeries.C (ℓ : O) ^ t * g1) =
        PowerSeries.C (ℓ : O) ^ t * (p1 ℓ ε u ^ y * g1) by ring] at h
      exact (mul_dvd_mul_iff_left (pow_ne_zero t hL)).mp h
    have h3 := (map_mk_eq_zero_iff _ _).mpr h2
    rw [map_mul, map_pow, residue_map_p1_eq] at h3
    have h4 : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O)})) g1 = 0 := by
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exfalso
        exact pow_ne_zero _ (mul_ne_zero (hu.map _).ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero)) h4
      · exact h4
    exact mul_dvd_mul_left _ ((map_mk_eq_zero_iff _ _).mp h4)

/- English proof (translation)
Establish `: (Ideal.span {(ℓ : O)}).IsPrime` using `(PrincipalIdealRing.isMaximal_of_irreducible hℓ).isPrime`. Establish `hℓpos : 0 < ℓ` using `(Fact.out : ℓ.Prime).pos`. Introduce `hmem`. Take `⟨a, b, hab⟩` from `Ideal.mem_span_pair.mp hmem`. Use `set L := PowerSeries.C (ℓ : O) with hLdef`.

Use `set P := p1 ℓ ε u with hPdef`. Use `set φ := PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O)})) with hφ`. Use `set E := ∑ j ∈ Finset.range N, L ^ (m j - μ) * w j * PowerSeries.X ^ r * P ^ j with hE`. Establish `hFE : (∑ j ∈ Finset.range N, L ^ m j * w j * PowerSeries.X ^ r * P ^ j) = L ^ μ * E`. Rewrite using `[hE, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Use `hmge j (Finset.mem_range.mp hj)` as an intermediate fact. Use `conv_lhs => rw [show m j = μ + (m j - μ) by omega, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hab` using `[hFE]`.

Establish `hdvd : L ^ μ ∣ P ^ y * a` using `⟨E - b * L, by linear_combination hab⟩`. Take `⟨a', rfl⟩` from `nzd hℓ ε u hu y μ a hdvd`. Establish `hL : L ≠ 0` using `C_ne_zero hℓ`. Establish `hE2 : E = a' * P ^ y + b * L`. Establish `: L ^ μ * E = L ^ μ * (a' * P ^ y + b * L)` using `by rw [← hab]; ring`.

Conclude with `mul_left_cancel₀ (pow_ne_zero μ hL) this`. Establish `hφL : φ L = 0` using `by rw [hφ, hLdef, PowerSeries.map_C, mk_self, map_zero]`. Establish `key` using `congrArg (fun f => PowerSeries.coeff (r + ℓ * j0) (φ f)) hE2`. Establish `hR : PowerSeries.coeff (r + ℓ * j0) (φ (a' * P ^ y + b * L)) = 0`. Establish `h1 : ℓ * (j0 + 1) ≤ ℓ * y` using `Nat.mul_le_mul_left ℓ (by omega)`.

Rewrite using `[map_add, map_mul, map_mul, map_pow, hPdef, residue_map_p1_eq, hφL, mul_zero, add_zero, mul_pow, ← pow_mul, ← mul_assoc, PowerSeries.coeff_mul_X_pow', if_neg]`. Introduce `h2`. Rewrite `h1` using `[Nat.mul_succ]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hterm : ∀ j, φ (L ^ (m j - μ) * w j * PowerSeries.X ^ r * P ^ j) = (φ L ^ (m j - μ) * φ (w j) * φ u ^ j) * PowerSeries.X ^ (r + ℓ * j)`.

Introduce `j`. Rewrite using `[map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, hPdef, residue_map_p1_eq, PowerSeries.map_X]`. Expand and normalize the polynomial expressions, which then agree. Establish `hLft : PowerSeries.coeff (r + ℓ * j0) (φ E) ≠ 0`. Rewrite using `[hE, map_sum, map_sum, Finset.sum_eq_single j0]`.

Rewrite using `[hterm, PowerSeries.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, hm0, Nat.sub_self, pow_zero, one_mul]`. Conclude with `((hw0.map φ).mul ((hu.map φ).pow j0)).map PowerSeries.constantCoeff |>.ne_zero`. Introduce `j hj hne`. Rewrite using `[hterm]`. Break down `Nat.lt_or_gt_of_ne hne with hlt' | hgt` into its components or cases.

Use `hlt j hlt'` as an intermediate fact. Rewrite using `[hφL, zero_pow (by omega), zero_mul, zero_mul, zero_mul, map_zero]`. Rewrite using `[PowerSeries.coeff_mul_X_pow', if_neg]`. Introduce `h2`. Establish `: ℓ * j0 < ℓ * j` using `Nat.mul_lt_mul_of_pos_left hgt hℓpos`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h`. Conclude with `absurd (Finset.mem_range.mpr hj0) h`. Conclude with `hLft (key.trans hR)`.
-/
lemma core {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : Irreducible (ℓ : O)) (ε u : PowerSeries O) (hu : IsUnit u)
    (y r N μ : ℕ) (hr : r < ℓ) (hN : N ≤ y) (m : ℕ → ℕ) (w : ℕ → PowerSeries O)
    (j0 : ℕ) (hj0 : j0 < N) (hw0 : IsUnit (w j0)) (hm0 : m j0 = μ)
    (hmge : ∀ j < N, μ ≤ m j) (hlt : ∀ j < j0, μ < m j) :
    (∑ j ∈ Finset.range N, PowerSeries.C (ℓ : O) ^ m j * w j * PowerSeries.X ^ r * p1 ℓ ε u ^ j) ∉
      Ideal.span {p1 ℓ ε u ^ y, PowerSeries.C (ℓ : O) ^ (μ + 1)} := by
  have : (Ideal.span {(ℓ : O)}).IsPrime := (PrincipalIdealRing.isMaximal_of_irreducible hℓ).isPrime
  have hℓpos : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  intro hmem
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmem
  set L := PowerSeries.C (ℓ : O) with hLdef
  set P := p1 ℓ ε u with hPdef
  set φ := PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O)})) with hφ
  set E := ∑ j ∈ Finset.range N, L ^ (m j - μ) * w j * PowerSeries.X ^ r * P ^ j with hE
  have hFE : (∑ j ∈ Finset.range N, L ^ m j * w j * PowerSeries.X ^ r * P ^ j) = L ^ μ * E := by
    rw [hE, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := hmge j (Finset.mem_range.mp hj)
    conv_lhs => rw [show m j = μ + (m j - μ) by omega, pow_add]
    ring
  rw [hFE] at hab
  have hdvd : L ^ μ ∣ P ^ y * a := ⟨E - b * L, by linear_combination hab⟩
  obtain ⟨a', rfl⟩ := nzd hℓ ε u hu y μ a hdvd
  have hL : L ≠ 0 := C_ne_zero hℓ
  have hE2 : E = a' * P ^ y + b * L := by
    have : L ^ μ * E = L ^ μ * (a' * P ^ y + b * L) := by rw [← hab]; ring
    exact mul_left_cancel₀ (pow_ne_zero μ hL) this
  have hφL : φ L = 0 := by rw [hφ, hLdef, PowerSeries.map_C, mk_self, map_zero]
  have key := congrArg (fun f => PowerSeries.coeff (r + ℓ * j0) (φ f)) hE2
  have hR : PowerSeries.coeff (r + ℓ * j0) (φ (a' * P ^ y + b * L)) = 0 := by
    have h1 : ℓ * (j0 + 1) ≤ ℓ * y := Nat.mul_le_mul_left ℓ (by omega)
    rw [map_add, map_mul, map_mul, map_pow, hPdef, residue_map_p1_eq, hφL, mul_zero, add_zero, mul_pow,
      ← pow_mul, ← mul_assoc, PowerSeries.coeff_mul_X_pow', if_neg]
    intro h2
    rw [Nat.mul_succ] at h1
    linarith
  have hterm : ∀ j, φ (L ^ (m j - μ) * w j * PowerSeries.X ^ r * P ^ j) =
      (φ L ^ (m j - μ) * φ (w j) * φ u ^ j) * PowerSeries.X ^ (r + ℓ * j) := by
    intro j
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, hPdef, residue_map_p1_eq, PowerSeries.map_X]
    ring
  have hLft : PowerSeries.coeff (r + ℓ * j0) (φ E) ≠ 0 := by
    rw [hE, map_sum, map_sum, Finset.sum_eq_single j0]
    · rw [hterm, PowerSeries.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hm0, Nat.sub_self, pow_zero, one_mul]
      exact ((hw0.map φ).mul ((hu.map φ).pow j0)).map PowerSeries.constantCoeff |>.ne_zero
    · intro j hj hne
      rw [hterm]
      rcases Nat.lt_or_gt_of_ne hne with hlt' | hgt
      · have := hlt j hlt'
        rw [hφL, zero_pow (by omega), zero_mul, zero_mul, zero_mul, map_zero]
      · rw [PowerSeries.coeff_mul_X_pow', if_neg]
        intro h2
        have : ℓ * j0 < ℓ * j := Nat.mul_lt_mul_of_pos_left hgt hℓpos
        linarith
    · intro h; exact absurd (Finset.mem_range.mpr hj0) h
  exact hLft (key.trans hR)

end AnnihilatorQuotientResidues

end Formalism.WindowSums
