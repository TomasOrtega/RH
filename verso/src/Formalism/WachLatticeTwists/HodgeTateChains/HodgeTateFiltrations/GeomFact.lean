import Formalism.WachLatticeTwists.HodgeTateChains.StatCharSum
import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

/- English proof (translation)
Introduce `ℓ hℓ s ρ hs h2 hρ hρs j hj1 hjs`. Use `Fact.mk hℓ` as an intermediate fact. Establish `hv : padicValNat ℓ j ≤ s`. Use `le_trans (padicValNat_le_nat_log j) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `hvq : (padicValNat ℓ j : ℚ) ≤ s` using `by exact_mod_cast hv`. Break down `Nat.lt_or_ge j 3 with h3 | h3` into its components or cases. Use `interval_cases j`. Simplify using `only [padicValNat.one]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hv2 : padicValNat ℓ 2 + 1 ≤ s`. Distinguish the cases in `hl : ℓ = 2`. Substitute `hl` using the available equality. Establish `: padicValNat 2 2 = 1` using `padicValNat.self (by norm_num)`.

Use `h2 rfl` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `: padicValNat ℓ 2 = 0`. Apply `padicValNat.eq_zero_of_not_dvd` to reduce the goal to its premises. Introduce `hd`.

Conclude with `hl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hd)`. Use linear arithmetic over natural numbers and integers. Establish `hv2q : (padicValNat ℓ 2 : ℚ) + 1 ≤ s` using `by exact_mod_cast hv2`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hj : (3 : ℚ) ≤ j` using `by exact_mod_cast h3`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem kappa : StatKappa := by
  intro ℓ hℓ s ρ hs h2 hρ hρs j hj1 hjs
  have := Fact.mk hℓ
  have hv : padicValNat ℓ j ≤ s := by
    refine le_trans (padicValNat_le_nat_log j) ?_
    calc Nat.log ℓ j ≤ Nat.log ℓ (ℓ ^ s) := Nat.log_mono_right hjs
      _ = s := Nat.log_pow hℓ.one_lt s
  have hvq : (padicValNat ℓ j : ℚ) ≤ s := by exact_mod_cast hv
  rcases Nat.lt_or_ge j 3 with h3 | h3
  · interval_cases j
    · simp only [padicValNat.one]; push_cast; linarith
    · have hv2 : padicValNat ℓ 2 + 1 ≤ s := by
        by_cases hl : ℓ = 2
        · subst hl
          have : padicValNat 2 2 = 1 := padicValNat.self (by norm_num)
          have := h2 rfl
          omega
        · have : padicValNat ℓ 2 = 0 := by
            apply padicValNat.eq_zero_of_not_dvd
            intro hd
            exact hl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hd)
          omega
      have hv2q : (padicValNat ℓ 2 : ℚ) + 1 ≤ s := by exact_mod_cast hv2
      push_cast
      linarith
  · have hj : (3 : ℚ) ≤ j := by exact_mod_cast h3
    nlinarith

/- English proof (translation)
Introduce `La _ a b M q hM hnil`. Establish `hb : b = a + (b - a)` using `by ring`. Establish `hd : (b - a) ^ M = 0`. Establish `: b - a = -(a - b)` using `by ring`. Rewrite using `[this, neg_pow, hnil, mul_zero]`.

Rewrite using `[hb, add_pow]`. Apply `Finset.dvd_sum` to reduce the goal to its premises. Introduce `m hm`. Rewrite `hm` using `[Finset.mem_range]`. Distinguish the cases in `hq : q ≤ m`.

Conclude with `Dvd.dvd.mul_right (Dvd.dvd.mul_right (pow_dvd_pow a hq) _) _`. Establish `hle : M ≤ q + M - 1 - m` using `by omega`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le hle`. Rewrite using `[hk, pow_add, hd]`. Simplify using the standard rewrite rules.
-/
theorem nilDiv : StatNilDiv := by
  intro La _ a b M q hM hnil
  have hb : b = a + (b - a) := by ring
  have hd : (b - a) ^ M = 0 := by
    have : b - a = -(a - b) := by ring
    rw [this, neg_pow, hnil, mul_zero]
  rw [hb, add_pow]
  apply Finset.dvd_sum
  intro m hm
  rw [Finset.mem_range] at hm
  by_cases hq : q ≤ m
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (pow_dvd_pow a hq) _) _
  · have hle : M ≤ q + M - 1 - m := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, pow_add, hd]
    simp

/- English proof (translation)
Proceed by induction on `b with`. Consider the case `zero => simp`. Consider the case `succ b ih`. Rewrite using `[Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]`. Use `congr 1`.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[pow_add, ← pow_mul, mul_comm]`.
-/
lemma geom_fact {R : Type} [CommRing R] (x : R) (a b : ℕ) :
    ∑ k ∈ Finset.range (a * b), x ^ k
      = (∑ k ∈ Finset.range a, x ^ k) * ∑ k ∈ Finset.range b, (x ^ a) ^ k := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add, ← pow_mul, mul_comm]

/- English proof (translation)
Introduce `R _ ℓ ζ h0 hζ h1 s j i n hjs`. Establish `hpow : ∀ t i, ζ (i + t) ^ (ℓ ^ t) = ζ i`. Introduce `t`. Proceed by induction on `t with`. Consider the case `zero => intro i`.

Simplify using the standard rewrite rules. Consider the case `succ t ih`. Introduce `i`. Rewrite using `[pow_succ', pow_mul, ← add_assoc, hζ, ih]`. Establish `hsplit : ∀ k, ζ i ^ (n + ℓ ^ j * k) = ζ i ^ n * (ζ i ^ (ℓ ^ j)) ^ k`.

Introduce `k`. Rewrite using `[pow_add, pow_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `hij`. Establish `hone : ζ i ^ (ℓ ^ j) = 1`.

Take `⟨p, rfl⟩` from `Nat.exists_eq_add_of_le hij`. Use `hpow i 0` as an intermediate fact. Rewrite `this` using `[zero_add, h0]`. Rewrite using `[pow_add, pow_mul, this, one_pow]`. Simplify using `only [hsplit, hone, one_pow, mul_one, Finset.sum_const, Finset.card_range]`.

Introduce `hji his`. Take `⟨t, rfl⟩ : ∃ t, i = j + (t + 1)` from `⟨i - j - 1, by omega⟩`. Establish `hy : ζ (j + (t + 1)) ^ (ℓ ^ j) = ζ (t + 1)`. Rewrite using `[add_comm j (t + 1)]`. Conclude with `hpow j (t + 1)`.

Simplify using `only [hsplit, hy]`. Rewrite using `[← Finset.mul_sum]`. Take `⟨p, hp⟩ : ∃ p, s - j = t + (1 + p)` from `⟨s - j - t - 1, by omega⟩`. Establish `hz : ζ (t + 1) ^ (ℓ ^ t) = ζ 1` using `by rw [add_comm t 1]; exact hpow t 1`. Rewrite using `[hp, pow_add, geom_fact, hz, pow_add, pow_one, geom_fact, h1, zero_mul, mul_zero, mul_zero]`.
-/
theorem charSum : StatCharSum := by
  intro R _ ℓ ζ h0 hζ h1 s j i n hjs
  have hpow : ∀ t i, ζ (i + t) ^ (ℓ ^ t) = ζ i := by
    intro t
    induction t with
    | zero => intro i; simp
    | succ t ih =>
      intro i
      rw [pow_succ', pow_mul, ← add_assoc, hζ, ih]
  have hsplit : ∀ k, ζ i ^ (n + ℓ ^ j * k) = ζ i ^ n * (ζ i ^ (ℓ ^ j)) ^ k := by
    intro k; rw [pow_add, pow_mul]
  constructor
  · intro hij
    have hone : ζ i ^ (ℓ ^ j) = 1 := by
      obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hij
      have := hpow i 0
      rw [zero_add, h0] at this
      rw [pow_add, pow_mul, this, one_pow]
    simp only [hsplit, hone, one_pow, mul_one, Finset.sum_const, Finset.card_range]
  · intro hji his
    obtain ⟨t, rfl⟩ : ∃ t, i = j + (t + 1) := ⟨i - j - 1, by omega⟩
    have hy : ζ (j + (t + 1)) ^ (ℓ ^ j) = ζ (t + 1) := by
      rw [add_comm j (t + 1)]; exact hpow j (t + 1)
    simp only [hsplit, hy]
    rw [← Finset.mul_sum]
    obtain ⟨p, hp⟩ : ∃ p, s - j = t + (1 + p) := ⟨s - j - t - 1, by omega⟩
    have hz : ζ (t + 1) ^ (ℓ ^ t) = ζ 1 := by rw [add_comm t 1]; exact hpow t 1
    rw [hp, pow_add, geom_fact, hz, pow_add, pow_one, geom_fact, h1, zero_mul, mul_zero, mul_zero]

/- English proof (translation)
Introduce `ℓ _ u s hs h2 hu e he abelian₂ _ _ L _ _ V β hV ω`. Take `⟨hne, hval⟩` from `Formalism.WindowSums.valuation_zpow_sub_one ℓ u s hs h2 hu (e : ℤ) (by omega)`. Rewrite `hval` using `[zpow_natCast, padicValInt.of_nat]`. Rewrite `hne` using `[zpow_natCast]`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : ℤ_[ℓ]ˣ, (((u ^ e : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) = (c : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ (s + padicValNat ℓ e) := by`.

Establish `h` using `PadicInt.unitCoeff_spec hne`. Rewrite `h` using `[hval]`. Conclude with `⟨_, h⟩`. Take `⟨la, hla1, hla⟩` from `hV (fun j => ((ℓ : ℤ_[ℓ]) ^ ((e + 1) * (s - 1) - e * (s - j) - (if j = 1 then s - 1 else s - j + 1))) • (β j).symm (((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • ω j))`. Use `⟨la, fun j hj1 hjs => ?_⟩` and prove the remaining obligations.

Establish `hVj : V j la = ((ℓ : ℤ_[ℓ]) ^ ((e + 1) * (s - 1) - e * (s - j))) • (β j).symm (((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • ω j)`. Distinguish the cases in `h1 : j = 1`. Substitute `h1` using the available equality. Rewrite using `[hla1, if_pos rfl, smul_smul, ← pow_add]`. Use `congr 2`.

Establish `: (e + 1) * (s - 1) = e * (s - 1) + (s - 1)` using `by ring`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hla j (by omega) hjs, if_neg h1, smul_smul, ← pow_add]`. Use `congr 2`. Take `⟨p, rfl⟩` from `Nat.exists_eq_add_of_le hjs`.

Take `⟨j', rfl⟩ : ∃ j', j = j' + 2` from `⟨j - 2, by omega⟩`. Establish `e1 : j' + 2 + p - (j' + 2) = p` using `by omega`. Establish `e2 : j' + 2 + p - 1 = j' + p + 1` using `by omega`. Rewrite using `[e1, e2]`. Establish `e3 : (e + 1) * (j' + p + 1) = e * p + (p + 1) + (e * j' + e + j')` using `by ring`.

Use linear arithmetic over natural numbers and integers. Establish `hle : e * (s - j) ≤ (e + 1) * (s - 1)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hVj, map_smul, LinearEquiv.apply_symm_apply, hc, smul_smul, smul_smul, smul_smul]`. Use `congr 1`.

Establish `hexp : (e + 1) * (s - 1) + s + padicValNat ℓ e = (s + padicValNat ℓ e) + (e * (s - j) + ((e + 1) * (s - 1) - e * (s - j)))` using `by omega`. Rewrite using `[hexp, pow_add, pow_add]`. Establish `hcc : (c : ℤ_[ℓ]) * ((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = 1` using `Units.mul_inv c`. Take the linear combination `((ℓ : ℤ_[ℓ]) ^ (s + padicValNat ℓ e) * ((ℓ : ℤ_[ℓ]) ^ (e * (s - j)) * (ℓ : ℤ_[ℓ]) ^ ((e + 1) * (s - 1) - e * (s - j)))) * hcc`.
-/
theorem rValues : StatRValues := by
  intro ℓ _ u s hs h2 hu e he abelian₂ _ _ L _ _ V β hV ω
  obtain ⟨hne, hval⟩ := Formalism.WindowSums.valuation_zpow_sub_one ℓ u s hs h2 hu (e : ℤ) (by omega)
  rw [zpow_natCast, padicValInt.of_nat] at hval
  rw [zpow_natCast] at hne
  obtain ⟨c, hc⟩ : ∃ c : ℤ_[ℓ]ˣ, (((u ^ e : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1)
      = (c : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ (s + padicValNat ℓ e) := by
    have h := PadicInt.unitCoeff_spec hne
    rw [hval] at h
    exact ⟨_, h⟩
  obtain ⟨la, hla1, hla⟩ := hV (fun j =>
    ((ℓ : ℤ_[ℓ]) ^ ((e + 1) * (s - 1) - e * (s - j) - (if j = 1 then s - 1 else s - j + 1))) •
      (β j).symm (((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • ω j))
  refine ⟨la, fun j hj1 hjs => ?_⟩
  have hVj : V j la = ((ℓ : ℤ_[ℓ]) ^ ((e + 1) * (s - 1) - e * (s - j))) •
      (β j).symm (((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • ω j) := by
    by_cases h1 : j = 1
    · subst h1
      rw [hla1, if_pos rfl, smul_smul, ← pow_add]
      congr 2
      have : (e + 1) * (s - 1) = e * (s - 1) + (s - 1) := by ring
      omega
    · rw [hla j (by omega) hjs, if_neg h1, smul_smul, ← pow_add]
      congr 2
      obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hjs
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
      have e1 : j' + 2 + p - (j' + 2) = p := by omega
      have e2 : j' + 2 + p - 1 = j' + p + 1 := by omega
      rw [e1, e2]
      have e3 : (e + 1) * (j' + p + 1) = e * p + (p + 1) + (e * j' + e + j') := by ring
      omega
  have hle : e * (s - j) ≤ (e + 1) * (s - 1) := by
    calc e * (s - j) ≤ e * (s - 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ (e + 1) * (s - 1) := Nat.mul_le_mul_right _ (by omega)
  rw [hVj, map_smul, LinearEquiv.apply_symm_apply, hc, smul_smul, smul_smul, smul_smul]
  congr 1
  have hexp : (e + 1) * (s - 1) + s + padicValNat ℓ e
      = (s + padicValNat ℓ e) + (e * (s - j) + ((e + 1) * (s - 1) - e * (s - j))) := by omega
  rw [hexp, pow_add, pow_add]
  have hcc : (c : ℤ_[ℓ]) * ((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = 1 := Units.mul_inv c
  linear_combination ((ℓ : ℤ_[ℓ]) ^ (s + padicValNat ℓ e) * ((ℓ : ℤ_[ℓ]) ^ (e * (s - j)) *
    (ℓ : ℤ_[ℓ]) ^ ((e + 1) * (s - 1) - e * (s - j)))) * hcc

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
