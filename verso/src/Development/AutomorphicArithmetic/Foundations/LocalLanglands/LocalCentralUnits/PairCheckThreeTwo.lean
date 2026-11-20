import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.PinFld

open Finset

namespace UpperTheory.Zero.LLC.CharacterSumPairs

private def Reg (g n N t : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, (t * g ^ i) % N = (t * g ^ j) % N → i = j

private def Cl (g n N e t : ℕ) : Prop :=
  ∀ i < n, ∃ j < n, (t * g ^ i + e) % N = (t * g ^ j) % N

private instance (g n N t : ℕ) : Decidable (Reg g n N t) := by
  unfold Reg
  infer_instance

private instance (g n N e t : ℕ) : Decidable (Cl g n N e t) := by
  unfold Cl
  infer_instance

private def Pair (g n N e t t' : ℕ) : Prop :=
  (Reg g n N t ∧ Cl g n N e t) → (Reg g n N t' ∧ Cl g n N e t') → ∃ j < n, t' % N = (t * g ^ j) % N

private instance (g n N e t t' : ℕ) : Decidable (Pair g n N e t t') := by
  unfold Pair
  infer_instance

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem pairCheck_two_two : ∀ t < 2 ^ 2 - 1, ∀ t' < 2 ^ 2 - 1, Pair 2 2 (2 ^ 2 - 1) 1 t t' := by
  decide

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem pairCheck_three_two : ∀ t < 3 ^ 2 - 1, ∀ t' < 3 ^ 2 - 1, Pair 3 2 (3 ^ 2 - 1) 2 t t' := by
  decide

set_option maxHeartbeats 4000000 in
/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem pairCheck_two_four : ∀ t < 2 ^ 4 - 1, ∀ t' < 2 ^ 4 - 1, Pair 2 4 (2 ^ 4 - 1) 3 t t' := by
  decide

set_option maxHeartbeats 40000000 in
/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem pairCheck_two_six : ∀ t < 2 ^ 6 - 1, ∀ t' < 2 ^ 6 - 1, Pair 2 6 (2 ^ 6 - 1) 21 t t' := by
  decide

section

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K]

/- English proof (translation)
Rewrite using `[Fintype.card_eq_nat_card, Nat.card_units, natCard_K hn hr]`.
-/
private theorem card_unitsK [Fintype Kˣ] (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) :
    Fintype.card Kˣ = g ^ n - 1 := by
  rw [Fintype.card_eq_nat_card, Nat.card_units, natCard_K hn hr]

/- English proof (translation)
Use `haveI := fin_of hn hr`. Use `letI : Fintype Kˣ := Fintype.ofFinite Kˣ`. Assume the negation of the conclusion as `hne`. Establish `hdisj` using `disj_cj hn hr θ θ' hne`. Take `⟨D, hD1, hD2, -⟩` from `exists_D (K := K) (g := g) hn hr`.

Establish `hdif : ∀ z ∉ D, dif (cj g n θ) (cj g n θ') z = 0`. Introduce `z hz`. Unfold `dif`. Rewrite using `[sum_cj hθ, sum_cj hθ', hs z (hD1 z hz), sub_self]`. Take `⟨η₀, hgen, hpow⟩` from `exists_gen_char (G := Kˣ)`.

Establish `hcard` using `card_unitsK (K := K) (g := g) hn hr`. Rewrite `hgen`, `hpow` using `[hcard]`. Establish `key : ∀ s : ℕ, (∀ i j, i < n → j < n → (η₀ ^ s) ^ g ^ i = (η₀ ^ s) ^ g ^ j → i = j) → (∀ ψ ∈ cj g n (η₀ ^ s), ψ * η₀ ^ e ∈ cj g n (η₀ ^ s)) → Reg g n (g ^ n - 1) s ∧ Cl g n (g ^ n - 1) e s`. Introduce `s hreg hcl`. Unfold `Reg Cl`.

Use `⟨fun i hi j hj hij => hreg i j hi hj ?_, fun i hi => ?_⟩` and prove the remaining obligations. Rewrite using `[← pow_mul, ← pow_mul, hpow]`. Conclude with `hij`. Establish `hm : (η₀ ^ s) ^ g ^ i ∈ cj g n (η₀ ^ s)` using `mem_cj.2 ⟨i, hi, rfl⟩`. Take `⟨j, hj, hjeq⟩` from `mem_cj.1 (hcl _ hm)`.

Use `⟨j, hj, ?_⟩` and prove the remaining obligations. Rewrite `hjeq` using `[← pow_mul, ← pow_mul, ← pow_add, hpow]`. Conclude with `hjeq.symm`. Establish `hηD : ∀ z ∈ D, (η₀ ^ e) z = 1`. Introduce `z hz`.

Take `⟨p, hp, hzp⟩` from `hD2 z hz`. Take `⟨c, hc⟩` from `he p hp`. Rewrite using `[MonoidHom.pow_apply, ← map_pow, hc, pow_mul, hzp, one_pow, map_one]`. Establish `hmm` using `mul_mem _ _ hdisj D hdif (η₀ ^ e) hηD`. Take `⟨t, ht, rfl⟩` from `hgen θ`.

Take `⟨t', ht', rfl⟩` from `hgen θ'`. Establish `hP` using `hcheck t ht t' ht'`. Unfold `Pair at hP`. Take `⟨j, hj, hjt⟩` from `hP (key t hθ (fun ψ hψ => (hmm ψ).1 hψ)) (key t' hθ' (fun ψ hψ => (hmm ψ).2 hψ))`. Conclude with `hne ⟨j, hj, by rw [← pow_mul, hpow]; exact hjt⟩`.
-/
private theorem exc (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (e : ℕ)
    (he : ∀ p ∈ n.primeFactors, (g ^ (n / p) - 1) ∣ e)
    (hcheck : ∀ t < g ^ n - 1, ∀ t' < g ^ n - 1, Pair g n (g ^ n - 1) e t t')
    (θ θ' : Kˣ →* ℂˣ)
    (hθ : ∀ i j, i < n → j < n → θ ^ g ^ i = θ ^ g ^ j → i = j)
    (hθ' : ∀ i j, i < n → j < n → θ' ^ g ^ i = θ' ^ g ^ j → i = j)
    (hs : ∀ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n →
      ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) = ∑ j ∈ range n, ((θ' (z ^ g ^ j) : ℂˣ) : ℂ)) :
    ∃ j < n, θ' = θ ^ g ^ j := by
  classical
  haveI := fin_of hn hr
  letI : Fintype Kˣ := Fintype.ofFinite Kˣ
  by_contra hne
  have hdisj := disj_cj hn hr θ θ' hne
  obtain ⟨D, hD1, hD2, -⟩ := exists_D (K := K) (g := g) hn hr
  have hdif : ∀ z ∉ D, dif (cj g n θ) (cj g n θ') z = 0 := by
    intro z hz
    unfold dif
    rw [sum_cj hθ, sum_cj hθ', hs z (hD1 z hz), sub_self]
  obtain ⟨η₀, hgen, hpow⟩ := exists_gen_char (G := Kˣ)
  have hcard := card_unitsK (K := K) (g := g) hn hr
  rw [hcard] at hgen hpow
  have key : ∀ s : ℕ, (∀ i j, i < n → j < n → (η₀ ^ s) ^ g ^ i = (η₀ ^ s) ^ g ^ j → i = j) →
      (∀ ψ ∈ cj g n (η₀ ^ s), ψ * η₀ ^ e ∈ cj g n (η₀ ^ s)) →
      Reg g n (g ^ n - 1) s ∧ Cl g n (g ^ n - 1) e s := by
    intro s hreg hcl
    unfold Reg Cl
    refine ⟨fun i hi j hj hij => hreg i j hi hj ?_, fun i hi => ?_⟩
    · rw [← pow_mul, ← pow_mul, hpow]
      exact hij
    · have hm : (η₀ ^ s) ^ g ^ i ∈ cj g n (η₀ ^ s) := mem_cj.2 ⟨i, hi, rfl⟩
      obtain ⟨j, hj, hjeq⟩ := mem_cj.1 (hcl _ hm)
      refine ⟨j, hj, ?_⟩
      rw [← pow_mul, ← pow_mul, ← pow_add, hpow] at hjeq
      exact hjeq.symm
  have hηD : ∀ z ∈ D, (η₀ ^ e) z = 1 := by
    intro z hz
    obtain ⟨p, hp, hzp⟩ := hD2 z hz
    obtain ⟨c, hc⟩ := he p hp
    rw [MonoidHom.pow_apply, ← map_pow, hc, pow_mul, hzp, one_pow, map_one]
  have hmm := mul_mem _ _ hdisj D hdif (η₀ ^ e) hηD
  obtain ⟨t, ht, rfl⟩ := hgen θ
  obtain ⟨t', ht', rfl⟩ := hgen θ'
  have hP := hcheck t ht t' ht'
  unfold Pair at hP
  obtain ⟨j, hj, hjt⟩ := hP (key t hθ (fun ψ hψ => (hmm ψ).1 hψ))
    (key t' hθ' (fun ψ hψ => (hmm ψ).2 hψ))
  exact hne ⟨j, hj, by rw [← pow_mul, hpow]; exact hjt⟩

/- English proof (translation)
Use `haveI := fin_of hn hr`. Use `letI : Fintype Kˣ := Fintype.ofFinite Kˣ`. Establish `hg2 : 2 ≤ g` using `(Fact.out : g.Prime).two_le`. Establish `hcard` using `card_unitsK (K := K) (g := g) hn hr`. Take `⟨D, hD1, hD2, hDb⟩` from `exists_D (K := K) (g := g) hn hr`.

Establish `hA` using `card_cj hθ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hno push_neg at hno`. Establish `hdif : ∀ z ∉ D, dif (cj g n θ) ∅ z = 0`. Introduce `z hz`.

Unfold `dif`. Rewrite using `[sum_cj hθ, hno z (hD1 z hz)]`. Simplify using the standard rewrite rules. Establish `hle` using `card_le (cj g n θ) ∅ (Finset.disjoint_empty_right _) D hdif (by simp [hA, hn])`. Rewrite `hle` using `[hA, hcard]`.

Simplify using `only [Finset.card_empty, add_zero] at hle`. Establish `h1` using `one_bd g n hg2 hn`. Establish `h2 : D.card * n ≤ n * bd g n`. Rewrite using `[mul_comm n]`. Conclude with `Nat.mul_le_mul_right n hDb`.

Use linear arithmetic over natural numbers and integers. Introduce `θ' hθ' hs`. Distinguish the cases in `hex : g = 2 ∧ n = 2 ∨ g = 3 ∧ n = 2 ∨ g = 2 ∧ n = 4 ∨ g = 2 ∧ n = 6`. Break down `hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases. Use `exc hn hr 1 ?_ pairCheck_two_two θ θ' hθ hθ' hs` and prove the remaining obligations.

Introduce `p hp`. Establish `h1` using `Nat.le_of_mem_primeFactors hp`. Establish `h2` using `Nat.dvd_of_mem_primeFactors hp`. Establish `h3` using `(Nat.prime_of_mem_primeFactors hp).two_le`. Apply the tactic sequence `interval_cases p <;> revert h2 <;> decide`.

Use `exc hn hr 2 ?_ pairCheck_three_two θ θ' hθ hθ' hs` and prove the remaining obligations. Introduce `p hp`. Establish `h1` using `Nat.le_of_mem_primeFactors hp`. Establish `h2` using `Nat.dvd_of_mem_primeFactors hp`. Establish `h3` using `(Nat.prime_of_mem_primeFactors hp).two_le`.

Apply the tactic sequence `interval_cases p <;> revert h2 <;> decide`. Use `exc hn hr 3 ?_ pairCheck_two_four θ θ' hθ hθ' hs` and prove the remaining obligations. Introduce `p hp`. Establish `h1` using `Nat.le_of_mem_primeFactors hp`. Establish `h2` using `Nat.dvd_of_mem_primeFactors hp`.

Establish `h3` using `(Nat.prime_of_mem_primeFactors hp).two_le`. Apply the tactic sequence `interval_cases p <;> revert h2 <;> decide`. Use `exc hn hr 21 ?_ pairCheck_two_six θ θ' hθ hθ' hs` and prove the remaining obligations. Introduce `p hp`. Establish `h1` using `Nat.le_of_mem_primeFactors hp`.

Establish `h2` using `Nat.dvd_of_mem_primeFactors hp`. Establish `h3` using `(Nat.prime_of_mem_primeFactors hp).two_le`. Apply the tactic sequence `interval_cases p <;> revert h2 <;> decide`. Assume the negation of the conclusion as `hne`. Establish `hB` using `card_cj hθ'`.

Establish `hdisj` using `disj_cj hn hr θ θ' hne`. Establish `hdif : ∀ z ∉ D, dif (cj g n θ) (cj g n θ') z = 0`. Introduce `z hz`. Unfold `dif`. Rewrite using `[sum_cj hθ, sum_cj hθ', hs z (hD1 z hz), sub_self]`.

Establish `hle` using `card_le _ _ hdisj D hdif (by rw [hA, hB]; omega)`. Rewrite `hle` using `[hA, hB, hcard]`. Establish `h1` using `two_bd g n hg2 hn hex`. Establish `h2 : D.card * (n + n) ≤ 2 * n * bd g n`. Combine the equalities or inequalities in the displayed calculation.

Use linear arithmetic over natural numbers and integers.
-/
private theorem main (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (θ : Kˣ →* ℂˣ)
    (hθ : ∀ i j, i < n → j < n → θ ^ g ^ i = θ ^ g ^ j → i = j) :
    (∃ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n ∧
      ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) ≠ 0) ∧
    ∀ θ' : Kˣ →* ℂˣ, (∀ i j, i < n → j < n → θ' ^ g ^ i = θ' ^ g ^ j → i = j) →
      (∀ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n →
        ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) = ∑ j ∈ range n, ((θ' (z ^ g ^ j) : ℂˣ) : ℂ)) →
      ∃ j < n, θ' = θ ^ g ^ j := by
  classical
  haveI := fin_of hn hr
  letI : Fintype Kˣ := Fintype.ofFinite Kˣ
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hcard := card_unitsK (K := K) (g := g) hn hr
  obtain ⟨D, hD1, hD2, hDb⟩ := exists_D (K := K) (g := g) hn hr
  have hA := card_cj hθ
  refine ⟨?_, ?_⟩
  · by_contra hno
    push_neg at hno
    have hdif : ∀ z ∉ D, dif (cj g n θ) ∅ z = 0 := by
      intro z hz
      unfold dif
      rw [sum_cj hθ, hno z (hD1 z hz)]
      simp
    have hle := card_le (cj g n θ) ∅ (Finset.disjoint_empty_right _) D hdif (by simp [hA, hn])
    rw [hA, hcard] at hle
    simp only [Finset.card_empty, add_zero] at hle
    have h1 := one_bd g n hg2 hn
    have h2 : D.card * n ≤ n * bd g n := by
      rw [mul_comm n]
      exact Nat.mul_le_mul_right n hDb
    omega
  · intro θ' hθ' hs
    by_cases hex : g = 2 ∧ n = 2 ∨ g = 3 ∧ n = 2 ∨ g = 2 ∧ n = 4 ∨ g = 2 ∧ n = 6
    · rcases hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine exc hn hr 1 ?_ pairCheck_two_two θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
      · refine exc hn hr 2 ?_ pairCheck_three_two θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
      · refine exc hn hr 3 ?_ pairCheck_two_four θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
      · refine exc hn hr 21 ?_ pairCheck_two_six θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
    · by_contra hne
      have hB := card_cj hθ'
      have hdisj := disj_cj hn hr θ θ' hne
      have hdif : ∀ z ∉ D, dif (cj g n θ) (cj g n θ') z = 0 := by
        intro z hz
        unfold dif
        rw [sum_cj hθ, sum_cj hθ', hs z (hD1 z hz), sub_self]
      have hle := card_le _ _ hdisj D hdif (by rw [hA, hB]; omega)
      rw [hA, hB, hcard] at hle
      have h1 := two_bd g n hg2 hn hex
      have h2 : D.card * (n + n) ≤ 2 * n * bd g n := by
        calc D.card * (n + n) ≤ bd g n * (n + n) := Nat.mul_le_mul_right _ hDb
          _ = 2 * n * bd g n := by ring
      omega

end

end UpperTheory.Zero.LLC.CharacterSumPairs

/- English proof (translation)
Unfold `UpperTheory.Zero.LLC.Pin`. Introduce `g _ n hn K _ _ hr θ hθ`. Conclude with `UpperTheory.Zero.LLC.CharacterSumPairs.main hn hr θ hθ`.
-/
theorem UpperTheory.Zero.LLC.pin :
    UpperTheory.Zero.LLC.Pin := by
  unfold UpperTheory.Zero.LLC.Pin
  intro g _ n hn K _ _ hr θ hθ
  exact UpperTheory.Zero.LLC.CharacterSumPairs.main hn hr θ hθ
