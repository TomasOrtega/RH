import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.Slope

open MvPowerSeries

variable {k : Type} [Field k]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`. Simplify using `[Fin.sum_univ_two, mul_comm]`.
-/
lemma weight_two (m n : ℕ) (s : Fin 2 →₀ ℕ) :
    Finsupp.weight (![m, n] : Fin 2 → ℕ) s = m * s 0 + n * s 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fin.sum_univ_two, mul_comm]

/- English proof (translation)
The claim follows from `exists_coeff_ne_zero_and_weightedOrder w ((ne_zero_iff_weightedOrder_finite w).1 hf)`.
-/
lemma exists_min (w : Fin 2 → ℕ) (f : MvPowerSeries (Fin 2) k) (hf : f ≠ 0) :
    ∃ s, coeff s f ≠ 0 ∧ (Finsupp.weight w s : ℕ∞) = weightedOrder w f :=
  exists_coeff_ne_zero_and_weightedOrder w ((ne_zero_iff_weightedOrder_finite w).1 hf)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hf : f ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h`.

Take `⟨s, hs, hs'⟩` from `exists_min ![m, n] f hf`. Use `⟨s, hs, fun t ht => ?_⟩` and prove the remaining obligations. Use `lt_of_lt_of_le (hs' ▸ h) (weightedOrder_le ![m, n] ht)` as an intermediate fact. Rewrite using `[← weight_two, ← weight_two]`. Conclude with `this` after adjusting the coercions.

Introduce and unpack `⟨s, hs, h⟩`. Use `lt_of_le_of_lt (weightedOrder_le _ hs) ?_` and prove the remaining obligations. Distinguish the cases in `hg : g = 0`. Substitute `hg` using the available equality. Simplify using the standard rewrite rules.

Take `⟨t, ht, ht'⟩` from `exists_min ![m, n] g hg`. Rewrite using `[← ht', weight_two, weight_two]`. Conclude with `h t ht` after adjusting the coercions.
-/
lemma lt_iff (m n : ℕ) (f g : MvPowerSeries (Fin 2) k) :
    weightedOrder (![m, n] : Fin 2 → ℕ) f < weightedOrder (![m, n] : Fin 2 → ℕ) g ↔
      ∃ s : Fin 2 →₀ ℕ, coeff s f ≠ 0 ∧ ∀ t : Fin 2 →₀ ℕ, coeff t g ≠ 0 →
        m * s 0 + n * s 1 < m * t 0 + n * t 1 := by
  constructor
  · intro h
    have hf : f ≠ 0 := by
      rintro rfl
      simp at h
    obtain ⟨s, hs, hs'⟩ := exists_min ![m, n] f hf
    refine ⟨s, hs, fun t ht => ?_⟩
    have := lt_of_lt_of_le (hs' ▸ h) (weightedOrder_le ![m, n] ht)
    rw [← weight_two, ← weight_two]
    exact_mod_cast this
  · rintro ⟨s, hs, h⟩
    refine lt_of_le_of_lt (weightedOrder_le _ hs) ?_
    by_cases hg : g = 0
    · subst hg
      simp
    · obtain ⟨t, ht, ht'⟩ := exists_min ![m, n] g hg
      rw [← ht', weight_two, weight_two]
      exact_mod_cast h t ht

/- English proof (translation)
Take `⟨t, ht, h⟩` from `(lt_iff m n f d).1 h`. Use `set N := (s₀ 0).factorial with hN`. Establish `hNpos : 0 < N` using `Nat.factorial_pos _`. Establish `ht1` using `hf t ht`. Establish `htle : t 1 ≤ s₀ 0`.

Use `h s₀ hs₀` as an intermediate fact. Rewrite `this` using `[hs₀']`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Use polynomial arithmetic with `[Nat.zero_le (m * t 0), Nat.mul_le_mul hmn hc.le]`.

Establish `hex : ∀ s : Fin 2 →₀ ℕ, coeff s d ≠ 0 → s 1 < t 1 → ∃ p, N * t 0 + p * t 1 = N * s 0 + p * s 1`. Introduce `s hs hlt`. Establish `h1` using `h s hs`. Establish `h2 : t 0 ≤ s 0`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Use polynomial arithmetic with `[Nat.mul_le_mul_left m hc.le, Nat.mul_le_mul_left n hlt.le]`. Take `⟨a, ha⟩` from `Nat.exists_eq_add_of_le h2`. Take `⟨b, hb⟩` from `Nat.exists_eq_add_of_le hlt.le`. Establish `: b ∣ N` using `Nat.dvd_factorial (by omega) (by omega)`.

Take `⟨c, hc⟩` from `this`. Use `⟨c * a, ?_⟩` and prove the remaining obligations. Rewrite using `[ha, hb, hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hP : ∃ p, ∃ s : Fin 2 →₀ ℕ, coeff s d ≠ 0 ∧ s 1 < t 1 ∧ N * t 0 + p * t 1 = N * s 0 + p * s 1`.

Take `⟨p, hp⟩` from `hex s₀ hs₀ (by omega)`. Conclude with `⟨p, s₀, hs₀, by omega, hp⟩`. Take `⟨s₁, hs₁, hlt₁, heq₁⟩` from `Nat.find_spec hP`. Use `set p := Nat.find hP with hp`. Establish `hbig : n * N < m * p`.

Establish `h1` using `h s₁ hs₁`. Take `⟨b, hb⟩` from `Nat.exists_eq_add_of_le hlt₁.le`. Rewrite `h1`, `heq₁` using `[hb]`. Establish `h2 : n * N * b < m * p * b` using `by nlinarith`. Conclude with `lt_of_mul_lt_mul_right h2 (Nat.zero_le _)`.

Use `⟨p, hbig, ?_⟩` and prove the remaining obligations. Rewrite using `[lt_iff]`. Introduce and unpack `⟨s, hs, hs'⟩`. Establish `h3` using `hs' t ht`. Distinguish the cases in `hlt : s 1 < t 1`.

Take `⟨q, hq⟩` from `hex s hs hlt`. Establish `hpq : p ≤ q` using `Nat.find_min' hP ⟨s, hs, hlt, hq⟩`. Take `⟨b, hb⟩` from `Nat.exists_eq_add_of_le hlt.le`. Rewrite `h3`, `hq` using `[hb]`. Use polynomial arithmetic with `[Nat.mul_le_mul_right b hpq]`.

Use `push Not at hlt`. Take `⟨b, hb⟩` from `Nat.exists_eq_add_of_le hlt`. Establish `h1` using `h s hs`. Rewrite `h3`, `h1` using `[hb]`. Establish `h4 : N * s 0 + p * b < N * t 0` using `by nlinarith`.

Establish `h5 : m * t 0 < m * s 0 + n * b` using `by nlinarith`. Establish `h6` using `Nat.mul_lt_mul_of_pos_left h4 (k := m) hm`. Establish `h7` using `Nat.mul_lt_mul_of_pos_left h5 (k := N) hNpos`. Use polynomial arithmetic with `[Nat.mul_le_mul_right b hbig.le]`.
-/
lemma step (f d : MvPowerSeries (Fin 2) k) (hf : ∀ t : Fin 2 →₀ ℕ, coeff t f ≠ 0 → 1 ≤ t 1)
    (s₀ : Fin 2 →₀ ℕ) (hs₀ : coeff s₀ d ≠ 0) (hs₀' : s₀ 1 = 0) (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    (h : weightedOrder (![m, n] : Fin 2 → ℕ) f < weightedOrder (![m, n] : Fin 2 → ℕ) d) :
    ∃ p, n * (s₀ 0).factorial < m * p ∧
      ¬ weightedOrder (![(s₀ 0).factorial, p] : Fin 2 → ℕ) d <
        weightedOrder (![(s₀ 0).factorial, p] : Fin 2 → ℕ) f := by
  classical
  obtain ⟨t, ht, h⟩ := (lt_iff m n f d).1 h
  set N := (s₀ 0).factorial with hN
  have hNpos : 0 < N := Nat.factorial_pos _
  have ht1 := hf t ht
  have htle : t 1 ≤ s₀ 0 := by
    have := h s₀ hs₀
    rw [hs₀'] at this
    by_contra hc
    push Not at hc
    nlinarith [Nat.zero_le (m * t 0), Nat.mul_le_mul hmn hc.le]
  have hex : ∀ s : Fin 2 →₀ ℕ, coeff s d ≠ 0 → s 1 < t 1 →
      ∃ p, N * t 0 + p * t 1 = N * s 0 + p * s 1 := by
    intro s hs hlt
    have h1 := h s hs
    have h2 : t 0 ≤ s 0 := by
      by_contra hc
      push Not at hc
      nlinarith [Nat.mul_le_mul_left m hc.le, Nat.mul_le_mul_left n hlt.le]
    obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le h2
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hlt.le
    have : b ∣ N := Nat.dvd_factorial (by omega) (by omega)
    obtain ⟨c, hc⟩ := this
    refine ⟨c * a, ?_⟩
    rw [ha, hb, hc]
    ring
  have hP : ∃ p, ∃ s : Fin 2 →₀ ℕ, coeff s d ≠ 0 ∧ s 1 < t 1 ∧
      N * t 0 + p * t 1 = N * s 0 + p * s 1 := by
    obtain ⟨p, hp⟩ := hex s₀ hs₀ (by omega)
    exact ⟨p, s₀, hs₀, by omega, hp⟩
  obtain ⟨s₁, hs₁, hlt₁, heq₁⟩ := Nat.find_spec hP
  set p := Nat.find hP with hp
  have hbig : n * N < m * p := by
    have h1 := h s₁ hs₁
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hlt₁.le
    rw [hb] at h1 heq₁
    have h2 : n * N * b < m * p * b := by nlinarith
    exact lt_of_mul_lt_mul_right h2 (Nat.zero_le _)
  refine ⟨p, hbig, ?_⟩
  rw [lt_iff]
  rintro ⟨s, hs, hs'⟩
  have h3 := hs' t ht
  by_cases hlt : s 1 < t 1
  · obtain ⟨q, hq⟩ := hex s hs hlt
    have hpq : p ≤ q := Nat.find_min' hP ⟨s, hs, hlt, hq⟩
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hlt.le
    rw [hb] at h3 hq
    nlinarith [Nat.mul_le_mul_right b hpq]
  · push Not at hlt
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hlt
    have h1 := h s hs
    rw [hb] at h3 h1
    have h4 : N * s 0 + p * b < N * t 0 := by nlinarith
    have h5 : m * t 0 < m * s 0 + n * b := by nlinarith
    have h6 := Nat.mul_lt_mul_of_pos_left h4 (k := m) hm
    have h7 := Nat.mul_lt_mul_of_pos_left h5 (k := N) hNpos
    nlinarith [Nat.mul_le_mul_right b hbig.le]

end GlobalTheory.SS.Slope

namespace GlobalTheory.SS

open MvPowerSeries Slope in

/- English proof (translation)
Introduce `k _ r h d hd Q hQ`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `hh hdX ⟨m, n, hm, hmn, hnQ⟩`. Establish `hf : ∀ i (t : Fin 2 →₀ ℕ), coeff t (h i) ≠ 0 → 1 ≤ t 1`. Introduce `i t ht`.

Assume the negation of the conclusion as `hc`. Conclude with `ht (X_dvd_iff.1 (hh i) t (by omega))`. Choose the witnesses or unpack the hypotheses as in `⟨s₀, hs₀', hs₀⟩ : ∃ s : Fin 2 →₀ ℕ, s 1 = 0 ∧ coeff s d ≠ 0 := by`. Rewrite `hdX` using `[X_dvd_iff]`. Use `push Not at hdX`.

Conclude with `hdX`. Assume the negation of the conclusion as `hcon`. Establish `key : ∀ m n, 1 ≤ m → m ≤ n → ¬ Q m n → ∃ p, n * (s₀ 0).factorial < m * p ∧ ¬ Q (s₀ 0).factorial p`. Introduce `m n hm hmn hnQ`. Distinguish the cases in `hall : ∀ i, weightedOrder (![m, n] : Fin 2 → ℕ) d ≤ weightedOrder (![m, n] : Fin 2 → ℕ) (h i)`.

It suffices to derive a contradiction. Apply `hcon` to reduce the goal to its premises. Use `⟨m, n, hm, hmn, hall, ?_⟩` and prove the remaining obligations. Rewrite `hnQ` using `[hQ]`. Use `push Not at hnQ`.

Take `⟨i, hi⟩` from `hnQ`. Conclude with `⟨i, le_antisymm (hall i) hi⟩`. Use `push Not at hall`. Take `⟨i, hi⟩` from `hall`. Take `⟨p, hp, hp'⟩` from `step (h i) d (hf i) s₀ hs₀ hs₀' m n hm hmn hi`.

Conclude with `⟨p, hp, fun hq => hp' ((hQ _ _).1 hq i)⟩`. Use `set N := (s₀ 0).factorial with hN`. Establish `hNpos : 0 < N` using `Nat.factorial_pos _`. Establish `unb : ∀ j : ℕ, ∃ p, N + j ≤ p ∧ ¬ Q N p`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero`. Take `⟨p, hp, hp'⟩` from `key m n hm hmn hnQ`. Use `⟨p, ?_, hp'⟩` and prove the remaining obligations. Establish `: m * N < m * p` using `lt_of_le_of_lt (Nat.mul_le_mul_right _ hmn) hp`.

Use `lt_of_mul_lt_mul_left this (Nat.zero_le _)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Consider the case `succ j ih`. Take `⟨q, hq, hq'⟩` from `ih`. Take `⟨p, hp, hp'⟩` from `key N q hNpos (by omega) hq'`.

Use `⟨p, ?_, hp'⟩` and prove the remaining obligations. Rewrite `hp` using `[mul_comm]`. Use `lt_of_mul_lt_mul_left hp (Nat.zero_le _)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨p, hp, hp'⟩` from `unb (N * s₀ 0)`.

Apply `hp'` to reduce the goal to its premises. Rewrite using `[hQ]`. Introduce `i`. Rewrite using `[lt_iff]`. Use `⟨s₀, hs₀, fun t ht => ?_⟩` and prove the remaining obligations.

Use `hf i t ht` as an intermediate fact. Rewrite using `[hs₀']`. Use polynomial arithmetic with `[Nat.mul_le_mul_left p this, Nat.zero_le (N * t 0)]`. Introduce `h11`. Take `⟨s, hs, hs'⟩` from `exists_min ![1, 1] d hd`.

Use `⟨s 1 + 1, fun m hm => ?_⟩` and prove the remaining obligations. Rewrite using `[hQ]`. Introduce `i`. Rewrite using `[lt_iff]`. Use `⟨s, hs, fun t ht => ?_⟩` and prove the remaining obligations.

Establish `h1` using `lt_of_lt_of_le (hs' ▸ (hQ _ _).1 h11 i) (weightedOrder_le ![1, 1] ht)`. Rewrite `h1` using `[weight_two, weight_two]`. Establish `h2 : 1 * s 0 + 1 * s 1 < 1 * t 0 + 1 * t 1` using `by exact_mod_cast h1`. Establish `h3 : s 0 + s 1 + 1 ≤ t 0 + t 1` using `by omega`. Use polynomial arithmetic with `[Nat.mul_le_mul_left m h3, Nat.zero_le (t 1)]`.

Introduce `m n l hl`. Rewrite using `[hQ, hQ]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[lt_iff, lt_iff]`. Use `exists_congr fun s => and_congr_right fun _ => forall_congr' fun t => imp_congr_right fun _ => ?_` and prove the remaining obligations.

Rewrite using `[Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add]`. Conclude with `Nat.mul_lt_mul_left hl`. Introduce `hall i`. Establish `hP : ∃ e, ∃ s : Fin 2 →₀ ℕ, coeff s d ≠ 0 ∧ s 1 = e`. Take `⟨s, hs, -⟩` from `exists_min ![1, 1] d hd`.

Conclude with `⟨_, s, hs, rfl⟩`. Take `⟨s₁, hs₁, he⟩` from `Nat.find_spec hP`. Use `set e := Nat.find hP with hedef`. Establish `hmin : ∀ s : Fin 2 →₀ ℕ, coeff s d ≠ 0 → e ≤ s 1` using `fun s hs => Nat.find_min' hP ⟨s, hs, rfl⟩`. Establish `hdv : (X 1 : MvPowerSeries (Fin 2) k) ^ e ∣ d`.

Rewrite using `[X_pow_dvd_iff]`. Introduce `s hs`. Assume the negation of the conclusion as `hc`. Use `hmin s hc` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hhu : (X 1 : MvPowerSeries (Fin 2) k) ^ e ∣ h i`. Rewrite using `[X_pow_dvd_iff]`. Introduce `t ht`. Assume the negation of the conclusion as `hc`. Take `⟨s, hs, hs'⟩` from `(lt_iff _ _ _ _).1 ((hQ _ _).1 (hall (t 0 + 1) (by omega)) i)`.

Establish `h1` using `hs' t hc`. Establish `h2 : t 1 + 1 ≤ s 1` using `le_trans ht (hmin s hs)`. Use polynomial arithmetic with `[Nat.mul_le_mul_left (t 0 + 1) h2, Nat.zero_le (s 0)]`. Take `⟨v, hv⟩` from `hdv`. Take `⟨u, hu⟩` from `hhu`.

Use `⟨u, v, ?_, by rw [hu, hv]; ring⟩` and prove the remaining obligations. Introduce and unpack `⟨w, hw⟩`. Establish `: (X 1 : MvPowerSeries (Fin 2) k) ^ (e + 1) ∣ d` using `⟨w, by rw [hv, hw]; ring⟩`. Conclude with `hs₁ (X_pow_dvd_iff.1 this s₁ (by omega))`.
-/
theorem weightedOrder_slope_comparison : ∀ (k : Type) [Field k] (r : ℕ) (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), d ≠ 0 → ∀ Q : ℕ → ℕ → Prop, (∀ m n, Q m n ↔ ∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) → ((∀ i, MvPowerSeries.X 1 ∣ h i) → ¬ MvPowerSeries.X 1 ∣ d → (∃ m n, 1 ≤ m ∧ m ≤ n ∧ ¬ Q m n) → ∃ m n, 1 ≤ m ∧ m ≤ n ∧ (∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) ∧ ∃ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d = MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) ∧ (Q 1 1 → ∃ m₀, ∀ m, m₀ ≤ m → Q m (m + 1)) ∧ (∀ m n l, 1 ≤ l → (Q (l * m) (l * n) ↔ Q m n)) ∧ ((∀ n, 1 ≤ n → Q 1 n) → ∀ i, ∃ u v, ¬ MvPowerSeries.X 1 ∣ v ∧ h i * v = d * u) := by
  classical
  intro k _ r h d hd Q hQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro hh hdX ⟨m, n, hm, hmn, hnQ⟩
    have hf : ∀ i (t : Fin 2 →₀ ℕ), coeff t (h i) ≠ 0 → 1 ≤ t 1 := by
      intro i t ht
      by_contra hc
      exact ht (X_dvd_iff.1 (hh i) t (by omega))
    obtain ⟨s₀, hs₀', hs₀⟩ : ∃ s : Fin 2 →₀ ℕ, s 1 = 0 ∧ coeff s d ≠ 0 := by
      rw [X_dvd_iff] at hdX
      push Not at hdX
      exact hdX
    by_contra hcon
    have key : ∀ m n, 1 ≤ m → m ≤ n → ¬ Q m n →
        ∃ p, n * (s₀ 0).factorial < m * p ∧ ¬ Q (s₀ 0).factorial p := by
      intro m n hm hmn hnQ
      by_cases hall : ∀ i, weightedOrder (![m, n] : Fin 2 → ℕ) d ≤
          weightedOrder (![m, n] : Fin 2 → ℕ) (h i)
      · exfalso
        apply hcon
        refine ⟨m, n, hm, hmn, hall, ?_⟩
        rw [hQ] at hnQ
        push Not at hnQ
        obtain ⟨i, hi⟩ := hnQ
        exact ⟨i, le_antisymm (hall i) hi⟩
      · push Not at hall
        obtain ⟨i, hi⟩ := hall
        obtain ⟨p, hp, hp'⟩ := step (h i) d (hf i) s₀ hs₀ hs₀' m n hm hmn hi
        exact ⟨p, hp, fun hq => hp' ((hQ _ _).1 hq i)⟩
    set N := (s₀ 0).factorial with hN
    have hNpos : 0 < N := Nat.factorial_pos _
    have unb : ∀ j : ℕ, ∃ p, N + j ≤ p ∧ ¬ Q N p := by
      intro j
      induction j with
      | zero =>
        obtain ⟨p, hp, hp'⟩ := key m n hm hmn hnQ
        refine ⟨p, ?_, hp'⟩
        have : m * N < m * p := lt_of_le_of_lt (Nat.mul_le_mul_right _ hmn) hp
        have := lt_of_mul_lt_mul_left this (Nat.zero_le _)
        omega
      | succ j ih =>
        obtain ⟨q, hq, hq'⟩ := ih
        obtain ⟨p, hp, hp'⟩ := key N q hNpos (by omega) hq'
        refine ⟨p, ?_, hp'⟩
        rw [mul_comm] at hp
        have := lt_of_mul_lt_mul_left hp (Nat.zero_le _)
        omega
    obtain ⟨p, hp, hp'⟩ := unb (N * s₀ 0)
    apply hp'
    rw [hQ]
    intro i
    rw [lt_iff]
    refine ⟨s₀, hs₀, fun t ht => ?_⟩
    have := hf i t ht
    rw [hs₀']
    nlinarith [Nat.mul_le_mul_left p this, Nat.zero_le (N * t 0)]
  · intro h11
    obtain ⟨s, hs, hs'⟩ := exists_min ![1, 1] d hd
    refine ⟨s 1 + 1, fun m hm => ?_⟩
    rw [hQ]
    intro i
    rw [lt_iff]
    refine ⟨s, hs, fun t ht => ?_⟩
    have h1 := lt_of_lt_of_le (hs' ▸ (hQ _ _).1 h11 i) (weightedOrder_le ![1, 1] ht)
    rw [weight_two, weight_two] at h1
    have h2 : 1 * s 0 + 1 * s 1 < 1 * t 0 + 1 * t 1 := by exact_mod_cast h1
    have h3 : s 0 + s 1 + 1 ≤ t 0 + t 1 := by omega
    nlinarith [Nat.mul_le_mul_left m h3, Nat.zero_le (t 1)]
  · intro m n l hl
    rw [hQ, hQ]
    refine forall_congr' fun i => ?_
    rw [lt_iff, lt_iff]
    refine exists_congr fun s => and_congr_right fun _ => forall_congr' fun t =>
      imp_congr_right fun _ => ?_
    rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add]
    exact Nat.mul_lt_mul_left hl
  · intro hall i
    have hP : ∃ e, ∃ s : Fin 2 →₀ ℕ, coeff s d ≠ 0 ∧ s 1 = e := by
      obtain ⟨s, hs, -⟩ := exists_min ![1, 1] d hd
      exact ⟨_, s, hs, rfl⟩
    obtain ⟨s₁, hs₁, he⟩ := Nat.find_spec hP
    set e := Nat.find hP with hedef
    have hmin : ∀ s : Fin 2 →₀ ℕ, coeff s d ≠ 0 → e ≤ s 1 := fun s hs =>
      Nat.find_min' hP ⟨s, hs, rfl⟩
    have hdv : (X 1 : MvPowerSeries (Fin 2) k) ^ e ∣ d := by
      rw [X_pow_dvd_iff]
      intro s hs
      by_contra hc
      have := hmin s hc
      omega
    have hhu : (X 1 : MvPowerSeries (Fin 2) k) ^ e ∣ h i := by
      rw [X_pow_dvd_iff]
      intro t ht
      by_contra hc
      obtain ⟨s, hs, hs'⟩ := (lt_iff _ _ _ _).1 ((hQ _ _).1 (hall (t 0 + 1) (by omega)) i)
      have h1 := hs' t hc
      have h2 : t 1 + 1 ≤ s 1 := le_trans ht (hmin s hs)
      nlinarith [Nat.mul_le_mul_left (t 0 + 1) h2, Nat.zero_le (s 0)]
    obtain ⟨v, hv⟩ := hdv
    obtain ⟨u, hu⟩ := hhu
    refine ⟨u, v, ?_, by rw [hu, hv]; ring⟩
    rintro ⟨w, hw⟩
    have : (X 1 : MvPowerSeries (Fin 2) k) ^ (e + 1) ∣ d := ⟨w, by rw [hv, hw]; ring⟩
    exact hs₁ (X_pow_dvd_iff.1 this s₁ (by omega))

end GlobalTheory.SS
