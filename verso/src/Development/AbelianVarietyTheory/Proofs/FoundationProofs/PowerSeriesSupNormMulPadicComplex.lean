import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

/- English proof (translation)
Establish `hex : ∃ i, ∀ j, b j ≤ b i`. Distinguish the cases in `hpos : ∃ k, 0 < b k`. Take `⟨k, hk⟩` from `hpos`. Take `⟨N, hN⟩` from `Filter.eventually_atTop.1 (hb.eventually (gt_mem_nhds hk))`. Take `⟨i, hi, hmax⟩` from `(Finset.range (max N (k + 1))).exists_max_image b ⟨k, Finset.mem_range.2 (lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _))⟩`.

Use `⟨i, fun j => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hj : j < max N (k + 1)`. Conclude with `hmax j (Finset.mem_range.2 hj)`. Establish `hjN : N ≤ j` using `le_trans (le_max_left _ _) (not_lt.1 hj)`. Establish `hkmem : k ∈ Finset.range (max N (k + 1))` using `Finset.mem_range.2 (lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _))`.

Conclude with `(hN j hjN).le.trans (hmax k hkmem)`. Use `push Not at hpos`. Conclude with `⟨0, fun j => (hpos j).trans (h0 0)⟩`. Use `⟨Nat.find hex, Nat.find_spec hex, fun i hi => ?_⟩` and prove the remaining obligations. Establish `hle : b i ≤ b (Nat.find hex)` using `Nat.find_spec hex i`.

Use `lt_of_le_of_ne hle fun heq => Nat.find_min hex hi ?_` and prove the remaining obligations. Introduce `j`. Rewrite using `[heq]`. Conclude with `Nat.find_spec hex j`.
-/
theorem exists_least_argmax_of_tendsto_zero (b : ℕ → ℝ) (h0 : ∀ i, 0 ≤ b i)
    (hb : Filter.Tendsto b Filter.atTop (nhds 0)) :
    ∃ i₀, (∀ i, b i ≤ b i₀) ∧ ∀ i < i₀, b i < b i₀ := by
  have hex : ∃ i, ∀ j, b j ≤ b i := by
    by_cases hpos : ∃ k, 0 < b k
    · obtain ⟨k, hk⟩ := hpos
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hb.eventually (gt_mem_nhds hk))
      obtain ⟨i, hi, hmax⟩ := (Finset.range (max N (k + 1))).exists_max_image b
        ⟨k, Finset.mem_range.2 (lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _))⟩
      refine ⟨i, fun j => ?_⟩
      by_cases hj : j < max N (k + 1)
      · exact hmax j (Finset.mem_range.2 hj)
      · have hjN : N ≤ j := le_trans (le_max_left _ _) (not_lt.1 hj)
        have hkmem : k ∈ Finset.range (max N (k + 1)) :=
          Finset.mem_range.2 (lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _))
        exact (hN j hjN).le.trans (hmax k hkmem)
    · push Not at hpos
      exact ⟨0, fun j => (hpos j).trans (h0 0)⟩
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, fun i hi => ?_⟩
  have hle : b i ≤ b (Nat.find hex) := Nat.find_spec hex i
  refine lt_of_le_of_ne hle fun heq => Nat.find_min hex hi ?_
  intro j
  rw [heq]
  exact Nat.find_spec hex j

/- English proof (translation)
Take `⟨B, hB⟩` from `hf`. Establish `hlim : Filter.Tendsto (fun i : ℕ => B * ρ ^ i) Filter.atTop (nhds 0)`. Simplify using `using (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).const_mul B`. Conclude with `squeeze_zero (fun i => by positivity) (fun i => mul_le_mul_of_nonneg_right (hB i) (pow_nonneg h0.le i)) hlim`.
-/
theorem BddSer.tendsto_weighted {K : Type*} [NormedField K] {f : PowerSeries K} (hf : BddSer f)
    {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    Filter.Tendsto (fun i => ‖PowerSeries.coeff i f‖ * ρ ^ i) Filter.atTop (nhds 0) := by
  obtain ⟨B, hB⟩ := hf
  have hlim : Filter.Tendsto (fun i : ℕ => B * ρ ^ i) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).const_mul B
  exact squeeze_zero (fun i => by positivity)
    (fun i => mul_le_mul_of_nonneg_right (hB i) (pow_nonneg h0.le i)) hlim

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hD`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Use `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)` and prove the remaining obligations.

Conclude with `hx a (Finset.mem_insert_self a s)`. Conclude with `ih fun p hp => hx p (Finset.mem_insert_of_mem hp)`.
-/
private lemma norm_finset_sum_lt_of_ultrametric {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*}
    (s : Finset ι) (x : ι → K) {D : ℝ} (hD : 0 < D) (hx : ∀ p ∈ s, ‖x p‖ < D) :
    ‖∑ p ∈ s, x p‖ < D := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hD
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · exact hx a (Finset.mem_insert_self a s)
    · exact ih fun p hp => hx p (Finset.mem_insert_of_mem hp)

/- English proof (translation)
Use `set A : ℕ → ℝ := fun k => ‖PowerSeries.coeff k f‖ * ρ ^ k with hAdef`. Use `set B : ℕ → ℝ := fun k => ‖PowerSeries.coeff k g‖ * ρ ^ k with hBdef`. Establish `hA0 : ∀ k, 0 ≤ A k` using `fun k => by positivity`. Establish `hB0 : ∀ k, 0 ≤ B k` using `fun k => by positivity`. Take `⟨i₀, hAi, hAlt⟩` from `exists_least_argmax_of_tendsto_zero A hA0 (hf.tendsto_weighted h0 h1)`.

Take `⟨j₀, hBj, hBlt⟩` from `exists_least_argmax_of_tendsto_zero B hB0 (hg.tendsto_weighted h0 h1)`. Establish `hc0 : 0 ≤ c` using `(norm_nonneg _).trans (hc 0)`. Establish `hstep : A i * B j ≤ A i₀ * B j₀` using `mul_le_mul (hAi i) (hBj j) (hB0 j) (hA0 i₀)`. Express the relevant statement in the definitionally equal form `A i * B j ≤ c`. Use `hstep.trans ?_` and prove the remaining obligations.

Break down `(mul_nonneg (hA0 i₀) (hB0 j₀)).eq_or_lt with hz | hpos` into its components or cases. Rewrite using `[← hz]`. Conclude with `hc0`. Establish `hApos : 0 < A i₀` using `lt_of_le_of_ne (hA0 i₀) fun h => by rw [← h, zero_mul] at hpos; exact lt_irrefl 0 hpos`. Establish `hBpos : 0 < B j₀` using `lt_of_le_of_ne (hB0 j₀) fun h => by rw [← h, mul_zero] at hpos; exact lt_irrefl 0 hpos`.

Use `set n := i₀ + j₀ with hn`. Establish `hρn : 0 < ρ ^ n` using `pow_pos h0 n`. Establish `hterm : ∀ p : ℕ × ℕ, p.1 + p.2 = n → A p.1 * B p.2 = ‖PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g‖ * ρ ^ n`. Introduce `p hp`. Rewrite using `[← hp, norm_mul, pow_add]`.

Simplify using `only [hAdef, hBdef]`. Expand and normalize the polynomial expressions, which then agree. Use `set D := PowerSeries.coeff i₀ f * PowerSeries.coeff j₀ g with hDdef`. Establish `hDA : A i₀ * B j₀ = ‖D‖ * ρ ^ n` using `hterm (i₀, j₀) rfl`. Establish `hDpos : 0 < ‖D‖`.

Establish `: 0 < ‖D‖ * ρ ^ n` using `hDA ▸ hpos`. Conclude with `pos_of_mul_pos_left this hρn.le`. Establish `hmem : (i₀, j₀) ∈ Finset.HasAntidiagonal.antidiagonal n` using `Finset.HasAntidiagonal.mem_antidiagonal.2 rfl`. Establish `hrest : ‖∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀), PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g‖ < ‖D‖`. Use `norm_finset_sum_lt_of_ultrametric _ _ hDpos fun p hp => ?_` and prove the remaining obligations.

Take `⟨hne, hp⟩` from `Finset.mem_erase.1 hp`. Establish `hsum : p.1 + p.2 = n` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hp`. Establish `hlt : A p.1 * B p.2 < A i₀ * B j₀`. Break down `lt_trichotomy p.1 i₀ with h | h | h` into its components or cases. Combine the equalities or inequalities in the displayed calculation.

It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Use `ext`. Conclude with `h`. Simplify using `only`.

Use linear arithmetic over natural numbers and integers. Establish `h2 : p.2 < j₀` using `by omega`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hlt` using `[hterm p hsum, hDA]`. Conclude with `lt_of_mul_lt_mul_right hlt hρn.le`.

Establish `hcoeff : PowerSeries.coeff n (f * g) = D + ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀), PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g`. Rewrite using `[PowerSeries.coeff_mul, ← Finset.add_sum_erase _ _ hmem]`. Establish `hDle : ‖D‖ ≤ ‖PowerSeries.coeff n (f * g)‖`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Establish `hD : D = PowerSeries.coeff n (f * g) + -(∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀), PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g)`. Rewrite using `[hcoeff]`. Expand and normalize the polynomial expressions, which then agree. Use `IsUltrametricDist.norm_add_le_max (PowerSeries.coeff n (f * g)) (-(∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀), PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g))` as an intermediate fact. Rewrite `this` using `[← hD, norm_neg]`.

Conclude with `lt_irrefl _ (lt_of_le_of_lt this (max_lt hcon hrest))`. Rewrite using `[hDA]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_coeff_mul_weighted_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    (f g : PowerSeries K) (c : ℝ) (hf : BddSer f) (hg : BddSer g)
    (hc : ∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ c) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) (i j : ℕ) :
    (‖PowerSeries.coeff i f‖ * ρ ^ i) * (‖PowerSeries.coeff j g‖ * ρ ^ j) ≤ c := by
  set A : ℕ → ℝ := fun k => ‖PowerSeries.coeff k f‖ * ρ ^ k with hAdef
  set B : ℕ → ℝ := fun k => ‖PowerSeries.coeff k g‖ * ρ ^ k with hBdef
  have hA0 : ∀ k, 0 ≤ A k := fun k => by positivity
  have hB0 : ∀ k, 0 ≤ B k := fun k => by positivity
  obtain ⟨i₀, hAi, hAlt⟩ := exists_least_argmax_of_tendsto_zero A hA0 (hf.tendsto_weighted h0 h1)
  obtain ⟨j₀, hBj, hBlt⟩ := exists_least_argmax_of_tendsto_zero B hB0 (hg.tendsto_weighted h0 h1)
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0)
  have hstep : A i * B j ≤ A i₀ * B j₀ := mul_le_mul (hAi i) (hBj j) (hB0 j) (hA0 i₀)
  change A i * B j ≤ c
  refine hstep.trans ?_
  rcases (mul_nonneg (hA0 i₀) (hB0 j₀)).eq_or_lt with hz | hpos
  · rw [← hz]; exact hc0
  have hApos : 0 < A i₀ := lt_of_le_of_ne (hA0 i₀) fun h => by rw [← h, zero_mul] at hpos; exact lt_irrefl 0 hpos
  have hBpos : 0 < B j₀ := lt_of_le_of_ne (hB0 j₀) fun h => by rw [← h, mul_zero] at hpos; exact lt_irrefl 0 hpos
  set n := i₀ + j₀ with hn
  have hρn : 0 < ρ ^ n := pow_pos h0 n
  have hterm : ∀ p : ℕ × ℕ, p.1 + p.2 = n →
      A p.1 * B p.2 = ‖PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g‖ * ρ ^ n := by
    intro p hp
    rw [← hp, norm_mul, pow_add]
    simp only [hAdef, hBdef]
    ring
  set D := PowerSeries.coeff i₀ f * PowerSeries.coeff j₀ g with hDdef
  have hDA : A i₀ * B j₀ = ‖D‖ * ρ ^ n := hterm (i₀, j₀) rfl
  have hDpos : 0 < ‖D‖ := by
    have : 0 < ‖D‖ * ρ ^ n := hDA ▸ hpos
    exact pos_of_mul_pos_left this hρn.le
  have hmem : (i₀, j₀) ∈ Finset.HasAntidiagonal.antidiagonal n := Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
  have hrest : ‖∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀),
      PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g‖ < ‖D‖ := by
    refine norm_finset_sum_lt_of_ultrametric _ _ hDpos fun p hp => ?_
    obtain ⟨hne, hp⟩ := Finset.mem_erase.1 hp
    have hsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    have hlt : A p.1 * B p.2 < A i₀ * B j₀ := by
      rcases lt_trichotomy p.1 i₀ with h | h | h
      · calc A p.1 * B p.2 ≤ A p.1 * B j₀ := mul_le_mul_of_nonneg_left (hBj _) (hA0 _)
          _ < A i₀ * B j₀ := mul_lt_mul_of_pos_right (hAlt _ h) hBpos
      · exfalso
        apply hne
        ext
        · exact h
        · simp only; omega
      · have h2 : p.2 < j₀ := by omega
        calc A p.1 * B p.2 ≤ A i₀ * B p.2 := mul_le_mul_of_nonneg_right (hAi _) (hB0 _)
          _ < A i₀ * B j₀ := mul_lt_mul_of_pos_left (hBlt _ h2) hApos
    rw [hterm p hsum, hDA] at hlt
    exact lt_of_mul_lt_mul_right hlt hρn.le
  have hcoeff : PowerSeries.coeff n (f * g) =
      D + ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀),
        PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g := by
    rw [PowerSeries.coeff_mul, ← Finset.add_sum_erase _ _ hmem]
  have hDle : ‖D‖ ≤ ‖PowerSeries.coeff n (f * g)‖ := by
    by_contra hcon
    push Not at hcon
    have hD : D = PowerSeries.coeff n (f * g) + -(∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀),
        PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g) := by
      rw [hcoeff]; ring
    have := IsUltrametricDist.norm_add_le_max (PowerSeries.coeff n (f * g))
      (-(∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀),
        PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g))
    rw [← hD, norm_neg] at this
    exact lt_irrefl _ (lt_of_le_of_lt this (max_lt hcon hrest))
  rw [hDA]
  calc ‖D‖ * ρ ^ n ≤ c * ρ ^ n := mul_le_mul_of_nonneg_right (hDle.trans (hc n)) hρn.le
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ h0.le h1.le) hc0
    _ = c := mul_one c

/- English proof (translation)
Establish `ht : Filter.Tendsto (fun ρ : ℝ => (‖PowerSeries.coeff i f‖ * ρ ^ i) * (‖PowerSeries.coeff j g‖ * ρ ^ j)) (nhdsWithin 1 (Set.Iio 1)) (nhds ((‖PowerSeries.coeff i f‖ * 1 ^ i) * (‖PowerSeries.coeff j g‖ * 1 ^ j)))` using `((Continuous.tendsto (by fun_prop) 1).mono_left nhdsWithin_le_nhds)`. Establish `hev : ∀ᶠ ρ in nhdsWithin (1 : ℝ) (Set.Iio 1), (‖PowerSeries.coeff i f‖ * ρ ^ i) * (‖PowerSeries.coeff j g‖ * ρ ^ j) ≤ c` using `by filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ`. Conclude with `norm_coeff_mul_weighted_le f g c hf hg hc hρ.1 hρ.2 i j`. Simplify using `using le_of_tendsto ht hev`.
-/
theorem norm_coeff_mul_norm_coeff_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    (f g : PowerSeries K) (c : ℝ) (hf : BddSer f) (hg : BddSer g)
    (hc : ∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ c) (i j : ℕ) :
    ‖PowerSeries.coeff i f‖ * ‖PowerSeries.coeff j g‖ ≤ c := by
  have ht : Filter.Tendsto
      (fun ρ : ℝ => (‖PowerSeries.coeff i f‖ * ρ ^ i) * (‖PowerSeries.coeff j g‖ * ρ ^ j))
      (nhdsWithin 1 (Set.Iio 1))
      (nhds ((‖PowerSeries.coeff i f‖ * 1 ^ i) * (‖PowerSeries.coeff j g‖ * 1 ^ j))) :=
    ((Continuous.tendsto (by fun_prop) 1).mono_left nhdsWithin_le_nhds)
  have hev : ∀ᶠ ρ in nhdsWithin (1 : ℝ) (Set.Iio 1),
      (‖PowerSeries.coeff i f‖ * ρ ^ i) * (‖PowerSeries.coeff j g‖ * ρ ^ j) ≤ c := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ
    exact norm_coeff_mul_weighted_le f g c hf hg hc hρ.1 hρ.2 i j
  simpa using le_of_tendsto ht hev

/- English proof (translation)
Introduce `p _ f g c hf hg hc i j`. Conclude with `norm_coeff_mul_norm_coeff_le f g c hf hg hc i j`.
-/
theorem sup_norm_mul_padicComplex : ∀ (p : ℕ) [Fact p.Prime] (f g : PowerSeries ℂ_[p]) (c : ℝ),
    BddSer f → BddSer g → (∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ c) →
      ∀ i j, ‖PowerSeries.coeff i f‖ * ‖PowerSeries.coeff j g‖ ≤ c := by
  intro p _ f g c hf hg hc i j
  exact norm_coeff_mul_norm_coeff_le f g c hf hg hc i j

end GlobalTheory.EvenTheta
