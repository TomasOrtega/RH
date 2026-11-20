import Mathlib
import Formalism.PeriodIntegrals.PrimesDyadicRS

noncomputable section

namespace PI.SqfPrimeFactor.W

open Finset

/- English proof (translation)
Establish `h2` using `Real.log_two_lt_d9`. Establish `h128 : Real.log 128 = 7 * Real.log 2`. Rewrite using `[show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num`. Establish `hq : Real.log 100 = Real.log 128 - Real.log (128 / 100)`. Rewrite using `[Real.log_div (by norm_num) (by norm_num)]; ring`.

Establish `hl : 1 - (128 / 100 : ℝ)⁻¹ ≤ Real.log (128 / 100)` using `Real.one_sub_inv_le_log_of_pos (by norm_num)`. Evaluate the numerical expressions using `at hl h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma ana_log : Real.log 100 < 4.64 := by
  have h2 := Real.log_two_lt_d9
  have h128 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
  have hq : Real.log 100 = Real.log 128 - Real.log (128 / 100) := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hl : 1 - (128 / 100 : ℝ)⁻¹ ≤ Real.log (128 / 100) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  norm_num at hl h2
  linarith

/- English proof (translation)
Establish `he : Real.exp 1 ≤ 100` using `by have := Real.exp_one_lt_d9; linarith`. Establish `h` using `Real.log_div_self_antitoneOn (Set.mem_Ici.2 he) (Set.mem_Ici.2 (he.trans hx)) hx`. Establish `hx0 : (0 : ℝ) < x` using `by linarith`. Establish `h100` using `ana_log`. Simplify using `only at h`.

Rewrite `h` using `[div_le_div_iff₀ hx0 (by norm_num)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma ana_log_le (x : ℝ) (hx : 100 ≤ x) : Real.log x ≤ 0.0464 * x := by
  have he : Real.exp 1 ≤ 100 := by have := Real.exp_one_lt_d9; linarith
  have h := Real.log_div_self_antitoneOn (Set.mem_Ici.2 he) (Set.mem_Ici.2 (he.trans hx)) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have h100 := ana_log
  simp only at h
  rw [div_le_div_iff₀ hx0 (by norm_num)] at h
  nlinarith

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨e, he, hev, he4⟩ : ∃ e ∈ ({r - 2, r - 1, r} : Finset ℕ), Even e ∧ 4 ≤ e := by`. Break down `Nat.even_or_odd r with h | h` into its components or cases. Conclude with `⟨r, by simp, h, by omega⟩`. Use `⟨r - 1, by simp, ?_, by omega⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `h`.

Conclude with `⟨k, by omega⟩`. Establish `hsub : ({r - 2, r - 1, r} : Finset ℕ).filter Nat.Prime ⊆ ({r - 2, r - 1, r} : Finset ℕ).erase e`. Introduce `x hx`. Rewrite `hx` using `[mem_filter]`. Rewrite using `[mem_erase]`.

Use `⟨?_, hx.1⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Use `hx.2.eq_one_or_self_of_dvd 2 (even_iff_two_dvd.1 hev)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation.
-/
lemma ana_three (r : ℕ) (hr : 100 ≤ r) :
    (({r - 2, r - 1, r} : Finset ℕ).filter Nat.Prime).card ≤ 2 := by
  obtain ⟨e, he, hev, he4⟩ : ∃ e ∈ ({r - 2, r - 1, r} : Finset ℕ), Even e ∧ 4 ≤ e := by
    rcases Nat.even_or_odd r with h | h
    · exact ⟨r, by simp, h, by omega⟩
    · refine ⟨r - 1, by simp, ?_, by omega⟩
      obtain ⟨k, hk⟩ := h
      exact ⟨k, by omega⟩
  have hsub : ({r - 2, r - 1, r} : Finset ℕ).filter Nat.Prime ⊆
      ({r - 2, r - 1, r} : Finset ℕ).erase e := by
    intro x hx
    rw [mem_filter] at hx
    rw [mem_erase]
    refine ⟨?_, hx.1⟩
    rintro rfl
    have := hx.2.eq_one_or_self_of_dvd 2 (even_iff_two_dvd.1 hev)
    omega
  calc _ ≤ _ := card_le_card hsub
    _ = _ := card_erase_of_mem he
    _ ≤ 3 - 1 := Nat.sub_le_sub_right card_le_three 1

/- English proof (translation)
Simplify using `only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]`. Establish `hsub : (range (r + 1)).filter Nat.Prime ⊆ ((range (r / 2 + 1)).filter Nat.Prime ∪ S) ∪ ({r - 2, r - 1, r} : Finset ℕ).filter Nat.Prime`. Introduce `p hp`. Rewrite `hp` using `[mem_filter, mem_range]`. Take `⟨hp1, hpp⟩` from `hp`.

Rewrite using `[mem_union, mem_union, mem_filter, mem_filter, mem_range, hS]`. Distinguish the cases in `h1 : p < r / 2 + 1`. Conclude with `Or.inl (Or.inl ⟨h1, hpp⟩)`. Distinguish the cases in `h2 : p + 3 ≤ r`. Conclude with `Or.inl (Or.inr ⟨hpp, by omega, h2⟩)`.

Use `Or.inr ⟨?_, hpp⟩` and prove the remaining obligations. Simplify using `only [mem_insert, mem_singleton]`. Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation.
-/
lemma ana_pi (r : ℕ) (hr : 100 ≤ r) (S : Finset ℕ)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ r < 2 * p ∧ p + 3 ≤ r) :
    Nat.primeCounting r ≤ Nat.primeCounting (r / 2) + S.card + 2 := by
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hsub : (range (r + 1)).filter Nat.Prime ⊆
      ((range (r / 2 + 1)).filter Nat.Prime ∪ S) ∪
        ({r - 2, r - 1, r} : Finset ℕ).filter Nat.Prime := by
    intro p hp
    rw [mem_filter, mem_range] at hp
    obtain ⟨hp1, hpp⟩ := hp
    rw [mem_union, mem_union, mem_filter, mem_filter, mem_range, hS]
    by_cases h1 : p < r / 2 + 1
    · exact Or.inl (Or.inl ⟨h1, hpp⟩)
    by_cases h2 : p + 3 ≤ r
    · exact Or.inl (Or.inr ⟨hpp, by omega, h2⟩)
    refine Or.inr ⟨?_, hpp⟩
    simp only [mem_insert, mem_singleton]
    omega
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := Nat.add_le_add (card_union_le _ _) (ana_three r hr)

/- English proof (translation)
Establish `hrR : (100 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hR` using `hRS ((r : ℝ) / 2) (by linarith)`. Establish `hf1 : ⌊2 * ((r : ℝ) / 2)⌋₊ = r`. Rewrite using `[mul_div_cancel₀ _ two_ne_zero]`. Conclude with `Nat.floor_natCast r`.

Establish `hf2 : ⌊(r : ℝ) / 2⌋₊ = r / 2`. Rewrite using `[Nat.floor_div_ofNat, Nat.floor_natCast]`. Rewrite `hR` using `[hf1, hf2]`. Establish `hcnt : (Nat.primeCounting r : ℝ) ≤ Nat.primeCounting (r / 2) + S.card + 2`. Conclude with `ana_pi r hr S hS` after adjusting the coercions.

Use `set L := Real.log r with hL`. Establish `hL2 : Real.log ((r : ℝ) / 2) < L` using `Real.log_lt_log (by linarith) (by linarith)`. Establish `hL2p : 0 < Real.log ((r : ℝ) / 2)` using `Real.log_pos (by linarith)`. Establish `hLp : 0 < L` using `by linarith`. Establish `hLle : L ≤ 0.0464 * r` using `ana_log_le r hrR`.

Establish `h3 : 3 * ((r : ℝ) / 2) / (5 * L) ≤ 3 * ((r : ℝ) / 2) / (5 * Real.log ((r : ℝ) / 2))` using `div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)`. Establish `hc0 : 3 * ((r : ℝ) / 2) / (5 * L) < S.card + 2` using `by linarith`. Rewrite `hc0` using `[div_lt_iff₀ (by positivity)]`. Establish `hcl : (r : ℝ) ≤ S.card * (5 * L) * (4095 / 4096)` using `by nlinarith`. Establish `hg0 : (4096 : ℝ) ≤ g` using `by exact_mod_cast hg`.

Establish `hgpos : (0 : ℝ) < g` using `by linarith`. Establish `hrpos : (0 : ℝ) < r` using `by linarith`. Establish `hterm : ∀ p ∈ S, (g : ℝ) ^ r * (4095 / 4096) / r ≤ ((g : ℝ) ^ p - g) / p * (g : ℝ) ^ (r - p)`. Introduce `p hp`. Take `⟨hpp, h2, h3⟩` from `(hS p).1 hp`.

Establish `hp2 : 2 ≤ p` using `hpp.two_le`. Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast hpp.pos`. Establish `hpr : (p : ℝ) ≤ r` using `by exact_mod_cast (show p ≤ r by omega)`. Establish `hsplit : (g : ℝ) ^ r = (g : ℝ) ^ p * (g : ℝ) ^ (r - p)`. Rewrite using `[← pow_add]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `hgp2 : (g : ℝ) ^ 2 ≤ (g : ℝ) ^ p` using `pow_le_pow_right₀ (by linarith) hp2`. Establish `hgp : (g : ℝ) * 4096 ≤ (g : ℝ) ^ p` using `by nlinarith`. Establish `hq : (0 : ℝ) ≤ (g : ℝ) ^ (r - p)` using `by positivity`.

Establish `hgpp : (0 : ℝ) < (g : ℝ) ^ p` using `by positivity`. Rewrite using `[hsplit]`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ hq` to reduce the goal to its premises. Apply `div_le_div_of_nonneg_right _ hp0.le` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum : S.card * ((g : ℝ) ^ r * (4095 / 4096) / r) ≤ ∑ p ∈ S, ((g : ℝ) ^ p - g) / p * (g : ℝ) ^ (r - p)`. Use `Finset.sum_le_sum hterm` as an intermediate fact. Rewrite `this` using `[Finset.sum_const, nsmul_eq_mul]`. Conclude with `this`.

Establish `hG : (0 : ℝ) < (g : ℝ) ^ r` using `by positivity`. Establish `hkey : (g : ℝ) ^ r / (5 * L) ≤ S.card * ((g : ℝ) ^ r * (4095 / 4096) / r)`. Rewrite using `[div_le_iff₀ (by positivity)]`. Establish `: S.card * ((g : ℝ) ^ r * (4095 / 4096) / r) * (5 * L) = (g : ℝ) ^ r * (S.card * (5 * L) * (4095 / 4096)) / r` using `by ring`. Rewrite using `[this, le_div_iff₀ hrpos]`.

Conclude with `mul_le_mul_of_nonneg_left hcl hG.le`. Establish `: (1 - 1 / (5 * L)) * (g : ℝ) ^ r = (g : ℝ) ^ r - (g : ℝ) ^ r / (5 * L)` using `by ring`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ana_main (hRS : PI.PrimesDyadicRS.Claim) (g r : ℕ) (hr : 100 ≤ r) (hg : 2 ^ 12 ≤ g)
    (S : Finset ℕ) (hS : ∀ p, p ∈ S ↔ p.Prime ∧ r < 2 * p ∧ p + 3 ≤ r) :
    (g : ℝ) ^ r - ∑ p ∈ S, ((g : ℝ) ^ p - g) / p * (g : ℝ) ^ (r - p) ≤
      (1 - 1 / (5 * Real.log r)) * (g : ℝ) ^ r := by
  have hrR : (100 : ℝ) ≤ r := by exact_mod_cast hr
  have hR := hRS ((r : ℝ) / 2) (by linarith)
  have hf1 : ⌊2 * ((r : ℝ) / 2)⌋₊ = r := by
    rw [mul_div_cancel₀ _ two_ne_zero]; exact Nat.floor_natCast r
  have hf2 : ⌊(r : ℝ) / 2⌋₊ = r / 2 := by
    rw [Nat.floor_div_ofNat, Nat.floor_natCast]
  rw [hf1, hf2] at hR
  have hcnt : (Nat.primeCounting r : ℝ) ≤ Nat.primeCounting (r / 2) + S.card + 2 := by
    exact_mod_cast ana_pi r hr S hS
  set L := Real.log r with hL
  have hL2 : Real.log ((r : ℝ) / 2) < L := Real.log_lt_log (by linarith) (by linarith)
  have hL2p : 0 < Real.log ((r : ℝ) / 2) := Real.log_pos (by linarith)
  have hLp : 0 < L := by linarith
  have hLle : L ≤ 0.0464 * r := ana_log_le r hrR

  have h3 : 3 * ((r : ℝ) / 2) / (5 * L) ≤ 3 * ((r : ℝ) / 2) / (5 * Real.log ((r : ℝ) / 2)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hc0 : 3 * ((r : ℝ) / 2) / (5 * L) < S.card + 2 := by linarith
  rw [div_lt_iff₀ (by positivity)] at hc0
  have hcl : (r : ℝ) ≤ S.card * (5 * L) * (4095 / 4096) := by nlinarith

  have hg0 : (4096 : ℝ) ≤ g := by exact_mod_cast hg
  have hgpos : (0 : ℝ) < g := by linarith
  have hrpos : (0 : ℝ) < r := by linarith
  have hterm : ∀ p ∈ S, (g : ℝ) ^ r * (4095 / 4096) / r ≤
      ((g : ℝ) ^ p - g) / p * (g : ℝ) ^ (r - p) := by
    intro p hp
    obtain ⟨hpp, h2, h3⟩ := (hS p).1 hp
    have hp2 : 2 ≤ p := hpp.two_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hpr : (p : ℝ) ≤ r := by exact_mod_cast (show p ≤ r by omega)
    have hsplit : (g : ℝ) ^ r = (g : ℝ) ^ p * (g : ℝ) ^ (r - p) := by
      rw [← pow_add]; congr 1; omega
    have hgp2 : (g : ℝ) ^ 2 ≤ (g : ℝ) ^ p := pow_le_pow_right₀ (by linarith) hp2
    have hgp : (g : ℝ) * 4096 ≤ (g : ℝ) ^ p := by nlinarith
    have hq : (0 : ℝ) ≤ (g : ℝ) ^ (r - p) := by positivity
    have hgpp : (0 : ℝ) < (g : ℝ) ^ p := by positivity
    rw [hsplit]
    calc (g : ℝ) ^ p * (g : ℝ) ^ (r - p) * (4095 / 4096) / r
        ≤ (g : ℝ) ^ p * (g : ℝ) ^ (r - p) * (4095 / 4096) / p :=
          div_le_div_of_nonneg_left (by positivity) hp0 hpr
      _ = ((g : ℝ) ^ p * (4095 / 4096)) / p * (g : ℝ) ^ (r - p) := by ring
      _ ≤ ((g : ℝ) ^ p - g) / p * (g : ℝ) ^ (r - p) := by
          apply mul_le_mul_of_nonneg_right _ hq
          apply div_le_div_of_nonneg_right _ hp0.le
          linarith
  have hsum : S.card * ((g : ℝ) ^ r * (4095 / 4096) / r) ≤
      ∑ p ∈ S, ((g : ℝ) ^ p - g) / p * (g : ℝ) ^ (r - p) := by
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have hG : (0 : ℝ) < (g : ℝ) ^ r := by positivity
  have hkey : (g : ℝ) ^ r / (5 * L) ≤ S.card * ((g : ℝ) ^ r * (4095 / 4096) / r) := by
    rw [div_le_iff₀ (by positivity)]
    have : S.card * ((g : ℝ) ^ r * (4095 / 4096) / r) * (5 * L) =
        (g : ℝ) ^ r * (S.card * (5 * L) * (4095 / 4096)) / r := by ring
    rw [this, le_div_iff₀ hrpos]
    exact mul_le_mul_of_nonneg_left hcl hG.le
  have : (1 - 1 / (5 * L)) * (g : ℝ) ^ r = (g : ℝ) ^ r - (g : ℝ) ^ r / (5 * L) := by ring
  rw [this]
  linarith

end PI.SqfPrimeFactor.W
