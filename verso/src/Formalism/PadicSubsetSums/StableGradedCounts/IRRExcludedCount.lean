import Formalism.PadicSubsetSums.StableGradedCounts.IRRBBCard
import Formalism.PadicSubsetSums.StableGradedCounts.IRRBBDivides

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Break down `S.eq_empty_or_nonempty with rfl | hne` into its components or cases. Simplify using `only [Finset.card_empty, Nat.cast_zero]`. Check the signs of the components of the expression. Use `set g0 := S.min' hne with hg0def`. Establish `hg0 : g0 ∈ S` using `S.min'_mem hne`.

Establish `hdvd : ∀ a ∈ S, g0 ≤ a ∧ M ∣ a - g0`. Introduce `a ha`. Establish `ha0 : g0 ≤ a` using `S.min'_le a ha`. Use `⟨ha0, (Nat.modEq_iff_dvd' ha0).mp ?_⟩` and prove the remaining obligations. Unfold `Nat.ModEq`.

Rewrite using `[(hS g0 hg0).2.2, (hS a ha).2.2]`. Establish `hinj : Set.InjOn (fun g => (g - g0) / M) (S : Set ℕ)`. Introduce `a ha b hb hab`. Take `⟨ha0, s, hs⟩` from `hdvd a ha`. Take `⟨hb0, t, ht⟩` from `hdvd b hb`.

Simplify using `only at hab`. Rewrite `hab` using `[hs, ht, Nat.mul_div_cancel_left _ hM, Nat.mul_div_cancel_left _ hM]`. Substitute `hab` using the available equality. Use linear arithmetic over natural numbers and integers. Establish `himg : S.image (fun g => (g - g0) / M) ⊆ Finset.range (⌊Y / M⌋₊ + 1)`.

Introduce `k hk`. Take `⟨a, ha, rfl⟩` from `Finset.mem_image.mp hk`. Rewrite using `[Finset.mem_range, Nat.lt_succ_iff]`. Apply `Nat.le_floor` to reduce the goal to its premises. Establish `ha0 : g0 ≤ a` using `(hdvd a ha).1`.

Establish `h1 : (((a - g0) / M : ℕ) : ℝ) ≤ ((a - g0 : ℕ) : ℝ) / M` using `Nat.cast_div_le`. Establish `h2 : ((a - g0 : ℕ) : ℝ) = (a : ℝ) - g0` using `Nat.cast_sub ha0`. Establish `h3 : (a : ℝ) - g0 ≤ Y` using `by linarith [(hS a ha).2.1, (hS g0 hg0).1]`. Establish `hM' : (0 : ℝ) < M` using `by exact_mod_cast hM`. Combine the equalities or inequalities in the displayed calculation.

Establish `hc : S.card ≤ ⌊Y / M⌋₊ + 1`. Rewrite using `[← Finset.card_image_of_injOn hinj]`. Simplify using `using Finset.card_le_card himg`. Establish `hfl : ((⌊Y / M⌋₊ : ℕ) : ℝ) ≤ Y / M` using `Nat.floor_le (by positivity)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_class_le (S : Finset ℕ) (Y : ℝ) (M r : ℕ) (hM : 0 < M) (hY : 0 ≤ Y)
    (hS : ∀ g ∈ S, Y ≤ (g : ℝ) ∧ (g : ℝ) ≤ 2 * Y ∧ g % M = r) :
    (S.card : ℝ) ≤ Y / M + 1 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]; positivity
  set g0 := S.min' hne with hg0def
  have hg0 : g0 ∈ S := S.min'_mem hne
  have hdvd : ∀ a ∈ S, g0 ≤ a ∧ M ∣ a - g0 := by
    intro a ha
    have ha0 : g0 ≤ a := S.min'_le a ha
    refine ⟨ha0, (Nat.modEq_iff_dvd' ha0).mp ?_⟩
    unfold Nat.ModEq
    rw [(hS g0 hg0).2.2, (hS a ha).2.2]
  have hinj : Set.InjOn (fun g => (g - g0) / M) (S : Set ℕ) := by
    intro a ha b hb hab
    obtain ⟨ha0, s, hs⟩ := hdvd a ha
    obtain ⟨hb0, t, ht⟩ := hdvd b hb
    simp only at hab
    rw [hs, ht, Nat.mul_div_cancel_left _ hM, Nat.mul_div_cancel_left _ hM] at hab
    subst hab
    omega
  have himg : S.image (fun g => (g - g0) / M) ⊆ Finset.range (⌊Y / M⌋₊ + 1) := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.le_floor
    have ha0 : g0 ≤ a := (hdvd a ha).1
    have h1 : (((a - g0) / M : ℕ) : ℝ) ≤ ((a - g0 : ℕ) : ℝ) / M := Nat.cast_div_le
    have h2 : ((a - g0 : ℕ) : ℝ) = (a : ℝ) - g0 := Nat.cast_sub ha0
    have h3 : (a : ℝ) - g0 ≤ Y := by linarith [(hS a ha).2.1, (hS g0 hg0).1]
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    calc (((a - g0) / M : ℕ) : ℝ) ≤ ((a - g0 : ℕ) : ℝ) / M := h1
      _ ≤ Y / M := by rw [h2]; exact div_le_div_of_nonneg_right h3 hM'.le
  have hc : S.card ≤ ⌊Y / M⌋₊ + 1 := by
    rw [← Finset.card_image_of_injOn hinj]
    simpa using Finset.card_le_card himg
  have hfl : ((⌊Y / M⌋₊ : ℕ) : ℝ) ≤ Y / M := Nat.floor_le (by positivity)
  calc (S.card : ℝ) ≤ ((⌊Y / M⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hc
    _ ≤ Y / M + 1 := by push_cast; linarith

/- English proof (translation)
Establish `hY0 : 0 < Y` using `by linarith`. Establish `h1 : Y ^ ((1 : ℝ) / 4) ≤ M`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `h4` using `pow_le_pow_left₀ hM.le hcon.le 4`.

Establish `h5 : (Y ^ ((1 : ℝ) / 4)) ^ 4 = Y`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hY0.le]`. Evaluate the numerical expressions. Rewrite `h4` using `[h5]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h2 : Y = Y ^ ((3 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4)`. Rewrite using `[← Real.rpow_add hY0]`. Evaluate the numerical expressions. Rewrite using `[div_le_iff₀ hM]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hY0.le _)`.
-/
theorem div_le_rpow (Y M : ℝ) (hY : 1 ≤ Y) (hM : 0 < M) (h : Y < M ^ 4) :
    Y / M ≤ Y ^ ((3 : ℝ) / 4) := by
  have hY0 : 0 < Y := by linarith
  have h1 : Y ^ ((1 : ℝ) / 4) ≤ M := by
    by_contra hcon
    push Not at hcon
    have h4 := pow_le_pow_left₀ hM.le hcon.le 4
    have h5 : (Y ^ ((1 : ℝ) / 4)) ^ 4 = Y := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
      norm_num
    rw [h5] at h4
    linarith
  have h2 : Y = Y ^ ((3 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hY0]; norm_num
  rw [div_le_iff₀ hM]
  calc Y = Y ^ ((3 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4) := h2
    _ ≤ Y ^ ((3 : ℝ) / 4) * M := by
        exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hY0.le _)

/- English proof (translation)
Use `set M := l ^ j with hMdef`. Establish `hM : 0 < M` using `pow_pos hl.pos j`. Establish `hM' : (0 : ℝ) < (M : ℝ)` using `by exact_mod_cast hM`. Use `set R := (Finset.range M).filter (fun x => x ^ d ≡ 1 [MOD M]) with hR`. Establish `hRcard : R.card ≤ 2 * d` using `Formalism.GaloisIrreducibility.residuesLe l j d hl hd`.

Establish `hmaps : ∀ g ∈ S, g % M ∈ R`. Introduce `g hg`. Take `⟨h1, _, h3⟩` from `hS g hg`. Establish `hg1 : 1 ≤ g`. Establish `: (1 : ℝ) ≤ (g : ℝ)` using `hY.trans h1`.

Conclude with `this` after adjusting the coercions. Establish `hgd : 1 ≤ g ^ d` using `Nat.one_le_pow _ _ hg1`. Establish `hmod : 1 ≡ g ^ d [MOD M]` using `(Nat.modEq_iff_dvd' hgd).mpr h3`. Rewrite using `[hR, Finset.mem_filter, Finset.mem_range]`. Use `⟨Nat.mod_lt _ hM, ?_⟩` and prove the remaining obligations.

Conclude with `((Nat.mod_modEq g M).pow d).trans hmod.symm`. Establish `hcard : S.card = ∑ r ∈ R, (S.filter (fun g => g % M = r)).card` using `Finset.card_eq_sum_card_fiberwise hmaps`. Establish `hfib : ∀ r ∈ R, ((S.filter (fun g => g % M = r)).card : ℝ) ≤ Y ^ ((3 : ℝ) / 4) + 1`. Introduce `r _`. Establish `h1` using `card_class_le (S.filter (fun g => g % M = r)) Y M r hM (by linarith) (by`.

Introduce `g hg`. Take `⟨hgS, hgr⟩` from `Finset.mem_filter.mp hg`. Conclude with `⟨(hS g hgS).1, (hS g hgS).2.1, hgr⟩)`. Establish `h2 : Y / (M : ℝ) ≤ Y ^ ((3 : ℝ) / 4)`. Apply `div_le_rpow Y M hY hM'` to reduce the goal to its premises.

Establish `: ((M : ℝ)) ^ 4 = (l : ℝ) ^ (4 * j)`. Rewrite using `[hMdef]`. Use `push_cast`. Rewrite using `[← pow_mul, mul_comm]`. Rewrite using `[this]`.

Conclude with `hj`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc0 : (0 : ℝ) ≤ Y ^ ((3 : ℝ) / 4) + 1`. Use `Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) ((3 : ℝ) / 4)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hcard]`. Use `push_cast`. Both sides reduce to the same expression. Use `_ ≤ ∑ _r ∈ R, (Y ^ ((3 : ℝ) / 4) + 1) := Finset.sum_le_sum hfib`.

Use `_ = (R.card : ℝ) * (Y ^ ((3 : ℝ) / 4) + 1) := by rw [Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ 2 * d * (Y ^ ((3 : ℝ) / 4) + 1) := by`. Apply `mul_le_mul_of_nonneg_right _ hc0` to reduce the goal to its premises. Conclude with `hRcard` after adjusting the coercions.
-/
theorem card_pow_class_le (S : Finset ℕ) (Y : ℝ) (l j d : ℕ) (hl : l.Prime) (hd : 1 ≤ d)
    (hY : 1 ≤ Y) (hj : Y < (l : ℝ) ^ (4 * j))
    (hS : ∀ g ∈ S, Y ≤ (g : ℝ) ∧ (g : ℝ) ≤ 2 * Y ∧ l ^ j ∣ g ^ d - 1) :
    (S.card : ℝ) ≤ 2 * d * (Y ^ ((3 : ℝ) / 4) + 1) := by
  classical
  set M := l ^ j with hMdef
  have hM : 0 < M := pow_pos hl.pos j
  have hM' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  set R := (Finset.range M).filter (fun x => x ^ d ≡ 1 [MOD M]) with hR
  have hRcard : R.card ≤ 2 * d := Formalism.GaloisIrreducibility.residuesLe l j d hl hd
  have hmaps : ∀ g ∈ S, g % M ∈ R := by
    intro g hg
    obtain ⟨h1, _, h3⟩ := hS g hg
    have hg1 : 1 ≤ g := by
      have : (1 : ℝ) ≤ (g : ℝ) := hY.trans h1
      exact_mod_cast this
    have hgd : 1 ≤ g ^ d := Nat.one_le_pow _ _ hg1
    have hmod : 1 ≡ g ^ d [MOD M] := (Nat.modEq_iff_dvd' hgd).mpr h3
    rw [hR, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hM, ?_⟩
    exact ((Nat.mod_modEq g M).pow d).trans hmod.symm
  have hcard : S.card = ∑ r ∈ R, (S.filter (fun g => g % M = r)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ r ∈ R, ((S.filter (fun g => g % M = r)).card : ℝ) ≤ Y ^ ((3 : ℝ) / 4) + 1 := by
    intro r _
    have h1 := card_class_le (S.filter (fun g => g % M = r)) Y M r hM (by linarith) (by
      intro g hg
      obtain ⟨hgS, hgr⟩ := Finset.mem_filter.mp hg
      exact ⟨(hS g hgS).1, (hS g hgS).2.1, hgr⟩)
    have h2 : Y / (M : ℝ) ≤ Y ^ ((3 : ℝ) / 4) := by
      apply div_le_rpow Y M hY hM'
      have : ((M : ℝ)) ^ 4 = (l : ℝ) ^ (4 * j) := by
        rw [hMdef]; push_cast; rw [← pow_mul, mul_comm]
      rw [this]; exact hj
    linarith
  have hc0 : (0 : ℝ) ≤ Y ^ ((3 : ℝ) / 4) + 1 := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) ((3 : ℝ) / 4)
    linarith
  calc (S.card : ℝ) = ∑ r ∈ R, ((S.filter (fun g => g % M = r)).card : ℝ) := by
        rw [hcard]; push_cast; rfl
    _ ≤ ∑ _r ∈ R, (Y ^ ((3 : ℝ) / 4) + 1) := Finset.sum_le_sum hfib
    _ = (R.card : ℝ) * (Y ^ ((3 : ℝ) / 4) + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * d * (Y ^ ((3 : ℝ) / 4) + 1) := by
        apply mul_le_mul_of_nonneg_right _ hc0
        exact_mod_cast hRcard

/- English proof (translation)
Introduce `N g₁ Y S hN hY hg₁ hS`. Use `set c : ℝ := Y ^ ((3 : ℝ) / 4) + 1 with hc`. Establish `hc0 : (0 : ℝ) ≤ c`. Use `Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) ((3 : ℝ) / 4)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hcover : S ⊆ (BB g₁ N).biUnion (fun l => S.filter (fun g => l ∈ BB g N))`. Introduce `g hg`. Take `⟨_, _, _, hnd⟩` from `hS g hg`. Rewrite `hnd` using `[Finset.not_disjoint_iff]`. Take `⟨l, h1, h2⟩` from `hnd`.

Conclude with `Finset.mem_biUnion.mpr ⟨l, h1, Finset.mem_filter.mpr ⟨hg, h2⟩⟩`. Establish `hper : ∀ l ∈ BB g₁ N, ((S.filter (fun g => l ∈ BB g N)).card : ℝ) ≤ 1 + 2 * (N : ℝ) ^ 2 * c`. Introduce `l hlB`. Establish `hl : l.Prime`. Simplify using `only [BB, Finset.mem_insert, Finset.mem_filter] at hlB`.

Break down `hlB with rfl | ⟨_, h2, _⟩` into its components or cases. Conclude with `hg₁`. Conclude with `h2`. Establish `hex : ∃ j : ℕ, Y < (l : ℝ) ^ (4 * j)`. Establish `h1 : (1 : ℝ) < (l : ℝ) ^ 4`.

Establish `: (1 : ℝ) < (l : ℝ)` using `by exact_mod_cast hl.one_lt`. Conclude with `one_lt_pow₀ this (by norm_num)`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt Y h1`. Conclude with `⟨n, by rw [pow_mul]; exact hn⟩`. Use `set j := Nat.find hex with hjdef`.

Establish `hj : Y < (l : ℝ) ^ (4 * j)` using `Nat.find_spec hex`. Establish `hmin : ∀ i < j, (l : ℝ) ^ (4 * i) ≤ Y` using `fun i hi => not_lt.mp (Nat.find_min hex hi)`. Use `set F : ℕ → Finset ℕ := fun d => S.filter (fun g => l ^ j ∣ g ^ d - 1) with hF`. Establish `hsub : S.filter (fun g => l ∈ BB g N) ⊆ insert l ((Finset.Icc 1 N).biUnion F)`. Introduce `g hg`.

Take `⟨hgS, hlg⟩` from `Finset.mem_filter.mp hg`. Take `⟨hgp, hYg, _, _⟩` from `hS g hgS`. Simplify using `only [BB, Finset.mem_insert, Finset.mem_filter] at hlg`. Break down `hlg with rfl | ⟨_, _, d, hd, h3⟩` into its components or cases. Conclude with `Finset.mem_insert_self _ _`.

Use `Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨d, hd, ?_⟩)` and prove the remaining obligations. Rewrite using `[hF]`. Use `Finset.mem_filter.mpr ⟨hgS, ?_⟩` and prove the remaining obligations. Conclude with `bad_primes_divides l g d j Y hl (Finset.mem_Icc.mp hd).1 hgp.two_le hYg h3 hj hmin`. Establish `hFd : ∀ d ∈ Finset.Icc 1 N, ((F d).card : ℝ) ≤ 2 * N * c`.

Introduce `d hd`. Take `⟨hd1, hdN⟩` from `Finset.mem_Icc.mp hd`. Establish `h1` using `card_pow_class_le (F d) Y l j d hl hd1 hY hj (by`. Introduce `g hg`. Take `⟨hgS, hdv⟩` from `Finset.mem_filter.mp hg`.

Conclude with `⟨(hS g hgS).2.1, (hS g hgS).2.2.1, hdv⟩)`. Establish `hdN' : (d : ℝ) ≤ (N : ℝ)` using `by exact_mod_cast hdN`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ hc0` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1 : (S.filter (fun g => l ∈ BB g N)).card ≤ (∑ d ∈ Finset.Icc 1 N, (F d).card) + 1`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ((S.filter (fun g => l ∈ BB g N)).card : ℝ) ≤ (∑ d ∈ Finset.Icc 1 N, ((F d).card : ℝ)) + 1` using `by exact_mod_cast h1`. Establish `h3 : (∑ d ∈ Finset.Icc 1 N, ((F d).card : ℝ)) ≤ ∑ _d ∈ Finset.Icc 1 N, 2 * (N : ℝ) * c` using `Finset.sum_le_sum hFd`. Establish `h4 : (∑ _d ∈ Finset.Icc 1 N, 2 * (N : ℝ) * c) = 2 * (N : ℝ) ^ 2 * c`.

Rewrite using `[Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]`. Simplify using `only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB0 : (0 : ℝ) ≤ 1 + 2 * (N : ℝ) ^ 2 * c` using `by positivity`.

Establish `hBB : ((BB g₁ N).card : ℝ) ≤ 3 * N + 1`. Conclude with `bad_primes_cardinality g₁ N hg₁.two_le` after adjusting the coercions. Establish `h1 : S.card ≤ ∑ l ∈ BB g₁ N, (S.filter (fun g => l ∈ BB g N)).card` using `(Finset.card_le_card hcover).trans Finset.card_biUnion_le`. Establish `h2 : (S.card : ℝ) ≤ ∑ l ∈ BB g₁ N, ((S.filter (fun g => l ∈ BB g N)).card : ℝ)`. Conclude with `h1` after adjusting the coercions.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * c) := mul_le_mul_of_nonneg_right hBB hB0`.
-/
theorem excluded_count_bound : ExcludedCount := by
  classical
  intro N g₁ Y S hN hY hg₁ hS
  set c : ℝ := Y ^ ((3 : ℝ) / 4) + 1 with hc
  have hc0 : (0 : ℝ) ≤ c := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) ((3 : ℝ) / 4)
    linarith
  have hcover : S ⊆ (BB g₁ N).biUnion (fun l => S.filter (fun g => l ∈ BB g N)) := by
    intro g hg
    obtain ⟨_, _, _, hnd⟩ := hS g hg
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨l, h1, h2⟩ := hnd
    exact Finset.mem_biUnion.mpr ⟨l, h1, Finset.mem_filter.mpr ⟨hg, h2⟩⟩
  have hper : ∀ l ∈ BB g₁ N,
      ((S.filter (fun g => l ∈ BB g N)).card : ℝ) ≤ 1 + 2 * (N : ℝ) ^ 2 * c := by
    intro l hlB
    have hl : l.Prime := by
      simp only [BB, Finset.mem_insert, Finset.mem_filter] at hlB
      rcases hlB with rfl | ⟨_, h2, _⟩
      · exact hg₁
      · exact h2
    have hex : ∃ j : ℕ, Y < (l : ℝ) ^ (4 * j) := by
      have h1 : (1 : ℝ) < (l : ℝ) ^ 4 := by
        have : (1 : ℝ) < (l : ℝ) := by exact_mod_cast hl.one_lt
        exact one_lt_pow₀ this (by norm_num)
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt Y h1
      exact ⟨n, by rw [pow_mul]; exact hn⟩
    set j := Nat.find hex with hjdef
    have hj : Y < (l : ℝ) ^ (4 * j) := Nat.find_spec hex
    have hmin : ∀ i < j, (l : ℝ) ^ (4 * i) ≤ Y := fun i hi => not_lt.mp (Nat.find_min hex hi)
    set F : ℕ → Finset ℕ := fun d => S.filter (fun g => l ^ j ∣ g ^ d - 1) with hF
    have hsub : S.filter (fun g => l ∈ BB g N) ⊆ insert l ((Finset.Icc 1 N).biUnion F) := by
      intro g hg
      obtain ⟨hgS, hlg⟩ := Finset.mem_filter.mp hg
      obtain ⟨hgp, hYg, _, _⟩ := hS g hgS
      simp only [BB, Finset.mem_insert, Finset.mem_filter] at hlg
      rcases hlg with rfl | ⟨_, _, d, hd, h3⟩
      · exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨d, hd, ?_⟩)
        rw [hF]
        refine Finset.mem_filter.mpr ⟨hgS, ?_⟩
        exact bad_primes_divides l g d j Y hl (Finset.mem_Icc.mp hd).1 hgp.two_le hYg h3 hj hmin
    have hFd : ∀ d ∈ Finset.Icc 1 N, ((F d).card : ℝ) ≤ 2 * N * c := by
      intro d hd
      obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
      have h1 := card_pow_class_le (F d) Y l j d hl hd1 hY hj (by
        intro g hg
        obtain ⟨hgS, hdv⟩ := Finset.mem_filter.mp hg
        exact ⟨(hS g hgS).2.1, (hS g hgS).2.2.1, hdv⟩)
      have hdN' : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdN
      calc ((F d).card : ℝ) ≤ 2 * d * c := h1
        _ ≤ 2 * N * c := by
            apply mul_le_mul_of_nonneg_right _ hc0
            linarith
    have h1 : (S.filter (fun g => l ∈ BB g N)).card ≤
        (∑ d ∈ Finset.Icc 1 N, (F d).card) + 1 :=
      calc (S.filter (fun g => l ∈ BB g N)).card
          ≤ (insert l ((Finset.Icc 1 N).biUnion F)).card := Finset.card_le_card hsub
        _ ≤ ((Finset.Icc 1 N).biUnion F).card + 1 := Finset.card_insert_le _ _
        _ ≤ (∑ d ∈ Finset.Icc 1 N, (F d).card) + 1 :=
            Nat.add_le_add_right Finset.card_biUnion_le 1
    have h2 : ((S.filter (fun g => l ∈ BB g N)).card : ℝ) ≤
        (∑ d ∈ Finset.Icc 1 N, ((F d).card : ℝ)) + 1 := by exact_mod_cast h1
    have h3 : (∑ d ∈ Finset.Icc 1 N, ((F d).card : ℝ)) ≤ ∑ _d ∈ Finset.Icc 1 N, 2 * (N : ℝ) * c :=
      Finset.sum_le_sum hFd
    have h4 : (∑ _d ∈ Finset.Icc 1 N, 2 * (N : ℝ) * c) = 2 * (N : ℝ) ^ 2 * c := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      simp only [Nat.add_sub_cancel]
      ring
    linarith
  have hB0 : (0 : ℝ) ≤ 1 + 2 * (N : ℝ) ^ 2 * c := by positivity
  have hBB : ((BB g₁ N).card : ℝ) ≤ 3 * N + 1 := by
    exact_mod_cast bad_primes_cardinality g₁ N hg₁.two_le
  have h1 : S.card ≤ ∑ l ∈ BB g₁ N, (S.filter (fun g => l ∈ BB g N)).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have h2 : (S.card : ℝ) ≤ ∑ l ∈ BB g₁ N, ((S.filter (fun g => l ∈ BB g N)).card : ℝ) := by
    exact_mod_cast h1
  calc (S.card : ℝ) ≤ ∑ l ∈ BB g₁ N, ((S.filter (fun g => l ∈ BB g N)).card : ℝ) := h2
    _ ≤ ∑ _l ∈ BB g₁ N, (1 + 2 * (N : ℝ) ^ 2 * c) := Finset.sum_le_sum hper
    _ = ((BB g₁ N).card : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * c) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * c) := mul_le_mul_of_nonneg_right hBB hB0

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
