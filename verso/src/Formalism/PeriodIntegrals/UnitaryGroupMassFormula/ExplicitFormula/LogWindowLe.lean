import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.NormSubCtrSq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.ExplicitFormulaFromGluing

noncomputable section

namespace PI.EF

open Complex Metric Filter Topology Set DirichletCharacter

variable {N : ℕ} [NeZero N]

/- English proof (translation)
Establish `hN : (1 : ℝ) ≤ N` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)`. Establish `ht` using `abs_nonneg t`. Establish `hu0` using `abs_nonneg u`. Rewrite using `[LL.eq_1]`. Establish `hpos : 0 < (N : ℝ) * (|u| + 2)` using `by positivity`.

Establish `h1 : (N : ℝ) * (|u| + 2) ≤ N * (|t| + 4)` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`. Establish `h2 : |t| + 4 ≤ (|t| + 2) ^ 2` using `by nlinarith`. Establish `h3 : (N : ℝ) * (|t| + 4) ≤ (N : ℝ) ^ 2 * (|t| + 2) ^ 2`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
lemma log_window_le (N : ℕ) [NeZero N] {t u : ℝ} (hu : |u| ≤ |t| + 2) :
    Real.log (N * (|u| + 2)) ≤ 2 * LL N t := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have ht := abs_nonneg t
  have hu0 := abs_nonneg u
  rw [LL.eq_1]
  have hpos : 0 < (N : ℝ) * (|u| + 2) := by positivity
  have h1 : (N : ℝ) * (|u| + 2) ≤ N * (|t| + 4) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : |t| + 4 ≤ (|t| + 2) ^ 2 := by nlinarith
  have h3 : (N : ℝ) * (|t| + 4) ≤ (N : ℝ) ^ 2 * (|t| + 2) ^ 2 := by
    calc (N : ℝ) * (|t| + 4) ≤ (N : ℝ) ^ 2 * (|t| + 4) :=
          mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
      _ ≤ (N : ℝ) ^ 2 * (|t| + 2) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
  calc Real.log (N * (|u| + 2)) ≤ Real.log ((N * (|t| + 2)) ^ 2) :=
        Real.log_le_log hpos (by rw [mul_pow]; linarith)
    _ = 2 * Real.log (N * (|t| + 2)) := by rw [Real.log_pow]; norm_num

/- English proof (translation)
Rewrite using `[Metric.mem_closedBall, ctr.eq_1, Complex.dist_eq]`. Establish `h : s - (2 + (s.im : ℂ) * Complex.I) = ((s.re - 2 : ℝ) : ℂ)`. Apply the tactic sequence `apply Complex.ext <;> simp`. Rewrite using `[h, Complex.norm_real, Real.norm_eq_abs, abs_le]`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem mem_ball_ctr (s : ℂ) (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3) :
    s ∈ closedBall (ctr s.im) (5 / 2) := by
  rw [Metric.mem_closedBall, ctr.eq_1, Complex.dist_eq]
  have h : s - (2 + (s.im : ℂ) * Complex.I) = ((s.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/- English proof (translation)
Establish `hsub : ZerosNear χ t ⊆ DZ χ t`. Introduce `ρ hρ`. Rewrite `hρ` using `[ZerosNear.eq_1]`. Take `⟨h0, h1, him, hL⟩` from `hρ`. Rewrite using `[DZ.eq_1, Set.mem_setOf_eq]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_closedBall, ctr.eq_1, Complex.dist_eq]`. Establish `hre : (ρ - (2 + (t : ℂ) * Complex.I)).re = ρ.re - 2` using `by simp`. Establish `him' : (ρ - (2 + (t : ℂ) * Complex.I)).im = ρ.im - t` using `by simp`. Take `⟨ha, hb⟩` from `abs_le.mp him`.

Rewrite using `[← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm, Complex.normSq_apply, hre, him']`. Use the polynomial consequences of the given equalities and inequalities. Establish `hne : ρ ≠ 1`. Introduce `h`. Rewrite `h1` using `[h]`.

Evaluate the numerical expressions using `at h1`. Rewrite using `[Lent.eq_1]`. Use `split_ifs with hχ`. Substitute `hχ` using the available equality. Establish `key : DirichletCharacter.LFunctionTrivChar₁ N ρ = (ρ - 1) * DirichletCharacter.LFunctionTrivChar N ρ` using `by first`.

Consider the case `simp [DirichletCharacter.LFunctionTrivChar₁, Function.update_apply, hne]`. Consider the case `(unfold DirichletCharacter.LFunctionTrivChar₁; rw [Function.update_of_ne hne])`. Consider the case `exact DirichletCharacter.LFunctionTrivChar₁_apply_ne_one N hne`. Rewrite using `[key]`. Conclude with `mul_eq_zero_of_right _ hL`.

Conclude with `hL`. Establish `h0Z : (0 : ℂ) ∉ ZerosNear χ t`. Introduce `h`. Rewrite `h` using `[ZerosNear.eq_1]`. Take `⟨h0, -⟩` from `h`.

Simplify using `at h0`. Establish `hZ : (ZerosNear χ t).Finite` using `hfin.subset hsub`. Use `⟨(hfin.toFinset.filter (fun ρ => ρ ∉ ZerosNear χ t)).filter (fun ρ => ρ ≠ 0), ?_, ?_⟩` and prove the remaining obligations. Introduce `ρ hρ`. Simplify using `only [Finset.mem_filter, Set.Finite.mem_toFinset] at hρ`.

Conclude with `⟨hρ.1.1, hρ.1.2, hρ.2⟩`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum F hfin, finsum_mem_eq_finite_toFinset_sum F hZ, ← Finset.sum_filter_add_sum_filter_not hfin.toFinset (fun ρ => ρ ∈ ZerosNear χ t)]`. Establish `e1 : hfin.toFinset.filter (fun ρ => ρ ∈ ZerosNear χ t) = hZ.toFinset`. Use extensionality with `ρ`. Simplify using `only [Finset.mem_filter, Set.Finite.mem_toFinset]`.

Conclude with `⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩`. Rewrite using `[e1, add_assoc]`. Use `congr 1`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not (hfin.toFinset.filter (fun ρ => ρ ∉ ZerosNear χ t)) (fun ρ => ρ ≠ 0)]`. Use `congr 1`.

Use `split_ifs with hD`. Establish `e2 : (hfin.toFinset.filter (fun ρ => ρ ∉ ZerosNear χ t)).filter (fun ρ => ¬ ρ ≠ 0) = {0}`. Use extensionality with `ρ`. Simplify using `only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_singleton, ne_eq, not_not]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨-, h⟩`. Conclude with `h`. Introduce and unpack `rfl`. Conclude with `⟨⟨hD, h0Z⟩, rfl⟩`. Rewrite using `[e2, Finset.sum_singleton]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `ρ hρ`. Simplify using `only [Finset.mem_filter, Set.Finite.mem_toFinset, ne_eq, not_not] at hρ`. Conclude with `absurd (hρ.2 ▸ hρ.1.1) hD`.
-/
lemma sum_DZ_eq {χ : DirichletCharacter ℂ N} (t : ℝ)
    (hfin : (DZ χ t).Finite) (F : ℂ → ℂ) :
    ∃ E : Finset ℂ, (∀ ρ ∈ E, ρ ∈ DZ χ t ∧ ρ ∉ ZerosNear χ t ∧ ρ ≠ 0) ∧
      ∑ᶠ ρ ∈ DZ χ t, F ρ = ∑ᶠ ρ ∈ ZerosNear χ t, F ρ + ∑ ρ ∈ E, F ρ +
        (open Classical in if (0 : ℂ) ∈ DZ χ t then F 0 else 0) := by
  classical
  have hsub : ZerosNear χ t ⊆ DZ χ t := by
    intro ρ hρ
    rw [ZerosNear.eq_1] at hρ
    obtain ⟨h0, h1, him, hL⟩ := hρ
    rw [DZ.eq_1, Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, ctr.eq_1, Complex.dist_eq]
      have hre : (ρ - (2 + (t : ℂ) * Complex.I)).re = ρ.re - 2 := by simp
      have him' : (ρ - (2 + (t : ℂ) * Complex.I)).im = ρ.im - t := by simp
      obtain ⟨ha, hb⟩ := abs_le.mp him
      rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm, Complex.normSq_apply,
        hre, him']
      nlinarith
    · have hne : ρ ≠ 1 := by
        intro h
        rw [h] at h1
        norm_num at h1
      rw [Lent.eq_1]
      split_ifs with hχ
      · subst hχ
        have key : DirichletCharacter.LFunctionTrivChar₁ N ρ =
            (ρ - 1) * DirichletCharacter.LFunctionTrivChar N ρ := by
          first
          | simp [DirichletCharacter.LFunctionTrivChar₁, Function.update_apply, hne]
          | (unfold DirichletCharacter.LFunctionTrivChar₁; rw [Function.update_of_ne hne])
          | exact DirichletCharacter.LFunctionTrivChar₁_apply_ne_one N hne
        rw [key]
        exact mul_eq_zero_of_right _ hL
      · exact hL
  have h0Z : (0 : ℂ) ∉ ZerosNear χ t := by
    intro h
    rw [ZerosNear.eq_1] at h
    obtain ⟨h0, -⟩ := h
    simp at h0
  have hZ : (ZerosNear χ t).Finite := hfin.subset hsub
  refine ⟨(hfin.toFinset.filter (fun ρ => ρ ∉ ZerosNear χ t)).filter (fun ρ => ρ ≠ 0), ?_, ?_⟩
  · intro ρ hρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
    exact ⟨hρ.1.1, hρ.1.2, hρ.2⟩
  · rw [finsum_mem_eq_finite_toFinset_sum F hfin, finsum_mem_eq_finite_toFinset_sum F hZ,
      ← Finset.sum_filter_add_sum_filter_not hfin.toFinset (fun ρ => ρ ∈ ZerosNear χ t)]
    have e1 : hfin.toFinset.filter (fun ρ => ρ ∈ ZerosNear χ t) = hZ.toFinset := by
      ext ρ
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
    rw [e1, add_assoc]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not
      (hfin.toFinset.filter (fun ρ => ρ ∉ ZerosNear χ t)) (fun ρ => ρ ≠ 0)]
    congr 1
    split_ifs with hD
    · have e2 : (hfin.toFinset.filter (fun ρ => ρ ∉ ZerosNear χ t)).filter
          (fun ρ => ¬ ρ ≠ 0) = {0} := by
        ext ρ
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_singleton, ne_eq,
          not_not]
        constructor
        · rintro ⟨-, h⟩
          exact h
        · rintro rfl
          exact ⟨⟨hD, h0Z⟩, rfl⟩
      rw [e2, Finset.sum_singleton]
    · apply Finset.sum_eq_zero
      intro ρ hρ
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, ne_eq, not_not] at hρ
      exact absurd (hρ.2 ▸ hρ.1.1) hD

/- English proof (translation)
Introduce `hLA hG hZL hW`. Take `⟨A, C, hA, hC, hG⟩` from `hG`. Take `⟨Cw, hCw, hW⟩` from `hW`. Take `⟨C₀, hC₀, hloc⟩` from `hLA (5 / 2) (11 / 4) 6 (by norm_num) (by norm_num) (by norm_num)`. Use `⟨C₀ * (2 * |Real.log (2 * C)| + 3 * A) + 4 * Cw + 2, by positivity, ?_⟩` and prove the remaining obligations.

Introduce `N _ χ hχ s h1 h2 hLs hs1`. Establish `hc0 : Lent χ (ctr s.im) ≠ 0`. Use `half_le_norm_Lent_ctr hI χ s.im` as an intermediate fact. Conclude with `norm_pos_iff.1 (lt_of_lt_of_le (by norm_num) this)`. Take `⟨hfin, hbound⟩` from `hloc (Lent χ) (ctr s.im) (Mfun A C N s.im) (fun z _ => (differentiable_Lent χ).analyticAt z) hc0 (Mfun_nonneg hA N s.im) (Lent_disc_bound hA hC hG hI hχ s.im)`.

Establish `hLs' : Lent χ s ≠ 0` using `fun h => hLs ((Lent_eq_zero_iff χ hs1).1 h)`. Establish `hb` using `hbound s (mem_ball_ctr s h1 h2) hLs'`. Establish `hfin' : (DZ χ s.im).Finite` using `hfin`. Establish `econgr : ∑ᶠ ρ ∈ {ρ | ρ ∈ closedBall (ctr s.im) (11 / 4) ∧ Lent χ ρ = 0}, (analyticOrderNatAt (Lent χ) ρ : ℂ) / (s - ρ) = ∑ᶠ ρ ∈ DZ χ s.im, (mult χ ρ : ℂ) / (s - ρ)` using `finsum_mem_congr rfl (fun ρ hρ => by rw [order_Lent χ (DZ_facts hZL hχ hρ).1])`. Rewrite `hb` using `[econgr]`.

Take `⟨E, hE, hdec⟩` from `sum_DZ_eq s.im hfin' (fun ρ => (mult χ ρ : ℂ) / (s - ρ))`. Establish `hfar` using `far_sum_le hW hZL hχ s rfl E hE`. Establish `hzero` using `zero_term_le hZL hχ s rfl`. Establish `hM` using `Mfun_le (C := C) hA N s.im`. Establish `hw1` using `log_window_le N (t := s.im) (u := s.im + 2) ((abs_add_le _ _).trans (by norm_num))`.

Establish `hw2` using `log_window_le N (t := s.im) (u := s.im - 2) ((abs_sub _ _).trans (by norm_num))`. Establish `hL1` using `one_le_two_LL N s.im`. Establish `key : logDeriv (LFunction χ) s - ∑ᶠ ρ ∈ ZerosNear χ s.im, (mult χ ρ : ℂ) / (s - ρ) - eps0 χ / s + del1 χ / (s - 1) = (logDeriv (Lent χ) s - ∑ᶠ ρ ∈ DZ χ s.im, (mult χ ρ : ℂ) / (s - ρ)) + ∑ ρ ∈ E, (mult χ ρ : ℂ) / (s - ρ) + ((open Classical in if (0 : ℂ) ∈ DZ χ s.im then (mult χ 0 …`. Rewrite using `[logDeriv_Lent χ hs1 hLs, hdec]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[key]`. Establish `hMnn` using `Mfun_nonneg (C := C) hA N s.im`. Combine the equalities or inequalities in the displayed calculation. Unfold `LL`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem localLemma_of (hI : PI.LInvRight) : GlueLocalLemma := by
  intro hLA hG hZL hW
  obtain ⟨A, C, hA, hC, hG⟩ := hG
  obtain ⟨Cw, hCw, hW⟩ := hW
  obtain ⟨C₀, hC₀, hloc⟩ := hLA (5 / 2) (11 / 4) 6 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C₀ * (2 * |Real.log (2 * C)| + 3 * A) + 4 * Cw + 2, by positivity, ?_⟩
  intro N _ χ hχ s h1 h2 hLs hs1
  have hc0 : Lent χ (ctr s.im) ≠ 0 := by
    have := half_le_norm_Lent_ctr hI χ s.im
    exact norm_pos_iff.1 (lt_of_lt_of_le (by norm_num) this)
  obtain ⟨hfin, hbound⟩ := hloc (Lent χ) (ctr s.im) (Mfun A C N s.im)
    (fun z _ => (differentiable_Lent χ).analyticAt z) hc0 (Mfun_nonneg hA N s.im)
    (Lent_disc_bound hA hC hG hI hχ s.im)
  have hLs' : Lent χ s ≠ 0 := fun h => hLs ((Lent_eq_zero_iff χ hs1).1 h)
  have hb := hbound s (mem_ball_ctr s h1 h2) hLs'
  have hfin' : (DZ χ s.im).Finite := hfin
  have econgr : ∑ᶠ ρ ∈ {ρ | ρ ∈ closedBall (ctr s.im) (11 / 4) ∧ Lent χ ρ = 0},
      (analyticOrderNatAt (Lent χ) ρ : ℂ) / (s - ρ) =
      ∑ᶠ ρ ∈ DZ χ s.im, (mult χ ρ : ℂ) / (s - ρ) :=
    finsum_mem_congr rfl (fun ρ hρ => by rw [order_Lent χ (DZ_facts hZL hχ hρ).1])
  rw [econgr] at hb
  obtain ⟨E, hE, hdec⟩ := sum_DZ_eq s.im hfin' (fun ρ => (mult χ ρ : ℂ) / (s - ρ))
  have hfar := far_sum_le hW hZL hχ s rfl E hE
  have hzero := zero_term_le hZL hχ s rfl
  have hM := Mfun_le (C := C) hA N s.im
  have hw1 := log_window_le N (t := s.im) (u := s.im + 2)
    ((abs_add_le _ _).trans (by norm_num))
  have hw2 := log_window_le N (t := s.im) (u := s.im - 2)
    ((abs_sub _ _).trans (by norm_num))
  have hL1 := one_le_two_LL N s.im
  have key : logDeriv (LFunction χ) s - ∑ᶠ ρ ∈ ZerosNear χ s.im, (mult χ ρ : ℂ) / (s - ρ) -
      eps0 χ / s + del1 χ / (s - 1) =
      (logDeriv (Lent χ) s - ∑ᶠ ρ ∈ DZ χ s.im, (mult χ ρ : ℂ) / (s - ρ)) +
        ∑ ρ ∈ E, (mult χ ρ : ℂ) / (s - ρ) +
        ((open Classical in if (0 : ℂ) ∈ DZ χ s.im then (mult χ 0 : ℂ) / (s - 0) else 0) -
          eps0 χ / s) := by
    rw [logDeriv_Lent χ hs1 hLs, hdec]
    ring
  rw [key]
  have hMnn := Mfun_nonneg (C := C) hA N s.im
  calc _ ≤ ‖logDeriv (Lent χ) s - ∑ᶠ ρ ∈ DZ χ s.im, (mult χ ρ : ℂ) / (s - ρ)‖ +
        ‖∑ ρ ∈ E, (mult χ ρ : ℂ) / (s - ρ)‖ +
        ‖(open Classical in if (0 : ℂ) ∈ DZ χ s.im then (mult χ 0 : ℂ) / (s - 0) else 0) -
          eps0 χ / s‖ := norm_add₃_le
    _ ≤ C₀ * Mfun A C N s.im + (Cw * Real.log (N * (|s.im + 2| + 2)) +
        Cw * Real.log (N * (|s.im - 2| + 2))) + 1 := add_le_add (add_le_add hb hfar) hzero
    _ ≤ C₀ * ((2 * |Real.log (2 * C)| + 3 * A) * LL N s.im) +
        (Cw * (2 * LL N s.im) + Cw * (2 * LL N s.im)) + 2 * LL N s.im := by
        gcongr
    _ = (C₀ * (2 * |Real.log (2 * C)| + 3 * A) + 4 * Cw + 2) * Real.log (N * (|s.im| + 2)) := by
        unfold LL
        ring

end PI.EF
