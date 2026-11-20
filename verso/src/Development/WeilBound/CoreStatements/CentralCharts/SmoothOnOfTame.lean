import Development.WeilBound.CoreStatements.CentralCharts.ExistsPermFirst

noncomputable section

namespace AnalyticReference.An

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Metric

variable {n : ℕ} {X : Type} [TopologicalSpace X]

/- English proof (translation)
Unfold `logR`. Establish `hs : 0 ≤ ∑ i : Fin n, (if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0)`. Use `Finset.sum_nonneg fun i _ => ?_` and prove the remaining obligations. Use `split_ifs`. Establish `h1` using `norm_le_pi_norm t i`.

Establish `h2 : ‖t i‖ ^ 2 ≤ 1` using `by nlinarith [norm_nonneg (t i)]`. Rewrite using `[one_div, Real.log_inv, neg_nonneg]`. Conclude with `Real.log_nonpos (by positivity) h2`. Conclude with `le_rfl`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exp_le_logR (a : ℕ) {t : Fin n → ℂ} (ht : ‖t‖ < 1) : Real.exp 1 ≤ logR a t := by
  unfold logR
  have hs : 0 ≤ ∑ i : Fin n, (if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) := by
    refine Finset.sum_nonneg fun i _ => ?_
    split_ifs
    · have h1 := norm_le_pi_norm t i
      have h2 : ‖t i‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (t i)]
      rw [one_div, Real.log_inv, neg_nonneg]
      exact Real.log_nonpos (by positivity) h2
    · exact le_rfl
  linarith

/- English proof (translation)
Establish `he : 1 ≤ Real.exp 1` using `Real.one_le_exp zero_le_one`. Establish `hr : 0 < r` using `by linarith`. Conclude with `⟨le_trans he h, (Real.le_log_iff_exp_le hr).mpr h⟩`.
-/
theorem one_le_of_exp_le {r : ℝ} (h : Real.exp 1 ≤ r) : 1 ≤ r ∧ 1 ≤ Real.log r := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hr : 0 < r := by linarith
  exact ⟨le_trans he h, (Real.le_log_iff_exp_le hr).mpr h⟩

/- English proof (translation)
Establish `hon : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (ball 0 1)` using `fun t ht => (hg t ht).contDiffWithinAt`. Establish `hK : IsCompact (closedBall (0 : Fin n → ℂ) (1 / 2))` using `isCompact_closedBall _ _`. Establish `hsub : closedBall (0 : Fin n → ℂ) (1 / 2) ⊆ ball 0 1` using `closedBall_subset_ball (by norm_num)`. Take `⟨B1, hB1⟩` from `hK.exists_bound_of_continuousOn (hon.continuousOn.mono hsub)`. Take `⟨B2, hB2⟩` from `hK.exists_bound_of_continuousOn ((hon.continuousOn_fderiv_of_isOpen isOpen_ball (by exact_mod_cast le_top)).mono hsub)`.

Use `⟨1 / 2, max (max B1 B2) 0, by norm_num, by norm_num, le_max_right _ _, fun t ht _ => ?_⟩` and prove the remaining obligations. Establish `htK : t ∈ closedBall (0 : Fin n → ℂ) (1 / 2)`. Rewrite using `[mem_closedBall, dist_zero_right]`. Conclude with `ht.le`. Establish `hR` using `exp_le_logR a (t := t) (by linarith)`.

Take `⟨hR1, hL1⟩` from `one_le_of_exp_le hR`. Establish `hC : 0 ≤ max (max B1 B2) 0` using `le_max_right _ _`. Use `⟨hg t (hsub htK), ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hB1 t htK`. Rewrite `h1` using `[Real.norm_eq_abs]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h1` using `hB2 t htK`. Establish `h2 : 1 ≤ logR a t ^ max (max B1 B2) 0` using `Real.one_le_rpow hR1 hC`. Establish `h3 : 1 ≤ Real.exp (logR a t / 2)` using `Real.one_le_exp (by linarith)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tame_smooth (a : ℕ) {g : (Fin n → ℂ) → ℝ}
    (hg : ∀ t ∈ ball (0 : Fin n → ℂ) 1, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g t) : Tame a g := by
  have hon : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (ball 0 1) := fun t ht => (hg t ht).contDiffWithinAt
  have hK : IsCompact (closedBall (0 : Fin n → ℂ) (1 / 2)) := isCompact_closedBall _ _
  have hsub : closedBall (0 : Fin n → ℂ) (1 / 2) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn (hon.continuousOn.mono hsub)
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn
    ((hon.continuousOn_fderiv_of_isOpen isOpen_ball (by exact_mod_cast le_top)).mono hsub)
  refine ⟨1 / 2, max (max B1 B2) 0, by norm_num, by norm_num, le_max_right _ _, fun t ht _ => ?_⟩
  have htK : t ∈ closedBall (0 : Fin n → ℂ) (1 / 2) := by
    rw [mem_closedBall, dist_zero_right]
    exact ht.le
  have hR := exp_le_logR a (t := t) (by linarith)
  obtain ⟨hR1, hL1⟩ := one_le_of_exp_le hR
  have hC : 0 ≤ max (max B1 B2) 0 := le_max_right _ _
  refine ⟨hg t (hsub htK), ?_, ?_⟩
  · have h1 := hB1 t htK
    rw [Real.norm_eq_abs] at h1
    calc |g t| ≤ max (max B1 B2) 0 := le_trans h1 (le_trans (le_max_left _ _) (le_max_left _ _))
      _ = max (max B1 B2) 0 * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hL1 hC
  · have h1 := hB2 t htK
    have h2 : 1 ≤ logR a t ^ max (max B1 B2) 0 := Real.one_le_rpow hR1 hC
    have h3 : 1 ≤ Real.exp (logR a t / 2) := Real.one_le_exp (by linarith)
    calc ‖fderiv ℝ g t‖ ≤ max (max B1 B2) 0 :=
          le_trans h1 (le_trans (le_max_right _ _) (le_max_left _ _))
      _ = max (max B1 B2) 0 * 1 * 1 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h2 hC) h3 zero_le_one (by positivity)

/- English proof (translation)
Use `hn y` as an intermediate fact. Unfold `rW`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exp_le_rW {L : LocPot X} {s : X → X → ℂ} (hn : ∀ y, logNormSec L s y ≤ 0) (y : X) :
    Real.exp 1 ≤ rW L s y := by
  have := hn y
  unfold rW
  linarith

variable {A : FinHolAtlas n X} {L : LocPot X} {s : X → X → ℂ} {U : X → Set X} {ph : X → ℝ}

/- English proof (translation)
Rewrite using `[← h.2.2.1]`. Conclude with `ψ.left_inv h.2.1`.
-/
theorem NChart.symm_zero {V : Set X} {x₀ : X} {ψ : OpenPartialHomeomorph X (Fin n → ℂ)} {a : ℕ} {M : ℝ}
    (h : NChart A V L s x₀ ψ a M) : ψ.symm 0 = x₀ := by
  rw [← h.2.2.1]
  exact ψ.left_inv h.2.1

/- English proof (translation)
Assume the negation of the conclusion as `ha`. Establish `h0` using `(h.2.2.2.2 0 (mem_ball_self one_pos)).2.2.1`. Rewrite `h0` using `[NChart.symm_zero h]`. Establish `hpos : 0 < a` using `Nat.pos_of_ne_zero ha`. Conclude with `hx (h0.mpr ⟨⟨0, lt_of_lt_of_le hpos h.2.2.2.1⟩, hpos, rfl⟩)`.
-/
theorem NChart.zero_of_not_mem {V : Set X} {x₀ : X} {ψ : OpenPartialHomeomorph X (Fin n → ℂ)} {a : ℕ} {M : ℝ}
    (h : NChart A V L s x₀ ψ a M) (hx : x₀ ∉ bdry s) : a = 0 := by
  by_contra ha
  have h0 := (h.2.2.2.2 0 (mem_ball_self one_pos)).2.2.1
  rw [NChart.symm_zero h] at h0
  have hpos : 0 < a := Nat.pos_of_ne_zero ha
  exact hx (h0.mpr ⟨⟨0, lt_of_lt_of_le hpos h.2.2.2.1⟩, hpos, rfl⟩)

/- English proof (translation)
Introduce `j y hy`. Take `⟨hyt, hyb⟩` from `hy`. Take `⟨ψ, a, M, hN, hTm⟩` from `hT ((A.chart j).symm y)`. Establish `ha : a = 0` using `hN.zero_of_not_mem hyb`. Substitute `ha` using the available equality.

Take `⟨ε, C, hε, -, -, hTt⟩` from `hTm`. Establish `hxs : (A.chart j).symm y ∈ ψ.source` using `hN.2.1`. Establish `hs0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ph (ψ.symm t)) (ψ ((A.chart j).symm y))`. Rewrite using `[hN.2.2.1]`. Conclude with `(hTt 0 (by simpa using hε) (fun i hi => absurd hi (Nat.not_lt_zero _))).1`.

Establish `hcomp : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y` using `(hN.1 j).1 y ⟨hyt, hxs⟩`. Establish `hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ ∘ (A.chart j).symm) y` using `(hcomp.contDiffAt).restrict_scalars ℝ`. Establish `heq : (fun t => ph (ψ.symm t)) ∘ (ψ ∘ (A.chart j).symm) =ᶠ[𝓝 y] ph ∘ (A.chart j).symm`. Establish `hopen : (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source ∈ 𝓝 y` using `((A.chart j).isOpen_inter_preimage_symm ψ.open_source).mem_nhds ⟨hyt, hxs⟩`. Use `filter_upwards [hopen] with w hw`.

Simplify using `[Function.comp, ψ.left_inv hw.2]`. Conclude with `((hs0.comp y hsm).congr_of_eventuallyEq heq.symm).contDiffWithinAt`.
-/
theorem smoothOn_of_tame (hT : ∀ x, ∃ ψ a M, NChart A (U x) L s x ψ a M ∧ Tame a fun t => ph (ψ.symm t)) :
    A.SmoothOn (bdry s)ᶜ ph := by
  intro j y hy
  obtain ⟨hyt, hyb⟩ := hy
  obtain ⟨ψ, a, M, hN, hTm⟩ := hT ((A.chart j).symm y)
  have ha : a = 0 := hN.zero_of_not_mem hyb
  subst ha
  obtain ⟨ε, C, hε, -, -, hTt⟩ := hTm
  have hxs : (A.chart j).symm y ∈ ψ.source := hN.2.1
  have hs0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ph (ψ.symm t)) (ψ ((A.chart j).symm y)) := by
    rw [hN.2.2.1]
    exact (hTt 0 (by simpa using hε) (fun i hi => absurd hi (Nat.not_lt_zero _))).1
  have hcomp : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y := (hN.1 j).1 y ⟨hyt, hxs⟩
  have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ ∘ (A.chart j).symm) y :=
    (hcomp.contDiffAt).restrict_scalars ℝ
  have heq : (fun t => ph (ψ.symm t)) ∘ (ψ ∘ (A.chart j).symm) =ᶠ[𝓝 y] ph ∘ (A.chart j).symm := by
    have hopen : (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source ∈ 𝓝 y :=
      ((A.chart j).isOpen_inter_preimage_symm ψ.open_source).mem_nhds ⟨hyt, hxs⟩
    filter_upwards [hopen] with w hw
    simp [Function.comp, ψ.left_inv hw.2]
  exact ((hs0.comp y hsm).congr_of_eventuallyEq heq.symm).contDiffWithinAt

/- English proof (translation)
The claim follows from `|ph x'| ≤ c * Real.log (rW L s x') ∧ ‖fderiv ℝ (ph ∘ ψ.symm) (ψ x')‖ ≤ c * rW L s x' ^ c * Real.exp (rW L s x' / 2) := by obtain ⟨ε, C, hε, hε1, hC, hTt⟩ := hT set K : ℝ := 1 + max M 0 with hK have hM0 : 0 ≤ max M 0 := le_max_right _ _ have hMM : M ≤ max M 0 := le_max_left _ _ ha …`.
-/
theorem local_of_tame (hn : ∀ y, logNormSec L s y ≤ 0) {V : Set X} {x : X}
    {ψ : OpenPartialHomeomorph X (Fin n → ℂ)} {a : ℕ} {M : ℝ} (h : NChart A V L s x ψ a M)
    (hT : Tame a fun t => ph (ψ.symm t)) :
    ∃ (V' : Set X) (c : ℝ), IsOpen V' ∧ x ∈ V' ∧ V' ⊆ ψ.source ∧ ∀ x' ∈ V', x' ∉ bdry s →
      |ph x'| ≤ c * Real.log (rW L s x') ∧
      ‖fderiv ℝ (ph ∘ ψ.symm) (ψ x')‖ ≤ c * rW L s x' ^ c * Real.exp (rW L s x' / 2) := by
  obtain ⟨ε, C, hε, hε1, hC, hTt⟩ := hT
  set K : ℝ := 1 + max M 0 with hK
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hMM : M ≤ max M 0 := le_max_left _ _
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  set c1 := C * (1 + Real.log K) with hc1d
  set c2 := C * K ^ C * Real.exp (K / 2) with hc2d
  have hKC : 1 ≤ K ^ C := Real.one_le_rpow hK1 hC
  have heK : 1 ≤ Real.exp (K / 2) := Real.one_le_exp (by linarith)
  have hCc2 : C ≤ c2 := by
    have h1 : 1 ≤ K ^ C * Real.exp (K / 2) := by nlinarith
    calc C = C * 1 := by ring
      _ ≤ C * (K ^ C * Real.exp (K / 2)) := mul_le_mul_of_nonneg_left h1 hC
      _ = c2 := by rw [hc2d]; ring
  have hc1 : c1 ≤ max c1 c2 := le_max_left _ _
  have hc2 : c2 ≤ max c1 c2 := le_max_right _ _
  refine ⟨ψ.source ∩ ψ ⁻¹' ball 0 ε, max c1 c2, ψ.isOpen_inter_preimage isOpen_ball,
    ⟨h.2.1, by simp [h.2.2.1, hε]⟩, Set.inter_subset_left, ?_⟩
  rintro x' ⟨hxs, hxb⟩ hxbd
  have htb : ‖ψ x'‖ < ε := by simpa using hxb
  have ht1 : ψ x' ∈ ball (0 : Fin n → ℂ) 1 := by
    rw [mem_ball_zero_iff]
    linarith
  have hsy : ψ.symm (ψ x') = x' := ψ.left_inv hxs
  have hN := h.2.2.2.2 (ψ x') ht1
  rw [hsy] at hN
  have hnz : ∀ i : Fin n, (i : ℕ) < a → ψ x' i ≠ 0 := fun i hi h0 => hxbd (hN.2.2.1.mpr ⟨i, hi, h0⟩)
  have hRb : logR a (ψ x') ≤ rW L s x' + M := hN.2.2.2 hxbd
  obtain ⟨-, hbd1, hbd2⟩ := hTt (ψ x') htb hnz
  have hrW := exp_le_rW hn x'
  obtain ⟨hrW1, hlrW⟩ := one_le_of_exp_le hrW
  obtain ⟨hR1, hlR⟩ := one_le_of_exp_le (exp_le_logR a (t := ψ x') (by linarith))
  have hRK : logR a (ψ x') ≤ rW L s x' * K := by
    rw [hK]
    nlinarith
  have hlog : Real.log (logR a (ψ x')) ≤ (1 + Real.log K) * Real.log (rW L s x') := by
    have h1 : Real.log (logR a (ψ x')) ≤ Real.log (rW L s x' * K) := Real.log_le_log (by linarith) hRK
    rw [Real.log_mul (by linarith) (by linarith)] at h1
    nlinarith
  refine ⟨?_, ?_⟩
  · have hb1 : |ph x'| ≤ C * Real.log (logR a (ψ x')) := by simpa [hsy] using hbd1
    calc |ph x'| ≤ C * Real.log (logR a (ψ x')) := hb1
      _ ≤ C * ((1 + Real.log K) * Real.log (rW L s x')) := mul_le_mul_of_nonneg_left hlog hC
      _ = c1 * Real.log (rW L s x') := by rw [hc1d]; ring
      _ ≤ max c1 c2 * Real.log (rW L s x') := mul_le_mul_of_nonneg_right hc1 (by linarith)
  · have hp1 : logR a (ψ x') ^ C ≤ rW L s x' ^ C * K ^ C := by
      rw [← Real.mul_rpow (by linarith) (by linarith)]
      exact Real.rpow_le_rpow (by linarith) hRK hC
    have hp2 : Real.exp (logR a (ψ x') / 2) ≤ Real.exp (rW L s x' / 2) * Real.exp (K / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [hK]
      linarith
    have hp3 : rW L s x' ^ C ≤ rW L s x' ^ max c1 c2 :=
      Real.rpow_le_rpow_of_exponent_le hrW1 (le_trans hCc2 hc2)
    have hfd : ‖fderiv ℝ (ph ∘ ψ.symm) (ψ x')‖ ≤ C * logR a (ψ x') ^ C * Real.exp (logR a (ψ x') / 2) :=
      hbd2
    have hE0 : 0 ≤ Real.exp (rW L s x' / 2) := (Real.exp_pos _).le
    have hrC : 0 ≤ rW L s x' ^ C := by positivity
    calc ‖fderiv ℝ (ph ∘ ψ.symm) (ψ x')‖ ≤ C * logR a (ψ x') ^ C * Real.exp (logR a (ψ x') / 2) := hfd
      _ ≤ C * (rW L s x' ^ C * K ^ C) * (Real.exp (rW L s x' / 2) * Real.exp (K / 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hp1 hC) hp2 (Real.exp_pos _).le (by positivity)
      _ = c2 * rW L s x' ^ C * Real.exp (rW L s x' / 2) := by rw [hc2d]; ring
      _ ≤ max c1 c2 * rW L s x' ^ max c1 c2 * Real.exp (rW L s x' / 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hc2 hp3 hrC (le_trans (le_trans hC hCc2) hc2)) hE0

/- English proof (translation)
Establish `key : ∀ x, ∃ (V' : Set X) (c : ℝ), IsOpen V' ∧ x ∈ V' ∧ ∀ x' ∈ V', x' ∉ bdry s → |ph x'| ≤ c * Real.log (rW L s x')` using `fun x => by`. Take `⟨ψ, a, M, h, ht⟩` from `hT x`. Take `⟨V', c, h1, h2, -, h3⟩` from `local_of_tame hn h ht`. Conclude with `⟨V', c, h1, h2, fun x' a b => (h3 x' a b).1⟩`. Use `choose V c h1 h2 h3 using key`.

Take `⟨F, hF⟩` from `isCompact_univ.elim_finite_subcover V h1 fun x _ => Set.mem_iUnion.2 ⟨x, h2 x⟩`. Use `⟨∑ x ∈ F, |c x|, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, hyx⟩` from `Set.mem_iUnion₂.1 (hF (Set.mem_univ y))`. Use `(one_le_of_exp_le (exp_le_rW hn y)).2` as an intermediate fact. Use `(h3 x y hyx hy).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) (by linarith))` and prove the remaining obligations.

Conclude with `Finset.single_le_sum (f := fun x => |c x|) (fun _ _ => abs_nonneg _) hx`.
-/
theorem size_of_tame [CompactSpace X] (hn : ∀ y, logNormSec L s y ≤ 0)
    (hT : ∀ x, ∃ ψ a M, NChart A (U x) L s x ψ a M ∧ Tame a fun t => ph (ψ.symm t)) :
    ∃ C : ℝ, ∀ y ∉ bdry s, |ph y| ≤ C * Real.log (rW L s y) := by
  have key : ∀ x, ∃ (V' : Set X) (c : ℝ), IsOpen V' ∧ x ∈ V' ∧ ∀ x' ∈ V', x' ∉ bdry s →
      |ph x'| ≤ c * Real.log (rW L s x') := fun x => by
    obtain ⟨ψ, a, M, h, ht⟩ := hT x
    obtain ⟨V', c, h1, h2, -, h3⟩ := local_of_tame hn h ht
    exact ⟨V', c, h1, h2, fun x' a b => (h3 x' a b).1⟩
  choose V c h1 h2 h3 using key
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover V h1 fun x _ => Set.mem_iUnion.2 ⟨x, h2 x⟩
  refine ⟨∑ x ∈ F, |c x|, fun y hy => ?_⟩
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ y))
  have := (one_le_of_exp_le (exp_le_rW hn y)).2
  refine (h3 x y hyx hy).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) (by linarith))
  exact Finset.single_le_sum (f := fun x => |c x|) (fun _ _ => abs_nonneg _) hx

/- English proof (translation)
Introduce `x j y hy w`. Take `⟨hyt, hyU, hyV⟩` from `hy`. Take `⟨ψ, hψc, hzs, hz0, hpsh⟩` from `h _ hyV`. Take `⟨Wd, hWo, hzW, G, hG, hdiff⟩` from `hP x _ hyU`. Establish `hτ : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y` using `(hψc j).1 y ⟨hyt, hzs⟩`.

Establish `hτy : (ψ ∘ (A.chart j).symm) y = 0` using `hz0`. Establish `hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y` using `hG j y ⟨hyt, hzW⟩`. Establish `hg2 : ContDiffAt ℝ 2 (fun t => P.φ ((A.chart j).symm y) (ψ.symm t)) ((ψ ∘ (A.chart j).symm) y)`. Rewrite using `[hτy]`. Conclude with `hpsh.1`.

Establish `hgc : ContDiffAt ℝ 2 ((fun t => P.φ ((A.chart j).symm y) (ψ.symm t)) ∘ (ψ ∘ (A.chart j).symm)) y` using `hg2.comp y ((hτ.contDiffAt).restrict_scalars ℝ)`. Establish `hre : ContDiffAt ℝ 2 (fun y' => ((G ∘ (A.chart j).symm) y').re) y` using `(Complex.reCLM.contDiff.contDiffAt).comp y ((hGa.contDiffAt).restrict_scalars ℝ)`. Establish `hN : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (Wd ∩ P.U x ∩ P.U ((A.chart j).symm y) ∩ ψ.source) ∈ 𝓝 y` using `((A.chart j).isOpen_inter_preimage_symm (((hWo.inter (P.isOpen_U x)).inter (P.isOpen_U _)).inter ψ.open_source)).mem_nhds ⟨hyt, ⟨⟨hzW, hyU⟩, P.mem_U _⟩, hzs⟩`. Establish `heq : (P.φ x ∘ (A.chart j).symm) =ᶠ[𝓝 y] fun y' => ((fun t => P.φ ((A.chart j).symm y) (ψ.symm t)) ∘ (ψ ∘ (A.chart j).symm)) y' + 1 * ((G ∘ (A.chart j).symm) y').re` using `by filter_upwards [hN] with y' hy'`. Take `⟨-, ⟨⟨hW', hx'⟩, hz'⟩, hs'⟩` from `hy'`.

Use `hdiff _ ⟨⟨hW', hx'⟩, hz'⟩` as an intermediate fact. Simplify using `only [Function.comp, ψ.left_inv hs', one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[levi_congr heq, levi_add_smul 1 hgc hre, levi_re_analytic hGa, levi_comp w hτ hg2, hτy]`. Simplify using `using hpsh.2 _`.
-/
theorem pshOn_of_local {V : Set X} (P : LocPot X)
    (hP : ∀ x z, z ∈ P.U x → ∃ W : Set X, IsOpen W ∧ z ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ w ∈ W ∩ P.U x ∩ P.U z, P.φ x w - P.φ z w = (G w).re)
    (h : ∀ z ∈ V, ∃ ψ : OpenPartialHomeomorph X (Fin n → ℂ), IsCompatChart A ψ ∧ z ∈ ψ.source ∧ ψ z = 0 ∧
      PshAt0 fun t => P.φ z (ψ.symm t)) : IsPshOn A V P := by
  intro x j y hy w
  obtain ⟨hyt, hyU, hyV⟩ := hy
  obtain ⟨ψ, hψc, hzs, hz0, hpsh⟩ := h _ hyV
  obtain ⟨Wd, hWo, hzW, G, hG, hdiff⟩ := hP x _ hyU
  have hτ : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y := (hψc j).1 y ⟨hyt, hzs⟩
  have hτy : (ψ ∘ (A.chart j).symm) y = 0 := hz0
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hyt, hzW⟩
  have hg2 : ContDiffAt ℝ 2 (fun t => P.φ ((A.chart j).symm y) (ψ.symm t)) ((ψ ∘ (A.chart j).symm) y) := by
    rw [hτy]
    exact hpsh.1
  have hgc : ContDiffAt ℝ 2 ((fun t => P.φ ((A.chart j).symm y) (ψ.symm t)) ∘ (ψ ∘ (A.chart j).symm)) y :=
    hg2.comp y ((hτ.contDiffAt).restrict_scalars ℝ)
  have hre : ContDiffAt ℝ 2 (fun y' => ((G ∘ (A.chart j).symm) y').re) y :=
    (Complex.reCLM.contDiff.contDiffAt).comp y ((hGa.contDiffAt).restrict_scalars ℝ)
  have hN : (A.chart j).target ∩ (A.chart j).symm ⁻¹'
      (Wd ∩ P.U x ∩ P.U ((A.chart j).symm y) ∩ ψ.source) ∈ 𝓝 y :=
    ((A.chart j).isOpen_inter_preimage_symm
      (((hWo.inter (P.isOpen_U x)).inter (P.isOpen_U _)).inter ψ.open_source)).mem_nhds
      ⟨hyt, ⟨⟨hzW, hyU⟩, P.mem_U _⟩, hzs⟩
  have heq : (P.φ x ∘ (A.chart j).symm) =ᶠ[𝓝 y] fun y' =>
      ((fun t => P.φ ((A.chart j).symm y) (ψ.symm t)) ∘ (ψ ∘ (A.chart j).symm)) y' +
        1 * ((G ∘ (A.chart j).symm) y').re := by
    filter_upwards [hN] with y' hy'
    obtain ⟨-, ⟨⟨hW', hx'⟩, hz'⟩, hs'⟩ := hy'
    have := hdiff _ ⟨⟨hW', hx'⟩, hz'⟩
    simp only [Function.comp, ψ.left_inv hs', one_mul]
    linarith
  rw [levi_congr heq, levi_add_smul 1 hgc hre, levi_re_analytic hGa, levi_comp w hτ hg2, hτy]
  simpa using hpsh.2 _

end AnalyticReference.An
