import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerTranslationSeminormBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerSmallTranslationContinuityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerInvariantOperatorTranslateStatement
open scoped SchwartzMap

namespace GlobalTheory.ArchUniq

/- English proof (translation)
Take `⟨s₀, C₀, -, hT⟩` from `Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) ((SchwartzMap.seminorm ℂ a n).comp T.toLinearMap) (by exact ((schwartz_withSeminorms ℂ V₁ ℂ).continuous_seminorm (a, n)).comp T.continuous)`. Take `⟨M, s₁, C₁, hC₁, hG⟩` from `GlobalTheory.T.schrodinger_translation_seminorm_bound P hP s₀`. Establish `uniq : ∀ {f g : 𝓢(V, ℂ)}, (⇑f : V → ℂ) = ⇑g → f = g` using `fun e => DFunLike.coe_injective e`. Establish `ex : ∀ (w : V × V) (h : 𝓢(V, ℂ)), ∃ g : 𝓢(V, ℂ), ⇑g = schrF P w ⇑h` using `fun w h => (hG w h).imp fun g hg => hg.1`. Establish `mono : ∀ (t t' : Finset (ℕ × ℕ)), t ⊆ t' → ∀ f : 𝓢(V, ℂ), (t.sup (schwartzSeminormFamily ℂ V ℂ)) f ≤ (t'.sup (schwartzSeminormFamily ℂ V ℂ)) f` using `fun t t' ht f => Seminorm.le_def.1 (Finset.sup_mono ht) f`.

Establish `base : ∀ (w : V × V) (h g : 𝓢(V, ℂ)), ⇑g = schrF P w ⇑h → SchwartzMap.seminorm ℂ a n (T g) ≤ (C₀ * C₁) * (1 + ‖w‖) ^ M * (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h`. Introduce `w h g hg`. Take `⟨g', hg', hb⟩` from `hG w h`. Take `rfl : g' = g` from `uniq (hg'.trans hg.symm)`. Establish `h1 : SchwartzMap.seminorm ℂ a n (T g') ≤ (C₀ : ℝ) * (s₀.sup (schwartzSeminormFamily ℂ V ℂ)) g'`.

Use `Seminorm.le_def.1 hT g'` as an intermediate fact. Rewrite `this` using `[Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]`. Conclude with `this`. Combine the equalities or inequalities in the displayed calculation. Use `⟨M, fun N => ?_⟩` and prove the remaining obligations.

It suffices to establish `key : ∀ N : ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (w : V × V) (h g : 𝓢(V, ℂ)), ⇑g = schrF P w ⇑h → (1 + ∑ j, |omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T g) ≤ C * (1 + ‖w‖) ^ M * (s.sup (schwartzSeminormFamily ℂ V ℂ)) h by`. Take `⟨s, C, -, hC⟩` from `key N`. Conclude with `⟨s, C, hC⟩`. Introduce `N`. Proceed by induction on `N with`.

Consider the case `zero => exact ⟨s₁, C₀ * C₁, mul_nonneg C₀.2 hC₁, fun w h g hg => by simpa using base w h g hg⟩`. Consider the case `succ N ih`. Take `⟨sN, CN, hCN, hN⟩` from `ih`. Use `choose sj Cj hCj hj using fun j => GlobalTheory.T.schrodinger_small_translation_continuity P hP (U j) sN`. Set `s'` to `sN ∪ Finset.univ.biUnion sj`.

Establish `perj : ∀ (j : ι) (w : V × V) (h g : 𝓢(V, ℂ)), ⇑g = schrF P w ⇑h → |omega P w (U j)| * ((1 + ∑ j, |omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T g)) ≤ (CN / 2 + CN * Cj j / 4) * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h`. Introduce `j w h g hg`. Establish `hX : 0 ≤ (1 + ‖w‖) ^ M` using `by positivity`. Establish `hh : 0 ≤ (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h` using `apply_nonneg _ _`. Establish `hq : 0 ≤ SchwartzMap.seminorm ℂ a n (T g)` using `apply_nonneg _ _`.

Establish `hA : 0 ≤ (1 + ∑ j, |omega P w (U j)|) ^ N` using `by positivity`. Establish `hCjj` using `hCj j`. Establish `hsN` using `mono sN s' Finset.subset_union_left h`. Distinguish the cases in `hω : |omega P w (U j)| ≤ 1 / 2`. Establish `e1` using `hN w h g hg`.

Establish `e2 : 0 ≤ CN * Cj j / 4 * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h`. Check the signs of the components of the expression. Establish `e3 : CN * (1 + ‖w‖) ^ M * (sN.sup (schwartzSeminormFamily ℂ V ℂ)) h ≤ CN * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h` using `by gcongr`. Establish `e4 : |omega P w (U j)| * ((1 + ∑ j, |omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T g)) ≤ 1 / 2 * ((1 + ∑ j, |omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T g))` using `mul_le_mul_of_nonneg_right hω (by positivity)`. Use the polynomial consequences of the given equalities and inequalities.

Use `push_neg at hω`. Establish `hω0 : omega P w (U j) ≠ 0`. Introduce `h0`. Rewrite `hω` using `[h0, abs_zero]`. Evaluate the numerical expressions using `at hω`.

Use `set ω := omega P w (U j) with hωdef`. Use `set t : ℝ := 1 / (2 * ω) with htdef`. Establish `htω : t * ω = 1 / 2` using `by rw [htdef]; field_simp`. Establish `hat : |ω| * |t| = 1 / 2` using `by rw [← abs_mul, mul_comm, htω]; norm_num`. Establish `ht : |t| ≤ 1`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `: (1 : ℝ) / 2 * 1 < |ω| * |t|` using `mul_lt_mul'' hω hc (by norm_num) (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨h', hh'⟩` from `ex (t • U j) h`.

Take `⟨g₁, hg₁⟩` from `ex w h'`. Take `⟨gd, hgd⟩` from `ex w (h' - h)`. Establish `egd : gd = g₁ - g` using `uniq (by`. Rewrite using `[hgd]`. Use function extensionality and compare the values at `y`.

Rewrite using `[SchwartzMap.sub_apply, congrFun hg₁ y, congrFun hg y]`. Simplify using `[schrF, mul_sub])`. Establish `e3` using `GlobalTheory.T.schrodinger_invariant_operator_translate P hP T (U j) (hU j) w t h h' g g₁ hh' hg hg₁`. Establish `hexp : Complex.exp (-(2 * Real.pi * Complex.I) * ((t * ω : ℝ) : ℂ)) = -1`. Rewrite using `[htω]`.

Use `push_cast`. Rewrite using `[show -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2 : ℂ) = -(Real.pi * Complex.I) by ring, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num`. Rewrite `e3` using `[hexp, neg_one_smul]`. Establish `eT : T gd = (-2 : ℂ) • T g`. Rewrite using `[egd, map_sub, e3, neg_smul, two_smul]`.

Normalize the expressions using the abelian group laws. Establish `hqd : SchwartzMap.seminorm ℂ a n (T gd) = 2 * SchwartzMap.seminorm ℂ a n (T g)`. Rewrite using `[eT, map_smul_eq_mul]`. Evaluate the numerical expressions. Establish `hd` using `hj j t ht h h' hh'`.

Establish `hN'` using `hN w (h' - h) gd hgd`. Establish `hsj : ((sj j).sup (schwartzSeminormFamily ℂ V ℂ)) h ≤ (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h` using `mono _ _ ((Finset.subset_biUnion_of_mem sj (Finset.mem_univ j)).trans Finset.subset_union_right) h`. Establish `hsupd : 0 ≤ (sN.sup (schwartzSeminormFamily ℂ V ℂ)) (h' - h)` using `apply_nonneg _ _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hqd]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ |ω| / 2 * (CN * (1 + ‖w‖) ^ M * (sN.sup (schwartzSeminormFamily ℂ V ℂ)) (h' - h)) := by gcongr`. Use `_ ≤ |ω| / 2 * (CN * (1 + ‖w‖) ^ M * (Cj j * |t| * ((sj j).sup (schwartzSeminormFamily ℂ V ℂ)) h)) := by gcongr`. Use `_ = CN * Cj j / 4 * (1 + ‖w‖) ^ M * ((sj j).sup (schwartzSeminormFamily ℂ V ℂ)) h := by`. Take the linear combination `(CN * (1 + ‖w‖) ^ M * Cj j * ((sj j).sup (schwartzSeminormFamily ℂ V ℂ)) h / 2) * hat`.

Use `_ ≤ CN * Cj j / 4 * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h := by gcongr`. Use `_ ≤ _ := by`. Establish `: 0 ≤ CN / 2 * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h`. Check the signs of the components of the expression. Use the polynomial consequences of the given equalities and inequalities.

Use `⟨s', CN + ∑ j, (CN / 2 + CN * Cj j / 4), ?_, ?_⟩` and prove the remaining obligations. Use `fun j => hCj j` as an intermediate fact. Establish `: 0 ≤ ∑ j, (CN / 2 + CN * Cj j / 4)` using `Finset.sum_nonneg fun j _ => by have := hCj j; positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `w h g hg`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pow_succ, ← Finset.sum_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ CN * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h + ∑ j, (CN / 2 + CN * Cj j / 4) * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h := by`. Use `add_le_add ((hN w h g hg).trans ?_) (Finset.sum_le_sum fun j _ => perj j w h g hg)` and prove the remaining obligations.

Use `gcongr`. Conclude with `mono sN s' Finset.subset_union_left h`. Use `_ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring`.
-/
theorem rapidDecay_omega_of_invariant {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] (P : V → V → ℝ)
    (hP : IsPairing P) (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V₁ ℂ) {ι : Type} [Fintype ι]
    (U : ι → V × V)
    (hU : ∀ (j : ι) (s : ℝ) (f g : SchwartzMap V ℂ), ⇑g = schrF P (s • U j) ⇑f → T g = T f)
    (a n : ℕ) : ∃ M : ℕ, ∀ N : ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), ∀ (w : V × V)
      (h g : SchwartzMap V ℂ), ⇑g = schrF P w ⇑h →
      (1 + ∑ j, |omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T g) ≤
        C * (1 + ‖w‖) ^ M * (s.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
  classical
  obtain ⟨s₀, C₀, -, hT⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ)
    ((SchwartzMap.seminorm ℂ a n).comp T.toLinearMap)
    (by exact ((schwartz_withSeminorms ℂ V₁ ℂ).continuous_seminorm (a, n)).comp T.continuous)
  obtain ⟨M, s₁, C₁, hC₁, hG⟩ := GlobalTheory.T.schrodinger_translation_seminorm_bound P hP s₀
  have uniq : ∀ {f g : 𝓢(V, ℂ)}, (⇑f : V → ℂ) = ⇑g → f = g := fun e => DFunLike.coe_injective e
  have ex : ∀ (w : V × V) (h : 𝓢(V, ℂ)), ∃ g : 𝓢(V, ℂ), ⇑g = schrF P w ⇑h :=
    fun w h => (hG w h).imp fun g hg => hg.1
  have mono : ∀ (t t' : Finset (ℕ × ℕ)), t ⊆ t' → ∀ f : 𝓢(V, ℂ),
      (t.sup (schwartzSeminormFamily ℂ V ℂ)) f ≤ (t'.sup (schwartzSeminormFamily ℂ V ℂ)) f :=
    fun t t' ht f => Seminorm.le_def.1 (Finset.sup_mono ht) f
  have base : ∀ (w : V × V) (h g : 𝓢(V, ℂ)), ⇑g = schrF P w ⇑h →
      SchwartzMap.seminorm ℂ a n (T g) ≤
        (C₀ * C₁) * (1 + ‖w‖) ^ M * (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
    intro w h g hg
    obtain ⟨g', hg', hb⟩ := hG w h
    obtain rfl : g' = g := uniq (hg'.trans hg.symm)
    have h1 : SchwartzMap.seminorm ℂ a n (T g') ≤
        (C₀ : ℝ) * (s₀.sup (schwartzSeminormFamily ℂ V ℂ)) g' := by
      have := Seminorm.le_def.1 hT g'
      rw [Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at this
      exact this
    calc _ ≤ (C₀ : ℝ) * (s₀.sup (schwartzSeminormFamily ℂ V ℂ)) g' := h1
      _ ≤ (C₀ : ℝ) * (C₁ * (1 + ‖w‖) ^ M * (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h) :=
          mul_le_mul_of_nonneg_left hb C₀.2
      _ = _ := by ring
  refine ⟨M, fun N => ?_⟩
  suffices key : ∀ N : ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (w : V × V) (h g : 𝓢(V, ℂ)),
      ⇑g = schrF P w ⇑h → (1 + ∑ j, |omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T g) ≤
        C * (1 + ‖w‖) ^ M * (s.sup (schwartzSeminormFamily ℂ V ℂ)) h by
    obtain ⟨s, C, -, hC⟩ := key N
    exact ⟨s, C, hC⟩
  intro N
  induction N with
  | zero => exact ⟨s₁, C₀ * C₁, mul_nonneg C₀.2 hC₁, fun w h g hg => by simpa using base w h g hg⟩
  | succ N ih =>
    obtain ⟨sN, CN, hCN, hN⟩ := ih
    choose sj Cj hCj hj using fun j => GlobalTheory.T.schrodinger_small_translation_continuity P hP (U j) sN
    let s' := sN ∪ Finset.univ.biUnion sj
    have perj : ∀ (j : ι) (w : V × V) (h g : 𝓢(V, ℂ)), ⇑g = schrF P w ⇑h →
        |omega P w (U j)| * ((1 + ∑ j, |omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T g)) ≤
          (CN / 2 + CN * Cj j / 4) * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
      intro j w h g hg
      have hX : 0 ≤ (1 + ‖w‖) ^ M := by positivity
      have hh : 0 ≤ (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h := apply_nonneg _ _
      have hq : 0 ≤ SchwartzMap.seminorm ℂ a n (T g) := apply_nonneg _ _
      have hA : 0 ≤ (1 + ∑ j, |omega P w (U j)|) ^ N := by positivity
      have hCjj := hCj j
      have hsN := mono sN s' Finset.subset_union_left h
      by_cases hω : |omega P w (U j)| ≤ 1 / 2
      · have e1 := hN w h g hg
        have e2 : 0 ≤ CN * Cj j / 4 * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
          positivity
        have e3 : CN * (1 + ‖w‖) ^ M * (sN.sup (schwartzSeminormFamily ℂ V ℂ)) h ≤
            CN * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h := by gcongr
        have e4 : |omega P w (U j)| * ((1 + ∑ j, |omega P w (U j)|) ^ N *
            SchwartzMap.seminorm ℂ a n (T g)) ≤ 1 / 2 * ((1 + ∑ j, |omega P w (U j)|) ^ N *
            SchwartzMap.seminorm ℂ a n (T g)) := mul_le_mul_of_nonneg_right hω (by positivity)
        nlinarith
      · push_neg at hω
        have hω0 : omega P w (U j) ≠ 0 := by
          intro h0; rw [h0, abs_zero] at hω; norm_num at hω
        set ω := omega P w (U j) with hωdef
        set t : ℝ := 1 / (2 * ω) with htdef
        have htω : t * ω = 1 / 2 := by rw [htdef]; field_simp
        have hat : |ω| * |t| = 1 / 2 := by rw [← abs_mul, mul_comm, htω]; norm_num
        have ht : |t| ≤ 1 := by
          by_contra hc; push_neg at hc
          have : (1 : ℝ) / 2 * 1 < |ω| * |t| := mul_lt_mul'' hω hc (by norm_num) (by norm_num)
          linarith
        obtain ⟨h', hh'⟩ := ex (t • U j) h
        obtain ⟨g₁, hg₁⟩ := ex w h'
        obtain ⟨gd, hgd⟩ := ex w (h' - h)
        have egd : gd = g₁ - g := uniq (by
          rw [hgd]; funext y
          rw [SchwartzMap.sub_apply, congrFun hg₁ y, congrFun hg y]
          simp [schrF, mul_sub])
        have e3 := GlobalTheory.T.schrodinger_invariant_operator_translate P hP T (U j) (hU j) w t h h' g g₁ hh' hg hg₁
        have hexp : Complex.exp (-(2 * Real.pi * Complex.I) * ((t * ω : ℝ) : ℂ)) = -1 := by
          rw [htω]; push_cast
          rw [show -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2 : ℂ) = -(Real.pi * Complex.I) by ring,
            Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
        rw [hexp, neg_one_smul] at e3
        have eT : T gd = (-2 : ℂ) • T g := by
          rw [egd, map_sub, e3, neg_smul, two_smul]; abel
        have hqd : SchwartzMap.seminorm ℂ a n (T gd) = 2 * SchwartzMap.seminorm ℂ a n (T g) := by
          rw [eT, map_smul_eq_mul]; norm_num
        have hd := hj j t ht h h' hh'
        have hN' := hN w (h' - h) gd hgd
        have hsj : ((sj j).sup (schwartzSeminormFamily ℂ V ℂ)) h ≤
            (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h :=
          mono _ _ ((Finset.subset_biUnion_of_mem sj (Finset.mem_univ j)).trans
            Finset.subset_union_right) h
        have hsupd : 0 ≤ (sN.sup (schwartzSeminormFamily ℂ V ℂ)) (h' - h) := apply_nonneg _ _
        calc |ω| * ((1 + ∑ j, |omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T g))
            = |ω| / 2 * ((1 + ∑ j, |omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T gd)) := by
              rw [hqd]; ring
          _ ≤ |ω| / 2 * (CN * (1 + ‖w‖) ^ M * (sN.sup (schwartzSeminormFamily ℂ V ℂ)) (h' - h)) := by
              gcongr
          _ ≤ |ω| / 2 * (CN * (1 + ‖w‖) ^ M *
                (Cj j * |t| * ((sj j).sup (schwartzSeminormFamily ℂ V ℂ)) h)) := by gcongr
          _ = CN * Cj j / 4 * (1 + ‖w‖) ^ M * ((sj j).sup (schwartzSeminormFamily ℂ V ℂ)) h := by
              linear_combination (CN * (1 + ‖w‖) ^ M * Cj j *
                ((sj j).sup (schwartzSeminormFamily ℂ V ℂ)) h / 2) * hat
          _ ≤ CN * Cj j / 4 * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
              gcongr
          _ ≤ _ := by
              have : 0 ≤ CN / 2 * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
                positivity
              nlinarith
    refine ⟨s', CN + ∑ j, (CN / 2 + CN * Cj j / 4), ?_, ?_⟩
    · have := fun j => hCj j
      have : 0 ≤ ∑ j, (CN / 2 + CN * Cj j / 4) :=
        Finset.sum_nonneg fun j _ => by have := hCj j; positivity
      linarith
    intro w h g hg
    calc (1 + ∑ j, |omega P w (U j)|) ^ (N + 1) * SchwartzMap.seminorm ℂ a n (T g)
        = (1 + ∑ j, |omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T g) +
          ∑ j, |omega P w (U j)| *
            ((1 + ∑ j, |omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T g)) := by
          rw [pow_succ, ← Finset.sum_mul]; ring
      _ ≤ CN * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h +
          ∑ j, (CN / 2 + CN * Cj j / 4) * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
          refine add_le_add ((hN w h g hg).trans ?_) (Finset.sum_le_sum fun j _ => perj j w h g hg)
          gcongr
          exact mono sN s' Finset.subset_union_left h
      _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

end GlobalTheory.ArchUniq
