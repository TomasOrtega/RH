import Formalism.HermitianCurvature.StatementJCCpt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.JCx5

section partE

open Formalism.FourierDecayAlt.P.JCx2 Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JCx4

/- English proof (translation)
Use `haveI : ProperSpace (Mat k r) := FiniteDimensional.proper_real _`. Take `⟨X, hXc, hXs, hXe, hXQ⟩` from `extend mm F hF z z' ε hε hsupp R hR`. Take `⟨Cb, hCb0, hCb⟩` from `dlr_bound (k := k) (r := r) (E := E) m0`. Choose the witnesses or unpack the hypotheses as in `⟨ρX, hρX⟩ : ∃ ρX : ℝ, ∀ g, X g ≠ 0 → ‖g‖ ≤ ρX := by`. Take `⟨ρ, hρ⟩` from `hXs.isCompact.isBounded.subset_closedBall (0 : Mat k r)`.

Conclude with `⟨ρ, fun g hg => by simpa using hρ (subset_tsupport _ hg)⟩`. Establish `hBc : IsCompact (Metric.closedBall (0 : Mat k r) (ρX + 1))` using `isCompact_closedBall _ _`. Establish `hGf : Continuous fun g : Mat k r => Gf k r z z' g` using `Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.gf_cont k r z z'`. Take `⟨δ₁, hδ₁, hδ₁'⟩` from `Metric.uniformContinuousOn_iff.1 (hBc.uniformContinuousOn_of_continuous hGf.continuousOn) (ε / 4) (by positivity)`. Establish `hgN : Continuous fun g : Mat k r => gN g` using `by unfold gN; fun_prop`.

Establish `hWc : Continuous fun g : Mat k r => gN g ^ A' * (1 + ‖g‖) ^ m0` using `((Real.continuous_rpow_const hA').comp hgN).mul (by fun_prop)`. Take `⟨W₀, hW₀⟩` from `hBc.exists_bound_of_continuousOn hWc.continuousOn`. Use `set W : ℝ := max W₀ 0 with hWdef`. Establish `hW : 0 ≤ W` using `le_max_right _ _`. Establish `hden : 0 < Cb * W * (m0 + 1) + 1`.

Establish `: 0 ≤ Cb * W * ((m0 : ℝ) + 1)` using `mul_nonneg (mul_nonneg hCb0 hW) (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set η : ℝ := τ / (Cb * W * (m0 + 1) + 1) with hηdef`. Establish `hη : 0 < η` using `div_pos hτ hden`. Establish `hCbη : Cb * W * (m0 + 1) * η ≤ τ`.

Rewrite using `[hηdef, mul_div_assoc']`. Rewrite using `[div_le_iff₀ hden]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hm0' : ((m0 : ℕ∞) : WithTop ℕ∞) ≤ ((mm : ℕ∞) : WithTop ℕ∞)` using `WithTop.coe_le_coe.2 (by exact_mod_cast hm0)`. Establish `htop : ∀ n : ℕ, ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)` using `fun n => WithTop.coe_le_coe.2 le_top`.

Take `⟨y, hys, hyc, hysupp, hyd⟩` from `mollify m0 X (hXc.of_le hm0') hXs η (min 1 δ₁) hη (lt_min one_pos hδ₁)`. Establish `hyB : ∀ g, y g ≠ 0 → ‖g‖ < ρX + 1`. Introduce `g hg`. Take `⟨g', hd, hX'⟩` from `hysupp g hg`. Establish `h1` using `hρX g' hX'`.

Establish `h2 : ‖g‖ ≤ ‖g'‖ + ‖g - g'‖`. Use `norm_add_le g' (g - g')` as an intermediate fact. Simplify using `using this`. Rewrite `hd` using `[dist_eq_norm]`. Establish `h3 : ‖g - g'‖ < 1` using `lt_of_lt_of_le hd (min_le_left _ _)`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨y, fun g₀ _ => ⟨Set.univ, y, isOpen_univ, trivial, hys.contDiffOn, fun _ _ _ => rfl⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `A'' m'`. Use `Formalism.FourierDecayAlt.P.compact_support_finite_class k r E y (Metric.closedBall 0 (ρX + 1)) (fun g₀ _ => ⟨Set.univ, y, isOpen_univ, trivial, hys.contDiffOn, fun _ _ _ => rfl⟩) hBc (fun g hg => ?_) A'' m'` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Conclude with `hg (mem_closedBall_zero_iff.2 (le_of_lt (hyB g h)))`. Introduce `g _ hy0`. Take `⟨g', hd, hX'⟩` from `hysupp g hy0`. Establish `h1` using `hXQ g' hX'`. Establish `hg'B : g' ∈ Metric.closedBall (0 : Mat k r) (ρX + 1)` using `mem_closedBall_zero_iff.2 (by linarith [hρX g' hX'])`.

Establish `hgB : g ∈ Metric.closedBall (0 : Mat k r) (ρX + 1)` using `mem_closedBall_zero_iff.2 (le_of_lt (hyB g hy0))`. Establish `h2` using `hδ₁' g hgB g' hg'B (lt_of_lt_of_le hd (min_le_right _ _))`. Rewrite `h2` using `[Real.dist_eq, abs_sub_lt_iff]`. Combine the linear relations using `[h2.2]`. Establish `hXY : CCle A' m0 (fun g => X g - y g) τ`.

Establish `hcd : ContDiff ℝ ((m0 : ℕ∞) : WithTop ℕ∞) (fun g => X g - y g)` using `(hXc.of_le hm0').sub (hys.of_le (htop m0))`. Use `⟨fun g₀ _ => ⟨Set.univ, fun g => X g - y g, isOpen_univ, trivial, hcd.contDiffOn, fun _ _ _ => rfl⟩, ?_⟩` and prove the remaining obligations. Introduce `u v hu hv hl g _`. Establish `hb` using `hCb (fun g => X g - y g) hcd u v hu hv hl g`. Establish `hgN0 : 0 ≤ gN g ^ A'` using `Real.rpow_nonneg (Real.sqrt_nonneg _) _`.

Distinguish the cases in `hgB : ‖g‖ ≤ ρX + 1`. Establish `hi : ∀ i ∈ Finset.range (m0 + 1), ‖iteratedFDeriv ℝ i (fun g => X g - y g) g‖ ≤ η`. Introduce `i hi`. Establish `hi' : i ≤ m0` using `by simpa [Nat.lt_succ_iff] using hi`. Establish `e1 : iteratedFDeriv ℝ i (fun g => X g - y g) g = iteratedFDeriv ℝ i X g - iteratedFDeriv ℝ i y g` using `iteratedFDeriv_sub_apply ((hXc.of_le (le_trans (WithTop.coe_le_coe.2 (by exact_mod_cast hi')) hm0')).contDiffAt) ((hys.of_le (htop i)).contDiffAt)`.

Rewrite using `[e1, norm_sub_rev]`. Conclude with `hyd i hi' g`. Establish `hsum : ∑ i ∈ Finset.range (m0 + 1), ‖iteratedFDeriv ℝ i (fun g => X g - y g) g‖ ≤ (m0 + 1) * η`. Use `Finset.sum_le_card_nsmul _ _ _ hi` as an intermediate fact. Simplify `this` using `[Finset.card_range, nsmul_eq_mul]`.

Establish `hWg : gN g ^ A' * (1 + ‖g‖) ^ m0 ≤ W`. Use `hW₀ g (mem_closedBall_zero_iff.2 hgB)` as an intermediate fact. Conclude with `le_trans (le_abs_self _) (le_trans (by simpa [Real.norm_eq_abs] using this) (le_max_left _ _))`. Establish `h1p : 0 ≤ (1 + ‖g‖) ^ m0` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Establish `: 0 ≤ ((m0 : ℝ) + 1) * η` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hWg hCb0]`. Use `_ ≤ τ := hCbη`. Establish `hev : (fun g => X g - y g) =ᶠ[nhds g] fun _ => (0 : E)` using `by filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds (not_le.1 hgB)] with g' hg'`. Establish `hX0 : X g' = 0`.

Assume the negation of the conclusion as `h`. Use `hρX g' h` as an intermediate fact. Establish `hg'' : ρX + 1 < ‖g'‖` using `hg'`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hy0 : y g' = 0`.

Assume the negation of the conclusion as `h`. Use `hyB g' h` as an intermediate fact. Establish `hg'' : ρX + 1 < ‖g'‖` using `hg'`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `[hX0, hy0]`.

Establish `hz : ∀ i, iteratedFDeriv ℝ i (fun g => X g - y g) g = 0`. Introduce `i`. Rewrite using `[(hev.iteratedFDeriv ℝ i).eq_of_nhds]`. Simplify using the standard rewrite rules. Simplify using `only [hz, norm_zero, Finset.sum_const_zero, mul_zero] at hb`.

Establish `: ‖dLR u v (fun g => X g - y g) g‖ = 0` using `le_antisymm hb (norm_nonneg _)`. Rewrite using `[this, mul_zero]`. Conclude with `hτ.le`. Conclude with `Formalism.FourierDecayAlt.P.JCx2.mn_ccle_congr (fun g hg => by simp only [hXe g hg]) hXY`. Use `HasCompactSupport.intro hBc fun g hg => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `h`. Conclude with `hg (mem_closedBall_zero_iff.2 (le_of_lt (hyB g h)))`.
-/
theorem me_approx_one_cpt {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (mm m0 : ℕ) (hm0 : m0 ≤ mm) (A' : ℝ) (hA' : 0 ≤ A') (F : Mat k r → E) (hF : CkOn (mm : ℕ∞) (GV k r) F)
    (z z' : Fin (2 * r + k + 1) → ℂ) (ε : ℝ) (hε : 0 < ε) (hsupp : ∀ g ∈ GV k r, F g ≠ 0 → ε ≤ Gf k r z z' g)
    (R τ : ℝ) (hR : 0 < R) (hτ : 0 < τ) :
    ∃ y : Mat k r → E, CkOn (⊤ : ℕ∞) (GV k r) y ∧ (∀ (A'' : ℝ) (m' : ℕ), InCC A'' m' y) ∧
      (∀ g ∈ GV k r, y g ≠ 0 → ε / 4 ≤ Gf k r z z' g) ∧
      CCle A' m0 (fun g => pdPhi (R⁻¹ • g) • F g - y g) τ ∧ HasCompactSupport y := by
  haveI : ProperSpace (Mat k r) := FiniteDimensional.proper_real _
  obtain ⟨X, hXc, hXs, hXe, hXQ⟩ := extend mm F hF z z' ε hε hsupp R hR
  obtain ⟨Cb, hCb0, hCb⟩ := dlr_bound (k := k) (r := r) (E := E) m0
  obtain ⟨ρX, hρX⟩ : ∃ ρX : ℝ, ∀ g, X g ≠ 0 → ‖g‖ ≤ ρX := by
    obtain ⟨ρ, hρ⟩ := hXs.isCompact.isBounded.subset_closedBall (0 : Mat k r)
    exact ⟨ρ, fun g hg => by simpa using hρ (subset_tsupport _ hg)⟩
  have hBc : IsCompact (Metric.closedBall (0 : Mat k r) (ρX + 1)) := isCompact_closedBall _ _
  have hGf : Continuous fun g : Mat k r => Gf k r z z' g := Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.gf_cont k r z z'
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.uniformContinuousOn_iff.1
    (hBc.uniformContinuousOn_of_continuous hGf.continuousOn) (ε / 4) (by positivity)
  have hgN : Continuous fun g : Mat k r => gN g := by unfold gN; fun_prop
  have hWc : Continuous fun g : Mat k r => gN g ^ A' * (1 + ‖g‖) ^ m0 :=
    ((Real.continuous_rpow_const hA').comp hgN).mul (by fun_prop)
  obtain ⟨W₀, hW₀⟩ := hBc.exists_bound_of_continuousOn hWc.continuousOn
  set W : ℝ := max W₀ 0 with hWdef
  have hW : 0 ≤ W := le_max_right _ _
  have hden : 0 < Cb * W * (m0 + 1) + 1 := by
    have : 0 ≤ Cb * W * ((m0 : ℝ) + 1) := mul_nonneg (mul_nonneg hCb0 hW) (by positivity)
    linarith
  set η : ℝ := τ / (Cb * W * (m0 + 1) + 1) with hηdef
  have hη : 0 < η := div_pos hτ hden
  have hCbη : Cb * W * (m0 + 1) * η ≤ τ := by
    rw [hηdef, mul_div_assoc']
    rw [div_le_iff₀ hden]
    nlinarith
  have hm0' : ((m0 : ℕ∞) : WithTop ℕ∞) ≤ ((mm : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 (by exact_mod_cast hm0)
  have htop : ∀ n : ℕ, ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun n => WithTop.coe_le_coe.2 le_top
  obtain ⟨y, hys, hyc, hysupp, hyd⟩ := mollify m0 X (hXc.of_le hm0') hXs η (min 1 δ₁) hη (lt_min one_pos hδ₁)
  have hyB : ∀ g, y g ≠ 0 → ‖g‖ < ρX + 1 := by
    intro g hg
    obtain ⟨g', hd, hX'⟩ := hysupp g hg
    have h1 := hρX g' hX'
    have h2 : ‖g‖ ≤ ‖g'‖ + ‖g - g'‖ := by
      have := norm_add_le g' (g - g')
      simpa using this
    rw [dist_eq_norm] at hd
    have h3 : ‖g - g'‖ < 1 := lt_of_lt_of_le hd (min_le_left _ _)
    linarith
  refine ⟨y, fun g₀ _ => ⟨Set.univ, y, isOpen_univ, trivial, hys.contDiffOn, fun _ _ _ => rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro A'' m'
    refine Formalism.FourierDecayAlt.P.compact_support_finite_class k r E y (Metric.closedBall 0 (ρX + 1))
      (fun g₀ _ => ⟨Set.univ, y, isOpen_univ, trivial, hys.contDiffOn, fun _ _ _ => rfl⟩) hBc (fun g hg => ?_) A'' m'
    by_contra h
    exact hg (mem_closedBall_zero_iff.2 (le_of_lt (hyB g h)))
  · intro g _ hy0
    obtain ⟨g', hd, hX'⟩ := hysupp g hy0
    have h1 := hXQ g' hX'
    have hg'B : g' ∈ Metric.closedBall (0 : Mat k r) (ρX + 1) :=
      mem_closedBall_zero_iff.2 (by linarith [hρX g' hX'])
    have hgB : g ∈ Metric.closedBall (0 : Mat k r) (ρX + 1) := mem_closedBall_zero_iff.2 (le_of_lt (hyB g hy0))
    have h2 := hδ₁' g hgB g' hg'B (lt_of_lt_of_le hd (min_le_right _ _))
    rw [Real.dist_eq, abs_sub_lt_iff] at h2
    linarith [h2.2]
  · have hXY : CCle A' m0 (fun g => X g - y g) τ := by
      have hcd : ContDiff ℝ ((m0 : ℕ∞) : WithTop ℕ∞) (fun g => X g - y g) := (hXc.of_le hm0').sub (hys.of_le (htop m0))
      refine ⟨fun g₀ _ => ⟨Set.univ, fun g => X g - y g, isOpen_univ, trivial, hcd.contDiffOn, fun _ _ _ => rfl⟩, ?_⟩
      intro u v hu hv hl g _
      have hb := hCb (fun g => X g - y g) hcd u v hu hv hl g
      have hgN0 : 0 ≤ gN g ^ A' := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      by_cases hgB : ‖g‖ ≤ ρX + 1
      · have hi : ∀ i ∈ Finset.range (m0 + 1), ‖iteratedFDeriv ℝ i (fun g => X g - y g) g‖ ≤ η := by
          intro i hi
          have hi' : i ≤ m0 := by simpa [Nat.lt_succ_iff] using hi
          have e1 : iteratedFDeriv ℝ i (fun g => X g - y g) g = iteratedFDeriv ℝ i X g - iteratedFDeriv ℝ i y g :=
            iteratedFDeriv_sub_apply ((hXc.of_le (le_trans (WithTop.coe_le_coe.2 (by exact_mod_cast hi')) hm0')).contDiffAt)
              ((hys.of_le (htop i)).contDiffAt)
          rw [e1, norm_sub_rev]
          exact hyd i hi' g
        have hsum : ∑ i ∈ Finset.range (m0 + 1), ‖iteratedFDeriv ℝ i (fun g => X g - y g) g‖ ≤ (m0 + 1) * η := by
          have := Finset.sum_le_card_nsmul _ _ _ hi
          simpa [Finset.card_range, nsmul_eq_mul] using this
        have hWg : gN g ^ A' * (1 + ‖g‖) ^ m0 ≤ W := by
          have := hW₀ g (mem_closedBall_zero_iff.2 hgB)
          exact le_trans (le_abs_self _) (le_trans (by simpa [Real.norm_eq_abs] using this) (le_max_left _ _))
        have h1p : 0 ≤ (1 + ‖g‖) ^ m0 := by positivity
        calc gN g ^ A' * ‖dLR u v (fun g => X g - y g) g‖
            ≤ gN g ^ A' * (Cb * (1 + ‖g‖) ^ m0 * ((m0 + 1) * η)) :=
              mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hsum (mul_nonneg hCb0 h1p))) hgN0
          _ = Cb * (gN g ^ A' * (1 + ‖g‖) ^ m0) * (m0 + 1) * η := by ring
          _ ≤ Cb * W * (m0 + 1) * η := by
              have : 0 ≤ ((m0 : ℝ) + 1) * η := by positivity
              nlinarith [mul_le_mul_of_nonneg_left hWg hCb0]
          _ ≤ τ := hCbη
      · have hev : (fun g => X g - y g) =ᶠ[nhds g] fun _ => (0 : E) := by
          filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds (not_le.1 hgB)] with g' hg'
          have hX0 : X g' = 0 := by
            by_contra h
            have := hρX g' h
            have hg'' : ρX + 1 < ‖g'‖ := hg'
            linarith
          have hy0 : y g' = 0 := by
            by_contra h
            have := hyB g' h
            have hg'' : ρX + 1 < ‖g'‖ := hg'
            linarith
          simp [hX0, hy0]
        have hz : ∀ i, iteratedFDeriv ℝ i (fun g => X g - y g) g = 0 := by
          intro i
          rw [(hev.iteratedFDeriv ℝ i).eq_of_nhds]
          simp
        simp only [hz, norm_zero, Finset.sum_const_zero, mul_zero] at hb
        have : ‖dLR u v (fun g => X g - y g) g‖ = 0 := le_antisymm hb (norm_nonneg _)
        rw [this, mul_zero]
        exact hτ.le
    exact Formalism.FourierDecayAlt.P.JCx2.mn_ccle_congr (fun g hg => by simp only [hXe g hg]) hXY
  · refine HasCompactSupport.intro hBc fun g hg => ?_
    by_contra h
    exact hg (mem_closedBall_zero_iff.2 (le_of_lt (hyB g h)))

end partE

end Formalism.FourierDecayAlt.P.JCx5

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.JCx2 Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JCx4 Formalism.FourierDecayAlt.P.JCx5

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P0 T s j w A mm ε hε hA hmm H x hx`. Establish `hm0 : 5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ mm` using `pd_thr_mm P0 j w.length mm hmm`. Establish `hAB` using `pd_thr_AB P0 j w.length A hA`. Establish `hN0 : (0 : ℝ) ≤ w.length` using `Nat.cast_nonneg _`. Establish `hAB0 : 0 < AB P0.k (P0.r - (j : ℕ))` using `by unfold AB; positivity`.

Establish `hA1 : 0 ≤ A - 1` using `by linarith`. Use `choose cx hcx using fun a => (hx a).2.1`. Establish `hcx0 : ∀ a, 0 ≤ cx a` using `fun a => pd_ccle_nonneg (hcx a)`. Use `set c0 : ℝ := ∑ a, cx a with hc0def`. Establish `hc0 : 0 ≤ c0` using `Finset.sum_nonneg fun a _ => hcx0 a`.

Establish `hX : ∀ a, CCle A mm (x a) c0` using `fun a => pd_ccle_mono_c (hcx a) (Finset.single_le_sum (f := cx) (fun b _ => hcx0 b) (Finset.mem_univ a))`. Take `⟨Cf, hCf0, hCf⟩` from `formLev_bound_mm P0 T s j w A hA`. Take `⟨Kc, hKc0, hKc⟩` from `pd_cut_ccle (k := P0.k) (r := P0.r - j) (E := Wq →L[ℂ] Wp) mm`. Use `pd_nonneg_of_approx _ (Cf * (2 * c0 + 1)) fun R hR1 => ?_` and prove the remaining obligations. Establish `hR0 : 0 < R` using `lt_of_lt_of_le one_pos hR1`.

Use `set τ : ℝ := 1 / R with hτdef`. Establish `hτ : 0 < τ` using `by positivity`. Establish `hτ1 : τ ≤ 1` using `by rw [hτdef, div_le_one hR0]; exact hR1`. Use `set R' : ℝ := max 1 (2 * Kc * c0 / τ) with hR'def`. Establish `hR' : 0 < R'` using `lt_of_lt_of_le one_pos (le_max_left _ _)`.

Establish `hcut : Kc * c0 / R' ≤ τ / 2`. Rewrite using `[div_le_iff₀ hR']`. Establish `h1 : 2 * Kc * c0 / τ ≤ R'` using `le_max_right _ _`. Rewrite `h1` using `[div_le_iff₀ hτ]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `happ` using `fun a => me_approx_one_cpt mm _ hm0 (A - 1) hA1 (x a) (hx a).1 (T.bs j).z (T.bs j).z' ε hε (hx a).2.2 R' (τ / 2) hR' (by positivity)`. Use `choose y hyck hyin hysupp hycc hycpt using happ`. Establish `hpos` using `H (ε / 4) (by positivity) y fun a => ⟨⟨hyck a, hyin a, hysupp a⟩, hycpt a⟩`. Use `set e : Wd.Ix (Fin w.length) → Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp) := x - y with hedef`. Establish `he : ∀ a, CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (e a) τ`.

Introduce `a`. Establish `h1` using `pd_ccle_mono le_rfl hm0 (hKc R' hR' A (x a) c0 (hX a))`. Establish `h2` using `CCle_add h1 (hycc a)`. Establish `e2 : (fun g => pdPsi R' g • x a g + (pdPhi (R'⁻¹ • g) • x a g - y a g)) = e a`. Use function extensionality and compare the values at `g`.

Simplify using `only [hedef, Pi.sub_apply, pdPsi, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite `h2` using `[e2]`. Conclude with `pd_ccle_mono_c h2 (by linarith)`. Establish `hx1 : ∀ a, CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (x a) c0` using `fun a => pd_ccle_mono (by linarith) hm0 (hX a)`.

Establish `hy1 : ∀ a, CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (y a) (c0 + τ)`. Introduce `a`. Establish `h` using `CCle_add (hx1 a) (CCle_smul (-1) (he a))`. Establish `e3 : (fun g => x a g + (-1 : ℂ) • e a g) = y a`. Use function extensionality and compare the values at `g`.

Simplify using `only [hedef, Pi.sub_apply, neg_smul, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite `h` using `[e3]`. Simplify using `using h`. Establish `hv : ∀ {F : Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)} {c : ℝ}, CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) F c → CCle (A - 1 - 2 * (w.length : ℝ)) 5 F c` using `fun h => pd_ccle_mono (by linarith) (by omega) h`.

Establish `hxI : ∀ a, InCC A mm (x a)` using `fun a => (hx a).2.1`. Establish `hyI : ∀ a, InCC A mm (y a)` using `fun a => hyin a A mm`. Establish `heI : ∀ a, InCC A mm (e a)`. Introduce `a`. Take `⟨c1, h1⟩` from `hxI a`.

Take `⟨c2, h2⟩` from `hyI a`. Establish `h` using `CCle_add h1 (CCle_smul (-1) h2)`. Establish `e4 : (fun g => x a g + (-1 : ℂ) • y a g) = e a`. Use function extensionality and compare the values at `g`. Simplify using `only [hedef, Pi.sub_apply, neg_smul, one_smul]`.

Normalize the expressions using the abelian group laws. Rewrite `h` using `[e4]`. Conclude with `⟨_, h⟩`. Establish `hsplit : y + (1 : ℂ) • e = x`. Use function extensionality and compare the values at `a g`.

Simplify using `only [hedef, Pi.add_apply, Pi.sub_apply, one_smul]`. Normalize the expressions using the abelian group laws. Establish `hS1` using `(formLev_sesq_core P0 T s j w A mm hA hmm y e x 1 hyI heI hxI).1`. Establish `hS2` using `(formLev_sesq_core P0 T s j w A mm hA hmm y e y 1 hyI heI hyI).2`. Rewrite `hS1`, `hS2` using `[hsplit]`.

Use `⟨D.formLev T s j w y y, hpos, ?_⟩` and prove the remaining obligations. Establish `hb1` using `hCf y e (c0 + τ) τ hy1 fun a => hv (he a)`. Establish `hb2` using `hCf e x τ c0 he fun a => hv (hx1 a)`. Rewrite using `[hS1, hS2, map_one, one_mul, one_mul]`. Establish `e5 : D.formLev T s j w y y + D.formLev T s j w y e + D.formLev T s j w e x - D.formLev T s j w y y = D.formLev T s j w y e + D.formLev T s j w e x` using `by ring`.

Rewrite using `[e5]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem positive_density_compact_support : Formalism.FourierDecayAlt.JC.PosDensityCpt := by
  intro Wp Wq _ _ _ _ _ _ P0 T s j w A mm ε hε hA hmm H x hx
  have hm0 : 5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ mm := pd_thr_mm P0 j w.length mm hmm
  have hAB := pd_thr_AB P0 j w.length A hA
  have hN0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
  have hAB0 : 0 < AB P0.k (P0.r - (j : ℕ)) := by unfold AB; positivity
  have hA1 : 0 ≤ A - 1 := by linarith

  choose cx hcx using fun a => (hx a).2.1
  have hcx0 : ∀ a, 0 ≤ cx a := fun a => pd_ccle_nonneg (hcx a)
  set c0 : ℝ := ∑ a, cx a with hc0def
  have hc0 : 0 ≤ c0 := Finset.sum_nonneg fun a _ => hcx0 a
  have hX : ∀ a, CCle A mm (x a) c0 := fun a => pd_ccle_mono_c (hcx a)
    (Finset.single_le_sum (f := cx) (fun b _ => hcx0 b) (Finset.mem_univ a))
  obtain ⟨Cf, hCf0, hCf⟩ := formLev_bound_mm P0 T s j w A hA
  obtain ⟨Kc, hKc0, hKc⟩ := pd_cut_ccle (k := P0.k) (r := P0.r - j) (E := Wq →L[ℂ] Wp) mm
  refine pd_nonneg_of_approx _ (Cf * (2 * c0 + 1)) fun R hR1 => ?_
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  set τ : ℝ := 1 / R with hτdef
  have hτ : 0 < τ := by positivity
  have hτ1 : τ ≤ 1 := by rw [hτdef, div_le_one hR0]; exact hR1
  set R' : ℝ := max 1 (2 * Kc * c0 / τ) with hR'def
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hcut : Kc * c0 / R' ≤ τ / 2 := by
    rw [div_le_iff₀ hR']
    have h1 : 2 * Kc * c0 / τ ≤ R' := le_max_right _ _
    rw [div_le_iff₀ hτ] at h1
    nlinarith
  have happ := fun a => me_approx_one_cpt mm _ hm0 (A - 1) hA1 (x a) (hx a).1 (T.bs j).z (T.bs j).z' ε hε (hx a).2.2
    R' (τ / 2) hR' (by positivity)
  choose y hyck hyin hysupp hycc hycpt using happ
  have hpos := H (ε / 4) (by positivity) y fun a => ⟨⟨hyck a, hyin a, hysupp a⟩, hycpt a⟩
  set e : Wd.Ix (Fin w.length) → Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp) := x - y with hedef
  have he : ∀ a, CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (e a) τ := by
    intro a
    have h1 := pd_ccle_mono le_rfl hm0 (hKc R' hR' A (x a) c0 (hX a))
    have h2 := CCle_add h1 (hycc a)
    have e2 : (fun g => pdPsi R' g • x a g + (pdPhi (R'⁻¹ • g) • x a g - y a g)) = e a := by
      funext g
      simp only [hedef, Pi.sub_apply, pdPsi, sub_smul, one_smul]
      abel
    rw [e2] at h2
    exact pd_ccle_mono_c h2 (by linarith)
  have hx1 : ∀ a, CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (x a) c0 :=
    fun a => pd_ccle_mono (by linarith) hm0 (hX a)
  have hy1 : ∀ a, CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (y a) (c0 + τ) := by
    intro a
    have h := CCle_add (hx1 a) (CCle_smul (-1) (he a))
    have e3 : (fun g => x a g + (-1 : ℂ) • e a g) = y a := by
      funext g
      simp only [hedef, Pi.sub_apply, neg_smul, one_smul]
      abel
    rw [e3] at h
    simpa using h
  have hv : ∀ {F : Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)} {c : ℝ},
      CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) F c →
      CCle (A - 1 - 2 * (w.length : ℝ)) 5 F c := fun h => pd_ccle_mono (by linarith) (by omega) h

  have hxI : ∀ a, InCC A mm (x a) := fun a => (hx a).2.1
  have hyI : ∀ a, InCC A mm (y a) := fun a => hyin a A mm
  have heI : ∀ a, InCC A mm (e a) := by
    intro a
    obtain ⟨c1, h1⟩ := hxI a
    obtain ⟨c2, h2⟩ := hyI a
    have h := CCle_add h1 (CCle_smul (-1) h2)
    have e4 : (fun g => x a g + (-1 : ℂ) • y a g) = e a := by
      funext g
      simp only [hedef, Pi.sub_apply, neg_smul, one_smul]
      abel
    rw [e4] at h
    exact ⟨_, h⟩
  have hsplit : y + (1 : ℂ) • e = x := by
    funext a g
    simp only [hedef, Pi.add_apply, Pi.sub_apply, one_smul]
    abel
  have hS1 := (formLev_sesq_core P0 T s j w A mm hA hmm y e x 1 hyI heI hxI).1
  have hS2 := (formLev_sesq_core P0 T s j w A mm hA hmm y e y 1 hyI heI hyI).2
  rw [hsplit] at hS1 hS2
  refine ⟨D.formLev T s j w y y, hpos, ?_⟩
  have hb1 := hCf y e (c0 + τ) τ hy1 fun a => hv (he a)
  have hb2 := hCf e x τ c0 he fun a => hv (hx1 a)
  rw [hS1, hS2, map_one, one_mul, one_mul]
  have e5 : D.formLev T s j w y y + D.formLev T s j w y e + D.formLev T s j w e x - D.formLev T s j w y y =
      D.formLev T s j w y e + D.formLev T s j w e x := by ring
  rw [e5]
  calc ‖D.formLev T s j w y e + D.formLev T s j w e x‖
      ≤ ‖D.formLev T s j w y e‖ + ‖D.formLev T s j w e x‖ := norm_add_le _ _
    _ ≤ Cf * (c0 + τ) * τ + Cf * τ * c0 := add_le_add hb1 hb2
    _ ≤ Cf * (2 * c0 + 1) * τ := by nlinarith [mul_nonneg hCf0 hτ.le]
    _ = Cf * (2 * c0 + 1) / R := by rw [hτdef]; ring

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt
open scoped ComplexOrder

/- English proof (translation)
Introduce `hP hRMF hPD hSesq Wp Wq _ _ _ _ _ _ P0 T l0 N admitted A mm hl0 hl0k hAdmN hA hmm hdata`. Use `⟨fun j => JCx2.KKcM (T.bs j) A mm, fun j w hw => ?_, fun j F ε hε hF hF1 hF3 => ⟨ε, hε, hF1, hF, hF3⟩⟩` and prove the remaining obligations. Establish `hlen` using `hAdmN w hw`. Establish `hA' : P5.Auser P0 w.length + 1 ≤ A` using `le_trans (by linarith [JCx2.auser_mono P0 hlen]) hA`. Establish `hmm' : P5.mmUser P0 w.length ≤ mm` using `le_trans (JCx2.mmUser_mono P0 hlen) hmm`.

Establish `hmemK : ∀ x : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp), x ∈ Submodule.pi Set.univ (fun _ => JCx2.KKcM (T.bs j) A mm) → ∃ ε, 0 < ε ∧ ∀ a, JC.CCCoefM (T.bs j) A mm ε (x a)`. Introduce `x hx`. Conclude with `JCx2.exists_common_eps (fun a ε => JC.CCCoefM (T.bs j) A mm ε (x a)) (fun a ε ε' _ h hF => JCx2.cCCoefM_mono h hF) (fun a => hx a (Set.mem_univ a))`. Use `⟨fun x hx x' hx' y hy c => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨e1, he1, h1⟩` from `hmemK x hx`.

Take `⟨e2, he2, h2⟩` from `hmemK x' hx'`. Take `⟨e3, he3, h3⟩` from `hmemK y hy`. Establish `hε : 0 < min e1 (min e2 e3)` using `lt_min he1 (lt_min he2 he3)`. Conclude with `hSesq Wp Wq P0 T (M.sgn P0 l0) j w A mm _ hε hA' hmm' x x' y c (fun a => JCx2.cCCoefM_mono (min_le_left _ _) (h1 a)) (fun a => JCx2.cCCoefM_mono ((min_le_right _ _).trans (min_le_left _ _)) (h2 a)) (fun a => JCx2.cCCoefM_mono ((min_le_right _ _).trans (min_le_right _ _)) (h3 a))`. Take `⟨ε, hε, hxε⟩` from `hmemK x hx`.

Use `hPD Wp Wq P0 T (M.sgn P0 l0) j w A mm ε hε hA' hmm' ?_ x hxε` and prove the remaining obligations. Introduce `ε₁ hε₁ v hvn`. Take `⟨X, μ, L, st, hD, hOK⟩` from `hdata j`. Take `⟨Cst, hC, hform⟩` from `hRMF Wp Wq P0 T j X μ L st l0 hD`. Establish `hvn' : ∀ a, JC.NiceCoef (T.bs j) ε₁ (v a)` using `fun a => (hvn a).1`.

Establish `hAu : P5.Auser (JC.parLev P0 j) (Fintype.card (Fin w.length)) ≤ A`. Rewrite using `[Fintype.card_fin]`. Combine the linear relations using `[JCx2.auser_parLev P0 j w.length]`. Establish `hmu : P5.mmUser (JC.parLev P0 j) (Fintype.card (Fin w.length)) ≤ mm`. Rewrite using `[Fintype.card_fin]`.

Conclude with `(JCx2.mmUser_parLev P0 j w.length).trans hmm'`. Take `⟨K, hThm, -, -, hJ⟩` from `hP Wp Wq (Fin w.length) (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0 (T.bs j) A mm hD hl0 hl0k rfl rfl rfl rfl hAu hmu`. Use `choose Φ hΦK hΦ using fun a => hJ (v a) ε₁ hε₁ (hvn a).1.2.1 (hvn a).2 (hvn a).1.2.2`. Rewrite using `[hform w v v Φ Φ ε₁ hε₁ hvn' hvn' hΦ hΦ]`. Establish `hpos` using `((hThm (D.positionted w) (hOK w hw)).2.2 0 (fun _ => 1) (fun _ => one_ne_zero)).2 Φ (fun a _ => hΦK a)`.

Establish `hpos' : 0 ≤ P5.form μ 0 (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ 0` using `hpos.trans_eq (JCx2.form_zero_indep μ _ _ _ _)`. Conclude with `mul_nonneg (by exact_mod_cast hC.le) hpos'`.
-/
theorem theorem_P_module_compact_support : Formalism.FourierDecayAlt.JC.ThmPModuleOfActualCpt := by
  intro hP hRMF hPD hSesq Wp Wq _ _ _ _ _ _ P0 T l0 N admitted A mm hl0 hl0k hAdmN hA hmm hdata
  refine ⟨fun j => JCx2.KKcM (T.bs j) A mm, fun j w hw => ?_, fun j F ε hε hF hF1 hF3 => ⟨ε, hε, hF1, hF, hF3⟩⟩
  have hlen := hAdmN w hw
  have hA' : P5.Auser P0 w.length + 1 ≤ A := le_trans (by linarith [JCx2.auser_mono P0 hlen]) hA
  have hmm' : P5.mmUser P0 w.length ≤ mm := le_trans (JCx2.mmUser_mono P0 hlen) hmm
  have hmemK : ∀ x : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp),
      x ∈ Submodule.pi Set.univ (fun _ => JCx2.KKcM (T.bs j) A mm) →
      ∃ ε, 0 < ε ∧ ∀ a, JC.CCCoefM (T.bs j) A mm ε (x a) := by
    intro x hx
    exact JCx2.exists_common_eps (fun a ε => JC.CCCoefM (T.bs j) A mm ε (x a))
      (fun a ε ε' _ h hF => JCx2.cCCoefM_mono h hF) (fun a => hx a (Set.mem_univ a))
  refine ⟨fun x hx x' hx' y hy c => ?_, fun x hx => ?_⟩
  · obtain ⟨e1, he1, h1⟩ := hmemK x hx
    obtain ⟨e2, he2, h2⟩ := hmemK x' hx'
    obtain ⟨e3, he3, h3⟩ := hmemK y hy
    have hε : 0 < min e1 (min e2 e3) := lt_min he1 (lt_min he2 he3)
    exact hSesq Wp Wq P0 T (M.sgn P0 l0) j w A mm _ hε hA' hmm' x x' y c
      (fun a => JCx2.cCCoefM_mono (min_le_left _ _) (h1 a))
      (fun a => JCx2.cCCoefM_mono ((min_le_right _ _).trans (min_le_left _ _)) (h2 a))
      (fun a => JCx2.cCCoefM_mono ((min_le_right _ _).trans (min_le_right _ _)) (h3 a))
  · obtain ⟨ε, hε, hxε⟩ := hmemK x hx
    refine hPD Wp Wq P0 T (M.sgn P0 l0) j w A mm ε hε hA' hmm' ?_ x hxε
    intro ε₁ hε₁ v hvn
    obtain ⟨X, μ, L, st, hD, hOK⟩ := hdata j
    obtain ⟨Cst, hC, hform⟩ := hRMF Wp Wq P0 T j X μ L st l0 hD
    have hvn' : ∀ a, JC.NiceCoef (T.bs j) ε₁ (v a) := fun a => (hvn a).1
    have hAu : P5.Auser (JC.parLev P0 j) (Fintype.card (Fin w.length)) ≤ A := by
      rw [Fintype.card_fin]
      linarith [JCx2.auser_parLev P0 j w.length]
    have hmu : P5.mmUser (JC.parLev P0 j) (Fintype.card (Fin w.length)) ≤ mm := by
      rw [Fintype.card_fin]
      exact (JCx2.mmUser_parLev P0 j w.length).trans hmm'
    obtain ⟨K, hThm, -, -, hJ⟩ := hP Wp Wq (Fin w.length) (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π
      (T.bs j).π' X μ L st l0 (T.bs j) A mm hD hl0 hl0k rfl rfl rfl rfl hAu hmu
    choose Φ hΦK hΦ using fun a => hJ (v a) ε₁ hε₁ (hvn a).1.2.1 (hvn a).2 (hvn a).1.2.2
    rw [hform w v v Φ Φ ε₁ hε₁ hvn' hvn' hΦ hΦ]
    have hpos := ((hThm (D.positionted w) (hOK w hw)).2.2 0 (fun _ => 1) (fun _ => one_ne_zero)).2 Φ
      (fun a _ => hΦK a)
    have hpos' : 0 ≤ P5.form μ 0 (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ 0 :=
      hpos.trans_eq (JCx2.form_zero_indep μ _ _ _ _)
    exact mul_nonneg (by exact_mod_cast hC.le) hpos'

end Formalism.FourierDecayAlt.P
