import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.SchurJT

noncomputable section

open Finset Filter Topology GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace PositivityTheory.RgJS

namespace BetaAllContinuity

variable {m : ℕ}

/- English proof (translation)
Unfold `hN`. Use `fun_prop`.
-/
theorem continuous_hN (p : ℕ) : Continuous fun α : Fin m → ℂ => hN p α := by
  unfold hN
  fun_prop

/- English proof (translation)
Distinguish the cases in `h : z < 0`. Simplify using `only [hZ, if_pos h]`. Conclude with `continuous_const`. Simplify using `only [hZ, if_neg h]`. Conclude with `continuous_hN _`.
-/
theorem continuous_hZ (z : ℤ) : Continuous fun α : Fin m → ℂ => hZ z α := by
  by_cases h : z < 0
  · simp only [hZ, if_pos h]
    exact continuous_const
  · simp only [hZ, if_neg h]
    exact continuous_hN _

/- English proof (translation)
Unfold `jt`. Use `Continuous.matrix_det ?_` and prove the remaining obligations. Conclude with `continuous_pi fun i => continuous_pi fun j => continuous_hZ _`.
-/
theorem continuous_jt {m' : ℕ} (l : Fin m' → ℕ) : Continuous fun γ : Fin m → ℂ => jt γ l := by
  unfold jt
  refine Continuous.matrix_det ?_
  exact continuous_pi fun i => continuous_pi fun j => continuous_hZ _

end BetaAllContinuity

open BetaAllContinuity in
/- English proof (translation)
Introduce `hG hS hJ m m' α β X A B hA hB hα hβ hX`. Unfold `BetaGen at hG`. Unfold `SumBd at hS`. Unfold `SchurJT at hJ`. Simplify using `only [hJ] at hG ⊢`.

Choose the witnesses or unpack the hypotheses as in `⟨B', hBB', hX'⟩ : ∃ B', B < B' ∧ ‖X‖ * A * B' < 1 := by`. Establish `hc : Filter.Tendsto (fun t : ℝ => ‖X‖ * A * t) (𝓝 B) (𝓝 (‖X‖ * A * B))` using `tendsto_const_nhds.mul tendsto_id`. Establish `hev : ∀ᶠ t in 𝓝[>] B, ‖X‖ * A * t < 1` using `(hc.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hX)`. Take `⟨t, ht1, ht2⟩` from `(hev.and self_mem_nhdsWithin).exists`. Conclude with `⟨t, ht2, ht1⟩`.

Establish `hB' : 0 < B'` using `hB.trans hBB'`. Set `γ : ℝ → Fin m' → ℂˣ` to `fun t j => β j * Units.mk0 ((Real.exp (t * ((j : ℕ) : ℝ)) : ℝ) : ℂ) (by exact_mod_cast (Real.exp_pos _).ne')`. Set `c : ℝ → Fin m' → ℂ` to `fun t j => ((γ t j : ℂˣ) : ℂ)`. Establish `hγt : ∀ j, Filter.Tendsto (fun t => c t j) (𝓝[>] (0 : ℝ)) (𝓝 (β j : ℂ))`. Introduce `j`.

Establish `hcont : Continuous fun t : ℝ => c t j`. Simplify using `only [c, γ, Units.val_mul, Units.val_mk0]`. Use `fun_prop`. Establish `h0 : c 0 j = β j` using `by simp [c, γ]`. Use `hcont.tendsto 0` as an intermediate fact.

Rewrite `this` using `[h0]`. Conclude with `this.mono_left nhdsWithin_le_nhds`. Establish `hγB : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ‖c t j‖ ≤ B'`. Rewrite using `[Filter.eventually_all]`. Introduce `j`.

Establish `h2 : ‖(β j : ℂ)‖ < B'` using `(hβ j).trans_lt hBB'`. Conclude with `((hγt j).norm.eventually (gt_mem_nhds h2)).mono fun t ht => ht.le`. Establish `hdist : ∀ᶠ t in 𝓝[>] (0 : ℝ), Pairwise fun j j' => c t j ≠ c t j'`. Establish `key : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j j', j ≠ j' → c t j ≠ c t j'`. Rewrite using `[Filter.eventually_all]`.

Introduce `j`. Rewrite using `[Filter.eventually_all]`. Introduce `j'`. Distinguish the cases in `hjj : j = j'`. Conclude with `Filter.Eventually.of_forall fun t h => absurd hjj h`.

Distinguish the cases in `hb : (β j : ℂ) = β j'`. Use `filter_upwards [self_mem_nhdsWithin] with t ht _`. Simplify using `only [c, γ, Units.val_mul, Units.val_mk0]`. Introduce `heq`. Rewrite `heq` using `[hb]`.

Establish `h3` using `mul_left_cancel₀ (β j').ne_zero heq`. Establish `h4 : Real.exp (t * ((j : ℕ) : ℝ)) = Real.exp (t * ((j' : ℕ) : ℝ))` using `by exact_mod_cast h3`. Establish `h5` using `Real.exp_injective h4`. Establish `ht' : (0 : ℝ) < t` using `ht`. Establish `h6 : ((j : ℕ) : ℝ) = ((j' : ℕ) : ℝ)` using `mul_left_cancel₀ ht'.ne' h5`.

Conclude with `hjj (Fin.ext (by exact_mod_cast h6))`. Establish `h1 : Filter.Tendsto (fun t => c t j - c t j') (𝓝[>] (0 : ℝ)) (𝓝 ((β j : ℂ) - β j'))` using `(hγt j).sub (hγt j')`. Establish `h2 : (β j : ℂ) - β j' ≠ 0` using `sub_ne_zero.mpr hb`. Conclude with `(h1.eventually (eventually_ne_nhds h2)).mono fun t ht _ => sub_ne_zero.mp ht`. Conclude with `key.mono fun t ht j j' h => ht j j' h`.

Set `G : (Fin m' → ℂ) → {l : Fin m' → ℕ // Antitone l} → ℂ` to `fun b l => jt α (l : Fin m' → ℕ) * jt b (l : Fin m' → ℕ) * X ^ ∑ j : Fin m', (l : Fin m' → ℕ) j`. Establish `hSa` using `hS m m' A B' ‖X‖ hA hB' (norm_nonneg _) hX'`. Establish `hSb` using `hS m' m' B' B' 0 hB' hB' le_rfl (by simp)`. Establish `hbound : ∀ b : Fin m' → ℂ, (∀ j, ‖b j‖ ≤ B') → ∀ l : {l : Fin m' → ℕ // Antitone l}, ‖G b l‖ ≤ cjt m A (l : Fin m' → ℕ) * cjt m' B' (l : Fin m' → ℕ) * ‖X‖ ^ ∑ j : Fin m', (l : Fin m' → ℕ) j`. Introduce `b hb l`.

Simplify using `only [G, norm_mul, norm_pow]`. Establish `h1` using `hSa.2 α hα (l : Fin m' → ℕ)`. Establish `h2` using `hSb.2 b hb (l : Fin m' → ℕ)`. Establish `h0 : 0 ≤ cjt m A (l : Fin m' → ℕ)` using `(norm_nonneg _).trans h1`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) h0) (pow_nonneg (norm_nonneg _) _)`.

Establish `hsumG : Summable (G fun j => (β j : ℂ))` using `Summable.of_norm_bounded hSa.1 (hbound _ fun j => (hβ j).trans hBB'.le)`. Establish `hc : Filter.Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 fun j => (β j : ℂ))` using `tendsto_pi_nhds.mpr hγt`. Establish `hpt : ∀ l, Filter.Tendsto (fun t => G (c t) l) (𝓝[>] (0 : ℝ)) (𝓝 (G (fun j => (β j : ℂ)) l))`. Introduce `l`. Establish `h` using `((continuous_jt (m := m') (l : Fin m' → ℕ)).tendsto _).comp hc`.

Conclude with `(tendsto_const_nhds.mul h).mul tendsto_const_nhds`. Establish `htsum : Filter.Tendsto (fun t => ∑' l, G (c t) l) (𝓝[>] (0 : ℝ)) (𝓝 (∑' l, G (fun j => (β j : ℂ)) l))` using `tendsto_tsum_of_dominated_convergence hSa.1 hpt (hγB.mono fun t ht l => hbound _ ht l)`. Establish `hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∏ i : Fin m, ∏ j : Fin m', (1 - α i * c t j * X)⁻¹ = ∑' l, G (c t) l` using `by filter_upwards [hγB, hdist] with t hb hd`. Conclude with `(hG m m' α (γ t) X A B' hA hB' hα hb hX' hd).tsum_eq.symm`. Establish `hP : Filter.Tendsto (fun t => ∏ i : Fin m, ∏ j : Fin m', (1 - α i * c t j * X)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 (∏ i : Fin m, ∏ j : Fin m', (1 - α i * (β j : ℂ) * X)⁻¹))`.

Use `tendsto_finset_prod _ fun i _ => tendsto_finset_prod _ fun j _ => ?_` and prove the remaining obligations. Use `(tendsto_const_nhds.sub ((tendsto_const_nhds.mul (hγt j)).mul tendsto_const_nhds)).inv₀ ?_` and prove the remaining obligations. Introduce `h0`. Establish `h1 : α i * (β j : ℂ) * X = 1` using `by linear_combination -h0`. Establish `h2 : ‖α i * (β j : ℂ) * X‖ < 1`.

Rewrite using `[norm_mul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hα i`. Conclude with `hβ j`. Use `_ = ‖X‖ * A * B := by ring`.

Use `_ < 1 := hX`. Rewrite `h2` using `[h1, norm_one]`. Conclude with `lt_irrefl _ h2`. Establish `heq : ∑' l, G (fun j => (β j : ℂ)) l = ∏ i : Fin m, ∏ j : Fin m', (1 - α i * (β j : ℂ) * X)⁻¹` using `tendsto_nhds_unique htsum (hP.congr' hev)`. Use `show HasSum (G fun j => (β j : ℂ)) _`.

Rewrite using `[← heq]`. Conclude with `hsumG.hasSum`.
-/
theorem beta_all_of_generating : BetaGen → SumBd → SchurJT → BetaAll := by
  intro hG hS hJ m m' α β X A B hA hB hα hβ hX
  unfold BetaGen at hG
  unfold SumBd at hS
  unfold SchurJT at hJ
  simp only [hJ] at hG ⊢
  obtain ⟨B', hBB', hX'⟩ : ∃ B', B < B' ∧ ‖X‖ * A * B' < 1 := by
    have hc : Filter.Tendsto (fun t : ℝ => ‖X‖ * A * t) (𝓝 B) (𝓝 (‖X‖ * A * B)) :=
      tendsto_const_nhds.mul tendsto_id
    have hev : ∀ᶠ t in 𝓝[>] B, ‖X‖ * A * t < 1 :=
      (hc.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hX)
    obtain ⟨t, ht1, ht2⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨t, ht2, ht1⟩
  have hB' : 0 < B' := hB.trans hBB'
  let γ : ℝ → Fin m' → ℂˣ := fun t j =>
    β j * Units.mk0 ((Real.exp (t * ((j : ℕ) : ℝ)) : ℝ) : ℂ) (by exact_mod_cast (Real.exp_pos _).ne')
  let c : ℝ → Fin m' → ℂ := fun t j => ((γ t j : ℂˣ) : ℂ)
  have hγt : ∀ j, Filter.Tendsto (fun t => c t j) (𝓝[>] (0 : ℝ)) (𝓝 (β j : ℂ)) := by
    intro j
    have hcont : Continuous fun t : ℝ => c t j := by
      simp only [c, γ, Units.val_mul, Units.val_mk0]
      fun_prop
    have h0 : c 0 j = β j := by simp [c, γ]
    have := hcont.tendsto 0
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hγB : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ‖c t j‖ ≤ B' := by
    rw [Filter.eventually_all]
    intro j
    have h2 : ‖(β j : ℂ)‖ < B' := (hβ j).trans_lt hBB'
    exact ((hγt j).norm.eventually (gt_mem_nhds h2)).mono fun t ht => ht.le
  have hdist : ∀ᶠ t in 𝓝[>] (0 : ℝ), Pairwise fun j j' => c t j ≠ c t j' := by
    have key : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j j', j ≠ j' → c t j ≠ c t j' := by
      rw [Filter.eventually_all]
      intro j
      rw [Filter.eventually_all]
      intro j'
      by_cases hjj : j = j'
      · exact Filter.Eventually.of_forall fun t h => absurd hjj h
      by_cases hb : (β j : ℂ) = β j'
      · filter_upwards [self_mem_nhdsWithin] with t ht _
        simp only [c, γ, Units.val_mul, Units.val_mk0]
        intro heq
        rw [hb] at heq
        have h3 := mul_left_cancel₀ (β j').ne_zero heq
        have h4 : Real.exp (t * ((j : ℕ) : ℝ)) = Real.exp (t * ((j' : ℕ) : ℝ)) := by exact_mod_cast h3
        have h5 := Real.exp_injective h4
        have ht' : (0 : ℝ) < t := ht
        have h6 : ((j : ℕ) : ℝ) = ((j' : ℕ) : ℝ) := mul_left_cancel₀ ht'.ne' h5
        exact hjj (Fin.ext (by exact_mod_cast h6))
      · have h1 : Filter.Tendsto (fun t => c t j - c t j') (𝓝[>] (0 : ℝ)) (𝓝 ((β j : ℂ) - β j')) :=
          (hγt j).sub (hγt j')
        have h2 : (β j : ℂ) - β j' ≠ 0 := sub_ne_zero.mpr hb
        exact (h1.eventually (eventually_ne_nhds h2)).mono fun t ht _ => sub_ne_zero.mp ht
    exact key.mono fun t ht j j' h => ht j j' h
  let G : (Fin m' → ℂ) → {l : Fin m' → ℕ // Antitone l} → ℂ := fun b l =>
    jt α (l : Fin m' → ℕ) * jt b (l : Fin m' → ℕ) * X ^ ∑ j : Fin m', (l : Fin m' → ℕ) j
  have hSa := hS m m' A B' ‖X‖ hA hB' (norm_nonneg _) hX'
  have hSb := hS m' m' B' B' 0 hB' hB' le_rfl (by simp)
  have hbound : ∀ b : Fin m' → ℂ, (∀ j, ‖b j‖ ≤ B') → ∀ l : {l : Fin m' → ℕ // Antitone l},
      ‖G b l‖ ≤ cjt m A (l : Fin m' → ℕ) * cjt m' B' (l : Fin m' → ℕ) * ‖X‖ ^ ∑ j : Fin m', (l : Fin m' → ℕ) j := by
    intro b hb l
    simp only [G, norm_mul, norm_pow]
    have h1 := hSa.2 α hα (l : Fin m' → ℕ)
    have h2 := hSb.2 b hb (l : Fin m' → ℕ)
    have h0 : 0 ≤ cjt m A (l : Fin m' → ℕ) := (norm_nonneg _).trans h1
    exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) h0) (pow_nonneg (norm_nonneg _) _)
  have hsumG : Summable (G fun j => (β j : ℂ)) :=
    Summable.of_norm_bounded hSa.1 (hbound _ fun j => (hβ j).trans hBB'.le)
  have hc : Filter.Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 fun j => (β j : ℂ)) := tendsto_pi_nhds.mpr hγt
  have hpt : ∀ l, Filter.Tendsto (fun t => G (c t) l) (𝓝[>] (0 : ℝ)) (𝓝 (G (fun j => (β j : ℂ)) l)) := by
    intro l
    have h := ((continuous_jt (m := m') (l : Fin m' → ℕ)).tendsto _).comp hc
    exact (tendsto_const_nhds.mul h).mul tendsto_const_nhds
  have htsum : Filter.Tendsto (fun t => ∑' l, G (c t) l) (𝓝[>] (0 : ℝ)) (𝓝 (∑' l, G (fun j => (β j : ℂ)) l)) :=
    tendsto_tsum_of_dominated_convergence hSa.1 hpt (hγB.mono fun t ht l => hbound _ ht l)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∏ i : Fin m, ∏ j : Fin m', (1 - α i * c t j * X)⁻¹ = ∑' l, G (c t) l := by
    filter_upwards [hγB, hdist] with t hb hd
    exact (hG m m' α (γ t) X A B' hA hB' hα hb hX' hd).tsum_eq.symm
  have hP : Filter.Tendsto (fun t => ∏ i : Fin m, ∏ j : Fin m', (1 - α i * c t j * X)⁻¹) (𝓝[>] (0 : ℝ))
      (𝓝 (∏ i : Fin m, ∏ j : Fin m', (1 - α i * (β j : ℂ) * X)⁻¹)) := by
    refine tendsto_finset_prod _ fun i _ => tendsto_finset_prod _ fun j _ => ?_
    refine (tendsto_const_nhds.sub ((tendsto_const_nhds.mul (hγt j)).mul tendsto_const_nhds)).inv₀ ?_
    intro h0
    have h1 : α i * (β j : ℂ) * X = 1 := by linear_combination -h0
    have h2 : ‖α i * (β j : ℂ) * X‖ < 1 := by
      rw [norm_mul, norm_mul]
      calc ‖α i‖ * ‖(β j : ℂ)‖ * ‖X‖ ≤ A * B * ‖X‖ := by
            gcongr
            · exact hα i
            · exact hβ j
        _ = ‖X‖ * A * B := by ring
        _ < 1 := hX
    rw [h1, norm_one] at h2
    exact lt_irrefl _ h2
  have heq : ∑' l, G (fun j => (β j : ℂ)) l = ∏ i : Fin m, ∏ j : Fin m', (1 - α i * (β j : ℂ) * X)⁻¹ :=
    tendsto_nhds_unique htsum (hP.congr' hev)
  show HasSum (G fun j => (β j : ℂ)) _
  rw [← heq]
  exact hsumG.hasSum

end PositivityTheory.RgJS
