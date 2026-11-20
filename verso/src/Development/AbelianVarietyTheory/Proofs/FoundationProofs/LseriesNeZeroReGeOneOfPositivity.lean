import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlobalPositivityIneqMultiplicativeCoeffStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NotSummableInvPrimesCongrNegOneStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

/- English proof (translation)
Introduce `hpM`. Establish `h1 : ((p + 1 : ℕ) : ZMod M) = 0` using `by push_cast; rw [h]; ring`. Establish `h1' : M ∣ p + 1` using `(CharP.cast_eq_zero_iff (ZMod M) M (p + 1)).mp h1`. Establish `: p ∣ p + 1` using `hpM.trans h1'`. Establish `: p ∣ 1` using `(Nat.dvd_add_right (dvd_refl p)).mp this`.

Conclude with `hp.one_lt.ne' (Nat.dvd_one.mp this)`.
-/
theorem not_dvd_of_prime_of_eq_neg_one {M p : ℕ} (hp : p.Prime) (h : (p : ZMod M) = -1) :
    ¬ p ∣ M := by
  intro hpM
  have h1 : ((p + 1 : ℕ) : ZMod M) = 0 := by push_cast; rw [h]; ring
  have h1' : M ∣ p + 1 := (CharP.cast_eq_zero_iff (ZMod M) M (p + 1)).mp h1
  have : p ∣ p + 1 := hpM.trans h1'
  have : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/- English proof (translation)
Introduce `M b ω C Λ hM hb1 hb0 hmul hcop hrec hC hsum hsC hre hdiff hL w hw`. Establish `G` using `fun s hs => GlobalTheory.T.global_positivity_ineq_multiplicative_coeff M b ω s C hs hb1 hb0 hmul hcop hrec hC (hsum s hs)`. Break down `hw.lt_or_eq with hw | rfl` into its components or cases. Introduce `h0`. Establish `hs : 0 < w - 1` using `by linarith`.

Use `G (w - 1) hs 0` as an intermediate fact. Establish `e : ((1 + (w - 1) : ℝ) : ℂ) = (w : ℂ)` using `by push_cast; ring`. Rewrite `this` using `[hL _ hs, e, h0]`. Evaluate the numerical expressions using `at this`. Introduce `h0`.

Rewrite `h0` using `[Complex.ofReal_one]`. Establish `hO` using `(hdiff 1).isBigO_sub`. Establish `ht : Tendsto (fun s : ℝ => ((1 + s : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 1)`. Establish `: Continuous fun s : ℝ => ((1 + s : ℝ) : ℂ)` using `by fun_prop`. Establish `h` using `this.tendsto 0`.

Simplify using `only [add_zero, Complex.ofReal_one] at h`. Conclude with `h.mono_left nhdsWithin_le_nhds`. Take `⟨c, hc, hcw⟩` from `(hO.comp_tendsto ht).exists_pos`. Establish `hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s ≤ 1 ∧ ‖Λ ((1 + s : ℝ) : ℂ)‖ ≤ c * s`. Establish `h1` using `hcw.bound`.

Establish `h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s` using `self_mem_nhdsWithin`. Establish `h3 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ≤ 1` using `nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num : (0:ℝ) < 1))`. Use `filter_upwards [h1, h2, h3] with s h1 h2 h3`. Use `⟨h2, h3, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp, h0, sub_zero] at h1`.

Establish `: ((1 + s : ℝ) : ℂ) - 1 = (s : ℂ)` using `by push_cast; ring`. Rewrite `h1` using `[this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2]`. Conclude with `h1`. Establish `hC0 : 0 ≤ C`. Use `hsC 1 one_pos le_rfl` as an intermediate fact.

Use `le_trans ?_ this` and prove the remaining obligations. Conclude with `mul_nonneg zero_le_one (tsum_nonneg fun n => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))`. Use `set B : ℝ := 4 * c ^ 2 * C with hB`. Set `T : ℕ → Finset ℕ` to `fun X => (Finset.range X).filter (fun p => p.Prime ∧ (p : ZMod M) = -1)`. Establish `key : ∀ X : ℕ, ∀ s : ℝ, 0 < s → s ≤ 1 → ‖Λ ((1 + s : ℝ) : ℂ)‖ ≤ c * s → ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + s) ≤ B`.

Introduce `X s hs hs1 hΛ`. Use `set S := ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) with hS`. Establish `hS0 : 0 ≤ S` using `tsum_nonneg fun n => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)`. Establish `g` using `G s hs X`. Rewrite `g` using `[hL s hs]`.

Use `set F := (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M)`. Establish `hsub : T X ⊆ F`. Introduce `p hp`. Simplify using `only [T, F, Finset.mem_filter] at hp ⊢`. Conclude with `⟨hp.1, hp.2.1, not_dvd_of_prime_of_eq_neg_one hp.2.1 hp.2.2⟩`.

Establish `h1 : ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + s) ≤ ∑ p ∈ T X, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `p hp`. Simplify using `only [T, Finset.mem_filter] at hp`. Establish `hre'` using `hre p hp.2.1 (not_dvd_of_prime_of_eq_neg_one hp.2.1 hp.2.2) hp.2.2`.

Establish `: (1 : ℝ) ≤ ‖1 + b p‖ ^ 2`. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Simplify using `only [Complex.add_re, Complex.one_re, hre', Complex.add_im, Complex.one_im]`. Use polynomial arithmetic with `[sq_nonneg (b p).im]`. Conclude with `div_le_div_of_nonneg_right this (Real.rpow_nonneg (Nat.cast_nonneg _) _)`.

Establish `h2 : ∑ p ∈ T X, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) ≤ ∑ p ∈ F, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)` using `Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))`. Establish `h3` using `Real.add_one_le_exp (∑ p ∈ F, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s))`. Establish `hL2 : ‖Λ ((1 + s : ℝ) : ℂ)‖ ^ 2 ≤ (c * s) ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) hΛ 2`. Establish `hsS` using `hsC s hs hs1`. Establish `h4 : 2 * (1 + 1 / s) * ‖Λ ((1 + s : ℝ) : ℂ)‖ ^ 2 * S ≤ B`.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT : ∀ X : ℕ, ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ≤ B`. Introduce `X`. Establish `ht : Tendsto (fun s : ℝ => ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + s)) (𝓝[>] (0 : ℝ)) (𝓝 (∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + (0:ℝ))))`.

Apply `Tendsto.mono_left _ nhdsWithin_le_nhds` to reduce the goal to its premises. Apply `tendsto_finset_sum` to reduce the goal to its premises. Introduce `p hp`. Simplify using `only [T, Finset.mem_filter] at hp`. Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast hp.2.1.pos`.

Apply `Continuous.tendsto` to reduce the goal to its premises. Conclude with `continuous_const.div (continuous_const.rpow (continuous_const.add continuous_id) (fun _ => Or.inl hp0.ne')) (fun _ => (Real.rpow_pos_of_pos hp0 _).ne')`. Simplify using `only [add_zero, Real.rpow_one] at ht`. Apply `le_of_tendsto ht` to reduce the goal to its premises. Use `filter_upwards [hev] with s hs`.

Conclude with `key X s hs.1 hs.2.1 hs.2.2`. Apply `GlobalTheory.T.not_summable_inv_primes_congr_neg_one M hM` to reduce the goal to its premises. Apply `summable_of_sum_range_le (c := B)` to reduce the goal to its premises. Apply the tactic sequence `intro n; split_ifs <;> positivity`. Introduce `X`.

Rewrite using `[← Finset.sum_filter]`. Conclude with `hT X`.
-/
theorem lseries_ne_zero_edge : ∀ (M : ℕ) (b ω : ℕ → ℂ) (C : ℝ) (Λ : ℂ → ℂ), 0 < M → b 1 = 1 → b 0 = 0 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime M → b n = 0) → (∀ p r : ℕ, p.Prime → ¬ p ∣ M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → (∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → (∀ s : ℝ, 0 < s → s ≤ 1 → s * ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) ≤ C) → (∀ p : ℕ, p.Prime → ¬ p ∣ M → (p : ZMod M) = -1 → (b p).re = 0) → Differentiable ℂ Λ → (∀ s : ℝ, 0 < s → LSeries b ((1 + s : ℝ) : ℂ) = Λ ((1 + s : ℝ) : ℂ)) → ∀ w : ℝ, 1 ≤ w → Λ w ≠ 0 := by
  intro M b ω C Λ hM hb1 hb0 hmul hcop hrec hC hsum hsC hre hdiff hL w hw
  have G := fun s hs => GlobalTheory.T.global_positivity_ineq_multiplicative_coeff M b ω s C hs hb1 hb0 hmul hcop hrec hC (hsum s hs)
  rcases hw.lt_or_eq with hw | rfl
  · intro h0
    have hs : 0 < w - 1 := by linarith
    have := G (w - 1) hs 0
    have e : ((1 + (w - 1) : ℝ) : ℂ) = (w : ℂ) := by push_cast; ring
    rw [hL _ hs, e, h0] at this
    norm_num at this
  · intro h0
    rw [Complex.ofReal_one] at h0

    have hO := (hdiff 1).isBigO_sub
    have ht : Tendsto (fun s : ℝ => ((1 + s : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have : Continuous fun s : ℝ => ((1 + s : ℝ) : ℂ) := by fun_prop
      have h := this.tendsto 0
      simp only [add_zero, Complex.ofReal_one] at h
      exact h.mono_left nhdsWithin_le_nhds
    obtain ⟨c, hc, hcw⟩ := (hO.comp_tendsto ht).exists_pos
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s ≤ 1 ∧ ‖Λ ((1 + s : ℝ) : ℂ)‖ ≤ c * s := by
      have h1 := hcw.bound
      have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
      have h3 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ≤ 1 :=
        nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num : (0:ℝ) < 1))
      filter_upwards [h1, h2, h3] with s h1 h2 h3
      refine ⟨h2, h3, ?_⟩
      simp only [Function.comp, h0, sub_zero] at h1
      have : ((1 + s : ℝ) : ℂ) - 1 = (s : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2] at h1
      exact h1

    have hC0 : 0 ≤ C := by
      have := hsC 1 one_pos le_rfl
      refine le_trans ?_ this
      exact mul_nonneg zero_le_one (tsum_nonneg fun n => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    set B : ℝ := 4 * c ^ 2 * C with hB
    let T : ℕ → Finset ℕ := fun X => (Finset.range X).filter (fun p => p.Prime ∧ (p : ZMod M) = -1)

    have key : ∀ X : ℕ, ∀ s : ℝ, 0 < s → s ≤ 1 → ‖Λ ((1 + s : ℝ) : ℂ)‖ ≤ c * s →
        ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + s) ≤ B := by
      intro X s hs hs1 hΛ
      set S := ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) with hS
      have hS0 : 0 ≤ S := tsum_nonneg fun n => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have g := G s hs X
      rw [hL s hs] at g
      set F := (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M)
      have hsub : T X ⊆ F := by
        intro p hp
        simp only [T, F, Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, hp.2.1, not_dvd_of_prime_of_eq_neg_one hp.2.1 hp.2.2⟩
      have h1 : ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + s) ≤ ∑ p ∈ T X, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) := by
        apply Finset.sum_le_sum
        intro p hp
        simp only [T, Finset.mem_filter] at hp
        have hre' := hre p hp.2.1 (not_dvd_of_prime_of_eq_neg_one hp.2.1 hp.2.2) hp.2.2
        have : (1 : ℝ) ≤ ‖1 + b p‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp only [Complex.add_re, Complex.one_re, hre', Complex.add_im, Complex.one_im]
          nlinarith [sq_nonneg (b p).im]
        exact div_le_div_of_nonneg_right this (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have h2 : ∑ p ∈ T X, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) ≤ ∑ p ∈ F, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      have h3 := Real.add_one_le_exp (∑ p ∈ F, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s))
      have hL2 : ‖Λ ((1 + s : ℝ) : ℂ)‖ ^ 2 ≤ (c * s) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hΛ 2
      have hsS := hsC s hs hs1
      have h4 : 2 * (1 + 1 / s) * ‖Λ ((1 + s : ℝ) : ℂ)‖ ^ 2 * S ≤ B := by
        calc 2 * (1 + 1 / s) * ‖Λ ((1 + s : ℝ) : ℂ)‖ ^ 2 * S
            ≤ 2 * (1 + 1 / s) * (c * s) ^ 2 * S := by gcongr
          _ = 2 * (s + 1) * c ^ 2 * (s * S) := by field_simp
          _ ≤ 2 * (1 + 1) * c ^ 2 * C := by gcongr
          _ = B := by rw [hB]; ring
      linarith

    have hT : ∀ X : ℕ, ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ≤ B := by
      intro X
      have ht : Tendsto (fun s : ℝ => ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + s)) (𝓝[>] (0 : ℝ))
          (𝓝 (∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + (0:ℝ)))) := by
        apply Tendsto.mono_left _ nhdsWithin_le_nhds
        apply tendsto_finset_sum
        intro p hp
        simp only [T, Finset.mem_filter] at hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.1.pos
        apply Continuous.tendsto
        exact continuous_const.div (continuous_const.rpow (continuous_const.add continuous_id) (fun _ => Or.inl hp0.ne'))
          (fun _ => (Real.rpow_pos_of_pos hp0 _).ne')
      simp only [add_zero, Real.rpow_one] at ht
      apply le_of_tendsto ht
      filter_upwards [hev] with s hs
      exact key X s hs.1 hs.2.1 hs.2.2
    apply GlobalTheory.T.not_summable_inv_primes_congr_neg_one M hM
    apply summable_of_sum_range_le (c := B)
    · intro n; split_ifs <;> positivity
    · intro X
      rw [← Finset.sum_filter]
      exact hT X

end GlobalTheory.EisM
