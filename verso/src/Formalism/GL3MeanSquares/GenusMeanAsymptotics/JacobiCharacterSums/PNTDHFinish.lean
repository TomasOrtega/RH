import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHSt
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHFinishB

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

namespace DHF

/- English proof (translation)
Establish `hMr : (3 : ℝ) ≤ M` using `by exact_mod_cast hM`. Establish `hx : (6 : ℝ) ≤ M * T` using `by nlinarith`. Establish `he` using `Real.exp_one_lt_d9`. Establish `h1 : Real.exp 1 ≤ (M : ℝ) * T` using `by linarith`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem logMT_ge_one (M : ℕ) (T : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) : 1 ≤ Real.log ((M : ℝ) * T) := by
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx : (6 : ℝ) ≤ M * T := by nlinarith
  have he := Real.exp_one_lt_d9
  have h1 : Real.exp 1 ≤ (M : ℝ) * T := by linarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log ((M : ℝ) * T) := Real.log_le_log (Real.exp_pos 1) h1

/- English proof (translation)
Take `⟨cR, hcR, hZ⟩` from `Formalism.ZeroFreeDirichlet.zFRDirichlet`. Use `⟨cR, hcR, ?_⟩` and prove the remaining obligations. Introduce `M _ χ₁ χ β₁ T c₁ ρ hM hT2 hχ1ne hLz hc₁0 hc₁ hβ₁ hρ hρim hne`. Establish `hLg1` using `logMT_ge_one M T hM hT2`. Establish `hLg0 : 0 < Real.log ((M : ℝ) * T)` using `by linarith`.

Establish `hM3 : (3 : ℝ) ≤ M` using `by exact_mod_cast hM`. Establish `hlog2M : Real.log ((M : ℝ) * (|((β₁ : ℂ)).im| + 2)) ≤ Real.log ((M : ℝ) * T)`. Simplify using `only [Complex.ofReal_im, abs_zero, zero_add]`. Conclude with `Real.log_le_log (by positivity) (by nlinarith)`. Establish `hlog2M0 : 0 < Real.log ((M : ℝ) * (|((β₁ : ℂ)).im| + 2))`.

Apply `Real.log_pos` to reduce the goal to its premises. Simplify using `only [Complex.ofReal_im, abs_zero, zero_add]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hreg : InRegion cR M (β₁ : ℂ)`. Unfold `InRegion`.

Establish `h1 : c₁ / Real.log ((M : ℝ) * T) ≤ cR / Real.log ((M : ℝ) * (|((β₁ : ℂ)).im| + 2))`. Rewrite using `[div_le_div_iff₀ hLg0 hlog2M0]`. Establish `h2` using `mul_le_mul_of_nonneg_left hlog2M hc₁0.le`. Establish `h3` using `mul_le_mul_of_nonneg_right hc₁ hLg0.le`. Combine the linear relations using `only [h2, h3]`.

Rewrite using `[Complex.ofReal_re]`. Combine the linear relations using `only [h1, hβ₁]`. Establish `hLz' : IsLZero χ₁ (β₁ : ℂ)` using `⟨Or.inl hχ1ne, hLz⟩`. Establish `hZ1` using `(hZ M χ₁ (β₁ : ℂ) hreg hLz').2.2.2.2`. Establish `hnreg : ¬ InRegion cR M ρ`.

Introduce `h`. Take `⟨h1, h2⟩` from `hZ1 χ ρ h hρ`. Conclude with `hne (Prod.ext h1 h2)`. Unfold `InRegion at hnreg`. Use `push Not at hnreg`.

Establish `hlogρ0 : 0 < Real.log ((M : ℝ) * (|ρ.im| + 2))`. Apply `Real.log_pos` to reduce the goal to its premises. Use `abs_nonneg ρ.im` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hlogρ : Real.log ((M : ℝ) * (|ρ.im| + 2)) ≤ 2 * Real.log ((M : ℝ) * T)`.

Rewrite using `[show (2 : ℝ) * Real.log ((M : ℝ) * T) = Real.log (((M : ℝ) * T) ^ 2) by`. Rewrite using `[Real.log_pow]`. Use `push_cast`. Use the proof step `ring]`. Apply `Real.log_le_log (by have := abs_nonneg ρ.im; positivity)` to reduce the goal to its premises.

Establish `: |ρ.im| + 2 ≤ 2 * T` using `by linarith`. Establish `hM0 : (0 : ℝ) ≤ M` using `by positivity`. Establish `hMT : (2 : ℝ) ≤ M * T` using `by nlinarith`. Establish `hMT2` using `mul_le_mul_of_nonneg_left hMT (by positivity : (0 : ℝ) ≤ M * T)`. Combine the equalities or inequalities in the displayed calculation.

Establish `h1 : cR / Real.log ((M : ℝ) * (|ρ.im| + 2)) < 1 - ρ.re` using `by linarith`. Rewrite `h1` using `[div_lt_iff₀ hlogρ0]`. Establish `hδ0 : 0 < 1 - ρ.re`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Use `mul_nonpos_of_nonpos_of_nonneg h hlogρ0.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `mul_le_mul_of_nonneg_left hlogρ hδ0.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem region_gap : ∃ cR : ℝ, 0 < cR ∧ ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (β₁ T c₁ : ℝ)
    (ρ : ℂ), 3 ≤ M → 2 ≤ T → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 → 0 < c₁ → c₁ ≤ cR →
    1 - c₁ / Real.log ((M : ℝ) * T) < β₁ → IsLZero χ ρ → |ρ.im| ≤ T → (χ, ρ) ≠ (χ₁, (β₁ : ℂ)) →
    cR / 2 ≤ (1 - ρ.re) * Real.log ((M : ℝ) * T) := by
  obtain ⟨cR, hcR, hZ⟩ := Formalism.ZeroFreeDirichlet.zFRDirichlet
  refine ⟨cR, hcR, ?_⟩
  intro M _ χ₁ χ β₁ T c₁ ρ hM hT2 hχ1ne hLz hc₁0 hc₁ hβ₁ hρ hρim hne
  have hLg1 := logMT_ge_one M T hM hT2
  have hLg0 : 0 < Real.log ((M : ℝ) * T) := by linarith
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog2M : Real.log ((M : ℝ) * (|((β₁ : ℂ)).im| + 2)) ≤ Real.log ((M : ℝ) * T) := by
    simp only [Complex.ofReal_im, abs_zero, zero_add]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlog2M0 : 0 < Real.log ((M : ℝ) * (|((β₁ : ℂ)).im| + 2)) := by
    apply Real.log_pos; simp only [Complex.ofReal_im, abs_zero, zero_add]; nlinarith
  have hreg : InRegion cR M (β₁ : ℂ) := by
    unfold InRegion
    have h1 : c₁ / Real.log ((M : ℝ) * T) ≤ cR / Real.log ((M : ℝ) * (|((β₁ : ℂ)).im| + 2)) := by
      rw [div_le_div_iff₀ hLg0 hlog2M0]
      have h2 := mul_le_mul_of_nonneg_left hlog2M hc₁0.le
      have h3 := mul_le_mul_of_nonneg_right hc₁ hLg0.le
      linarith only [h2, h3]
    rw [Complex.ofReal_re]; linarith only [h1, hβ₁]
  have hLz' : IsLZero χ₁ (β₁ : ℂ) := ⟨Or.inl hχ1ne, hLz⟩
  have hZ1 := (hZ M χ₁ (β₁ : ℂ) hreg hLz').2.2.2.2
  have hnreg : ¬ InRegion cR M ρ := by
    intro h
    obtain ⟨h1, h2⟩ := hZ1 χ ρ h hρ
    exact hne (Prod.ext h1 h2)
  unfold InRegion at hnreg
  push Not at hnreg
  have hlogρ0 : 0 < Real.log ((M : ℝ) * (|ρ.im| + 2)) := by
    apply Real.log_pos; have := abs_nonneg ρ.im; nlinarith
  have hlogρ : Real.log ((M : ℝ) * (|ρ.im| + 2)) ≤ 2 * Real.log ((M : ℝ) * T) := by
    rw [show (2 : ℝ) * Real.log ((M : ℝ) * T) = Real.log (((M : ℝ) * T) ^ 2) by
      rw [Real.log_pow]; push_cast; ring]
    apply Real.log_le_log (by have := abs_nonneg ρ.im; positivity)
    have : |ρ.im| + 2 ≤ 2 * T := by linarith
    have hM0 : (0 : ℝ) ≤ M := by positivity
    have hMT : (2 : ℝ) ≤ M * T := by nlinarith
    have hMT2 := mul_le_mul_of_nonneg_left hMT (by positivity : (0 : ℝ) ≤ M * T)
    calc (M : ℝ) * (|ρ.im| + 2) ≤ M * (2 * T) := mul_le_mul_of_nonneg_left this hM0
      _ ≤ _ := by rw [sq]; linarith
  have h1 : cR / Real.log ((M : ℝ) * (|ρ.im| + 2)) < 1 - ρ.re := by linarith
  rw [div_lt_iff₀ hlogρ0] at h1
  have hδ0 : 0 < 1 - ρ.re := by
    by_contra h; push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h hlogρ0.le
    linarith
  have := mul_le_mul_of_nonneg_left hlogρ hδ0.le
  linarith

end DHF

/- English proof (translation)
Introduce `hT hI`. Take `⟨cT, AT, BT, hcT, hTur⟩` from `hT`. Take `⟨C, hC, hIneq⟩` from `hI`. Take `⟨cR, hcR, hZ⟩` from `DHF.region_gap`. Use `set c : ℝ := min cR (1 / 20) with hc_def`.

Establish `hc0 : 0 < c` using `lt_min hcR (by norm_num)`. Establish `hccR : c ≤ cR` using `min_le_left _ _`. Establish `hc20 : c ≤ 1 / 20` using `min_le_right _ _`. Use `set A : ℕ := max AT 1 with hA_def`. Use `set B : ℕ := max BT 1 with hB_def`.

Establish `hA1 : 1 ≤ A` using `le_max_right _ _`. Establish `hB1 : 1 ≤ B` using `le_max_right _ _`. Use `set c' : ℝ := min cT (1 / 2) with hc'_def`. Establish `hc'0 : 0 < c'` using `lt_min hcT (by norm_num)`. Establish `hc'2 : c' ≤ 1 / 2` using `min_le_right _ _`.

Establish `hTur' : ∀ (n K : ℕ) (z : Fin n → ℂ), 1 ≤ n → B * n ≤ K → (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) → (∀ i, ‖z i‖ ^ 2 ≤ 2 * (z i).re) → ∃ k : ℕ, K ≤ k ∧ k ≤ A * K ∧ c' ^ K ≤ (∑ i, z i ^ k).re`. Introduce `n K z hn hBn h1 h2 h3`. Establish `hBn' : BT * n ≤ K` using `le_trans (Nat.mul_le_mul_right _ (le_max_left _ _)) hBn`. Take `⟨k, hk1, hk2, hk3⟩` from `hTur n K z hn hBn' h1 h2 h3`. Use `⟨k, hk1, le_trans hk2 (Nat.mul_le_mul_right _ (le_max_left _ _)), le_trans ?_ hk3⟩` and prove the remaining obligations.

Conclude with `pow_le_pow_left₀ hc'0.le (min_le_left _ _) K`. Use `set q : ℝ := c' / 2 ^ A with hq_def`. Establish `h2A : (2 : ℝ) ≤ 2 ^ A`. Combine the equalities or inequalities in the displayed calculation. Establish `hq0 : 0 < q` using `by positivity`.

Establish `hq4 : q ≤ 1 / 4`. Rewrite using `[hq_def, div_le_iff₀ (by positivity)]; nlinarith`. Use `set ε : ℝ := q / 4 with hε_def`. Establish `hε0 : 0 < ε` using `by positivity`. Use `set c₀ : ℝ := q ^ 2 / 200 with hc₀_def`.

Establish `hc₀0 : 0 < c₀` using `by positivity`. Establish `hc₀s : c₀ ≤ 1 / 3200`. Rewrite using `[hc₀_def]`. Establish `: q ^ 2 ≤ (1 / 4) ^ 2` using `pow_le_pow_left₀ hq0.le hq4 2`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `set l : ℝ := -Real.log q with hl_def`. Use `set b : ℝ := 2 * B / ε ^ 2 + 4 with hb_def`. Establish `hb0 : 0 ≤ b` using `by positivity`. Use `set K0m : ℝ := b + 64 * A * Real.exp (l * b) + 1 with hK0m_def`. Establish `hK0m : 0 < K0m` using `by positivity`.

Establish `hl0 : 0 ≤ l`. Rewrite using `[hl_def]; have := Real.log_nonpos hq0.le (by linarith); linarith`. Use `set c₂ : ℝ := min (c / (2 * K0m)) (ε ^ 2 / (25 * B * C * (2 * l + 2))) with hc₂_def`. Establish `hc₂0 : 0 < c₂` using `lt_min (by positivity) (by positivity)`. Establish `hc₂a : c₂ ≤ c / (2 * K0m)` using `min_le_left _ _`.

Establish `hc₂b : c₂ ≤ ε ^ 2 / (25 * B * C * (2 * l + 2))` using `min_le_right _ _`. Use `set c₁ : ℝ := c / 2 with hc₁_def`. Establish `hc₁0 : 0 < c₁` using `by positivity`. Use `clear_value c A B c' q ε c₀ l b K0m c₂ c₁`. Use `⟨c₀, c₁, c₂, hc₀0, hc₁0, hc₂0, ?_⟩` and prove the remaining obligations.

Introduce `M _ χ₁ χ β₁ T ρ hM hT2 hχ1sq hχ1ne hLz hβ₁ hβ1 hρ hρre hρim hne`. Establish `hLg1` using `DHF.logMT_ge_one M T hM hT2`. Use `set large₂ : ℝ := Real.log ((M : ℝ) * T) with hLg_def`. Establish `hLg0 : 0 < large₂` using `by linarith`. Use `set lam : ℝ := 1 - β₁ with hlam_def`.

Establish `hlam0 : 0 < lam` using `by linarith`. Establish `hlamL : lam * large₂ < c₁`. Establish `: lam < c₁ / large₂` using `by linarith`. Rewrite `this` using `[lt_div_iff₀ hLg0]`. Then use the resulting hypothesis. Establish `hδL` using `hZ M χ₁ χ β₁ T c₁ ρ hM hT2 hχ1ne hLz hc₁0 (by linarith) hβ₁ hρ hρim hne`.

Use `set δ : ℝ := 1 - ρ.re with hδ_def`. Establish `hδL' : c₁ ≤ δ * large₂` using `by linarith`. Establish `hδ0 : 0 < δ`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Use `mul_nonpos_of_nonpos_of_nonneg h hLg0.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `set K0 : ℝ := Real.log (c₁ / (lam * large₂)) with hK0_def`. Establish `hexpK0 : Real.exp K0 = c₁ / (lam * large₂)` using `Real.exp_log (by positivity)`. Rewrite using `[div_le_iff₀ hLg0]`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hK0big : K0m < K0`. Establish `h1 : c₂ * K0m ≤ c / 2`. Combine the equalities or inequalities in the displayed calculation.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Use `mul_le_mul_of_nonneg_left h hc₂0.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlamη : lam / δ ≤ Real.exp (-K0)`.

Rewrite using `[Real.exp_neg, hexpK0, inv_div, div_le_div_iff₀ hδ0 hc₁0]`. Use `mul_le_mul_of_nonneg_left hδL' hlam0.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hβ20 : 19 / 20 ≤ β₁`. Establish `: c₁ / large₂ ≤ c₁` using `div_le_self hc₁0.le hLg1`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨N, w, hw, ⟨i0, hi0⟩, -, -, hpow⟩` from `hIneq M χ₁ χ β₁ T δ ρ hM hT2 hχ1sq hχ1ne hLz hβ20 hβ1 hρ (by linarith) hρim hne hδ0 (by linarith)`. Conclude with `DHF.core c' C A B hc'0 hc'2 hA1 hB1 hC hTur' q ε l b c₂ hq_def hε_def hl_def hb_def hc₂0 hc₂b large₂ lam δ K0 (by linarith) hδ0 (by linarith) hlam0 hlamη hcon hLg0 N w hw ⟨i0, hi0⟩ hpow`.
-/
theorem deuring_heilbronn_finish : DHFinishOf := by
  intro hT hI
  obtain ⟨cT, AT, BT, hcT, hTur⟩ := hT
  obtain ⟨C, hC, hIneq⟩ := hI
  obtain ⟨cR, hcR, hZ⟩ := DHF.region_gap
  set c : ℝ := min cR (1 / 20) with hc_def
  have hc0 : 0 < c := lt_min hcR (by norm_num)
  have hccR : c ≤ cR := min_le_left _ _
  have hc20 : c ≤ 1 / 20 := min_le_right _ _
  set A : ℕ := max AT 1 with hA_def
  set B : ℕ := max BT 1 with hB_def
  have hA1 : 1 ≤ A := le_max_right _ _
  have hB1 : 1 ≤ B := le_max_right _ _
  set c' : ℝ := min cT (1 / 2) with hc'_def
  have hc'0 : 0 < c' := lt_min hcT (by norm_num)
  have hc'2 : c' ≤ 1 / 2 := min_le_right _ _
  have hTur' : ∀ (n K : ℕ) (z : Fin n → ℂ), 1 ≤ n → B * n ≤ K →
      (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) → (∀ i, ‖z i‖ ^ 2 ≤ 2 * (z i).re) →
      ∃ k : ℕ, K ≤ k ∧ k ≤ A * K ∧ c' ^ K ≤ (∑ i, z i ^ k).re := by
    intro n K z hn hBn h1 h2 h3
    have hBn' : BT * n ≤ K := le_trans (Nat.mul_le_mul_right _ (le_max_left _ _)) hBn
    obtain ⟨k, hk1, hk2, hk3⟩ := hTur n K z hn hBn' h1 h2 h3
    refine ⟨k, hk1, le_trans hk2 (Nat.mul_le_mul_right _ (le_max_left _ _)), le_trans ?_ hk3⟩
    exact pow_le_pow_left₀ hc'0.le (min_le_left _ _) K
  set q : ℝ := c' / 2 ^ A with hq_def
  have h2A : (2 : ℝ) ≤ 2 ^ A := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ A := pow_le_pow_right₀ (by norm_num) hA1
  have hq0 : 0 < q := by positivity
  have hq4 : q ≤ 1 / 4 := by
    rw [hq_def, div_le_iff₀ (by positivity)]; nlinarith
  set ε : ℝ := q / 4 with hε_def
  have hε0 : 0 < ε := by positivity
  set c₀ : ℝ := q ^ 2 / 200 with hc₀_def
  have hc₀0 : 0 < c₀ := by positivity
  have hc₀s : c₀ ≤ 1 / 3200 := by
    rw [hc₀_def]; have : q ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ hq0.le hq4 2
    linarith
  set l : ℝ := -Real.log q with hl_def
  set b : ℝ := 2 * B / ε ^ 2 + 4 with hb_def
  have hb0 : 0 ≤ b := by positivity
  set K0m : ℝ := b + 64 * A * Real.exp (l * b) + 1 with hK0m_def
  have hK0m : 0 < K0m := by positivity
  have hl0 : 0 ≤ l := by
    rw [hl_def]; have := Real.log_nonpos hq0.le (by linarith); linarith
  set c₂ : ℝ := min (c / (2 * K0m)) (ε ^ 2 / (25 * B * C * (2 * l + 2))) with hc₂_def
  have hc₂0 : 0 < c₂ := lt_min (by positivity) (by positivity)
  have hc₂a : c₂ ≤ c / (2 * K0m) := min_le_left _ _
  have hc₂b : c₂ ≤ ε ^ 2 / (25 * B * C * (2 * l + 2)) := min_le_right _ _
  set c₁ : ℝ := c / 2 with hc₁_def
  have hc₁0 : 0 < c₁ := by positivity
  clear_value c A B c' q ε c₀ l b K0m c₂ c₁
  refine ⟨c₀, c₁, c₂, hc₀0, hc₁0, hc₂0, ?_⟩
  intro M _ χ₁ χ β₁ T ρ hM hT2 hχ1sq hχ1ne hLz hβ₁ hβ1 hρ hρre hρim hne
  have hLg1 := DHF.logMT_ge_one M T hM hT2
  set large₂ : ℝ := Real.log ((M : ℝ) * T) with hLg_def
  have hLg0 : 0 < large₂ := by linarith
  set lam : ℝ := 1 - β₁ with hlam_def
  have hlam0 : 0 < lam := by linarith
  have hlamL : lam * large₂ < c₁ := by
    have : lam < c₁ / large₂ := by linarith
    rwa [lt_div_iff₀ hLg0] at this
  have hδL := hZ M χ₁ χ β₁ T c₁ ρ hM hT2 hχ1ne hLz hc₁0 (by linarith) hβ₁ hρ hρim hne
  set δ : ℝ := 1 - ρ.re with hδ_def
  have hδL' : c₁ ≤ δ * large₂ := by linarith
  have hδ0 : 0 < δ := by
    by_contra h; push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h hLg0.le
    linarith
  set K0 : ℝ := Real.log (c₁ / (lam * large₂)) with hK0_def
  have hexpK0 : Real.exp K0 = c₁ / (lam * large₂) := Real.exp_log (by positivity)
  rw [div_le_iff₀ hLg0]
  by_contra hcon
  push Not at hcon
  have hK0big : K0m < K0 := by
    have h1 : c₂ * K0m ≤ c / 2 := by
      calc c₂ * K0m ≤ c / (2 * K0m) * K0m := mul_le_mul_of_nonneg_right hc₂a hK0m.le
        _ = c / 2 := by field_simp
    by_contra h; push Not at h
    have := mul_le_mul_of_nonneg_left h hc₂0.le
    linarith
  have hlamη : lam / δ ≤ Real.exp (-K0) := by
    rw [Real.exp_neg, hexpK0, inv_div, div_le_div_iff₀ hδ0 hc₁0]
    have := mul_le_mul_of_nonneg_left hδL' hlam0.le
    linarith
  have hβ20 : 19 / 20 ≤ β₁ := by
    have : c₁ / large₂ ≤ c₁ := div_le_self hc₁0.le hLg1
    linarith
  obtain ⟨N, w, hw, ⟨i0, hi0⟩, -, -, hpow⟩ :=
    hIneq M χ₁ χ β₁ T δ ρ hM hT2 hχ1sq hχ1ne hLz hβ20 hβ1 hρ (by linarith) hρim hne hδ0 (by linarith)
  exact DHF.core c' C A B hc'0 hc'2 hA1 hB1 hC hTur' q ε l b c₂ hq_def hε_def hl_def hb_def hc₂0 hc₂b
    large₂ lam δ K0 (by linarith) hδ0 (by linarith) hlam0 hlamη hcon hLg0 N w hw ⟨i0, hi0⟩ hpow

end Formalism.HermitianLattices.Ext.PrimesInProgressions
