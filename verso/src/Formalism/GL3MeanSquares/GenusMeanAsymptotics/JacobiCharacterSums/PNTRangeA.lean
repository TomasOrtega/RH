import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTEOf

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

/- English proof (translation)
Establish `h : (Finset.univ : Finset (DirichletCharacter ℂ M)).card = M.totient`. Rewrite using `[Finset.card_univ, ← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ M]`. Rewrite using `[h]`. Conclude with `Nat.totient_le M` after adjusting the coercions.
-/
theorem rangeA_card_char_le (M : ℕ) [NeZero M] :
    ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) ≤ M := by
  have h : (Finset.univ : Finset (DirichletCharacter ℂ M)).card = M.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ M]
  rw [h]
  exact_mod_cast Nat.totient_le M

/- English proof (translation)
Establish `hy0 : 0 < y` using `by linarith`. Establish `hL : 0 ≤ Real.log y` using `Real.log_nonneg (by linarith)`. Use `set s := Real.sqrt (Real.log y) with hs`. Establish `hs0 : 0 ≤ s` using `Real.sqrt_nonneg _`. Establish `hss : s * s = Real.log y` using `Real.mul_self_sqrt hL`.

Establish `hMr : (8 : ℝ) ≤ M` using `by exact_mod_cast hM`. Establish `hZ` using `cZ_pos`. Unfold `InRegion at hr`. Simplify using `only [Complex.ofReal_im, abs_zero, zero_add, Complex.ofReal_re, not_le] at hr`. Use `set l := Real.log ((M : ℝ) * 2) with hl'`.

Establish `hl0 : 0 < l` using `Real.log_pos (by linarith)`. Establish `hl2 : l ≤ 2 * Real.log M`. Rewrite using `[hl', Real.log_mul (by linarith) (by norm_num)]`. Establish `: Real.log 2 ≤ Real.log M` using `Real.log_le_log (by norm_num) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hl3 : l ≤ 2 * cZ * s` using `by nlinarith`. Establish `h1 : cZ < (1 - β) * l`. Establish `: cZ / l < 1 - β` using `by linarith`. Rewrite `this` using `[div_lt_iff₀ hl0]`. Then use the resulting hypothesis. Establish `hb1 : 0 < 1 - β`.

Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_lt]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : s / 2 ≤ (1 - β) * Real.log y`. Establish `h3 : cZ * s ≤ (1 - β) * (2 * cZ * s) * s`.

Establish `: (1 - β) * l ≤ (1 - β) * (2 * cZ * s)` using `mul_le_mul_of_nonneg_left hl3 hb1.le`. Use the polynomial consequences of the given equalities and inequalities. Establish `h4 : cZ * (s / 2) ≤ cZ * ((1 - β) * (s * s))` using `by nlinarith`. Rewrite using `[← hss]`. Conclude with `le_of_mul_le_mul_left h4 hZ`.

Rewrite using `[norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < β)]`. Establish `h5 : y ^ β = y * Real.exp (-((1 - β) * Real.log y))`. Rewrite using `[Real.rpow_def_of_pos hy0]`. Use `nth_rewrite 2 [← Real.exp_log hy0]`. Rewrite using `[← Real.exp_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `h6 : Real.exp (-((1 - β) * Real.log y)) ≤ Real.exp (-(s / 2))` using `Real.exp_le_exp.mpr (by linarith)`. Rewrite using `[div_le_iff₀ (by linarith), h5]`. Establish `h7 : 0 < Real.exp (-(s / 2))` using `Real.exp_pos _`.

Establish `: y * Real.exp (-((1 - β) * Real.log y)) ≤ y * Real.exp (-(s / 2))` using `mul_le_mul_of_nonneg_left h6 hy0.le`. Establish `h8 : 0 ≤ y * Real.exp (-(s / 2))` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem rangeA_far_term (M : ℕ) (hM : 8 ≤ M) (y cA β : ℝ) (hy : 2 ≤ y) (hcA : cA ≤ cZ)
    (hl : Real.log M ≤ cA * Real.sqrt (Real.log y)) (hβ : 1 / 2 ≤ β)
    (hr : ¬ InRegion cZ M (β : ℂ)) :
    ‖(y : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ 2 * y * Real.exp (-(Real.sqrt (Real.log y) / 2)) := by
  have hy0 : 0 < y := by linarith
  have hL : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  set s := Real.sqrt (Real.log y) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = Real.log y := Real.mul_self_sqrt hL
  have hMr : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hZ := cZ_pos
  unfold InRegion at hr
  simp only [Complex.ofReal_im, abs_zero, zero_add, Complex.ofReal_re, not_le] at hr
  set l := Real.log ((M : ℝ) * 2) with hl'
  have hl0 : 0 < l := Real.log_pos (by linarith)
  have hl2 : l ≤ 2 * Real.log M := by
    rw [hl', Real.log_mul (by linarith) (by norm_num)]
    have : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hl3 : l ≤ 2 * cZ * s := by nlinarith
  have h1 : cZ < (1 - β) * l := by
    have : cZ / l < 1 - β := by linarith
    rwa [div_lt_iff₀ hl0] at this
  have hb1 : 0 < 1 - β := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have h2 : s / 2 ≤ (1 - β) * Real.log y := by
    have h3 : cZ * s ≤ (1 - β) * (2 * cZ * s) * s := by
      have : (1 - β) * l ≤ (1 - β) * (2 * cZ * s) := mul_le_mul_of_nonneg_left hl3 hb1.le
      nlinarith
    have h4 : cZ * (s / 2) ≤ cZ * ((1 - β) * (s * s)) := by nlinarith
    rw [← hss]
    exact le_of_mul_le_mul_left h4 hZ
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.ofReal_re, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < β)]
  have h5 : y ^ β = y * Real.exp (-((1 - β) * Real.log y)) := by
    rw [Real.rpow_def_of_pos hy0]
    nth_rewrite 2 [← Real.exp_log hy0]
    rw [← Real.exp_add]
    congr 1
    ring
  have h6 : Real.exp (-((1 - β) * Real.log y)) ≤ Real.exp (-(s / 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [div_le_iff₀ (by linarith), h5]
  have h7 : 0 < Real.exp (-(s / 2)) := Real.exp_pos _
  have : y * Real.exp (-((1 - β) * Real.log y)) ≤ y * Real.exp (-(s / 2)) :=
    mul_le_mul_of_nonneg_left h6 hy0.le
  have h8 : 0 ≤ y * Real.exp (-(s / 2)) := by positivity
  nlinarith

/- English proof (translation)
Use `⟨by simp, by simp, ?_⟩` and prove the remaining obligations. Introduce `s hs hz`. Take `⟨β₁, h1, h2, -⟩` from `zero_in_region M hM χ s hs hz`. Conclude with `absurd (h2 ▸ hs) (h β₁ h1)`.
-/
theorem rangeA_excZeros_empty (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M)
    (h : ∀ β : ℝ, eOf M = some (χ, β) → ¬ InRegion cZ M (β : ℂ)) : ExcZeros cZ χ ∅ := by
  refine ⟨by simp, by simp, ?_⟩
  intro s hs hz
  obtain ⟨β₁, h1, h2, -⟩ := zero_in_region M hM χ s hs hz
  exact absurd (h2 ▸ hs) (h β₁ h1)

/- English proof (translation)
Establish `he` using `eOf_exc M _ h`. Establish `hz : IsLZero χ (β : ℂ)` using `⟨Or.inl he.2.1, he.2.2.1⟩`. Take `⟨-, -, -, hd⟩` from `zero_in_region M hM χ _ hr hz`. Use `⟨by simp, ?_, ?_⟩` and prove the remaining obligations. Introduce `b hb`.

Rewrite `hb` using `[Finset.mem_singleton]`. Substitute `hb` using the available equality. Conclude with `⟨he.2.1, hr, he.2.2.1, hd⟩`. Introduce `s hs hz'`. Take `⟨β₁, h1, h2, -⟩` from `zero_in_region M hM χ s hs hz'`.

Rewrite `h1` using `[h]`. Establish `: β = β₁` using `by simpa using h1`. Conclude with `⟨β, by simp, by rw [h2, this]⟩`.
-/
theorem rangeA_excZeros_single (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M) (β : ℝ)
    (h : eOf M = some (χ, β)) (hr : InRegion cZ M (β : ℂ)) : ExcZeros cZ χ {β} := by
  have he := eOf_exc M _ h
  have hz : IsLZero χ (β : ℂ) := ⟨Or.inl he.2.1, he.2.2.1⟩
  obtain ⟨-, -, -, hd⟩ := zero_in_region M hM χ _ hr hz
  refine ⟨by simp, ?_, ?_⟩
  · intro b hb
    rw [Finset.mem_singleton] at hb
    subst hb
    exact ⟨he.2.1, hr, he.2.2.1, hd⟩
  · intro s hs hz'
    obtain ⟨β₁, h1, h2, -⟩ := zero_in_region M hM χ s hs hz'
    rw [h] at h1
    have : β = β₁ := by simpa using h1
    exact ⟨β, by simp, by rw [h2, this]⟩

/- English proof (translation)
Establish `hM2 : 2 ≤ M` using `by omega`. Establish `hMr : (8 : ℝ) ≤ M` using `by exact_mod_cast hM`. Establish `hs0 : 0 ≤ Real.sqrt (Real.log y)` using `Real.sqrt_nonneg _`. Establish `hq : (M : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log y))`. Rewrite using `[← Real.exp_log (by linarith : (0 : ℝ) < M)]`.

Conclude with `Real.exp_le_exp.mpr (hl.trans (mul_le_mul_of_nonneg_right hcA' hs0))`. Establish `hE : 0 ≤ 2 * y * Real.exp (-(Real.sqrt (Real.log y) / 2))` using `by positivity`. Establish `H' : ∀ B : Finset ℝ, ExcZeros cZ χ B → ‖psiChi χ y - mainPsi none χ y + ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ C * y * Real.exp (-c * Real.sqrt (Real.log y))`. Introduce `B hB`. Establish `h0` using `H M χ B y hB hy hq`.

Simplify using `only [mainPsi, sub_zero]`. Use `h0` and compare the differences between its conclusion and the goal. Establish `hsome : ∀ (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ), mainPsi (some (χ₁, β₁)) χ y = mainPsi none χ y - (if χ = χ₁ then (y : ℂ) ^ (β₁ : ℂ) / (β₁ : ℂ) else 0)`. Introduce `χ₁ β₁`. Simplify using `only [mainPsi, sub_zero]`.

Reduce the equality to equality of the corresponding arguments. Break down `he : eOf M with _ | ⟨χ₁, β₁⟩` into its components or cases. Establish `h0` using `H' ∅ (rangeA_excZeros_empty M hM2 χ (by intro β hβ; rw [he] at hβ; simp at hβ))`. Simplify using `only [Finset.sum_empty, add_zero] at h0`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hsome]`. Distinguish the cases in `hχ : χ = χ₁`. Substitute `hχ` using the available equality. Rewrite using `[if_pos rfl, ← sub_add]`. Distinguish the cases in `hr : InRegion cZ M (β₁ : ℂ)`.

Establish `h0` using `H' {β₁} (rangeA_excZeros_single M hM2 χ β₁ he hr)`. Simplify using `only [Finset.sum_singleton] at h0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h0` using `H' ∅ (rangeA_excZeros_empty M hM2 χ (by`. Introduce `β hβ`.

Rewrite `hβ` using `[he]`. Establish `: β₁ = β` using `by simpa using hβ`. Rewrite using `[← this]`. Conclude with `hr))`. Simplify using `only [Finset.sum_empty, add_zero] at h0`.

Establish `hex` using `eOf_exc M _ he`. Establish `hβ : 1 / 2 ≤ β₁`. Establish `h1` using `hex.2.2.2.1`. Establish `hlog : 1 ≤ Real.log M`. Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`.

Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: 1 / (8 * Real.log M) ≤ 1 / 8`. Apply `one_div_le_one_div_of_le (by norm_num) (by linarith)` to reduce the goal to its premises. Simplify using `only at h1`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `rangeA_far_term M hM y cA β₁ hy hcA hl hβ hr`. Conclude with `(norm_add_le _ _).trans (add_le_add h0 h1)`. Establish `h0` using `H' ∅ (rangeA_excZeros_empty M hM2 χ (by`. Introduce `β hβ`.

Rewrite `hβ` using `[he]`. Establish `: χ₁ = χ`. Use `Option.some.inj hβ` as an intermediate fact. Conclude with `(Prod.mk.inj this).1`. Conclude with `absurd this.symm hχ))`.

Simplify using `only [Finset.sum_empty, add_zero] at h0`. Rewrite using `[if_neg hχ, sub_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rangeA_one_char (c C cA : ℝ)
    (H : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : Finset ℝ) (x : ℝ), ExcZeros cZ χ B → 2 ≤ x →
      (q : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log x)) →
      ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0) + ∑ β ∈ B, (x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)))
    (hcA : cA ≤ cZ) (hcA' : cA ≤ c) (M : ℕ) [NeZero M] (hM : 8 ≤ M) (y : ℝ) (hy : 2 ≤ y)
    (hl : Real.log M ≤ cA * Real.sqrt (Real.log y)) (χ : DirichletCharacter ℂ M) :
    ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      C * y * Real.exp (-c * Real.sqrt (Real.log y)) + 2 * y * Real.exp (-(Real.sqrt (Real.log y) / 2)) := by
  have hM2 : 2 ≤ M := by omega
  have hMr : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hs0 : 0 ≤ Real.sqrt (Real.log y) := Real.sqrt_nonneg _
  have hq : (M : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log y)) := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < M)]
    exact Real.exp_le_exp.mpr (hl.trans (mul_le_mul_of_nonneg_right hcA' hs0))
  have hE : 0 ≤ 2 * y * Real.exp (-(Real.sqrt (Real.log y) / 2)) := by positivity
  have H' : ∀ B : Finset ℝ, ExcZeros cZ χ B →
      ‖psiChi χ y - mainPsi none χ y + ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
        C * y * Real.exp (-c * Real.sqrt (Real.log y)) := by
    intro B hB
    have h0 := H M χ B y hB hy hq
    simp only [mainPsi, sub_zero]
    convert h0
  have hsome : ∀ (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ), mainPsi (some (χ₁, β₁)) χ y =
      mainPsi none χ y - (if χ = χ₁ then (y : ℂ) ^ (β₁ : ℂ) / (β₁ : ℂ) else 0) := by
    intro χ₁ β₁
    simp only [mainPsi, sub_zero]
    congr
  rcases he : eOf M with _ | ⟨χ₁, β₁⟩
  · have h0 := H' ∅ (rangeA_excZeros_empty M hM2 χ (by intro β hβ; rw [he] at hβ; simp at hβ))
    simp only [Finset.sum_empty, add_zero] at h0
    linarith
  · rw [hsome]
    by_cases hχ : χ = χ₁
    · subst hχ
      rw [if_pos rfl, ← sub_add]
      by_cases hr : InRegion cZ M (β₁ : ℂ)
      · have h0 := H' {β₁} (rangeA_excZeros_single M hM2 χ β₁ he hr)
        simp only [Finset.sum_singleton] at h0
        linarith
      · have h0 := H' ∅ (rangeA_excZeros_empty M hM2 χ (by
          intro β hβ; rw [he] at hβ
          have : β₁ = β := by simpa using hβ
          rw [← this]; exact hr))
        simp only [Finset.sum_empty, add_zero] at h0
        have hex := eOf_exc M _ he
        have hβ : 1 / 2 ≤ β₁ := by
          have h1 := hex.2.2.2.1
          have hlog : 1 ≤ Real.log M := by
            rw [Real.le_log_iff_exp_le (by linarith)]
            have := Real.exp_one_lt_d9
            linarith
          have : 1 / (8 * Real.log M) ≤ 1 / 8 := by
            apply one_div_le_one_div_of_le (by norm_num) (by linarith)
          simp only at h1
          linarith
        have h1 := rangeA_far_term M hM y cA β₁ hy hcA hl hβ hr
        exact (norm_add_le _ _).trans (add_le_add h0 h1)
    · have h0 := H' ∅ (rangeA_excZeros_empty M hM2 χ (by
          intro β hβ; rw [he] at hβ
          have : χ₁ = χ := by
            have := Option.some.inj hβ
            exact (Prod.mk.inj this).1
          exact absurd this.symm hχ))
      simp only [Finset.sum_empty, add_zero] at h0
      rw [if_neg hχ, sub_zero]
      linarith

/- English proof (translation)
Take `⟨c, C, hc, H⟩` from `psiChiBound cZ cZ_pos cZ_le`. Take `⟨c₁, hc₁, H₁⟩` from `etaOf_lower 1 one_pos`. Establish `hZ` using `cZ_pos`. Establish `hZ'` using `cZ_le`. Use `⟨min (c / 4) cZ, min (c / 2) (2 / 5), (|C| + 2) / c₁, lt_min (by linarith) hZ, lt_min (by linarith) (by norm_num), ?_⟩` and prove the remaining obligations.

Introduce `M _ h8 y hy hl`. Establish `hM : 8 ≤ M` using `Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h8`. Establish `hMr : (8 : ℝ) ≤ M` using `by exact_mod_cast hM`. Establish `hy0 : 0 < y` using `by linarith`. Use `set cA := min (c / 4) cZ with hcA`.

Use `set c' := min (c / 2) (2 / 5 : ℝ) with hc'`. Use `set s := Real.sqrt (Real.log y) with hs`. Establish `hs0 : 0 ≤ s` using `Real.sqrt_nonneg _`. Establish `hA1 : cA ≤ c / 4` using `min_le_left _ _`. Establish `hA2 : cA ≤ cZ` using `min_le_right _ _`.

Establish `hc1 : c' ≤ c / 2` using `min_le_left _ _`. Establish `hc2 : c' ≤ 2 / 5` using `min_le_right _ _`. Establish `hsum : ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤ (M : ℝ) * (|C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2)))`. Establish `hb : 0 ≤ |C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2))` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `χ _`. Establish `h0` using `rangeA_one_char c C cA H hA2 (by linarith) M hM y hy hl χ`. Establish `h1 : C * y * Real.exp (-c * s) ≤ |C| * y * Real.exp (-c * s)`. Establish `: 0 ≤ y * Real.exp (-c * s)` using `by positivity`.

Establish `h2` using `mul_le_mul_of_nonneg_right (le_abs_self C) this`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) * (|C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2))) := by`. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`.

Use `_ ≤ _ := mul_le_mul_of_nonneg_right (rangeA_card_char_le M) hb`. Establish `heta : c₁ ≤ etaOf M * M`. Establish `h0` using `H₁ M (by omega)`. Rewrite `h0` using `[Real.rpow_neg_one]`. Establish `h1` using `mul_le_mul_of_nonneg_right h0 (by linarith : (0 : ℝ) ≤ M)`.

Rewrite `h1` using `[mul_assoc, inv_mul_cancel₀ (by linarith), mul_one]`. Then use the resulting hypothesis. Establish `hMe : (M : ℝ) ≤ Real.exp (cA * s)`. Rewrite using `[← Real.exp_log (by linarith : (0 : ℝ) < M)]`. Conclude with `Real.exp_le_exp.mpr hl`. Establish `hMM : (M : ℝ) * M ≤ Real.exp (2 * cA * s)`.

Establish `: Real.exp (2 * cA * s) = Real.exp (cA * s) * Real.exp (cA * s)`. Rewrite using `[← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `mul_le_mul hMe hMe (by linarith) (Real.exp_pos _).le`. Establish `e1 : (M : ℝ) * M * Real.exp (-c * s) ≤ Real.exp (-(c' * s))`. Combine the equalities or inequalities in the displayed calculation. Establish `e2 : (M : ℝ) * M * Real.exp (-(s / 2)) ≤ Real.exp (-(c' * s))`. Combine the equalities or inequalities in the displayed calculation.

Use `hsum.trans ?_` and prove the remaining obligations. Use `set X := Real.exp (-(c' * s)) with hX`. Establish `hX0 : 0 < X` using `Real.exp_pos _`. Establish `hM0 : (0 : ℝ) < M` using `by linarith`. Establish `key : (M : ℝ) * ((M : ℝ) * (|C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2)))) ≤ (|C| + 2) * y * X`.

Establish `a1 : |C| * y * ((M : ℝ) * M * Real.exp (-c * s)) ≤ |C| * y * X` using `mul_le_mul_of_nonneg_left e1 (by positivity)`. Establish `a2 : 2 * y * ((M : ℝ) * M * Real.exp (-(s / 2))) ≤ 2 * y * X` using `mul_le_mul_of_nonneg_left e2 (by positivity)`. Use the polynomial consequences of the given equalities and inequalities. Establish `key2 : (|C| + 2) * y * X ≤ (M : ℝ) * ((|C| + 2) / c₁ * y * etaOf M * X)`. Establish `: (M : ℝ) * ((|C| + 2) / c₁ * y * etaOf M * X) = (|C| + 2) * y * X * ((etaOf M * M) / c₁)`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Establish `h1 : 1 ≤ (etaOf M * M) / c₁` using `by rwa [le_div_iff₀ hc₁, one_mul]`. Establish `h2 : 0 ≤ (|C| + 2) * y * X` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `le_of_mul_le_mul_left (key.trans key2) hM0`.
-/
theorem psi_relative_near_range : PsiRelA := by
  obtain ⟨c, C, hc, H⟩ := psiChiBound cZ cZ_pos cZ_le
  obtain ⟨c₁, hc₁, H₁⟩ := etaOf_lower 1 one_pos
  have hZ := cZ_pos
  have hZ' := cZ_le
  refine ⟨min (c / 4) cZ, min (c / 2) (2 / 5), (|C| + 2) / c₁, lt_min (by linarith) hZ,
    lt_min (by linarith) (by norm_num), ?_⟩
  intro M _ h8 y hy hl
  have hM : 8 ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h8
  have hMr : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hy0 : 0 < y := by linarith
  set cA := min (c / 4) cZ with hcA
  set c' := min (c / 2) (2 / 5 : ℝ) with hc'
  set s := Real.sqrt (Real.log y) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hA1 : cA ≤ c / 4 := min_le_left _ _
  have hA2 : cA ≤ cZ := min_le_right _ _
  have hc1 : c' ≤ c / 2 := min_le_left _ _
  have hc2 : c' ≤ 2 / 5 := min_le_right _ _
  have hsum : ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      (M : ℝ) * (|C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2))) := by
    have hb : 0 ≤ |C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2)) := by positivity
    calc ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖
        ≤ ∑ _χ : DirichletCharacter ℂ M, (|C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2))) := by
          apply Finset.sum_le_sum
          intro χ _
          have h0 := rangeA_one_char c C cA H hA2 (by linarith) M hM y hy hl χ
          have h1 : C * y * Real.exp (-c * s) ≤ |C| * y * Real.exp (-c * s) := by
            have : 0 ≤ y * Real.exp (-c * s) := by positivity
            have h2 := mul_le_mul_of_nonneg_right (le_abs_self C) this
            linarith
          linarith
      _ = ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) *
            (|C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (rangeA_card_char_le M) hb
  have heta : c₁ ≤ etaOf M * M := by
    have h0 := H₁ M (by omega)
    rw [Real.rpow_neg_one] at h0
    have h1 := mul_le_mul_of_nonneg_right h0 (by linarith : (0 : ℝ) ≤ M)
    rwa [mul_assoc, inv_mul_cancel₀ (by linarith), mul_one] at h1
  have hMe : (M : ℝ) ≤ Real.exp (cA * s) := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < M)]
    exact Real.exp_le_exp.mpr hl
  have hMM : (M : ℝ) * M ≤ Real.exp (2 * cA * s) := by
    have : Real.exp (2 * cA * s) = Real.exp (cA * s) * Real.exp (cA * s) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]
    exact mul_le_mul hMe hMe (by linarith) (Real.exp_pos _).le
  have e1 : (M : ℝ) * M * Real.exp (-c * s) ≤ Real.exp (-(c' * s)) := by
    calc (M : ℝ) * M * Real.exp (-c * s) ≤ Real.exp (2 * cA * s) * Real.exp (-c * s) :=
          mul_le_mul_of_nonneg_right hMM (Real.exp_pos _).le
      _ = Real.exp (2 * cA * s + -c * s) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have e2 : (M : ℝ) * M * Real.exp (-(s / 2)) ≤ Real.exp (-(c' * s)) := by
    calc (M : ℝ) * M * Real.exp (-(s / 2)) ≤ Real.exp (2 * cA * s) * Real.exp (-(s / 2)) :=
          mul_le_mul_of_nonneg_right hMM (Real.exp_pos _).le
      _ = Real.exp (2 * cA * s + -(s / 2)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  refine hsum.trans ?_
  set X := Real.exp (-(c' * s)) with hX
  have hX0 : 0 < X := Real.exp_pos _
  have hM0 : (0 : ℝ) < M := by linarith

  have key : (M : ℝ) * ((M : ℝ) * (|C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2)))) ≤
      (|C| + 2) * y * X := by
    have a1 : |C| * y * ((M : ℝ) * M * Real.exp (-c * s)) ≤ |C| * y * X :=
      mul_le_mul_of_nonneg_left e1 (by positivity)
    have a2 : 2 * y * ((M : ℝ) * M * Real.exp (-(s / 2))) ≤ 2 * y * X :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    nlinarith
  have key2 : (|C| + 2) * y * X ≤ (M : ℝ) * ((|C| + 2) / c₁ * y * etaOf M * X) := by
    have : (M : ℝ) * ((|C| + 2) / c₁ * y * etaOf M * X) = (|C| + 2) * y * X * ((etaOf M * M) / c₁) := by
      field_simp
    rw [this]
    have h1 : 1 ≤ (etaOf M * M) / c₁ := by rwa [le_div_iff₀ hc₁, one_mul]
    have h2 : 0 ≤ (|C| + 2) * y * X := by positivity
    nlinarith
  exact le_of_mul_le_mul_left (key.trans key2) hM0

end Formalism.HermitianLattices.Ext.PrimesInProgressions
