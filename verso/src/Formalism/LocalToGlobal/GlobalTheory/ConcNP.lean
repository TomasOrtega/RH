import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
import Formalism.PadicSubsetSums.StableGradedCounts.DominantNumbersEighthOfSharp

open NumberField

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ConcN

open Formalism Formalism.LFunctionChainParameters Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.FamCol

/- English proof (translation)
The claim follows from `h.irr`.
-/
theorem irrAt_of_rowTr {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} [Fintype I]
    {C : ColObj K I} {R : RowArg C} {x ε : ℝ} (h : FamColC.RowTr C R x ε) : IrrAt R x ε := h.irr

/- English proof (translation)
Both sides reduce to the same expression.
-/
example {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} [Fintype I]
    {C : ColObj K I} {R : RowArg C} {x ε : ℝ} :
    IrrAt R x ε = ((1 - LChain6.E7 x ε) * (Fintype.card (R.κ ⊕ R.κ₁) : ℝ) ≤ (Fintype.card R.κ : ℝ)) := rfl

/- English proof (translation)
The claim follows from `FamColC.RowTr.irr h`.
-/
example {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} [Fintype I]
    {C : ColObj K I} {R : RowArg C} {x ε : ℝ} (h : FamColC.RowTr C R x ε) : IrrAt R x ε := FamColC.RowTr.irr h

/- English proof (translation)
Introduce `K _ _ _ I C R x ε εC W₁ W₂ hS hN`. Unfold `ShareAt at hS`. Unfold `IrrAt`. Establish `hcard : (Fintype.card (R.κ ⊕ R.κ₁) : ℝ) = Fintype.card R.κ + Fintype.card R.κ₁`. Rewrite using `[Fintype.card_sum]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hle` using `le_trans hS hN`. Break down `(Nat.cast_nonneg (Fintype.card (R.κ ⊕ R.κ₁)) : (0 : ℝ) ≤ _).eq_or_lt with h0 | hpos` into its components or cases. Rewrite using `[← h0, mul_zero]`.

Conclude with `Nat.cast_nonneg _`. Establish `hb` using `(div_le_iff₀ hpos).mp hle`. Use polynomial arithmetic with `[hb, hcard]`.
-/
theorem irreducible_of_share : IrreducibleOfShare := by
  intro K _ _ _ I C R x ε εC W₁ W₂ hS hN
  unfold ShareAt at hS
  unfold IrrAt
  have hcard : (Fintype.card (R.κ ⊕ R.κ₁) : ℝ) = Fintype.card R.κ + Fintype.card R.κ₁ := by
    rw [Fintype.card_sum]; push_cast; ring
  have hle := le_trans hS hN
  rcases (Nat.cast_nonneg (Fintype.card (R.κ ⊕ R.κ₁)) : (0 : ℝ) ≤ _).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact Nat.cast_nonneg _
  · have hb := (div_le_iff₀ hpos).mp hle
    nlinarith [hb, hcard]

/- English proof (translation)
Introduce `hSF K _ _ _ I C R εC W₁ W₂ hC`. Take `⟨PP₁, PP₂, D₁, D₂, Dstar, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩` from `hC`. Conclude with `hSF εC W₁ W₂ PP₁ PP₂ D₁ D₂ _ Dstar _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11`.
-/
theorem share_from_count_rows : ShareFromCountRows := by
  intro hSF K _ _ _ I C R εC W₁ W₂ hC
  obtain ⟨PP₁, PP₂, D₁, D₂, Dstar, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hC
  exact hSF εC W₁ W₂ PP₁ PP₂ D₁ D₂ _ Dstar _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

/- English proof (translation)
Introduce `hND C ε hε`. Use `filter_upwards [hND C ε hε] with x hx εC W₁ W₂ hN`. Take `⟨h0, h12, hW1, hW2⟩` from `hN`. Establish `hq : (1 + εC) / (1 - εC) ≤ 3`. Rewrite using `[div_le_iff₀ (by linarith)]; linarith`.

Establish `hq0 : 0 ≤ (1 + εC) / (1 - εC)` using `div_nonneg (by linarith) (by linarith)`. Unfold `LChain6.E7`. Establish `he : 0 ≤ Real.exp (-x ^ (ε / 7))` using `(Real.exp_pos _).le`. Break down `le_total 0 (W₁ + W₂) with hs | hs` into its components or cases. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem numbers_dominant_large : NumbersDominantLarge := by
  intro hND C ε hε
  filter_upwards [hND C ε hε] with x hx εC W₁ W₂ hN
  obtain ⟨h0, h12, hW1, hW2⟩ := hN
  have hq : (1 + εC) / (1 - εC) ≤ 3 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hq0 : 0 ≤ (1 + εC) / (1 - εC) := div_nonneg (by linarith) (by linarith)
  unfold LChain6.E7
  have he : 0 ≤ Real.exp (-x ^ (ε / 7)) := (Real.exp_pos _).le
  rcases le_total 0 (W₁ + W₂) with hs | hs
  · calc (1 + εC) / (1 - εC) * (W₁ + W₂) ≤ 3 * (W₁ + W₂) := mul_le_mul_of_nonneg_right hq hs
      _ ≤ Real.exp (-x ^ (ε / 7)) := by linarith
  · calc (1 + εC) / (1 - εC) * (W₁ + W₂) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq0 hs
      _ ≤ Real.exp (-x ^ (ε / 7)) := he

/- English proof (translation)
Introduce `hSF hND C0 ε hε`. Take `⟨x0, hx0⟩` from `Filter.eventually_atTop.mp (numbers_dominant_large hND C0 ε hε)`. Conclude with `⟨x0, fun x hx K _ _ _ I C R εC W₁ W₂ hC hN => irreducible_of_share K I C R x ε εC W₁ W₂ (share_from_count_rows hSF K I C R εC W₁ W₂ hC) (hx0 x hx εC W₁ W₂ hN)⟩`.
-/
theorem irreducible_of_count : IrreducibleOfCount := by
  intro hSF hND C0 ε hε
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.mp (numbers_dominant_large hND C0 ε hε)
  exact ⟨x0, fun x hx K _ _ _ I C R εC W₁ W₂ hC hN =>
    irreducible_of_share K I C R x ε εC W₁ W₂ (share_from_count_rows hSF K I C R εC W₁ W₂ hC) (hx0 x hx εC W₁ W₂ hN)⟩

/- English proof (translation)
The claim follows from `irreducible_of_count Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.share_from_count Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.dominant_numbers_sharp_holds`.
-/
theorem irr_of_count :
    ∀ C0 ε : ℝ, 0 < ε → ∃ x0 : ℝ, ∀ x ≥ x0,
      ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) (C : ColObj K I) (R : RowArg C)
        (εC W₁ W₂ : ℝ), CountAt R εC W₁ W₂ → NumbersAt x ε εC C0 W₁ W₂ → IrrAt R x ε :=
  irreducible_of_count Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.share_from_count Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.dominant_numbers_sharp_holds

/- English proof (translation)
Establish `hp : (0 : ℝ) < (Fintype.card (R.κ ⊕ R.κ₁) : ℝ)` using `by exact_mod_cast hpos`. Use `⟨(Fintype.card R.κ₁ : ℝ) / (Fintype.card (R.κ ⊕ R.κ₁) : ℝ), 0, Fintype.card R.κ₁, 0, Fintype.card (R.κ ⊕ R.κ₁), le_refl _, by norm_num, hp, by positivity, le_refl _, le_refl _, le_refl _, by simp, ?_, by simp, by simp⟩` and prove the remaining obligations. Rewrite using `[div_mul_cancel₀ _ hp.ne']`. Simplify using the standard rewrite rules.
-/
example {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} {C : ColObj K I} (R : RowArg C)
    (hpos : 0 < Fintype.card (R.κ ⊕ R.κ₁)) :
    CountAt R 0 ((Fintype.card R.κ₁ : ℝ) / (Fintype.card (R.κ ⊕ R.κ₁) : ℝ)) 0 := by
  have hp : (0 : ℝ) < (Fintype.card (R.κ ⊕ R.κ₁) : ℝ) := by exact_mod_cast hpos
  refine ⟨(Fintype.card R.κ₁ : ℝ) / (Fintype.card (R.κ ⊕ R.κ₁) : ℝ), 0, Fintype.card R.κ₁, 0,
    Fintype.card (R.κ ⊕ R.κ₁), le_refl _, by norm_num, hp, by positivity, le_refl _, le_refl _, le_refl _,
    by simp, ?_, by simp, by simp⟩
  rw [div_mul_cancel₀ _ hp.ne']; simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨le_refl _, by norm_num, by positivity, by positivity⟩`.
-/
example (x ε C : ℝ) (hx : 0 ≤ x) : NumbersAt x ε 0 C 0 0 :=
  ⟨le_refl _, by norm_num, by positivity, by positivity⟩

/- English proof (translation)
Unfold `IrrAt`. Establish `hE : LChain6.E7 x ε < 1` using `by show Real.exp (-(x ^ (ε / 7))) < 1`. Use `Real.rpow_pos_of_pos hx (ε / 7)` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Fintype.card_sum, h0]`.

Establish `: (1 : ℝ) ≤ (Fintype.card R.κ₁ : ℝ)` using `by exact_mod_cast h1`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
-/
example {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} {C : ColObj K I} (R : RowArg C)
    (x ε : ℝ) (hx : 0 < x) (hε : 0 < ε) (h0 : Fintype.card R.κ = 0) (h1 : 1 ≤ Fintype.card R.κ₁) :
    ¬ IrrAt R x ε := by
  unfold IrrAt
  have hE : LChain6.E7 x ε < 1 := by
    show Real.exp (-(x ^ (ε / 7))) < 1
    have := Real.rpow_pos_of_pos hx (ε / 7)
    calc Real.exp (-(x ^ (ε / 7))) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  rw [Fintype.card_sum, h0]
  have : (1 : ℝ) ≤ (Fintype.card R.κ₁ : ℝ) := by exact_mod_cast h1
  push_cast
  nlinarith

/- English proof (translation)
Unfold `Wg`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wg_eq_propW (f m N g q₁ d : ℕ) :
    Wg f m N g q₁ d = (f : ℝ) / (g : ℝ) + (2 * (f : ℝ) / (g : ℝ) +
      23 * (f : ℝ) * Real.log (g : ℝ) / Real.sqrt (g : ℝ) +
      2 * (f : ℝ) * (m : ℝ) * (1 / (4 * ((min q₁ d : ℕ) : ℝ)) + (1 + Real.log (N : ℝ)) / ((g : ℝ) - 1)) +
      (N : ℝ) / 2 * (7 / 8 : ℝ) ^ f +
      Real.exp (-(f : ℝ) / (5 * Real.log (N : ℝ)))) := by
  unfold Wg
  ring

/- English proof (translation)
Establish `hP0 : 0 ≤ P` using `le_trans hf0 hfP`. Establish `hfm : f * m ≤ P * P` using `mul_le_mul hfP hmP hm0 hP0`. Establish `hAB : A + B ≤ eu + 2 * P * eu` using `add_le_add hA hB`. Establish `h3 : f * m * (A + B) ≤ P * P * (eu + 2 * P * eu)` using `mul_le_mul hfm hAB (add_nonneg hA0 hB0) (mul_nonneg hP0 hP0)`. Use polynomial arithmetic with `[h3]`.
-/
theorem third_fourth_terms_bound (f m P A B eu : ℝ) (hf0 : 0 ≤ f) (hm0 : 0 ≤ m) (hfP : f ≤ P) (hmP : m ≤ P) (hA0 : 0 ≤ A)
    (hB0 : 0 ≤ B) (hA : A ≤ eu) (hB : B ≤ 2 * P * eu) : 2 * f * m * (A + B) ≤ 2 * (P * P) * (eu + 2 * P * eu) := by
  have hP0 : 0 ≤ P := le_trans hf0 hfP
  have hfm : f * m ≤ P * P := mul_le_mul hfP hmP hm0 hP0
  have hAB : A + B ≤ eu + 2 * P * eu := add_le_add hA hB
  have h3 : f * m * (A + B) ≤ P * P * (eu + 2 * P * eu) :=
    mul_le_mul hfm hAB (add_nonneg hA0 hB0) (mul_nonneg hP0 hP0)
  nlinarith [h3]

/- English proof (translation)
Establish `hP0 : 0 ≤ P` using `le_trans zero_le_one hP1`. Establish `hPP : 1 ≤ P * P` using `by nlinarith`. Establish `hP3 : P ^ 3 = P * P * P` using `by ring`. Establish `a1 : P * eu ≤ P ^ 3 * eu`. Rewrite using `[hP3]; exact mul_le_mul_of_nonneg_right (by nlinarith) heu`.

Establish `a2 : P * P * eu ≤ P ^ 3 * eu`. Rewrite using `[hP3]; exact mul_le_mul_of_nonneg_right (by nlinarith) heu`. Establish `a3 : eu ≤ P ^ 3 * eu`. Rewrite using `[hP3]`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg hP0 hP0) heu]`.

Establish `a4 : P ^ 3 * 103 * eu ≤ P ^ 3 * X3 * eu`. Establish `h0 : 0 ≤ P ^ 3 * eu` using `mul_nonneg (pow_nonneg hP0 3) heu`. Use polynomial arithmetic with `[h0]`. Establish `e1 : 2 * (P * P) * (eu + 2 * P * eu) = 2 * (P * P * eu) + 4 * (P ^ 3 * eu)` using `by ring`. Use polynomial arithmetic with `[a1, a2, a3, a4, e1]`.
-/
theorem wsum (t1 t2 t34 t5 t6 : ℝ) (P eu X3 : ℝ) (hP1 : 1 ≤ P) (heu : 0 ≤ eu) (hX : 103 ≤ X3)
    (h1 : t1 ≤ 3 * P * eu) (h2 : t2 ≤ 92 * P * eu) (h34 : t34 ≤ 2 * (P * P) * (eu + 2 * P * eu))
    (h5 : t5 ≤ P * eu) (h6 : t6 ≤ eu) : t1 + t2 + t34 + t5 + t6 ≤ P ^ 3 * X3 * eu := by
  have hP0 : 0 ≤ P := le_trans zero_le_one hP1
  have hPP : 1 ≤ P * P := by nlinarith
  have hP3 : P ^ 3 = P * P * P := by ring
  have a1 : P * eu ≤ P ^ 3 * eu := by
    rw [hP3]; exact mul_le_mul_of_nonneg_right (by nlinarith) heu
  have a2 : P * P * eu ≤ P ^ 3 * eu := by
    rw [hP3]; exact mul_le_mul_of_nonneg_right (by nlinarith) heu
  have a3 : eu ≤ P ^ 3 * eu := by
    rw [hP3]; nlinarith [mul_nonneg (mul_nonneg hP0 hP0) heu]
  have a4 : P ^ 3 * 103 * eu ≤ P ^ 3 * X3 * eu := by
    have h0 : 0 ≤ P ^ 3 * eu := mul_nonneg (pow_nonneg hP0 3) heu
    nlinarith [h0]
  have e1 : 2 * (P * P) * (eu + 2 * P * eu) = 2 * (P * P * eu) + 4 * (P ^ 3 * eu) := by ring
  nlinarith [a1, a2, a3, a4, e1]

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `ε Cs hε hε1`. Use `filter_upwards [Filter.eventually_ge_atTop (max 10 (100 * Cs ^ 2 + 1))] with x hx`. Introduce `f m N g q₁ d hS`. Take `⟨hg, hf2, hfP, hmP, hN100, hNP, hmin⟩` from `hS`. Establish `hx10 : (10 : ℝ) ≤ x` using `le_trans (le_max_left _ _) hx`.

Establish `hxC : 100 * Cs ^ 2 + 1 ≤ x` using `le_trans (le_max_right _ _) hx`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hx1 : 1 ≤ x` using `by linarith`. Establish `hN : (100 : ℝ) ≤ (N : ℝ)` using `by exact_mod_cast hN100`. Establish `hP100 : (100 : ℝ) ≤ x ^ Cs` using `le_trans hN hNP`.

Establish `hCs : 0 < Cs`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `: x ^ Cs ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx1 h`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `set P := x ^ Cs with hPdef`. Use `set E := x ^ ε with hEdef`. Use `set u := x ^ (ε / 6) with hudef`. Establish `hE1 : 1 ≤ E` using `Real.one_le_rpow hx1 hε.le`. Establish `hu1 : 1 ≤ u` using `Real.one_le_rpow hx1 (by positivity)`.

Establish `huE : u ≤ E` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `hux : u ≤ x`. Combine the equalities or inequalities in the displayed calculation. Use `set eu := Real.exp (-u) with heu`. Establish `heu0 : 0 < eu` using `Real.exp_pos _`.

Establish `hf0 : (0 : ℝ) ≤ (f : ℝ)` using `Nat.cast_nonneg _`. Establish `hm0 : (0 : ℝ) ≤ (m : ℝ)` using `Nat.cast_nonneg _`. Establish `hP1 : 1 ≤ P` using `by linarith`. Establish `h8E : 1 + 8 * E ≤ Real.exp (8 * E)` using `by have := Real.add_one_le_exp (8 * E); linarith`. Establish `hg9 : (9 : ℝ) ≤ (g : ℝ)` using `by linarith`.

Establish `hgpos : (0 : ℝ) < (g : ℝ)` using `by linarith`. Establish `hginv : 1 / (g : ℝ) ≤ eu`. Rewrite using `[div_le_iff₀ hgpos]`. Establish `h1 : Real.exp (-u) * Real.exp (8 * E) ≤ Real.exp (-u) * (g : ℝ)` using `mul_le_mul_of_nonneg_left hg heu0.le`. Establish `h2 : Real.exp (-u) * Real.exp (8 * E) = Real.exp (8 * E - u)`.

Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form. Establish `h3 : 1 ≤ Real.exp (8 * E - u)` using `Real.one_le_exp (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT1 : 3 * (f : ℝ) / (g : ℝ) ≤ 3 * P * eu`.

Establish `: 3 * (f : ℝ) / (g : ℝ) = 3 * (f : ℝ) * (1 / (g : ℝ))` using `by ring`. Rewrite using `[this]`. Conclude with `mul_le_mul (by linarith) hginv (by positivity) (by positivity)`. Use `set s := Real.sqrt (Real.sqrt (g : ℝ)) with hsdef`. Establish `hsg : Real.sqrt (g : ℝ) = s ^ 2`.

Rewrite using `[hsdef, Real.sq_sqrt (Real.sqrt_nonneg _)]`. Establish `hs4 : (g : ℝ) = s ^ 4`. Establish `: s ^ 4 = (s ^ 2) ^ 2` using `by ring`. Rewrite using `[this, ← hsg, Real.sq_sqrt hgpos.le]`. Establish `hs0 : 0 < s`.

Rewrite using `[hsdef]`. Conclude with `Real.sqrt_pos.2 (Real.sqrt_pos.2 hgpos)`. Establish `hlogs : Real.log (g : ℝ) ≤ 4 * s`. Rewrite using `[hs4, Real.log_pow]`. Use `Real.log_le_sub_one_of_pos hs0` as an intermediate fact.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsE : Real.exp (2 * E) ≤ s`. Establish `h4 : Real.exp (2 * E) ^ 4 ≤ s ^ 4`. Rewrite using `[← hs4, ← Real.exp_nat_mul]`.

Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(pow_le_pow_iff_left₀ (Real.exp_pos _).le hs0.le (by norm_num)).1 h4`. Establish `hsinv : 1 / s ≤ eu`. Rewrite using `[div_le_iff₀ hs0]`.

Establish `h1 : Real.exp (-u) * Real.exp (2 * E) ≤ Real.exp (-u) * s` using `mul_le_mul_of_nonneg_left hsE heu0.le`. Establish `h2 : Real.exp (-u) * Real.exp (2 * E) = Real.exp (2 * E - u)`. Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form. Establish `h3 : 1 ≤ Real.exp (2 * E - u)` using `Real.one_le_exp (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT2 : 23 * (f : ℝ) * Real.log (g : ℝ) / Real.sqrt (g : ℝ) ≤ 92 * P * eu`. Rewrite using `[hsg]`. Establish `hlog0 : 0 ≤ Real.log (g : ℝ)` using `Real.log_nonneg (by linarith)`. Establish `hA : 23 * (f : ℝ) * Real.log (g : ℝ) / s ^ 2 ≤ 92 * (f : ℝ) * (1 / s)`.

Rewrite using `[div_le_iff₀ (by positivity)]`. Establish `: 92 * (f : ℝ) * (1 / s) * s ^ 2 = 23 * (f : ℝ) * (4 * s)` using `by field_simp; ring`. Rewrite using `[this]`. Conclude with `mul_le_mul_of_nonneg_left hlogs (by positivity)`. Use `hA.trans ?_` and prove the remaining obligations.

Establish `: 92 * (f : ℝ) * (1 / s) ≤ 92 * P * eu` using `mul_le_mul (by linarith) hsinv (by positivity) (by positivity)`. Conclude with `this`. Establish `hM : Real.exp u ≤ ((min q₁ d : ℕ) : ℝ)` using `hmin`. Establish `hMpos : 0 < ((min q₁ d : ℕ) : ℝ)` using `lt_of_lt_of_le (Real.exp_pos _) hM`. Establish `hA3 : 1 / (4 * ((min q₁ d : ℕ) : ℝ)) ≤ eu`.

Rewrite using `[div_le_iff₀ (by positivity)]`. Establish `h1 : Real.exp (-u) * Real.exp u = 1` using `by rw [← Real.exp_add]; simp`. Establish `h2 : Real.exp (-u) * Real.exp u ≤ Real.exp (-u) * ((min q₁ d : ℕ) : ℝ)` using `mul_le_mul_of_nonneg_left hM heu0.le`. Establish `h3 : Real.exp (-u) * (4 * ((min q₁ d : ℕ) : ℝ)) = 4 * (Real.exp (-u) * ((min q₁ d : ℕ) : ℝ))` using `by ring`. Rewrite using `[heu, h3]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogN : 1 + Real.log (N : ℝ) ≤ P`. Use `Real.log_le_sub_one_of_pos (show (0 : ℝ) < N by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogN0 : 0 ≤ 1 + Real.log (N : ℝ)`.

Use `Real.log_nonneg (show (1 : ℝ) ≤ N by linarith); linarith` as an intermediate fact. Establish `hB4 : (1 + Real.log (N : ℝ)) / ((g : ℝ) - 1) ≤ 2 * P * eu`. Establish `hg1 : 0 < (g : ℝ) - 1` using `by linarith`. Rewrite using `[div_le_iff₀ hg1]`. Establish `h1 : 1 ≤ eu * (g : ℝ)` using `by rwa [div_le_iff₀ hgpos] at hginv`.

Establish `h2 : eu * 9 ≤ eu * (g : ℝ)` using `mul_le_mul_of_nonneg_left hg9 heu0.le`. Establish `h2' : eu * ((g : ℝ) - 1) = eu * (g : ℝ) - eu` using `by ring`. Establish `h3 : 1 / 2 ≤ eu * ((g : ℝ) - 1)` using `by linarith`. Establish `h4 : 2 * P * (1 / 2) ≤ 2 * P * (eu * ((g : ℝ) - 1))` using `mul_le_mul_of_nonneg_left h3 (by linarith)`. Establish `h5 : 2 * P * eu * ((g : ℝ) - 1) = 2 * P * (eu * ((g : ℝ) - 1))` using `by ring`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT34` using `third_fourth_terms_bound (f : ℝ) (m : ℝ) P (1 / (4 * ((min q₁ d : ℕ) : ℝ))) ((1 + Real.log (N : ℝ)) / ((g : ℝ) - 1)) eu hf0 hm0 hfP hmP (by positivity) (by have hg1 : 0 < (g : ℝ) - 1 := by linarith positivity) hA3 hB4`. Establish `h78 : (7 / 8 : ℝ) ≤ Real.exp (-(1 / 8))`. Use `Real.add_one_le_exp (-(1 / 8 : ℝ))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hT5 : (N : ℝ) / 2 * (7 / 8 : ℝ) ^ f ≤ P * eu`. Establish `hpow : (7 / 8 : ℝ) ^ f ≤ Real.exp (-(1 / 8)) ^ f` using `pow_le_pow_left₀ (by norm_num) h78 f`. Rewrite `hpow` using `[← Real.exp_nat_mul]`. Establish `h8x : 8 * x ≤ x ^ 2` using `by rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith) hx0.le`. Establish `hfu : u ≤ (f : ℝ) / 8` using `by linarith`.

Establish `hexp : Real.exp ((f : ℝ) * (-(1 / 8))) ≤ eu` using `Real.exp_le_exp.2 (by linarith)`. Establish `hN2 : (N : ℝ) / 2 ≤ P` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Establish `hlogNpos : 0 < Real.log (N : ℝ)` using `Real.log_pos (by linarith)`. Establish `hlogNx : Real.log (N : ℝ) ≤ Cs * Real.log x`.

Rewrite using `[← Real.log_rpow hx0]`. Conclude with `Real.log_le_log (by linarith) hNP`. Establish `hsqx : 10 * Cs ≤ Real.sqrt x`. Rewrite using `[Real.le_sqrt (by linarith) hx0.le]`. Establish `: (10 * Cs) ^ 2 = 100 * Cs ^ 2` using `by ring`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogx : Real.log x ≤ 2 * Real.sqrt x`. Establish `hsx : 0 < Real.sqrt x` using `Real.sqrt_pos.2 hx0`. Establish `h1 : Real.log x = 2 * Real.log (Real.sqrt x)`. Rewrite using `[← Real.log_rpow hsx]`.

Use `congr 1`. Rewrite using `[show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.sq_sqrt hx0.le]`. Use `Real.log_le_sub_one_of_pos hsx` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hxx : Real.sqrt x * Real.sqrt x = x` using `Real.mul_self_sqrt hx0.le`.

Establish `hT6 : Real.exp (-(f : ℝ) / (5 * Real.log (N : ℝ))) ≤ eu`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Establish `hkey : u * (5 * Real.log (N : ℝ)) ≤ (f : ℝ)`. Establish `h1 : u * (5 * Real.log (N : ℝ)) ≤ x * (5 * (Cs * Real.log x))` using `mul_le_mul hux (mul_le_mul_of_nonneg_left hlogNx (by norm_num)) (by positivity) hx0.le`. Establish `h2 : x * (5 * (Cs * Real.log x)) ≤ x * (5 * (Cs * (2 * Real.sqrt x)))` using `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogx hCs.le) (by norm_num)) hx0.le`.

Establish `h3 : x * (5 * (Cs * (2 * Real.sqrt x))) ≤ x ^ 2`. Establish `h10 : 10 * Cs * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x` using `mul_le_mul_of_nonneg_right hsqx (Real.sqrt_nonneg x)`. Establish `: 5 * (Cs * (2 * Real.sqrt x)) ≤ x`. Combine the equalities or inequalities in the displayed calculation. Establish `h11 : x * (5 * (Cs * (2 * Real.sqrt x))) ≤ x * x` using `mul_le_mul_of_nonneg_left this hx0.le`.

Rewrite using `[sq]`. Conclude with `h11`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]`. Conclude with `hkey`.

Establish `hpow3 : x ^ (3 * Cs + 3) = P ^ 3 * x ^ 3`. Rewrite using `[show 3 * Cs + 3 = Cs * 3 + 3 by ring, Real.rpow_add hx0, Real.rpow_mul hx0.le]`. Rewrite using `[show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]`. Establish `hx3 : (103 : ℝ) ≤ x ^ 3`. Establish `: (10 : ℝ) ^ 3 ≤ x ^ 3` using `pow_le_pow_left₀ (by norm_num) hx10 3`.

Evaluate the numerical expressions using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `Wg`. Rewrite using `[hpow3]`. Conclude with `wsum _ _ _ _ _ P eu (x ^ 3) hP1 heu0.le hx3 hT1 hT2 hT34 hT5 hT6`.
-/
theorem weight_numbers_bound : WeightNumbersBound := by
  intro ε Cs hε hε1
  filter_upwards [Filter.eventually_ge_atTop (max 10 (100 * Cs ^ 2 + 1))] with x hx
  intro f m N g q₁ d hS
  obtain ⟨hg, hf2, hfP, hmP, hN100, hNP, hmin⟩ := hS
  have hx10 : (10 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have hxC : 100 * Cs ^ 2 + 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hN : (100 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN100
  have hP100 : (100 : ℝ) ≤ x ^ Cs := le_trans hN hNP
  have hCs : 0 < Cs := by
    by_contra h
    push Not at h
    have : x ^ Cs ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 h
    linarith
  set P := x ^ Cs with hPdef
  set E := x ^ ε with hEdef
  set u := x ^ (ε / 6) with hudef
  have hE1 : 1 ≤ E := Real.one_le_rpow hx1 hε.le
  have hu1 : 1 ≤ u := Real.one_le_rpow hx1 (by positivity)
  have huE : u ≤ E := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hux : u ≤ x := by
    calc u ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one x
  set eu := Real.exp (-u) with heu
  have heu0 : 0 < eu := Real.exp_pos _
  have hf0 : (0 : ℝ) ≤ (f : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hP1 : 1 ≤ P := by linarith

  have h8E : 1 + 8 * E ≤ Real.exp (8 * E) := by have := Real.add_one_le_exp (8 * E); linarith
  have hg9 : (9 : ℝ) ≤ (g : ℝ) := by linarith
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hginv : 1 / (g : ℝ) ≤ eu := by
    rw [div_le_iff₀ hgpos]
    have h1 : Real.exp (-u) * Real.exp (8 * E) ≤ Real.exp (-u) * (g : ℝ) :=
      mul_le_mul_of_nonneg_left hg heu0.le
    have h2 : Real.exp (-u) * Real.exp (8 * E) = Real.exp (8 * E - u) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : 1 ≤ Real.exp (8 * E - u) := Real.one_le_exp (by linarith)
    linarith

  have hT1 : 3 * (f : ℝ) / (g : ℝ) ≤ 3 * P * eu := by
    have : 3 * (f : ℝ) / (g : ℝ) = 3 * (f : ℝ) * (1 / (g : ℝ)) := by ring
    rw [this]
    exact mul_le_mul (by linarith) hginv (by positivity) (by positivity)

  set s := Real.sqrt (Real.sqrt (g : ℝ)) with hsdef
  have hsg : Real.sqrt (g : ℝ) = s ^ 2 := by
    rw [hsdef, Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hs4 : (g : ℝ) = s ^ 4 := by
    have : s ^ 4 = (s ^ 2) ^ 2 := by ring
    rw [this, ← hsg, Real.sq_sqrt hgpos.le]
  have hs0 : 0 < s := by
    rw [hsdef]; exact Real.sqrt_pos.2 (Real.sqrt_pos.2 hgpos)
  have hlogs : Real.log (g : ℝ) ≤ 4 * s := by
    rw [hs4, Real.log_pow]
    have := Real.log_le_sub_one_of_pos hs0
    push_cast; linarith
  have hsE : Real.exp (2 * E) ≤ s := by
    have h4 : Real.exp (2 * E) ^ 4 ≤ s ^ 4 := by
      rw [← hs4, ← Real.exp_nat_mul]; push_cast
      calc Real.exp (4 * (2 * E)) = Real.exp (8 * E) := by ring_nf
        _ ≤ (g : ℝ) := hg
    exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le hs0.le (by norm_num)).1 h4
  have hsinv : 1 / s ≤ eu := by
    rw [div_le_iff₀ hs0]
    have h1 : Real.exp (-u) * Real.exp (2 * E) ≤ Real.exp (-u) * s := mul_le_mul_of_nonneg_left hsE heu0.le
    have h2 : Real.exp (-u) * Real.exp (2 * E) = Real.exp (2 * E - u) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : 1 ≤ Real.exp (2 * E - u) := Real.one_le_exp (by linarith)
    linarith
  have hT2 : 23 * (f : ℝ) * Real.log (g : ℝ) / Real.sqrt (g : ℝ) ≤ 92 * P * eu := by
    rw [hsg]
    have hlog0 : 0 ≤ Real.log (g : ℝ) := Real.log_nonneg (by linarith)
    have hA : 23 * (f : ℝ) * Real.log (g : ℝ) / s ^ 2 ≤ 92 * (f : ℝ) * (1 / s) := by
      rw [div_le_iff₀ (by positivity)]
      have : 92 * (f : ℝ) * (1 / s) * s ^ 2 = 23 * (f : ℝ) * (4 * s) := by field_simp; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hlogs (by positivity)
    refine hA.trans ?_
    have : 92 * (f : ℝ) * (1 / s) ≤ 92 * P * eu :=
      mul_le_mul (by linarith) hsinv (by positivity) (by positivity)
    exact this

  have hM : Real.exp u ≤ ((min q₁ d : ℕ) : ℝ) := hmin
  have hMpos : 0 < ((min q₁ d : ℕ) : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hM
  have hA3 : 1 / (4 * ((min q₁ d : ℕ) : ℝ)) ≤ eu := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    have h2 : Real.exp (-u) * Real.exp u ≤ Real.exp (-u) * ((min q₁ d : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hM heu0.le
    have h3 : Real.exp (-u) * (4 * ((min q₁ d : ℕ) : ℝ)) = 4 * (Real.exp (-u) * ((min q₁ d : ℕ) : ℝ)) := by ring
    rw [heu, h3]; linarith
  have hlogN : 1 + Real.log (N : ℝ) ≤ P := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < N by linarith)
    linarith
  have hlogN0 : 0 ≤ 1 + Real.log (N : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ N by linarith); linarith
  have hB4 : (1 + Real.log (N : ℝ)) / ((g : ℝ) - 1) ≤ 2 * P * eu := by
    have hg1 : 0 < (g : ℝ) - 1 := by linarith
    rw [div_le_iff₀ hg1]
    have h1 : 1 ≤ eu * (g : ℝ) := by rwa [div_le_iff₀ hgpos] at hginv
    have h2 : eu * 9 ≤ eu * (g : ℝ) := mul_le_mul_of_nonneg_left hg9 heu0.le
    have h2' : eu * ((g : ℝ) - 1) = eu * (g : ℝ) - eu := by ring
    have h3 : 1 / 2 ≤ eu * ((g : ℝ) - 1) := by linarith
    have h4 : 2 * P * (1 / 2) ≤ 2 * P * (eu * ((g : ℝ) - 1)) := mul_le_mul_of_nonneg_left h3 (by linarith)
    have h5 : 2 * P * eu * ((g : ℝ) - 1) = 2 * P * (eu * ((g : ℝ) - 1)) := by ring
    linarith
  have hT34 := third_fourth_terms_bound (f : ℝ) (m : ℝ) P (1 / (4 * ((min q₁ d : ℕ) : ℝ)))
    ((1 + Real.log (N : ℝ)) / ((g : ℝ) - 1)) eu hf0 hm0 hfP hmP (by positivity)
    (by have hg1 : 0 < (g : ℝ) - 1 := by linarith
        positivity) hA3 hB4

  have h78 : (7 / 8 : ℝ) ≤ Real.exp (-(1 / 8)) := by
    have := Real.add_one_le_exp (-(1 / 8 : ℝ)); linarith
  have hT5 : (N : ℝ) / 2 * (7 / 8 : ℝ) ^ f ≤ P * eu := by
    have hpow : (7 / 8 : ℝ) ^ f ≤ Real.exp (-(1 / 8)) ^ f := pow_le_pow_left₀ (by norm_num) h78 f
    rw [← Real.exp_nat_mul] at hpow
    have h8x : 8 * x ≤ x ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith) hx0.le
    have hfu : u ≤ (f : ℝ) / 8 := by linarith
    have hexp : Real.exp ((f : ℝ) * (-(1 / 8))) ≤ eu := Real.exp_le_exp.2 (by linarith)
    have hN2 : (N : ℝ) / 2 ≤ P := by linarith
    calc (N : ℝ) / 2 * (7 / 8 : ℝ) ^ f ≤ P * Real.exp ((f : ℝ) * (-(1 / 8))) :=
          mul_le_mul hN2 hpow (by positivity) (by linarith)
      _ ≤ P * eu := mul_le_mul_of_nonneg_left hexp (by linarith)

  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hlogNx : Real.log (N : ℝ) ≤ Cs * Real.log x := by
    rw [← Real.log_rpow hx0]
    exact Real.log_le_log (by linarith) hNP
  have hsqx : 10 * Cs ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by linarith) hx0.le]
    have : (10 * Cs) ^ 2 = 100 * Cs ^ 2 := by ring
    linarith
  have hlogx : Real.log x ≤ 2 * Real.sqrt x := by
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [← Real.log_rpow hsx]; congr 1
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.sq_sqrt hx0.le]
    have := Real.log_le_sub_one_of_pos hsx
    linarith
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hT6 : Real.exp (-(f : ℝ) / (5 * Real.log (N : ℝ))) ≤ eu := by
    apply Real.exp_le_exp.2
    have hkey : u * (5 * Real.log (N : ℝ)) ≤ (f : ℝ) := by
      have h1 : u * (5 * Real.log (N : ℝ)) ≤ x * (5 * (Cs * Real.log x)) :=
        mul_le_mul hux (mul_le_mul_of_nonneg_left hlogNx (by norm_num)) (by positivity) hx0.le
      have h2 : x * (5 * (Cs * Real.log x)) ≤ x * (5 * (Cs * (2 * Real.sqrt x))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogx hCs.le) (by norm_num)) hx0.le
      have h3 : x * (5 * (Cs * (2 * Real.sqrt x))) ≤ x ^ 2 := by
        have h10 : 10 * Cs * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_right hsqx (Real.sqrt_nonneg x)
        have : 5 * (Cs * (2 * Real.sqrt x)) ≤ x := by
          calc 5 * (Cs * (2 * Real.sqrt x)) = 10 * Cs * Real.sqrt x := by ring
            _ ≤ Real.sqrt x * Real.sqrt x := h10
            _ = x := hxx
        have h11 : x * (5 * (Cs * (2 * Real.sqrt x))) ≤ x * x := mul_le_mul_of_nonneg_left this hx0.le
        rw [sq]; exact h11
      linarith
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    exact hkey

  have hpow3 : x ^ (3 * Cs + 3) = P ^ 3 * x ^ 3 := by
    rw [show 3 * Cs + 3 = Cs * 3 + 3 by ring, Real.rpow_add hx0, Real.rpow_mul hx0.le]
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
  have hx3 : (103 : ℝ) ≤ x ^ 3 := by
    have : (10 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx10 3
    norm_num at this; linarith
  unfold Wg
  rw [hpow3]
  exact wsum _ _ _ _ _ P eu (x ^ 3) hP1 heu0.le hx3 hT1 hT2 hT34 hT5 hT6

/- English proof (translation)
Introduce `c hc`. Use `filter_upwards [Filter.eventually_ge_atTop (max 1 (1 / c))] with x hx N f hN hf`. Establish `hx1 : 1 ≤ x` using `le_trans (le_max_left _ _) hx`. Establish `hxc : 1 / c ≤ x` using `le_trans (le_max_right _ _) hx`. Establish `hcx : 1 ≤ c * x`.

Rewrite `hxc` using `[div_le_iff₀ hc]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcx2 : 1 ≤ c * x ^ 2` using `by nlinarith`. Establish `hN' : (100 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `hlog : 1 ≤ Real.log N`.

Establish `h1 : Real.exp 1 ≤ (N : ℝ)`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2` using `Real.log_le_log (Real.exp_pos 1) h1`. Rewrite `h2` using `[Real.log_exp]`. Then use the resulting hypothesis.

Establish `h2 : 1 ≤ c * f` using `le_trans hcx2 (mul_le_mul_of_nonneg_left hf hc.le)`. Establish `h3 : 1 ≤ (N : ℝ) * Real.log N` using `by nlinarith`. Establish `key : 1 ≤ c * (N : ℝ) * (f : ℝ) * Real.log (N : ℝ)`. Combine the equalities or inequalities in the displayed calculation. Unfold `epsC`.

Establish `hle : Real.exp (-(c * (N : ℝ) * (f : ℝ) * Real.log (N : ℝ))) ≤ Real.exp (-1)` using `Real.exp_le_exp.mpr (by linarith)`. Establish `he` using `Real.add_one_le_exp (1 : ℝ)`. Establish `hm : Real.exp (-1) * Real.exp 1 = 1`. Rewrite using `[← Real.exp_add]`. Evaluate the numerical expressions.

Establish `hp : 0 < Real.exp (-1)` using `Real.exp_pos _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem epsilon_bound_large_x : EpsilonBoundLargeX := by
  intro c hc
  filter_upwards [Filter.eventually_ge_atTop (max 1 (1 / c))] with x hx N f hN hf
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxc : 1 / c ≤ x := le_trans (le_max_right _ _) hx
  have hcx : 1 ≤ c * x := by
    rw [div_le_iff₀ hc] at hxc; linarith
  have hcx2 : 1 ≤ c * x ^ 2 := by nlinarith
  have hN' : (100 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 1 ≤ Real.log N := by
    have h1 : Real.exp 1 ≤ (N : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    have h2 := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h2
  have h2 : 1 ≤ c * f := le_trans hcx2 (mul_le_mul_of_nonneg_left hf hc.le)
  have h3 : 1 ≤ (N : ℝ) * Real.log N := by nlinarith
  have key : 1 ≤ c * (N : ℝ) * (f : ℝ) * Real.log (N : ℝ) := by
    calc (1 : ℝ) ≤ (c * f) * (N * Real.log N) := one_le_mul_of_one_le_of_one_le h2 h3
      _ = c * (N : ℝ) * (f : ℝ) * Real.log (N : ℝ) := by ring
  unfold epsC
  have hle : Real.exp (-(c * (N : ℝ) * (f : ℝ) * Real.log (N : ℝ))) ≤ Real.exp (-1) :=
    Real.exp_le_exp.mpr (by linarith)
  have he := Real.add_one_le_exp (1 : ℝ)
  have hm : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]; norm_num
  have hp : 0 < Real.exp (-1) := Real.exp_pos _
  nlinarith

/- English proof (translation)
Introduce `hSF hND ε Cs c hε hε1 hc`. Establish `hW` using `weight_numbers_bound ε Cs hε hε1`. Establish `hE` using `epsilon_bound_large_x c hc`. Establish `hNm` using `numbers_dominant_large hND (3 * Cs + 3) ε hε`. Take `⟨x0, hx0⟩` from `Filter.eventually_atTop.mp (hW.and (hE.and hNm))`.

Use `⟨x0, fun x hx K _ _ _ I C R f m N g₁ g₂ q₁ d hS1 hS2 hC => ?_⟩` and prove the remaining obligations. Take `⟨hw, he, hn⟩` from `hx0 x hx`. Take `⟨-, hf1, -, -, hN1, -, -⟩` from `id hS1`. Establish `hNA : NumbersAt x ε (epsC c N f) (3 * Cs + 3) (Wg f m N g₁ q₁ d) (Wg f m N g₂ q₁ d)` using `⟨(Real.exp_pos _).le, he N f hN1 hf1, hw f m N g₁ q₁ d hS1, hw f m N g₂ q₁ d hS2⟩`. Conclude with `irreducible_of_share K I C R x ε _ _ _ (share_from_count_rows hSF K I C R _ _ _ hC) (hn _ _ _ hNA)`.
-/
theorem irreducible_of_count_sizes : IrreducibleOfCountSizes := by
  intro hSF hND ε Cs c hε hε1 hc
  have hW := weight_numbers_bound ε Cs hε hε1
  have hE := epsilon_bound_large_x c hc
  have hNm := numbers_dominant_large hND (3 * Cs + 3) ε hε
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.mp (hW.and (hE.and hNm))
  refine ⟨x0, fun x hx K _ _ _ I C R f m N g₁ g₂ q₁ d hS1 hS2 hC => ?_⟩
  obtain ⟨hw, he, hn⟩ := hx0 x hx
  obtain ⟨-, hf1, -, -, hN1, -, -⟩ := id hS1
  have hNA : NumbersAt x ε (epsC c N f) (3 * Cs + 3) (Wg f m N g₁ q₁ d) (Wg f m N g₂ q₁ d) :=
    ⟨(Real.exp_pos _).le, he N f hN1 hf1, hw f m N g₁ q₁ d hS1, hw f m N g₂ q₁ d hS2⟩
  exact irreducible_of_share K I C R x ε _ _ _ (share_from_count_rows hSF K I C R _ _ _ hC) (hn _ _ _ hNA)

/- English proof (translation)
The claim follows from `irreducible_of_count_sizes Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.share_from_count Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.dominant_numbers_sharp_holds`.
-/
theorem irr_of_count_sizes :
    ∀ ε Cs c : ℝ, 0 < ε → ε ≤ 1 → 0 < c → ∃ x0 : ℝ, ∀ x ≥ x0,
      ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) (C : ColObj K I) (R : RowArg C)
        (f m N g₁ g₂ q₁ d : ℕ), SizesAt x ε Cs f m N g₁ q₁ d → SizesAt x ε Cs f m N g₂ q₁ d →
        CountAt R (epsC c N f) (Wg f m N g₁ q₁ d) (Wg f m N g₂ q₁ d) → IrrAt R x ε :=
  irreducible_of_count_sizes Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.share_from_count Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.dominant_numbers_sharp_holds

/- English proof (translation)
Introduce `hB K _ _ _ I C R k _ HH _ _ _ e₁ e₂ εC W₁ W₂ hT`. Take `⟨h1, h2, h3, hdim, hrk, PP₁, PP₂, Dstar, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩` from `hT`. Use `⟨PP₁, PP₂, (Module.finrank k (LinearMap.range e₁) : ℝ), (Module.finrank k (LinearMap.range e₂) : ℝ), Dstar, a1, a2, a3, a4, a5, a6, a7, ?_, a9, a10, ?_⟩` and prove the remaining obligations. Rewrite using `[← hdim]`. Conclude with `a8`.

Rewrite using `[← hrk]`. Conclude with `hB k HH e₁ e₂ h1 h2 h3` after adjusting the coercions.
-/
theorem tied_count_arithmetic : CompatibleCountArithmetic := by
  intro hB K _ _ _ I C R k _ HH _ _ _ e₁ e₂ εC W₁ W₂ hT
  obtain ⟨h1, h2, h3, hdim, hrk, PP₁, PP₂, Dstar, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hT
  refine ⟨PP₁, PP₂, (Module.finrank k (LinearMap.range e₁) : ℝ), (Module.finrank k (LinearMap.range e₂) : ℝ),
    Dstar, a1, a2, a3, a4, a5, a6, a7, ?_, a9, a10, ?_⟩
  · rw [← hdim]
    exact a8
  · rw [← hrk]
    exact_mod_cast hB k HH e₁ e₂ h1 h2 h3

/- English proof (translation)
Introduce `hSF hB hND ε Cs c hε hε1 hc`. Take `⟨x0, hx0⟩` from `irreducible_of_count_sizes hSF hND ε Cs c hε hε1 hc`. Conclude with `⟨x0, fun x hx K _ _ _ I C R k _ HH _ _ _ e₁ e₂ f m N g₁ g₂ q₁ d hS1 hS2 hT => hx0 x hx K I C R f m N g₁ g₂ q₁ d hS1 hS2 (tied_count_arithmetic hB K I C R k HH e₁ e₂ _ _ _ hT)⟩`.
-/
theorem irreducible_of_tied_sizes : IrreducibleOfCompatibleSizes := by
  intro hSF hB hND ε Cs c hε hε1 hc
  obtain ⟨x0, hx0⟩ := irreducible_of_count_sizes hSF hND ε Cs c hε hε1 hc
  exact ⟨x0, fun x hx K _ _ _ I C R k _ HH _ _ _ e₁ e₂ f m N g₁ g₂ q₁ d hS1 hS2 hT =>
    hx0 x hx K I C R f m N g₁ g₂ q₁ d hS1 hS2 (tied_count_arithmetic hB K I C R k HH e₁ e₂ _ _ _ hT)⟩

/- English proof (translation)
The claim follows from `irreducible_of_tied_sizes Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.share_from_count Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.bad_rank_union_bound Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.dominant_numbers_sharp_holds`.
-/
theorem irr_of_tied_sizes :
    ∀ ε Cs c : ℝ, 0 < ε → ε ≤ 1 → 0 < c → ∃ x0 : ℝ, ∀ x ≥ x0,
      ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) (C : ColObj K I) (R : RowArg C)
        (k : Type) [Field k] (HH : Type) [AddCommGroup HH] [Module k HH] [FiniteDimensional k HH]
        (e₁ e₂ : HH →ₗ[k] HH) (f m N g₁ g₂ q₁ d : ℕ),
        SizesAt x ε Cs f m N g₁ q₁ d → SizesAt x ε Cs f m N g₂ q₁ d →
        CountBoundForCompatibleRows R HH e₁ e₂ (epsC c N f) (Wg f m N g₁ q₁ d) (Wg f m N g₂ q₁ d) → IrrAt R x ε :=
  irreducible_of_tied_sizes Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.share_from_count Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.bad_rank_union_bound Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.dominant_numbers_sharp_holds

/- English proof (translation)
Use `set e := (LinearMap.inl ℚ (Fin (Fintype.card R.κ₁) → ℚ) (Fin (Fintype.card R.κ) → ℚ)).comp (LinearMap.fst ℚ (Fin (Fintype.card R.κ₁) → ℚ) (Fin (Fintype.card R.κ) → ℚ)) with he`. Establish `hdim : Module.finrank ℚ ((Fin (Fintype.card R.κ₁) → ℚ) × (Fin (Fintype.card R.κ) → ℚ)) = Fintype.card (R.κ ⊕ R.κ₁)`. Rewrite using `[Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun, Fintype.card_sum, add_comm]`. Establish `hrange : Module.finrank ℚ (LinearMap.range e) = Fintype.card R.κ₁`. Rewrite using `[he, LinearMap.range_comp, LinearMap.range_eq_top.mpr (fun x => ⟨(x, 0), rfl⟩), Submodule.map_top, LinearMap.finrank_range_of_inj (LinearMap.inl_injective), Module.finrank_fin_fun]`.

Establish `hidem : e ∘ₗ e = e`. Apply the tactic sequence `ext x <;> simp [he]`. Establish `hp : (0 : ℝ) < (Fintype.card (R.κ ⊕ R.κ₁) : ℝ)` using `by exact_mod_cast hpos`. Use `⟨hidem, by simp, by simp, hdim, ?_, (Fintype.card R.κ₁ : ℝ) / (Fintype.card (R.κ ⊕ R.κ₁) : ℝ), 0, (Fintype.card (R.κ ⊕ R.κ₁) : ℝ), le_refl _, by norm_num, hp, by positivity, le_refl _, le_refl _, le_refl _, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [show e + 0 - e ∘ₗ 0 = e by ext x <;> simp]; exact hrange`.

Rewrite using `[hdim]`. Simplify using the standard rewrite rules. Rewrite using `[hrange, div_mul_cancel₀ _ hp.ne']`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
example {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} {C : ColObj K I} (R : RowArg C)
    (hpos : 0 < Fintype.card (R.κ ⊕ R.κ₁)) :
    CountBoundForCompatibleRows (k := ℚ) R ((Fin (Fintype.card R.κ₁) → ℚ) × (Fin (Fintype.card R.κ) → ℚ))
      ((LinearMap.inl ℚ _ _).comp (LinearMap.fst ℚ _ _)) 0 0
      ((Fintype.card R.κ₁ : ℝ) / (Fintype.card (R.κ ⊕ R.κ₁) : ℝ)) 0 := by
  set e := (LinearMap.inl ℚ (Fin (Fintype.card R.κ₁) → ℚ) (Fin (Fintype.card R.κ) → ℚ)).comp
    (LinearMap.fst ℚ (Fin (Fintype.card R.κ₁) → ℚ) (Fin (Fintype.card R.κ) → ℚ)) with he
  have hdim : Module.finrank ℚ ((Fin (Fintype.card R.κ₁) → ℚ) × (Fin (Fintype.card R.κ) → ℚ)) =
      Fintype.card (R.κ ⊕ R.κ₁) := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun, Fintype.card_sum, add_comm]
  have hrange : Module.finrank ℚ (LinearMap.range e) = Fintype.card R.κ₁ := by
    rw [he, LinearMap.range_comp, LinearMap.range_eq_top.mpr (fun x => ⟨(x, 0), rfl⟩), Submodule.map_top,
      LinearMap.finrank_range_of_inj (LinearMap.inl_injective), Module.finrank_fin_fun]
  have hidem : e ∘ₗ e = e := by
    ext x <;> simp [he]
  have hp : (0 : ℝ) < (Fintype.card (R.κ ⊕ R.κ₁) : ℝ) := by exact_mod_cast hpos
  refine ⟨hidem, by simp, by simp, hdim, ?_, (Fintype.card R.κ₁ : ℝ) / (Fintype.card (R.κ ⊕ R.κ₁) : ℝ), 0,
    (Fintype.card (R.κ ⊕ R.κ₁) : ℝ), le_refl _, by norm_num, hp, by positivity, le_refl _, le_refl _, le_refl _,
    ?_, ?_, ?_⟩
  · rw [show e + 0 - e ∘ₗ 0 = e by ext x <;> simp]; exact hrange
  · rw [hdim]; simp
  · rw [hrange, div_mul_cancel₀ _ hp.ne']; simp
  · simp

section Rec

open Formalism.BasicNotions Formalism.MainNotions

/- English proof (translation)
Introduce `hSF hBRU hV7 eps Cs c he he1 hc Fm k _ HH _ _ _ e₁ e₂ hT`. Take `⟨x0, hx0⟩` from `hT`. Establish `hez : 0 < Fm.ez` using `div_pos he (lt_of_lt_of_le one_pos Fm.one_le_J)`. Establish `hez1 : Fm.ez ≤ 1` using `(div_le_self he.le Fm.one_le_J).trans he1`. Establish `hev` using `((numbers_dominant_large hV7 (3 * Cs + 3) Fm.ez hez).and (weight_numbers_bound Fm.ez Cs hez hez1)).and (epsilon_bound_large_x c hc)`.

Take `⟨x1, hx1⟩` from `Filter.eventually_atTop.1 hev`. Use `⟨max x0 x1, fun x hx i => ?_⟩` and prove the remaining obligations. Take `⟨hS, hC⟩` from `hx0 x (le_trans (le_max_left _ _) hx) i`. Take `⟨⟨hnum, hw⟩, heps⟩` from `hx1 x (le_trans (le_max_right _ _) hx)`. Take `⟨h1, h2, h12, hall, hbad, PP₁, PP₂, Dstar, h0, hlt, hD, hP1, hP1W, hP2, hP2W, hA, hc1, hc2⟩` from `hC`.

Establish `hU` using `hBRU k (HH x i) (e₁ x i) (e₂ x i) h1 h2 h12`. Establish `hsh` using `hSF _ _ _ PP₁ PP₂ _ _ (Module.finrank k (HH x i) : ℝ) Dstar (Module.finrank k (LinearMap.range (e₁ x i + e₂ x i - e₁ x i ∘ₗ e₂ x i)) : ℝ) h0 hlt hD hP1 hP1W hP2 hP2W hA hc1 hc2 (by exact_mod_cast hU)`. Establish `hN : NumbersAt x Fm.ez (epsC c (Fm.D x i).R.r (Fm.D x i).R.f) (3 * Cs + 3) (Wg (Fm.D x i).R.f (Fm.D x i).R.m (Fm.D x i).R.r ((Fm.D x i).host.g 0) (Fm.D x i).host.q (Fm.D x i).host.d) (Wg (Fm.D x i).R.f (Fm.D x i).R.m (Fm.D x i).R.r ((Fm.D x i).host.g 1) (Fm.D x i).host.q (Fm.D x …` using `⟨(Real.exp_pos _).le, heps _ _ (hS 0).2.2.2.2.1 (hS 0).2.1, hw _ _ _ _ _ _ (hS 0), hw _ _ _ _ _ _ (hS 1)⟩`. Establish `hle` using `hnum _ _ _ hN`. Use `set b : ℝ := (Module.finrank k (LinearMap.range (e₁ x i + e₂ x i - e₁ x i ∘ₗ e₂ x i)) : ℝ) with hb`.

Use `set A : ℝ := (Module.finrank k (HH x i) : ℝ) with hAdef`. Establish `hApos : 0 < A`. Use `(abs_sub_le_iff.1 hA).2` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hbE : b ≤ LChain6.E7 x Fm.ez * A`.

Use `hsh.trans hle` as an intermediate fact. Rewrite `this` using `[div_le_iff₀ hApos]`. Then use the resulting hypothesis. Establish `hb0 : 0 ≤ b` using `by positivity`. Establish `hDeq` using `(Fm.D x i).what₂.D_eq`. Establish `hAll : ((Fm.D x i).what₂.Dall : ℝ) = A` using `by rw [hAdef, hall]`.

Establish `hSum : ((Fm.D x i).what₂.Drows : ℝ) + b = A`. Rewrite using `[hb, ← hAll]`. Conclude with `hbad` after adjusting the coercions. Rewrite `hDeq` using `[hAll]`. Establish `hdel : (Fm.D x i).what₂.delp * A = b` using `by linarith`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show 0 ≤ (Fm.D x i).what₂.delp`. Assume the negation of the conclusion as `hneg`. Use `push Not at hneg`. Establish `: (Fm.D x i).what₂.delp * A < 0` using `mul_neg_of_neg_of_pos hneg hApos`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `: (Fm.D x i).what₂.delp * A ≤ LChain6.E7 x Fm.ez * A` using `by rw [hdel]; exact hbE`. Conclude with `le_of_mul_le_mul_right this hApos`.
-/
theorem link_irreducible_tied : IrreducibleOfCompatibleForms := by
  intro hSF hBRU hV7 eps Cs c he he1 hc Fm k _ HH _ _ _ e₁ e₂ hT
  obtain ⟨x0, hx0⟩ := hT
  have hez : 0 < Fm.ez := div_pos he (lt_of_lt_of_le one_pos Fm.one_le_J)
  have hez1 : Fm.ez ≤ 1 := (div_le_self he.le Fm.one_le_J).trans he1
  have hev := ((numbers_dominant_large hV7 (3 * Cs + 3) Fm.ez hez).and (weight_numbers_bound Fm.ez Cs hez hez1)).and (epsilon_bound_large_x c hc)
  obtain ⟨x1, hx1⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max x0 x1, fun x hx i => ?_⟩
  obtain ⟨hS, hC⟩ := hx0 x (le_trans (le_max_left _ _) hx) i
  obtain ⟨⟨hnum, hw⟩, heps⟩ := hx1 x (le_trans (le_max_right _ _) hx)
  obtain ⟨h1, h2, h12, hall, hbad, PP₁, PP₂, Dstar, h0, hlt, hD, hP1, hP1W, hP2, hP2W, hA, hc1, hc2⟩ := hC
  have hU := hBRU k (HH x i) (e₁ x i) (e₂ x i) h1 h2 h12
  have hsh := hSF _ _ _ PP₁ PP₂ _ _ (Module.finrank k (HH x i) : ℝ) Dstar
    (Module.finrank k (LinearMap.range (e₁ x i + e₂ x i - e₁ x i ∘ₗ e₂ x i)) : ℝ) h0 hlt hD hP1 hP1W hP2 hP2W hA
    hc1 hc2 (by exact_mod_cast hU)
  have hN : NumbersAt x Fm.ez (epsC c (Fm.D x i).R.r (Fm.D x i).R.f) (3 * Cs + 3)
      (Wg (Fm.D x i).R.f (Fm.D x i).R.m (Fm.D x i).R.r ((Fm.D x i).host.g 0) (Fm.D x i).host.q (Fm.D x i).host.d)
      (Wg (Fm.D x i).R.f (Fm.D x i).R.m (Fm.D x i).R.r ((Fm.D x i).host.g 1) (Fm.D x i).host.q (Fm.D x i).host.d) :=
    ⟨(Real.exp_pos _).le, heps _ _ (hS 0).2.2.2.2.1 (hS 0).2.1, hw _ _ _ _ _ _ (hS 0), hw _ _ _ _ _ _ (hS 1)⟩
  have hle := hnum _ _ _ hN
  set b : ℝ := (Module.finrank k (LinearMap.range (e₁ x i + e₂ x i - e₁ x i ∘ₗ e₂ x i)) : ℝ) with hb
  set A : ℝ := (Module.finrank k (HH x i) : ℝ) with hAdef
  have hApos : 0 < A := by
    have := (abs_sub_le_iff.1 hA).2
    nlinarith
  have hbE : b ≤ LChain6.E7 x Fm.ez * A := by
    have := hsh.trans hle
    rwa [div_le_iff₀ hApos] at this
  have hb0 : 0 ≤ b := by positivity
  have hDeq := (Fm.D x i).what₂.D_eq
  have hAll : ((Fm.D x i).what₂.Dall : ℝ) = A := by rw [hAdef, hall]
  have hSum : ((Fm.D x i).what₂.Drows : ℝ) + b = A := by
    rw [hb, ← hAll]; exact_mod_cast hbad
  rw [hAll] at hDeq
  have hdel : (Fm.D x i).what₂.delp * A = b := by linarith
  refine ⟨?_, ?_⟩
  · show 0 ≤ (Fm.D x i).what₂.delp
    by_contra hneg
    push Not at hneg
    have : (Fm.D x i).what₂.delp * A < 0 := mul_neg_of_neg_of_pos hneg hApos
    linarith
  · have : (Fm.D x i).what₂.delp * A ≤ LChain6.E7 x Fm.ez * A := by rw [hdel]; exact hbE
    exact le_of_mul_le_mul_right this hApos

/- English proof (translation)
The claim follows from `link_irreducible_tied Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.share_from_count Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.bad_rank_union_bound Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.dominant_numbers_sharp_holds`.
-/
theorem linkIRR_of_tied :
    ∀ (eps Cs c : ℝ), 0 < eps → eps ≤ 1 → 0 < c → ∀ (Fm : FamP eps) (k : Type) [Field k]
      (HH : ∀ x, Fm.Ix x → Type) [∀ x i, AddCommGroup (HH x i)] [∀ x i, Module k (HH x i)]
      [∀ x i, FiniteDimensional k (HH x i)] (e₁ e₂ : ∀ x i, HH x i →ₗ[k] HH x i),
      (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, SizesRec (Fm.D x i) x Fm.ez Cs ∧
        CountBoundForCompatibleRowsRecursive (Fm.D x i) (HH x i) (e₁ x i) (e₂ x i) (epsC c (Fm.D x i).R.r (Fm.D x i).R.f)
          (Wg (Fm.D x i).R.f (Fm.D x i).R.m (Fm.D x i).R.r ((Fm.D x i).host.g 0) (Fm.D x i).host.q (Fm.D x i).host.d)
          (Wg (Fm.D x i).R.f (Fm.D x i).R.m (Fm.D x i).R.r ((Fm.D x i).host.g 1) (Fm.D x i).host.q (Fm.D x i).host.d)) →
      LinkIRR Fm :=
  link_irreducible_tied Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.share_from_count Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.bad_rank_union_bound Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.dominant_numbers_sharp_holds

end Rec

section Inputs

open Formalism.BasicNotions Formalism.MainNotions

/- English proof (translation)
Introduce `hSF hBRU hV7 eps Cs c he he1 hc Fm k _ HH _ _ _ e₁ e₂ PP hIn`. Take `⟨x0, hx0⟩` from `hIn`. Use `link_irreducible_tied hSF hBRU hV7 eps Cs c he he1 hc Fm k HH e₁ e₂ ⟨x0, fun x hx i => ?_⟩` and prove the remaining obligations. Take `⟨⟨h1, h2, h12, hall, hbad⟩, ⟨h0, hlt, Dstar, hD, hA, hc1, hc2⟩, hW, hS⟩` from `hx0 x hx i`. Conclude with `⟨hS, h1, h2, h12, hall, hbad, PP x i 0, PP x i 1, Dstar, h0, hlt, hD, (hW 0).1, (hW 0).2, (hW 1).1, (hW 1).2, hA, hc1, hc2⟩`.
-/
theorem link_irreducible_inputs : LinkIrreducibleInputs := by
  intro hSF hBRU hV7 eps Cs c he he1 hc Fm k _ HH _ _ _ e₁ e₂ PP hIn
  obtain ⟨x0, hx0⟩ := hIn
  refine link_irreducible_tied hSF hBRU hV7 eps Cs c he he1 hc Fm k HH e₁ e₂ ⟨x0, fun x hx i => ?_⟩
  obtain ⟨⟨h1, h2, h12, hall, hbad⟩, ⟨h0, hlt, Dstar, hD, hA, hc1, hc2⟩, hW, hS⟩ := hx0 x hx i
  exact ⟨hS, h1, h2, h12, hall, hbad, PP x i 0, PP x i 1, Dstar, h0, hlt, hD, (hW 0).1, (hW 0).2, (hW 1).1,
    (hW 1).2, hA, hc1, hc2⟩

/- English proof (translation)
The claim follows from `link_irreducible_inputs Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.share_from_count Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.bad_rank_union_bound Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.dominant_numbers_sharp_holds`.
-/
theorem linkIRR_of_inputs :
    ∀ (eps Cs c : ℝ), 0 < eps → eps ≤ 1 → 0 < c → ∀ (Fm : FamP eps) (k : Type) [Field k]
      (HH : ∀ x, Fm.Ix x → Type) [∀ x i, AddCommGroup (HH x i)] [∀ x i, Module k (HH x i)]
      [∀ x i, FiniteDimensional k (HH x i)] (e₁ e₂ : ∀ x i, HH x i →ₗ[k] HH x i) (PP : ∀ x, Fm.Ix x → Fin 2 → ℝ),
      (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
        AllRowsRec (Fm.D x i) (HH x i) (e₁ x i) (e₂ x i) ∧
        CountRec (HH x i) (e₁ x i) (e₂ x i) (epsC c (Fm.D x i).R.r (Fm.D x i).R.f) (PP x i) ∧
        WeightRec (Fm.D x i) (PP x i) ∧
        SizesRec (Fm.D x i) x Fm.ez Cs) →
      LinkIRR Fm :=
  link_irreducible_inputs Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.share_from_count Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.bad_rank_union_bound Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.dominant_numbers_sharp_holds

/- English proof (translation)
Establish `hp : (0 : ℝ) < ((a + b : ℕ) : ℝ)` using `by exact_mod_cast hpos`. Establish `hdim : Module.finrank ℚ ((Fin b → ℚ) × (Fin a → ℚ)) = a + b`. Rewrite using `[Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun, add_comm]`. Establish `hrange : Module.finrank ℚ (LinearMap.range ((LinearMap.inl ℚ (Fin b → ℚ) (Fin a → ℚ)).comp (LinearMap.fst ℚ (Fin b → ℚ) (Fin a → ℚ)))) = b`. Rewrite using `[LinearMap.range_comp, LinearMap.range_eq_top.mpr (fun x => ⟨(x, 0), rfl⟩), Submodule.map_top, LinearMap.finrank_range_of_inj (LinearMap.inl_injective), Module.finrank_fin_fun]`.

Use `⟨le_refl _, by norm_num, ((a + b : ℕ) : ℝ), hp, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hdim]`. Simplify using the standard rewrite rules. Rewrite using `[hrange]`. Simplify using `only [Matrix.cons_val_zero, div_mul_cancel₀ _ hp.ne', sub_self, abs_zero, zero_mul, le_refl]`.

Simplify using the standard rewrite rules.
-/
example (a b : ℕ) (hpos : 0 < a + b) :
    CountRec (k := ℚ) ((Fin b → ℚ) × (Fin a → ℚ)) ((LinearMap.inl ℚ _ _).comp (LinearMap.fst ℚ _ _)) 0 0
      ![(b : ℝ) / ((a + b : ℕ) : ℝ), 0] := by
  have hp : (0 : ℝ) < ((a + b : ℕ) : ℝ) := by exact_mod_cast hpos
  have hdim : Module.finrank ℚ ((Fin b → ℚ) × (Fin a → ℚ)) = a + b := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun, add_comm]
  have hrange : Module.finrank ℚ (LinearMap.range ((LinearMap.inl ℚ (Fin b → ℚ) (Fin a → ℚ)).comp
      (LinearMap.fst ℚ (Fin b → ℚ) (Fin a → ℚ)))) = b := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr (fun x => ⟨(x, 0), rfl⟩), Submodule.map_top,
      LinearMap.finrank_range_of_inj (LinearMap.inl_injective), Module.finrank_fin_fun]
  refine ⟨le_refl _, by norm_num, ((a + b : ℕ) : ℝ), hp, ?_, ?_, ?_⟩
  · rw [hdim]; simp
  · rw [hrange]
    simp only [Matrix.cons_val_zero, div_mul_cancel₀ _ hp.ne', sub_self, abs_zero, zero_mul, le_refl]
  · simp

end Inputs

section AllRowsIn

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders

/- English proof (translation)
Take `⟨hT3a, hinj, hlab, hgood⟩` from `hT3`. Take `⟨h0, hlt, hdSpos, hcount⟩` from `hC`. Take `⟨hwt, hW⟩` from `hW`. Use `set dS := DstarE A A.B.e with hdS`. Establish `hDS : ∀ (k : Fin 2) (S : Finset (Tup D k)), DstarE A (A.eT (cyl D k (S : Set (Tup D k)))) = dS * locShare D A.eVec k S`.

Introduce `k S`. Simplify using `only [hdS, DstarE, Formalism.MainNotions.S.AutInst.Dstar, locShare]`. Rewrite using `[A.eT_one k S]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdimU : A.dimT (cyl D 0 Set.univ) = D.what₂.Dall`.

Rewrite using `[hT3a]`. Establish `hall : ∀ τ : Fin D.what₂.Dall, (fun k => A.labAll k τ) ∈ cyl D 0 Set.univ` using `fun τ => by simp [cyl]`. Rewrite using `[Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_eq_fintype_card, Fintype.card_fin]`. Establish `hU` using `hcount 0 Set.univ`. Rewrite `hU` using `[hdimU, Formalism.MainNotions.FamilyNumericLemmas.cyl_univ, A.eT_univ]`.

Set `Sk : (k : Fin 2) → Finset (Tup D k)` to `fun k => (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D k (A.labAll k τ)).image fun τ => A.labAll k τ`. Establish `hSk : ∀ k, ∀ t ∈ Sk k, ¬ goodAt D k t`. Introduce `k t ht`. Take `⟨τ, hτ, rfl⟩` from `Finset.mem_image.mp ht`. Conclude with `(Finset.mem_filter.mp hτ).2`.

Establish `hmem : ∀ (k : Fin 2) (τ : Fin D.what₂.Dall), (fun k => A.labAll k τ) ∈ cyl D k ((Sk k : Finset (Tup D k)) : Set (Tup D k)) ↔ ¬ goodAt D k (A.labAll k τ)`. Introduce `k τ`. Prove the components needed by the constructor for the conclusion. Introduce `hτ`. Conclude with `hSk k _ hτ`.

Introduce `hτ show A.labAll k τ ∈ ((Sk k : Finset (Tup D k)) : Set (Tup D k))`. Conclude with `Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨τ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ⟩, rfl⟩)`. Establish `hdimK : ∀ k, A.dimT (cyl D k ((Sk k : Finset (Tup D k)) : Set (Tup D k))) = (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D k (A.labAll k τ)).card`. Introduce `k`. Rewrite using `[hT3a, ← Nat.card_eq_finsetCard]`.

Conclude with `Nat.card_congr (Equiv.subtypeEquivRight (fun τ => by rw [hmem k τ]; simp))`. Establish `hDrows : (Finset.univ.filter fun τ : Fin D.what₂.Dall => D.ntypes.goodTuple (fun k => A.labAll k τ)).card = D.what₂.Drows`. Establish `: (Finset.univ.filter fun τ : Fin D.what₂.Dall => D.ntypes.goodTuple (fun k => A.labAll k τ)) = Finset.univ.image A.inc`. Use extensionality with `τ`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]`.

Rewrite using `[hgood τ]`. Simplify using `[Set.mem_range]`. Rewrite using `[this, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]`. Establish `hle : D.what₂.Drows ≤ D.what₂.Dall`. Rewrite using `[← hDrows]`.

Conclude with `(Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])`. Establish `hbad : D.what₂.Dall ≤ D.what₂.Drows + (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 0 (A.labAll 0 τ)).card + (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 1 (A.labAll 1 τ)).card`. Establish `hsub : (Finset.univ : Finset (Fin D.what₂.Dall)) ⊆ ((Finset.univ.filter fun τ : Fin D.what₂.Dall => D.ntypes.goodTuple (fun k => A.labAll k τ)) ∪ (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 0 (A.labAll 0 τ))) ∪ (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ good …`. Introduce `τ _`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]`.

Distinguish the cases in `hg : D.ntypes.goodTuple (fun k => A.labAll k τ)`. Conclude with `Or.inl (Or.inl hg)`. Assume the negation of the conclusion as `hc push Not at hc`. Apply `hg` to reduce the goal to its premises. Introduce `k`.

Use `fin_cases k`. Conclude with `hc.1.2`. Conclude with `hc.2`. Use `(Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))` as an intermediate fact. Rewrite `this` using `[Finset.card_univ, Fintype.card_fin, hDrows]`.

Conclude with `this`. Establish `hloc : ∀ k, 0 ≤ locShare D A.eVec k (Sk k)`. Introduce `k`. Unfold `locShare`. Conclude with `Finset.sum_nonneg (fun t _ => Finset.prod_nonneg (fun v _ => hwt k v (t v)))`.

Establish `hK : ∀ k, |((Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D k (A.labAll k τ)).card : ℝ) - locShare D A.eVec k (Sk k) * dS| ≤ εC * (locShare D A.eVec k (Sk k) * dS)`. Introduce `k`. Establish `h` using `hcount k ((Sk k : Finset (Tup D k)) : Set (Tup D k))`. Rewrite `h` using `[hdimK k, hDS k (Sk k)]`. Rewrite `h` using `[mul_comm dS]`. Then use the resulting hypothesis.

Establish `hbadR : (D.what₂.Dall : ℝ) - (D.what₂.Drows : ℝ) ≤ ((Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 0 (A.labAll 0 τ)).card : ℝ) + ((Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 1 (A.labAll 1 τ)).card : ℝ)`. Establish `: ((D.what₂.Dall : ℕ) : ℝ) ≤ ((D.what₂.Drows + (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 0 (A.labAll 0 τ)).card + (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 1 (A.labAll 1 τ)).card : ℕ) : ℝ)`. Conclude with `hbad` after adjusting the coercions. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hsh` using `hSF εC _ _ (locShare D A.eVec 0 (Sk 0)) (locShare D A.eVec 1 (Sk 1)) _ _ (D.what₂.Dall : ℝ) dS ((D.what₂.Dall : ℝ) - (D.what₂.Drows : ℝ)) h0 hlt hdSpos (hloc 0) (hW 0 (Sk 0) (hSk 0)) (hloc 1) (hW 1 (Sk 1) (hSk 1)) hU (hK 0) (hK 1) hbadR`. Establish `hApos : 0 < (D.what₂.Dall : ℝ)`. Use `(abs_sub_le_iff.1 hU).2` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hbE : (D.what₂.Dall : ℝ) - (D.what₂.Drows : ℝ) ≤ LChain6.E7 x ε * (D.what₂.Dall : ℝ)`.

Use `hsh.trans hnum` as an intermediate fact. Rewrite `this` using `[div_le_iff₀ hApos]`. Then use the resulting hypothesis. Establish `hDeq` using `D.what₂.D_eq`. Establish `hdel : D.what₂.delp * (D.what₂.Dall : ℝ) = (D.what₂.Dall : ℝ) - (D.what₂.Drows : ℝ)` using `by linarith`. Establish `hle' : (D.what₂.Drows : ℝ) ≤ (D.what₂.Dall : ℝ)` using `by exact_mod_cast hle`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show 0 ≤ D.what₂.delp`. Assume the negation of the conclusion as `hneg`. Use `push Not at hneg`. Establish `: D.what₂.delp * (D.what₂.Dall : ℝ) < 0` using `mul_neg_of_neg_of_pos hneg hApos`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `: D.what₂.delp * (D.what₂.Dall : ℝ) ≤ LChain6.E7 x ε * (D.what₂.Dall : ℝ)` using `by rw [hdel]; exact hbE`. Conclude with `le_of_mul_le_mul_right this hApos`.
-/
theorem delp_of_allRows (hSF : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.ShareFromCount) {D : D7} (A : AllRows D) (εC x ε : ℝ)
    (hT3 : LabelCountGoodInjective A) (hC : CountAllRows A εC) (hW : WeightAllRows A)
    (hnum : (1 + εC) / (1 - εC) *
      (Wg D.R.f D.R.m D.R.r (D.host.g 0) D.host.q D.host.d + Wg D.R.f D.R.m D.R.r (D.host.g 1) D.host.q D.host.d)
        ≤ LChain6.E7 x ε) :
    Rows.DelpNonneg D.what₂ ∧ D.what₂.delp ≤ Real.exp (-(x ^ (ε / 7))) := by
  classical
  obtain ⟨hT3a, hinj, hlab, hgood⟩ := hT3
  obtain ⟨h0, hlt, hdSpos, hcount⟩ := hC
  obtain ⟨hwt, hW⟩ := hW
  set dS := DstarE A A.B.e with hdS

  have hDS : ∀ (k : Fin 2) (S : Finset (Tup D k)),
      DstarE A (A.eT (cyl D k (S : Set (Tup D k)))) = dS * locShare D A.eVec k S := by
    intro k S
    simp only [hdS, DstarE, Formalism.MainNotions.S.AutInst.Dstar, locShare]
    rw [A.eT_one k S]
    ring

  have hdimU : A.dimT (cyl D 0 Set.univ) = D.what₂.Dall := by
    rw [hT3a]
    have hall : ∀ τ : Fin D.what₂.Dall, (fun k => A.labAll k τ) ∈ cyl D 0 Set.univ := fun τ => by simp [cyl]
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_eq_fintype_card, Fintype.card_fin]
  have hU := hcount 0 Set.univ
  rw [hdimU, Formalism.MainNotions.FamilyNumericLemmas.cyl_univ, A.eT_univ] at hU

  let Sk : (k : Fin 2) → Finset (Tup D k) := fun k =>
    (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D k (A.labAll k τ)).image fun τ => A.labAll k τ
  have hSk : ∀ k, ∀ t ∈ Sk k, ¬ goodAt D k t := by
    intro k t ht
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_filter.mp hτ).2
  have hmem : ∀ (k : Fin 2) (τ : Fin D.what₂.Dall),
      (fun k => A.labAll k τ) ∈ cyl D k ((Sk k : Finset (Tup D k)) : Set (Tup D k)) ↔
        ¬ goodAt D k (A.labAll k τ) := by
    intro k τ
    constructor
    · intro hτ; exact hSk k _ hτ
    · intro hτ
      show A.labAll k τ ∈ ((Sk k : Finset (Tup D k)) : Set (Tup D k))
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨τ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ⟩, rfl⟩)
  have hdimK : ∀ k, A.dimT (cyl D k ((Sk k : Finset (Tup D k)) : Set (Tup D k))) =
      (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D k (A.labAll k τ)).card := by
    intro k
    rw [hT3a, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun τ => by rw [hmem k τ]; simp))

  have hDrows : (Finset.univ.filter fun τ : Fin D.what₂.Dall => D.ntypes.goodTuple (fun k => A.labAll k τ)).card =
      D.what₂.Drows := by
    have : (Finset.univ.filter fun τ : Fin D.what₂.Dall => D.ntypes.goodTuple (fun k => A.labAll k τ)) =
        Finset.univ.image A.inc := by
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      rw [hgood τ]
      simp [Set.mem_range]
    rw [this, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hle : D.what₂.Drows ≤ D.what₂.Dall := by
    rw [← hDrows]
    exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])
  have hbad : D.what₂.Dall ≤ D.what₂.Drows +
      (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 0 (A.labAll 0 τ)).card +
      (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 1 (A.labAll 1 τ)).card := by
    have hsub : (Finset.univ : Finset (Fin D.what₂.Dall)) ⊆
        ((Finset.univ.filter fun τ : Fin D.what₂.Dall => D.ntypes.goodTuple (fun k => A.labAll k τ)) ∪
          (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 0 (A.labAll 0 τ))) ∪
        (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 1 (A.labAll 1 τ)) := by
      intro τ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      by_cases hg : D.ntypes.goodTuple (fun k => A.labAll k τ)
      · exact Or.inl (Or.inl hg)
      · by_contra hc
        push Not at hc
        apply hg
        intro k
        fin_cases k
        · exact hc.1.2
        · exact hc.2
    have := (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    rw [Finset.card_univ, Fintype.card_fin, hDrows] at this
    exact this

  have hloc : ∀ k, 0 ≤ locShare D A.eVec k (Sk k) := by
    intro k
    unfold locShare
    exact Finset.sum_nonneg (fun t _ => Finset.prod_nonneg (fun v _ => hwt k v (t v)))
  have hK : ∀ k, |((Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D k (A.labAll k τ)).card : ℝ) -
      locShare D A.eVec k (Sk k) * dS| ≤ εC * (locShare D A.eVec k (Sk k) * dS) := by
    intro k
    have h := hcount k ((Sk k : Finset (Tup D k)) : Set (Tup D k))
    rw [hdimK k, hDS k (Sk k)] at h
    rwa [mul_comm dS] at h
  have hbadR : (D.what₂.Dall : ℝ) - (D.what₂.Drows : ℝ) ≤
      ((Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 0 (A.labAll 0 τ)).card : ℝ) +
      ((Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 1 (A.labAll 1 τ)).card : ℝ) := by
    have : ((D.what₂.Dall : ℕ) : ℝ) ≤ ((D.what₂.Drows +
      (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 0 (A.labAll 0 τ)).card +
      (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 1 (A.labAll 1 τ)).card : ℕ) : ℝ) := by
      exact_mod_cast hbad
    push_cast at this
    linarith
  have hsh := hSF εC _ _ (locShare D A.eVec 0 (Sk 0)) (locShare D A.eVec 1 (Sk 1)) _ _ (D.what₂.Dall : ℝ) dS
    ((D.what₂.Dall : ℝ) - (D.what₂.Drows : ℝ)) h0 hlt hdSpos (hloc 0) (hW 0 (Sk 0) (hSk 0)) (hloc 1)
    (hW 1 (Sk 1) (hSk 1)) hU (hK 0) (hK 1) hbadR
  have hApos : 0 < (D.what₂.Dall : ℝ) := by
    have := (abs_sub_le_iff.1 hU).2
    nlinarith
  have hbE : (D.what₂.Dall : ℝ) - (D.what₂.Drows : ℝ) ≤ LChain6.E7 x ε * (D.what₂.Dall : ℝ) := by
    have := hsh.trans hnum
    rwa [div_le_iff₀ hApos] at this
  have hDeq := D.what₂.D_eq
  have hdel : D.what₂.delp * (D.what₂.Dall : ℝ) = (D.what₂.Dall : ℝ) - (D.what₂.Drows : ℝ) := by linarith
  have hle' : (D.what₂.Drows : ℝ) ≤ (D.what₂.Dall : ℝ) := by exact_mod_cast hle
  refine ⟨?_, ?_⟩
  · show 0 ≤ D.what₂.delp
    by_contra hneg
    push Not at hneg
    have : D.what₂.delp * (D.what₂.Dall : ℝ) < 0 := mul_neg_of_neg_of_pos hneg hApos
    linarith
  · have : D.what₂.delp * (D.what₂.Dall : ℝ) ≤ LChain6.E7 x ε * (D.what₂.Dall : ℝ) := by rw [hdel]; exact hbE
    exact le_of_mul_le_mul_right this hApos

/- English proof (translation)
Introduce `hSF hV7 eps Cs c he he1 hc Fm hIn`. Take `⟨x0, hx0⟩` from `hIn`. Establish `hez : 0 < Fm.ez` using `div_pos he (lt_of_lt_of_le one_pos Fm.one_le_J)`. Establish `hez1 : Fm.ez ≤ 1` using `(div_le_self he.le Fm.one_le_J).trans he1`. Establish `hev` using `((numbers_dominant_large hV7 (3 * Cs + 3) Fm.ez hez).and (weight_numbers_bound Fm.ez Cs hez hez1)).and (epsilon_bound_large_x c hc)`.

Take `⟨x1, hx1⟩` from `Filter.eventually_atTop.1 hev`. Use `⟨max x0 x1, fun x hx i => ?_⟩` and prove the remaining obligations. Take `⟨A, hT3, hC, hW, hS⟩` from `hx0 x (le_trans (le_max_left _ _) hx) i`. Take `⟨⟨hnum, hw⟩, heps⟩` from `hx1 x (le_trans (le_max_right _ _) hx)`. Establish `hN : NumbersAt x Fm.ez (epsC c (Fm.D x i).R.r (Fm.D x i).R.f) (3 * Cs + 3) (Wg (Fm.D x i).R.f (Fm.D x i).R.m (Fm.D x i).R.r ((Fm.D x i).host.g 0) (Fm.D x i).host.q (Fm.D x i).host.d) (Wg (Fm.D x i).R.f (Fm.D x i).R.m (Fm.D x i).R.r ((Fm.D x i).host.g 1) (Fm.D x i).host.q (Fm.D x …` using `⟨(Real.exp_pos _).le, heps _ _ (hS 0).2.2.2.2.1 (hS 0).2.1, hw _ _ _ _ _ _ (hS 0), hw _ _ _ _ _ _ (hS 1)⟩`.

Conclude with `delp_of_allRows hSF A _ x Fm.ez hT3 hC hW (hnum _ _ _ hN)`.
-/
theorem link_irreducible_all_rows : FamilyIrreducibleOfCountWeightSizes := by
  intro hSF hV7 eps Cs c he he1 hc Fm hIn
  obtain ⟨x0, hx0⟩ := hIn
  have hez : 0 < Fm.ez := div_pos he (lt_of_lt_of_le one_pos Fm.one_le_J)
  have hez1 : Fm.ez ≤ 1 := (div_le_self he.le Fm.one_le_J).trans he1
  have hev := ((numbers_dominant_large hV7 (3 * Cs + 3) Fm.ez hez).and (weight_numbers_bound Fm.ez Cs hez hez1)).and (epsilon_bound_large_x c hc)
  obtain ⟨x1, hx1⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max x0 x1, fun x hx i => ?_⟩
  obtain ⟨A, hT3, hC, hW, hS⟩ := hx0 x (le_trans (le_max_left _ _) hx) i
  obtain ⟨⟨hnum, hw⟩, heps⟩ := hx1 x (le_trans (le_max_right _ _) hx)
  have hN : NumbersAt x Fm.ez (epsC c (Fm.D x i).R.r (Fm.D x i).R.f) (3 * Cs + 3)
      (Wg (Fm.D x i).R.f (Fm.D x i).R.m (Fm.D x i).R.r ((Fm.D x i).host.g 0) (Fm.D x i).host.q (Fm.D x i).host.d)
      (Wg (Fm.D x i).R.f (Fm.D x i).R.m (Fm.D x i).R.r ((Fm.D x i).host.g 1) (Fm.D x i).host.q (Fm.D x i).host.d) :=
    ⟨(Real.exp_pos _).le, heps _ _ (hS 0).2.2.2.2.1 (hS 0).2.1, hw _ _ _ _ _ _ (hS 0), hw _ _ _ _ _ _ (hS 1)⟩
  exact delp_of_allRows hSF A _ x Fm.ez hT3 hC hW (hnum _ _ _ hN)

/- English proof (translation)
The claim follows from `link_irreducible_all_rows Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.share_from_count Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.dominant_numbers_sharp_holds`.
-/
theorem linkIRR_of_allRows :
    ∀ (eps Cs c : ℝ), 0 < eps → eps ≤ 1 → 0 < c → ∀ (Fm : FamP eps),
      (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : AllRows (Fm.D x i),
        LabelCountGoodInjective A ∧
        CountAllRows A (epsC c (Fm.D x i).R.r (Fm.D x i).R.f) ∧
        WeightAllRows A ∧
        SizesRec (Fm.D x i) x Fm.ez Cs) →
      LinkIRR Fm :=
  link_irreducible_all_rows Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.share_from_count Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.dominant_numbers_sharp_holds

end AllRowsIn

/- English proof (translation)
Take `⟨x0, hx0⟩` from `h`. Conclude with `linkIRR_of_allRows eps Cs c he he1 hc Fm ⟨x0, fun x hx i => ⟨A x i, hx0 x hx i⟩⟩`.
-/
theorem linkIRR_of_allRowsArg (eps Cs c : ℝ) (he : 0 < eps) (he1 : eps ≤ 1) (hc : 0 < c) (Fm : Formalism.MainNotions.FamP eps)
    (A : ∀ x (i : Fm.Ix x), Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i))
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective (A x i) ∧ CountAllRows (A x i) (epsC c (Fm.D x i).R.r (Fm.D x i).R.f) ∧
      WeightAllRows (A x i) ∧ SizesRec (Fm.D x i) x Fm.ez Cs) :
    Formalism.MainNotions.LinkIRR Fm := by
  obtain ⟨x0, hx0⟩ := h
  exact linkIRR_of_allRows eps Cs c he he1 hc Fm ⟨x0, fun x hx i => ⟨A x i, hx0 x hx i⟩⟩

end Formalism.L2.GlobalTheoryTheory.ConcN
