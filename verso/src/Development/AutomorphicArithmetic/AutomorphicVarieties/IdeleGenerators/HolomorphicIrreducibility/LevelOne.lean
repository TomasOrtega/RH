import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

open UpperHalfPlane CongruenceSubgroup UpperTheory.V.Af
open scoped MatrixGroups ModularForm

namespace UpperTheory.V.Sd

private def GoodWt (k : ℕ) : Prop :=
  ∃ f : ModularForm 𝒮ℒ (k : ℤ), coef f 0 = 1 ∧ ∀ n, ∃ c : ℤ, coef f n = c

/- English proof (translation)
Rewrite using `[bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]`.
-/
private lemma bern4 : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]

/- English proof (translation)
Establish `h5 : bernoulli' 5 = 0` using `bernoulli'_eq_zero_of_odd (by decide) (by norm_num)`. Rewrite using `[bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]`. Evaluate the numerical expressions using `[Finset.sum_range_succ, h5, Nat.choose, bernoulli'_four, bernoulli'_three, bernoulli'_two]`.
-/
private lemma bern6 : bernoulli 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
  norm_num [Finset.sum_range_succ, h5, Nat.choose, bernoulli'_four, bernoulli'_three, bernoulli'_two]

/- English proof (translation)
Use `⟨(1 : ModularForm 𝒮ℒ 0), ?_, fun n => ?_⟩` and prove the remaining obligations. Simplify using `[coef, qExpansion_one]`. Use `⟨if n = 0 then 1 else 0, ?_⟩` and prove the remaining obligations. Simplify using `[coef, qExpansion_one, PowerSeries.coeff_one]`.
-/
private lemma good0 : GoodWt 0 := by
  refine ⟨(1 : ModularForm 𝒮ℒ 0), ?_, fun n => ?_⟩
  · simp [coef, qExpansion_one]
  · refine ⟨if n = 0 then 1 else 0, ?_⟩
    simp [coef, qExpansion_one, PowerSeries.coeff_one]

/- English proof (translation)
Use `⟨ModularForm.E (k := 4) (by norm_num), ?_, fun n => ?_⟩` and prove the remaining obligations. Conclude with `EisensteinSeries.E_qExpansion_coeff_zero _ (by decide)`. Use `⟨if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℤ), ?_⟩` and prove the remaining obligations. Unfold `coef`. Rewrite using `[EisensteinSeries.E_qExpansion_coeff _ (by decide), bern4]`.

Use `split_ifs`. Simplify using the standard rewrite rules. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma good4 : GoodWt 4 := by
  refine ⟨ModularForm.E (k := 4) (by norm_num), ?_, fun n => ?_⟩
  · exact EisensteinSeries.E_qExpansion_coeff_zero _ (by decide)
  · refine ⟨if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℤ), ?_⟩
    unfold coef
    rw [EisensteinSeries.E_qExpansion_coeff _ (by decide), bern4]
    split_ifs
    · simp
    · push_cast; ring

/- English proof (translation)
Use `⟨ModularForm.E (k := 6) (by norm_num), ?_, fun n => ?_⟩` and prove the remaining obligations. Conclude with `EisensteinSeries.E_qExpansion_coeff_zero _ (by decide)`. Use `⟨if n = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 n : ℤ), ?_⟩` and prove the remaining obligations. Unfold `coef`. Rewrite using `[EisensteinSeries.E_qExpansion_coeff _ (by decide), bern6]`.

Use `split_ifs`. Simplify using the standard rewrite rules. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma good6 : GoodWt 6 := by
  refine ⟨ModularForm.E (k := 6) (by norm_num), ?_, fun n => ?_⟩
  · exact EisensteinSeries.E_qExpansion_coeff_zero _ (by decide)
  · refine ⟨if n = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 n : ℤ), ?_⟩
    unfold coef
    rw [EisensteinSeries.E_qExpansion_coeff _ (by decide), bern6]
    split_ifs
    · simp
    · push_cast; ring

/- English proof (translation)
Take `⟨f, hf0, hf⟩` from `ha`. Take `⟨g, hg0, hg⟩` from `hb`. Establish `h` using `ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f g`. Establish `key : ∀ n, coef (ModularForm.mcast (show (a : ℤ) + b = ((a + b : ℕ) : ℤ) by push_cast; ring) (f.mul g)) n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coef f p.1 * coef g p.2`. Introduce `n`.

Unfold `coef`. Rewrite using `[ModularForm.coe_mcast, h, PowerSeries.coeff_mul]`. Use `⟨ModularForm.mcast (show (a : ℤ) + b = ((a + b : ℕ) : ℤ) by push_cast; ring) (f.mul g), ?_, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[key]`. Simplify using `[hf0, hg0]`.

Use `choose c hc using hf choose d hd using hg`. Use `⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c p.1 * d p.2, ?_⟩` and prove the remaining obligations. Rewrite using `[key]`. Simplify using `[hc, hd]`.
-/
private lemma good_add {a b : ℕ} (ha : GoodWt a) (hb : GoodWt b) : GoodWt (a + b) := by
  obtain ⟨f, hf0, hf⟩ := ha
  obtain ⟨g, hg0, hg⟩ := hb
  have h := ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f g
  have key : ∀ n, coef (ModularForm.mcast (show (a : ℤ) + b = ((a + b : ℕ) : ℤ) by push_cast; ring) (f.mul g)) n =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coef f p.1 * coef g p.2 := by
    intro n
    unfold coef
    rw [ModularForm.coe_mcast, h, PowerSeries.coeff_mul]
  refine ⟨ModularForm.mcast (show (a : ℤ) + b = ((a + b : ℕ) : ℤ) by push_cast; ring) (f.mul g), ?_, fun n => ?_⟩
  · rw [key]; simp [hf0, hg0]
  · choose c hc using hf
    choose d hd using hg
    refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c p.1 * d p.2, ?_⟩
    rw [key]
    simp [hc, hd]

/- English proof (translation)
Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Take `⟨m, hm⟩` from `hk`. Distinguish the cases in `h0 : k = 0`. Substitute `h0` using the available equality.

Conclude with `good0`. Distinguish the cases in `h6 : k = 6`. Substitute `h6` using the available equality. Conclude with `good6`. Establish `: k = (k - 4) + 4` using `by omega`.

Rewrite using `[this]`. Conclude with `good_add (ih _ (by omega) ⟨m - 2, by omega⟩ (by omega)) good4`.
-/
private lemma good_all (k : ℕ) (hk : Even k) (h2 : k ≠ 2) : GoodWt k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨m, hm⟩ := hk
    by_cases h0 : k = 0
    · subst h0; exact good0
    by_cases h6 : k = 6
    · subst h6; exact good6
    have : k = (k - 4) + 4 := by omega
    rw [this]
    exact good_add (ih _ (by omega) ⟨m - 2, by omega⟩ (by omega)) good4

end UpperTheory.V.Sd

/- English proof (translation)
Introduce `N k _ hk h2`. Take `⟨f, hf0, hf⟩` from `UpperTheory.V.Sd.good_all k hk h2`. Establish `hle : (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)) ≤ 𝒮ℒ` using `Subgroup.map_le_range _ _`. Use `⟨⟨⟨f, fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ (hle hγ)⟩, ModularFormClass.holo f, fun hc => f.bdd_at_cusps' (hc.mono hle)⟩, fun γ => ?_, hf0, hf⟩` and prove the remaining obligations. Conclude with `SlashInvariantFormClass.slash_action_eq f (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, rfl⟩`.
-/
theorem UpperTheory.V.Sd.levelOne :
    UpperTheory.V.Sd.LevelOne := by
  intro N k _ hk h2
  obtain ⟨f, hf0, hf⟩ := UpperTheory.V.Sd.good_all k hk h2
  have hle : (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)) ≤ 𝒮ℒ := Subgroup.map_le_range _ _
  refine ⟨⟨⟨f, fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ (hle hγ)⟩, ModularFormClass.holo f,
    fun hc => f.bdd_at_cusps' (hc.mono hle)⟩, fun γ => ?_, hf0, hf⟩
  exact SlashInvariantFormClass.slash_action_eq f (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, rfl⟩
