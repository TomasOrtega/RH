import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.LetterShift
import Formalism.FormalGroupWitt.WeightInvariance
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA
import Lemmata.GeneralBFactUpper.Imports

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF UnrOK frobVar frobVar_eq_expand)

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_upper.goal1 .. | (apply Bl.general_b_fact_upper.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_upper.goal1 <;> assumpt …`.
-/
theorem ip_norm_pow_sub_pow_le {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (n : ℕ) : ‖x ^ n - y ^ n‖ ≤ ‖x - y‖ := by
  first | exact Bl.general_b_fact_upper.goal1 .. | (apply Bl.general_b_fact_upper.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_upper.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_upper.goal1 K ‹_› ‹_› x y hx hy n | exact @Bl.general_b_fact_upper.goal1 K ‹_› ‹_› x y hx hy | exact @Bl.general_b_fact_upper.goal1 K ‹_› ‹_› x y hx | exact @Bl.general_b_fact_upper.goal1 K ‹_› ‹_› x y | exact @Bl.general_b_fact_upper.goal1 K ‹_› ‹_› x | exact @Bl.general_b_fact_upper.goal1 K ‹_› ‹_› | exact @Bl.general_b_fact_upper.goal1 K ‹_› | exact @Bl.general_b_fact_upper.goal1 K

/- English proof (translation)
Introduce `K _ _ _ l σ h`. Take `⟨hl, _, hn, _, hσ⟩` from `h`. Establish `hl1 : ((l : ℝ))⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ (by exact_mod_cast hl.one_le)`. Establish `hball : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1`. Introduce `a ha`.

Establish `h : σ a = (σ a - a ^ l) + a ^ l` using `by ring`. Rewrite using `[h]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hσ a ha).trans hl1) ?_)` and prove the remaining obligations. Rewrite using `[norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) ha`.

Use `⟨⟨hl, ⟨2, by norm_num, rfl⟩, ?_, ?_⟩, hball⟩` and prove the remaining obligations. Rewrite using `[hn]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)`. Introduce `a ha`. Rewrite using `[hn]`.

Establish `h : (σ.comp σ) a - a ^ (l ^ 2) = (σ (σ a) - (σ a) ^ l) + ((σ a) ^ l - (a ^ l) ^ l)`. Rewrite using `[RingHom.comp_apply, pow_two, pow_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hσ _ (hball a ha)) ?_)` and prove the remaining obligations.

Conclude with `(ip_norm_pow_sub_pow_le (hball a ha) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha) l).trans (hσ a ha)`.
-/
theorem frobenius_square : FrobSq := by
  intro K _ _ _ l σ h
  obtain ⟨hl, _, hn, _, hσ⟩ := h
  have hl1 : ((l : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hl.one_le)
  have hball : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1 := by
    intro a ha
    have h : σ a = (σ a - a ^ l) + a ^ l := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hσ a ha).trans hl1) ?_)
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ha
  refine ⟨⟨hl, ⟨2, by norm_num, rfl⟩, ?_, ?_⟩, hball⟩
  · rw [hn]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  · intro a ha
    rw [hn]
    have h : (σ.comp σ) a - a ^ (l ^ 2) =
        (σ (σ a) - (σ a) ^ l) + ((σ a) ^ l - (a ^ l) ^ l) := by
      rw [RingHom.comp_apply, pow_two, pow_mul]
      ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hσ _ (hball a ha)) ?_)
    exact (ip_norm_pow_sub_pow_le (hball a ha)
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha) l).trans (hσ a ha)

section Closure

variable {K : Type} [NormedField K] {τ : Type}

/- English proof (translation)
Introduce `n` and use `by rw [map_add] exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))`.
-/
theorem ip_integral_add [IsUltrametricDist K] {f g : MvPowerSeries τ K} (hf : Integral f)
    (hg : Integral g) : Integral (f + g) := fun n => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))

/- English proof (translation)
Introduce `n` and use `by rw [MvPowerSeries.coeff_C_mul, norm_mul] exact mul_le_one₀ hc (norm_nonneg _) (hg n)`.
-/
theorem ip_integral_C_mul {c : K} {g : MvPowerSeries τ K} (hc : ‖c‖ ≤ 1) (hg : Integral g) :
    Integral (MvPowerSeries.C c * g) := fun n => by
  rw [MvPowerSeries.coeff_C_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (hg n)

/- English proof (translation)
Break down `Nat.eq_zero_or_pos l with rfl | hl` into its components or cases. Simplify using the standard rewrite rules. Establish `hq : l ^ 2 ≠ 0` using `by positivity`. Rewrite using `[frobVar_eq_expand hq, map_zero, map_zero, mul_zero]`.
-/
theorem ip_op_zero (l : ℕ) (σ : K →+* K) :
    MvPowerSeries.C ((l : K)⁻¹) *
      frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) (0 : MvPowerSeries τ K)) = 0 := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  · have hq : l ^ 2 ≠ 0 := by positivity
    rw [frobVar_eq_expand hq, map_zero, map_zero, mul_zero]

/- English proof (translation)
Break down `Nat.eq_zero_or_pos l with rfl | hl` into its components or cases. Simplify using the standard rewrite rules. Establish `hq : l ^ 2 ≠ 0` using `by positivity`. Rewrite using `[frobVar_eq_expand hq, frobVar_eq_expand hq, frobVar_eq_expand hq, map_add, map_add, mul_add]`.
-/
theorem ip_op_add (l : ℕ) (σ : K →+* K) (g g' : MvPowerSeries τ K) :
    MvPowerSeries.C ((l : K)⁻¹) * frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) (g + g')) =
      MvPowerSeries.C ((l : K)⁻¹) * frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) g) +
      MvPowerSeries.C ((l : K)⁻¹) * frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) g') := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  · have hq : l ^ 2 ≠ 0 := by positivity
    rw [frobVar_eq_expand hq, frobVar_eq_expand hq, frobVar_eq_expand hq, map_add, map_add,
      mul_add]

/- English proof (translation)
Break down `Nat.eq_zero_or_pos l with rfl | hl` into its components or cases. Simplify using the standard rewrite rules. Establish `hq : l ^ 2 ≠ 0` using `by positivity`. Rewrite using `[frobVar_eq_expand hq, frobVar_eq_expand hq, map_mul, MvPowerSeries.map_C, map_mul, MvPowerSeries.expand_C, RingHom.comp_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ip_op_C_mul (l : ℕ) (σ : K →+* K) (c : K) (g : MvPowerSeries τ K) :
    MvPowerSeries.C ((l : K)⁻¹) *
        frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) (MvPowerSeries.C c * g)) =
      MvPowerSeries.C (σ (σ c)) *
        (MvPowerSeries.C ((l : K)⁻¹) * frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) g)) := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  · have hq : l ^ 2 ≠ 0 := by positivity
    rw [frobVar_eq_expand hq, frobVar_eq_expand hq, map_mul, MvPowerSeries.map_C, map_mul,
      MvPowerSeries.expand_C, RingHom.comp_apply]
    ring

end Closure

/- English proof (translation)
Introduce `K _ _ _ l σ τ _`. Use `⟨⟨map_zero _, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ip_op_zero, sub_zero]`. Introduce `n`. Simplify using the standard rewrite rules.

Introduce and unpack `g g' ⟨h0, hI⟩ ⟨h0', hI'⟩`. Use `⟨by rw [map_add, h0, h0', add_zero], ?_⟩` and prove the remaining obligations. Rewrite using `[ip_op_add, add_sub_add_comm]`. Conclude with `ip_integral_add hI hI'`. Introduce and unpack `c g hc hσ ⟨h0, hI⟩`.

Use `⟨by rw [map_mul, h0, mul_zero], ?_⟩` and prove the remaining obligations. Rewrite using `[ip_op_C_mul, hσ, ← mul_sub]`. Conclude with `ip_integral_C_mul hc hI`.
-/
theorem integral_part_closure : IPClosure := by
  intro K _ _ _ l σ τ _
  refine ⟨⟨map_zero _, ?_⟩, ?_, ?_⟩
  · rw [ip_op_zero, sub_zero]
    intro n
    simp
  · rintro g g' ⟨h0, hI⟩ ⟨h0', hI'⟩
    refine ⟨by rw [map_add, h0, h0', add_zero], ?_⟩
    rw [ip_op_add, add_sub_add_comm]
    exact ip_integral_add hI hI'
  · rintro c g hc hσ ⟨h0, hI⟩
    refine ⟨by rw [map_mul, h0, mul_zero], ?_⟩
    rw [ip_op_C_mul, hσ, ← mul_sub]
    exact ip_integral_C_mul hc hI

/- English proof (translation)
Express the relevant statement in the definitionally equal form `PowerSeries.map φ (lgF K l) = lgF K l`. Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_map]`. Unfold `lgF`. Rewrite using `[PowerSeries.coeff_mk, map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[map_inv₀, map_pow, map_natCast]`. Rewrite using `[map_zero]`.
-/
theorem ip_map_lgF {K : Type} [Field K] (l : ℕ) (φ : K →+* K) :
    MvPowerSeries.map φ (lgF K l : MvPowerSeries Unit K) = lgF K l := by
  change PowerSeries.map φ (lgF K l) = lgF K l
  ext n
  rw [PowerSeries.coeff_map]
  unfold lgF
  rw [PowerSeries.coeff_mk, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [map_inv₀, map_pow, map_natCast]
  · rw [map_zero]

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem ip_expand_congr {K τ : Type} [Field K] {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a = b)
    (f : MvPowerSeries τ K) : MvPowerSeries.expand a ha f = MvPowerSeries.expand b hb f := by
  subst h
  rfl

/- English proof (translation)
Establish `hl0 : l ≠ 0` using `by omega`. Take `⟨h1, h2⟩` from `Formalism.InvariantFactorPaths.G7.g_zero_relation_holds K l hl hlK`. Establish `e : ∀ f : PowerSeries K, (PowerSeries.subst (PowerSeries.X ^ l : PowerSeries K) f : PowerSeries K) = MvPowerSeries.expand l hl0 (f : MvPowerSeries Unit K)` using `fun f => frobVar_eq_expand hl0 (f : MvPowerSeries Unit K)`. Rewrite `h2` using `[h1, e, e]`. Establish `h3 : MvPowerSeries.expand l hl0 ((MvPowerSeries.C ((l : K)⁻¹) : MvPowerSeries Unit K) * MvPowerSeries.expand l hl0 (lgF K l : MvPowerSeries Unit K)) = (lgF K l : MvPowerSeries Unit K) - MvPowerSeries.X ()` using `h2`.

Rewrite `h3` using `[map_mul, MvPowerSeries.expand_C, ← MvPowerSeries.expand_mul, ip_expand_congr (Nat.mul_ne_zero hl0 hl0) hq (pow_two l).symm, ← MvPowerSeries.smul_eq_C_mul]`. Rewrite using `[h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ip_lgF_funEq {K : Type} [Field K] {l : ℕ} (hl : 2 ≤ l) (hlK : (l : K) ≠ 0)
    (hq : l ^ 2 ≠ 0) :
    (lgF K l : MvPowerSeries Unit K) -
      (l : K)⁻¹ • MvPowerSeries.expand (l ^ 2) hq (lgF K l : MvPowerSeries Unit K) =
      MvPowerSeries.X () := by
  have hl0 : l ≠ 0 := by omega
  obtain ⟨h1, h2⟩ := Formalism.InvariantFactorPaths.G7.g_zero_relation_holds K l hl hlK
  have e : ∀ f : PowerSeries K, (PowerSeries.subst (PowerSeries.X ^ l : PowerSeries K) f :
      PowerSeries K) = MvPowerSeries.expand l hl0 (f : MvPowerSeries Unit K) :=
    fun f => frobVar_eq_expand hl0 (f : MvPowerSeries Unit K)
  rw [h1, e, e] at h2
  have h3 : MvPowerSeries.expand l hl0 ((MvPowerSeries.C ((l : K)⁻¹) : MvPowerSeries Unit K) *
      MvPowerSeries.expand l hl0 (lgF K l : MvPowerSeries Unit K)) =
      (lgF K l : MvPowerSeries Unit K) - MvPowerSeries.X () := h2
  rw [map_mul, MvPowerSeries.expand_C, ← MvPowerSeries.expand_mul,
    ip_expand_congr (Nat.mul_ne_zero hl0 hl0) hq (pow_two l).symm,
    ← MvPowerSeries.smul_eq_C_mul] at h3
  rw [h3]
  ring

/- English proof (translation)
Introduce `hF K _ _ _ l σ h τ _ g hg`. Take `⟨hset, _⟩` from `hF K l σ h`. Establish `hl : l.Prime` using `h.1`. Establish `hq : l ^ 2 ≠ 0` using `pow_ne_zero 2 hl.ne_zero`. Establish `hlK : (l : K) ≠ 0` using `Nat.cast_ne_zero.mpr hl.ne_zero`.

Establish `hid : Formalism.FG.IsIdMod2 (fun _ : Unit => (lgF K l : MvPowerSeries Unit K))`. Use `⟨fun _ => ?_, fun j i => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Establish `hc' : PowerSeries.coeff 0 (lgF K l) ≠ 0`. Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff]`.

Conclude with `hc`. Take `⟨j, hj⟩` from `Formalism.InvariantFactorPaths.G7.coeff_lgF_ne_zero hc'`. Conclude with `(pow_ne_zero j hq) hj.symm`. Establish `h1` using `Formalism.InvariantFactorPaths.G7.coeff_lgF_pow K hl.two_le 0`. Simplify using `only [pow_zero, inv_one] at h1`.

Rewrite using `[if_pos (Subsingleton.elim i j)]`. Conclude with `h1`. Establish `hf : Formalism.FG.IsFunEqTypeV l (l ^ 2) hq (σ.comp σ) (fun _ _ : Unit => (1 : K)) (fun _ : Unit => (lgF K l : MvPowerSeries Unit K))`. Introduce `_`. Simplify using `only [Finset.univ_unique, Finset.sum_singleton, one_smul]`.

Rewrite using `[ip_map_lgF, ip_lgF_funEq hl.two_le hlK hq]`. Introduce `d`. Rewrite using `[MvPowerSeries.coeff_X]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hgt : Formalism.FG.IsFunEqTypeV l (l ^ 2) hq (σ.comp σ) (fun _ _ : Unit => (1 : K)) (fun _ : Unit => g)`.

Introduce `_`. Simplify using `only [Finset.univ_unique, Finset.sum_singleton, one_smul]`. Rewrite using `[MvPowerSeries.smul_eq_C_mul, ← frobVar_eq_expand hq]`. Conclude with `hg.2`. Take `⟨hh, h0, hI, hs⟩` from `Formalism.FG.funEqHomV K l (l ^ 2) hq (σ.comp σ) hset Unit (fun _ _ => 1) (fun _ _ => by simp) (fun _ => lgF K l) hid hf τ (fun _ => g) (fun _ => hg.1) hgt`.

Conclude with `⟨hh (), h0 (), hI (), hs ()⟩`.
-/
theorem IPLemma_of : FrobSq → IPLemma := by
  intro hF K _ _ _ l σ h τ _ g hg
  obtain ⟨hset, _⟩ := hF K l σ h
  have hl : l.Prime := h.1
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hl.ne_zero
  have hlK : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hid : Formalism.FG.IsIdMod2 (fun _ : Unit => (lgF K l : MvPowerSeries Unit K)) := by
    refine ⟨fun _ => ?_, fun j i => ?_⟩
    · by_contra hc
      have hc' : PowerSeries.coeff 0 (lgF K l) ≠ 0 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff]
        exact hc
      obtain ⟨j, hj⟩ := Formalism.InvariantFactorPaths.G7.coeff_lgF_ne_zero hc'
      exact (pow_ne_zero j hq) hj.symm
    · have h1 := Formalism.InvariantFactorPaths.G7.coeff_lgF_pow K hl.two_le 0
      simp only [pow_zero, inv_one] at h1
      rw [if_pos (Subsingleton.elim i j)]
      exact h1
  have hf : Formalism.FG.IsFunEqTypeV l (l ^ 2) hq (σ.comp σ) (fun _ _ : Unit => (1 : K))
      (fun _ : Unit => (lgF K l : MvPowerSeries Unit K)) := by
    intro _
    simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
    rw [ip_map_lgF, ip_lgF_funEq hl.two_le hlK hq]
    intro d
    rw [MvPowerSeries.coeff_X]
    split_ifs <;> simp
  have hgt : Formalism.FG.IsFunEqTypeV l (l ^ 2) hq (σ.comp σ) (fun _ _ : Unit => (1 : K))
      (fun _ : Unit => g) := by
    intro _
    simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
    rw [MvPowerSeries.smul_eq_C_mul, ← frobVar_eq_expand hq]
    exact hg.2
  obtain ⟨hh, h0, hI, hs⟩ := Formalism.FG.funEqHomV K l (l ^ 2) hq (σ.comp σ) hset Unit
    (fun _ _ => 1) (fun _ _ => by simp) (fun _ => lgF K l) hid hf τ (fun _ => g)
    (fun _ => hg.1) hgt
  exact ⟨hh (), h0 (), hI (), hs ()⟩

/- English proof (translation)
The claim follows from `IPLemma_of frobenius_square`.
-/
theorem integral_part_lemma : IPLemma := IPLemma_of frobenius_square

end Formalism.L2.Th1.D
