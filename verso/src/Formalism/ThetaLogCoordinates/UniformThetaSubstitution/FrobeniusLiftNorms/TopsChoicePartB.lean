import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.OddLogRelation
import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison
import Formalism.FormalGroupWitt.FormalGroupWittProofs.IntegralSubstVector
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low WtGe MonoWtGe dot dot_const substitution_weight_bound)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff)

def clSum {K ι : Type} [Field K] (pp : K) (hh : MvPowerSeries ι K) (U : ℕ → MvPowerSeries ι K)
    (M : ℕ) : MvPowerSeries ι K :=
  ∑ i ∈ range M, MvPowerSeries.C ((pp ^ i)⁻¹) * (hh ^ i * U i)

/- English proof (translation)
Introduce `d hd`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun a ha => h a ha d hd`.
-/
theorem low_sum {K ι α : Type} [Field K] (s : Finset α) (f : α → MvPowerSeries ι K) (N : ℕ)
    (h : ∀ a ∈ s, Low N (f a)) : Low N (∑ a ∈ s, f a) := by
  intro d hd
  rw [map_sum]
  exact Finset.sum_eq_zero fun a ha => h a ha d hd

/- English proof (translation)
Simplify using `using low_mul (low_pow ((low_one_iff _).2 h0) i) (low_zero U)`.
-/
theorem low_pow_mul {K ι : Type} [Field K] {hh : MvPowerSeries ι K}
    (h0 : MvPowerSeries.constantCoeff hh = 0) (i : ℕ) (U : MvPowerSeries ι K) :
    Low i (hh ^ i * U) := by
  simpa using low_mul (low_pow ((low_one_iff _).2 h0) i) (low_zero U)

/- English proof (translation)
Simplify using `only [clSum, map_sum, MvPowerSeries.coeff_C_mul]`.
-/
theorem coeff_clSum {K ι : Type} [Field K] (pp : K) (hh : MvPowerSeries ι K)
    (U : ℕ → MvPowerSeries ι K) (M : ℕ) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (clSum pp hh U M) =
      ∑ i ∈ range M, (pp ^ i)⁻¹ * MvPowerSeries.coeff n (hh ^ i * U i) := by
  simp only [clSum, map_sum, MvPowerSeries.coeff_C_mul]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨U, hU, h⟩`. Use `⟨U, hU, fun M d hd => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, h d, coeff_clSum, sub_eq_zero]`. Use `Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun i _ hi => ?_` and prove the remaining obligations.

Rewrite using `[low_pow_mul h0 i (U i) d (by simp only [mem_range] at hi; omega), mul_zero]`. Introduce and unpack `⟨U, hU, h⟩`. Use `⟨U, hU, fun n => ?_⟩` and prove the remaining obligations. Use `h (n.degree + 1) n (by omega)` as an intermediate fact. Rewrite `this` using `[map_sub, coeff_clSum, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem inClass_iff {K ι : Type} [NormedField K] {pp : K} {hh : MvPowerSeries ι K}
    (h0 : MvPowerSeries.constantCoeff hh = 0) (F : MvPowerSeries ι K) :
    InClass pp hh F ↔ ∃ U : ℕ → MvPowerSeries ι K, (∀ i, Integral (U i)) ∧
      ∀ M, Low M (F - clSum pp hh U M) := by
  constructor
  · rintro ⟨U, hU, h⟩
    refine ⟨U, hU, fun M d hd => ?_⟩
    rw [map_sub, h d, coeff_clSum, sub_eq_zero]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun i _ hi => ?_
    rw [low_pow_mul h0 i (U i) d (by simp only [mem_range] at hi; omega), mul_zero]
  · rintro ⟨U, hU, h⟩
    refine ⟨U, hU, fun n => ?_⟩
    have := h (n.degree + 1) n (by omega)
    rwa [map_sub, coeff_clSum, sub_eq_zero] at this

/- English proof (translation)
Introduce `K ι _ _ pp hh F V h0 hV hF`. Rewrite `hF`, the goal using `[inClass_iff h0]`. Take `⟨U, hU, h⟩` from `hF`. Use `⟨fun i => U i * V, fun i => Formalism.FG.IntegralSubstitution.integral_mul (hU i) hV, fun M => ?_⟩` and prove the remaining obligations. Establish `e : F * V - clSum pp hh (fun i => U i * V) M = (F - clSum pp hh U M) * V`.

Simplify using `only [clSum, sub_mul, Finset.sum_mul]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[e]`. Simplify using `using low_mul (h M) (low_zero V)`.
-/
theorem class_multiplication : ClassMul := by
  intro K ι _ _ pp hh F V h0 hV hF
  rw [inClass_iff h0] at hF ⊢
  obtain ⟨U, hU, h⟩ := hF
  refine ⟨fun i => U i * V, fun i => Formalism.FG.IntegralSubstitution.integral_mul (hU i) hV, fun M => ?_⟩
  have e : F * V - clSum pp hh (fun i => U i * V) M = (F - clSum pp hh U M) * V := by
    simp only [clSum, sub_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  simpa using low_mul (h M) (low_zero V)

/- English proof (translation)
Introduce `K ι κ _ _ _ pp hh F φ h0 hφ0 hφ hF`. Establish `hs : MvPowerSeries.HasSubst φ` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0`. Establish `h0' : MvPowerSeries.constantCoeff (MvPowerSeries.subst φ hh) = 0` using `(low_one_iff _).1 (low_subst_of_low hφ0 ((low_one_iff _).2 h0))`. Rewrite `hF` using `[inClass_iff h0]`. Rewrite using `[inClass_iff h0']`.

Take `⟨U, hU, h⟩` from `hF`. Use `⟨fun i => MvPowerSeries.subst φ (U i), fun i => Formalism.FG.IntegralSubstitution.integralSubstV _ _ (hU i) hφ0 hφ, fun M => ?_⟩` and prove the remaining obligations. Establish `e : MvPowerSeries.subst φ F - clSum pp (MvPowerSeries.subst φ hh) (fun i => MvPowerSeries.subst φ (U i)) M = MvPowerSeries.subst φ (F - clSum pp hh U M)`. Simplify using `only [clSum, ← MvPowerSeries.coe_substAlgHom hs, map_sub, map_sum, map_mul, map_pow]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `((MvPowerSeries.substAlgHom hs).commutes ((pp ^ i)⁻¹)).symm`. Rewrite using `[e]`. Conclude with `low_subst_of_low hφ0 (h M)`.
-/
theorem class_substitution : ClassSubst := by
  intro K ι κ _ _ _ pp hh F φ h0 hφ0 hφ hF
  have hs : MvPowerSeries.HasSubst φ := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0
  have h0' : MvPowerSeries.constantCoeff (MvPowerSeries.subst φ hh) = 0 :=
    (low_one_iff _).1 (low_subst_of_low hφ0 ((low_one_iff _).2 h0))
  rw [inClass_iff h0] at hF
  rw [inClass_iff h0']
  obtain ⟨U, hU, h⟩ := hF
  refine ⟨fun i => MvPowerSeries.subst φ (U i),
    fun i => Formalism.FG.IntegralSubstitution.integralSubstV _ _ (hU i) hφ0 hφ, fun M => ?_⟩
  have e : MvPowerSeries.subst φ F -
      clSum pp (MvPowerSeries.subst φ hh) (fun i => MvPowerSeries.subst φ (U i)) M =
      MvPowerSeries.subst φ (F - clSum pp hh U M) := by
    simp only [clSum, ← MvPowerSeries.coe_substAlgHom hs, map_sub, map_sum, map_mul, map_pow]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact ((MvPowerSeries.substAlgHom hs).commutes ((pp ^ i)⁻¹)).symm
  rw [e]
  exact low_subst_of_low hφ0 (h M)

def chT {K ι : Type} [Field K] (Y : MvPowerSeries ι K) (U : ℕ → MvPowerSeries ι K) (b a : ℕ) :
    MvPowerSeries ι K :=
  MvPowerSeries.C (((b + a).choose b : ℕ) : K) * ((-Y) ^ a * U (b + a))

def chU {K ι : Type} [Field K] (Y : MvPowerSeries ι K) (U : ℕ → MvPowerSeries ι K) (b : ℕ) :
    MvPowerSeries ι K :=
  fun n => ∑ a ∈ range (n.degree + 1), MvPowerSeries.coeff n (chT Y U b a)

/- English proof (translation)
Establish `hY' : MvPowerSeries.constantCoeff (-Y) = 0` using `by rw [map_neg, hY, neg_zero]`. Simplify `low_mul (low_zero (MvPowerSeries.C (((b + a).choose b : ℕ) : K))) (low_pow_mul hY' a (U (b + a)))` using `[chT]`.
-/
theorem low_chT {K ι : Type} [Field K] {Y : MvPowerSeries ι K}
    (hY : MvPowerSeries.constantCoeff Y = 0) (U : ℕ → MvPowerSeries ι K) (b a : ℕ) :
    Low a (chT Y U b a) := by
  have hY' : MvPowerSeries.constantCoeff (-Y) = 0 := by rw [map_neg, hY, neg_zero]
  simpa [chT] using low_mul (low_zero (MvPowerSeries.C (((b + a).choose b : ℕ) : K)))
    (low_pow_mul hY' a (U (b + a)))

/- English proof (translation)
Introduce `d hd`. Rewrite using `[map_sub, map_sum, sub_eq_zero]`. Use `symm`. Use `Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun a _ ha => ?_` and prove the remaining obligations. Conclude with `low_chT hY U b a d (by simp only [mem_range] at ha; omega)`.
-/
theorem low_chU {K ι : Type} [Field K] {Y : MvPowerSeries ι K}
    (hY : MvPowerSeries.constantCoeff Y = 0) (U : ℕ → MvPowerSeries ι K) (b N : ℕ) :
    Low N (∑ a ∈ range N, chT Y U b a - chU Y U b) := by
  intro d hd
  rw [map_sub, map_sum, sub_eq_zero]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun a _ ha => ?_
  exact low_chT hY U b a d (by simp only [mem_range] at ha; omega)

/- English proof (translation)
Introduce `n`. Express the relevant statement in the definitionally equal form `‖∑ a ∈ range (n.degree + 1), MvPowerSeries.coeff n (chT Y U b a)‖ ≤ 1`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun a _ => ?_` and prove the remaining obligations. Establish `hY' : Integral (-Y)` using `fun m => by rw [map_neg, norm_neg]; exact hY m`. Rewrite using `[chT, MvPowerSeries.coeff_C_mul, norm_mul]`.

Conclude with `mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one K _) (norm_nonneg _) (Formalism.FG.IntegralSubstitution.integral_mul (Formalism.FG.IntegralSubstitution.integral_pow hY' a) (hU _) n)`.
-/
theorem integral_chU {K ι : Type} [NormedField K] [IsUltrametricDist K] {Y : MvPowerSeries ι K}
    (hY : Integral Y) {U : ℕ → MvPowerSeries ι K} (hU : ∀ i, Integral (U i)) (b : ℕ) :
    Integral (chU Y U b) := by
  intro n
  change ‖∑ a ∈ range (n.degree + 1), MvPowerSeries.coeff n (chT Y U b a)‖ ≤ 1
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun a _ => ?_
  have hY' : Integral (-Y) := fun m => by rw [map_neg, norm_neg]; exact hY m
  rw [chT, MvPowerSeries.coeff_C_mul, norm_mul]
  exact mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one K _) (norm_nonneg _)
    (Formalism.FG.IntegralSubstitution.integral_mul (Formalism.FG.IntegralSubstitution.integral_pow hY' a) (hU _) n)

/- English proof (translation)
Rewrite using `[Finset.sum_comm' (t' := range M) (s' := fun b => Finset.Ico b M) (by intro i b; simp only [mem_range, Finset.mem_Ico]; omega)]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_Ico_eq_sum_range]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [Nat.add_sub_cancel_left]`.
-/
theorem sum_triangle {A : Type} [AddCommMonoid A] (g : ℕ → ℕ → A) (M : ℕ) :
    ∑ i ∈ range M, ∑ b ∈ range (i + 1), g b (i - b) =
      ∑ b ∈ range M, ∑ a ∈ range (M - b), g b a := by
  rw [Finset.sum_comm' (t' := range M) (s' := fun b => Finset.Ico b M)
    (by intro i b; simp only [mem_range, Finset.mem_Ico]; omega)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_Ico_eq_sum_range]
  exact Finset.sum_congr rfl fun a _ => by rw [Nat.add_sub_cancel_left]

/- English proof (translation)
Establish `e : hh = (hh + MvPowerSeries.C pp * Y) + MvPowerSeries.C pp * (-Y)` using `by ring`. Use `conv_lhs => rw [e, add_pow, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b hb => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩ : ∃ a, i = b + a` from `⟨i - b, by simp only [mem_range] at hb; omega⟩`. Establish `key : (MvPowerSeries.C ((pp ^ (b + a))⁻¹) : MvPowerSeries ι K) * MvPowerSeries.C pp ^ a = MvPowerSeries.C ((pp ^ b)⁻¹)`.

Rewrite using `[← map_pow, ← map_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Nat.add_sub_cancel_left, chT, mul_pow, map_natCast, ← key]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem term_change {K ι : Type} [Field K] {pp : K} (hpp : pp ≠ 0) (hh Y : MvPowerSeries ι K)
    (U : ℕ → MvPowerSeries ι K) (i : ℕ) :
    MvPowerSeries.C ((pp ^ i)⁻¹) * (hh ^ i * U i) =
      ∑ b ∈ range (i + 1), MvPowerSeries.C ((pp ^ b)⁻¹) *
        ((hh + MvPowerSeries.C pp * Y) ^ b * chT Y U b (i - b)) := by
  have e : hh = (hh + MvPowerSeries.C pp * Y) + MvPowerSeries.C pp * (-Y) := by ring
  conv_lhs => rw [e, add_pow, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  obtain ⟨a, rfl⟩ : ∃ a, i = b + a := ⟨i - b, by simp only [mem_range] at hb; omega⟩
  have key : (MvPowerSeries.C ((pp ^ (b + a))⁻¹) : MvPowerSeries ι K) * MvPowerSeries.C pp ^ a =
      MvPowerSeries.C ((pp ^ b)⁻¹) := by
    rw [← map_pow, ← map_mul]
    congr 1
    field_simp
    ring
  rw [Nat.add_sub_cancel_left, chT, mul_pow, map_natCast, ← key]
  ring

/- English proof (translation)
Introduce `K ι _ _ pp hpp _ hh Y F h0 hY0 hY hF`. Establish `h0' : MvPowerSeries.constantCoeff (hh + MvPowerSeries.C pp * Y) = 0`. Rewrite using `[map_add, map_mul, h0, hY0, mul_zero, add_zero]`. Rewrite `hF` using `[inClass_iff h0]`. Rewrite using `[inClass_iff h0']`.

Take `⟨U, hU, h⟩` from `hF`. Use `⟨chU Y U, integral_chU hY hU, fun M => ?_⟩` and prove the remaining obligations. Establish `e : clSum pp hh U M = ∑ b ∈ range M, MvPowerSeries.C ((pp ^ b)⁻¹) * ((hh + MvPowerSeries.C pp * Y) ^ b * ∑ a ∈ range (M - b), chT Y U b a)`. Unfold `clSum`. Rewrite using `[Finset.sum_congr rfl fun i _ => term_change hpp hh Y U i]`.

Rewrite using `[sum_triangle (fun b a => MvPowerSeries.C ((pp ^ b)⁻¹) * ((hh + MvPowerSeries.C pp * Y) ^ b * chT Y U b a)) M]`. Conclude with `Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum, Finset.mul_sum]`. Establish `e2 : F - clSum pp (hh + MvPowerSeries.C pp * Y) (chU Y U) M = (F - clSum pp hh U M) + ∑ b ∈ range M, MvPowerSeries.C ((pp ^ b)⁻¹) * ((hh + MvPowerSeries.C pp * Y) ^ b * (∑ a ∈ range (M - b), chT Y U b a - chU Y U b))`. Rewrite using `[e]`. Unfold `clSum`.

Simplify using `only [mul_sub, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Use `low_add (h M) (low_sum _ _ _ fun b hb => ?_)` and prove the remaining obligations. Establish `hb' : b < M` using `mem_range.1 hb`.

Use `low_mul (low_zero (MvPowerSeries.C ((pp ^ b)⁻¹) : MvPowerSeries ι K)) (low_mul (low_pow ((low_one_iff _).2 h0') b) (low_chU hY0 U b (M - b)))` as an intermediate fact. Conclude with `low_mono (by omega) this`.
-/
theorem classChange_statement : ClassChange := by
  intro K ι _ _ pp hpp _ hh Y F h0 hY0 hY hF
  have h0' : MvPowerSeries.constantCoeff (hh + MvPowerSeries.C pp * Y) = 0 := by
    rw [map_add, map_mul, h0, hY0, mul_zero, add_zero]
  rw [inClass_iff h0] at hF
  rw [inClass_iff h0']
  obtain ⟨U, hU, h⟩ := hF
  refine ⟨chU Y U, integral_chU hY hU, fun M => ?_⟩
  have e : clSum pp hh U M = ∑ b ∈ range M, MvPowerSeries.C ((pp ^ b)⁻¹) *
      ((hh + MvPowerSeries.C pp * Y) ^ b * ∑ a ∈ range (M - b), chT Y U b a) := by
    unfold clSum
    rw [Finset.sum_congr rfl fun i _ => term_change hpp hh Y U i]
    rw [sum_triangle (fun b a => MvPowerSeries.C ((pp ^ b)⁻¹) *
        ((hh + MvPowerSeries.C pp * Y) ^ b * chT Y U b a)) M]
    exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum, Finset.mul_sum]
  have e2 : F - clSum pp (hh + MvPowerSeries.C pp * Y) (chU Y U) M =
      (F - clSum pp hh U M) + ∑ b ∈ range M, MvPowerSeries.C ((pp ^ b)⁻¹) *
        ((hh + MvPowerSeries.C pp * Y) ^ b * (∑ a ∈ range (M - b), chT Y U b a - chU Y U b)) := by
    rw [e]
    unfold clSum
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [e2]
  refine low_add (h M) (low_sum _ _ _ fun b hb => ?_)
  have hb' : b < M := mem_range.1 hb
  have := low_mul (low_zero (MvPowerSeries.C ((pp ^ b)⁻¹) : MvPowerSeries ι K))
    (low_mul (low_pow ((low_one_iff _).2 h0') b) (low_chU hY0 U b (M - b)))
  exact low_mono (by omega) this

def expSum {K ι : Type} [Field K] (f : MvPowerSeries ι K) (M : ℕ) : MvPowerSeries ι K :=
  ∑ k ∈ range M, MvPowerSeries.C ((k.factorial : K)⁻¹) * f ^ k

/- English proof (translation)
Introduce `d hd`. Rewrite using `[map_sub, coeff_mvExp hf, expSum, map_sum, sub_eq_zero]`. Simplify using `only [MvPowerSeries.coeff_C_mul]`. Use `Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun k _ hk => ?_` and prove the remaining obligations. Rewrite using `[low_pow ((low_one_iff _).2 hf) k d (by simp only [mem_range] at hk; omega), mul_zero]`.
-/
theorem low_mvExp_sub {K ι : Type} [NormedField K] [CharZero K] {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) (M : ℕ) : Low M (mvExp f - expSum f M) := by
  intro d hd
  rw [map_sub, coeff_mvExp hf, expSum, map_sum, sub_eq_zero]
  simp only [MvPowerSeries.coeff_C_mul]
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun k _ hk => ?_
  rw [low_pow ((low_one_iff _).2 hf) k d (by simp only [mem_range] at hk; omega), mul_zero]

/- English proof (translation)
Use extensionality with `d`. Use `h (d.degree + 1) d (by omega)` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem eq_of_low {K ι : Type} [Field K] {f g : MvPowerSeries ι K} (h : ∀ M, Low M (f - g)) :
    f = g := by
  ext d
  have := h (d.degree + 1) d (by omega)
  rwa [map_sub, sub_eq_zero] at this

/- English proof (translation)
Rewrite using `[add_pow, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Take `⟨l, rfl⟩ : ∃ l, i = k + l` from `⟨i - k, by simp only [mem_range] at hk; omega⟩`. Establish `key : (MvPowerSeries.C (((k + l).factorial : K)⁻¹) : MvPowerSeries ι K) * (((k + l).choose k : ℕ) : MvPowerSeries ι K) = MvPowerSeries.C ((k.factorial : K)⁻¹) * MvPowerSeries.C ((l.factorial : K)⁻¹)`. Rewrite using `[← map_natCast (MvPowerSeries.C : K →+* MvPowerSeries ι K), ← map_mul, ← map_mul]`.

Use `congr 1`. Establish `h1` using `Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k l)`. Rewrite `h1` using `[Nat.add_sub_cancel_left]`. Establish `h2 : (((k + l).choose k : ℕ) : K) * (k.factorial : K) * (l.factorial : K) = ((k + l).factorial : K)` using `by exact_mod_cast h1`. Establish `hc : (((k + l).choose k : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.2 (Nat.choose_pos (Nat.le_add_right k l)).ne'`.

Establish `hk0 : (k.factorial : K) ≠ 0` using `Nat.cast_ne_zero.2 k.factorial_ne_zero`. Establish `hl0 : (l.factorial : K) ≠ 0` using `Nat.cast_ne_zero.2 l.factorial_ne_zero`. Rewrite using `[← h2]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Nat.add_sub_cancel_left]`.

Take the linear combination `(a ^ k * b ^ l) * key`.
-/
theorem exp_term {K ι : Type} [Field K] [CharZero K] (a b : MvPowerSeries ι K) (i : ℕ) :
    MvPowerSeries.C ((i.factorial : K)⁻¹) * (a + b) ^ i =
      ∑ k ∈ range (i + 1), (MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k) *
        (MvPowerSeries.C (((i - k).factorial : K)⁻¹) * b ^ (i - k)) := by
  rw [add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨l, rfl⟩ : ∃ l, i = k + l := ⟨i - k, by simp only [mem_range] at hk; omega⟩
  have key : (MvPowerSeries.C (((k + l).factorial : K)⁻¹) : MvPowerSeries ι K) *
      (((k + l).choose k : ℕ) : MvPowerSeries ι K) =
      MvPowerSeries.C ((k.factorial : K)⁻¹) * MvPowerSeries.C ((l.factorial : K)⁻¹) := by
    rw [← map_natCast (MvPowerSeries.C : K →+* MvPowerSeries ι K), ← map_mul, ← map_mul]
    congr 1
    have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k l)
    rw [Nat.add_sub_cancel_left] at h1
    have h2 : (((k + l).choose k : ℕ) : K) * (k.factorial : K) * (l.factorial : K) =
        ((k + l).factorial : K) := by exact_mod_cast h1
    have hc : (((k + l).choose k : ℕ) : K) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.choose_pos (Nat.le_add_right k l)).ne'
    have hk0 : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
    have hl0 : (l.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 l.factorial_ne_zero
    rw [← h2]
    field_simp
  rw [Nat.add_sub_cancel_left]
  linear_combination (a ^ k * b ^ l) * key

/- English proof (translation)
Establish `hab : MvPowerSeries.constantCoeff (a + b) = 0` using `by rw [map_add, ha, hb, add_zero]`. Establish `la` using `(low_one_iff _).2 ha`. Establish `lb` using `(low_one_iff _).2 hb`. Use `eq_of_low fun M => ?_` and prove the remaining obligations. Establish `h3 : Low M (expSum a M * expSum b M - expSum (a + b) M)`.

Establish `e : expSum (a + b) M = ∑ k ∈ range M, ∑ l ∈ range (M - k), (MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k) * (MvPowerSeries.C ((l.factorial : K)⁻¹) * b ^ l)`. Unfold `expSum`. Rewrite using `[Finset.sum_congr rfl fun i _ => exp_term a b i]`. Conclude with `sum_triangle (fun k l => (MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k) * (MvPowerSeries.C ((l.factorial : K)⁻¹) * b ^ l)) M`. Rewrite using `[e]`.

Unfold `expSum`. Rewrite using `[Finset.sum_mul, ← Finset.sum_sub_distrib]`. Use `low_sum _ _ _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Introduce `d hd`.

Rewrite using `[map_sub, map_sum, map_sum, sub_eq_zero]`. Use `symm`. Use `Finset.sum_subset (Finset.range_subset_range.2 (Nat.sub_le _ _)) fun l _ hl => ?_` and prove the remaining obligations. Establish `hkl : Low (k + l) ((MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k) * (MvPowerSeries.C ((l.factorial : K)⁻¹) * b ^ l))`. Simplify using `using low_mul (low_mul (low_zero (MvPowerSeries.C ((k.factorial : K)⁻¹))) (low_pow la k)) (low_mul (low_zero (MvPowerSeries.C ((l.factorial : K)⁻¹))) (low_pow lb l))`.

Conclude with `hkl d (by simp only [mem_range] at hl; omega)`. Establish `e : mvExp (a + b) - mvExp a * mvExp b = (mvExp (a + b) - expSum (a + b) M) - ((mvExp a - expSum a M) * mvExp b + expSum a M * (mvExp b - expSum b M) + (expSum a M * expSum b M - expSum (a + b) M))` using `by ring`. Rewrite using `[e]`. Use `low_sub (low_mvExp_sub hab M) (low_add (low_add ?_ ?_) h3)` and prove the remaining obligations. Simplify using `using low_mul (low_mvExp_sub ha M) (low_zero (mvExp b))`.

Simplify using `using low_mul (low_zero (expSum a M)) (low_mvExp_sub hb M)`.
-/
theorem mvExp_add {K ι : Type} [NormedField K] [CharZero K] {a b : MvPowerSeries ι K}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    mvExp (a + b) = mvExp a * mvExp b := by
  have hab : MvPowerSeries.constantCoeff (a + b) = 0 := by rw [map_add, ha, hb, add_zero]
  have la := (low_one_iff _).2 ha
  have lb := (low_one_iff _).2 hb
  refine eq_of_low fun M => ?_
  have h3 : Low M (expSum a M * expSum b M - expSum (a + b) M) := by
    have e : expSum (a + b) M = ∑ k ∈ range M, ∑ l ∈ range (M - k),
        (MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k) *
          (MvPowerSeries.C ((l.factorial : K)⁻¹) * b ^ l) := by
      unfold expSum
      rw [Finset.sum_congr rfl fun i _ => exp_term a b i]
      exact sum_triangle (fun k l => (MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k) *
          (MvPowerSeries.C ((l.factorial : K)⁻¹) * b ^ l)) M
    rw [e]
    unfold expSum
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine low_sum _ _ _ fun k _ => ?_
    rw [Finset.mul_sum]
    intro d hd
    rw [map_sub, map_sum, map_sum, sub_eq_zero]
    symm
    refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.sub_le _ _)) fun l _ hl => ?_
    have hkl : Low (k + l) ((MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k) *
          (MvPowerSeries.C ((l.factorial : K)⁻¹) * b ^ l)) := by
      simpa using low_mul (low_mul (low_zero (MvPowerSeries.C ((k.factorial : K)⁻¹))) (low_pow la k))
        (low_mul (low_zero (MvPowerSeries.C ((l.factorial : K)⁻¹))) (low_pow lb l))
    exact hkl d (by simp only [mem_range] at hl; omega)
  have e : mvExp (a + b) - mvExp a * mvExp b = (mvExp (a + b) - expSum (a + b) M) -
      ((mvExp a - expSum a M) * mvExp b + expSum a M * (mvExp b - expSum b M) +
        (expSum a M * expSum b M - expSum (a + b) M)) := by ring
  rw [e]
  refine low_sub (low_mvExp_sub hab M) (low_add (low_add ?_ ?_) h3)
  · simpa using low_mul (low_mvExp_sub ha M) (low_zero (mvExp b))
  · simpa using low_mul (low_zero (expSum a M)) (low_mvExp_sub hb M)

def leadT (K : Type) [Field K] (p : ℕ) (x y : Fin 2) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.C ((p : K)⁻¹) * (MvPowerSeries.X x * MvPowerSeries.X y ^ p)

/- English proof (translation)
Rewrite using `[leadT, MvPowerSeries.X_pow_eq, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, ← MvPowerSeries.monomial_zero_eq_C_apply, MvPowerSeries.monomial_mul_monomial]`. Simplify using the standard rewrite rules.
-/
theorem leadT_eq (K : Type) [Field K] (p : ℕ) (x y : Fin 2) :
    leadT K p x y =
      MvPowerSeries.monomial (Finsupp.single x 1 + Finsupp.single y p) ((p : K)⁻¹) := by
  rw [leadT, MvPowerSeries.X_pow_eq, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial,
    ← MvPowerSeries.monomial_zero_eq_C_apply, MvPowerSeries.monomial_mul_monomial]
  simp

/- English proof (translation)
Establish `h : ∀ x y : Fin 2, x ≠ y → (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)` using `by decide`. Rewrite using `[Finsupp.degree_eq_sum, Fin.sum_univ_two]`. Break down `h x y hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases. Both sides reduce to the same expression. Conclude with `add_comm _ _`.
-/
theorem degree_fin_two_eq_add_of_ne {x y : Fin 2} (hxy : x ≠ y) (d : Fin 2 →₀ ℕ) : d.degree = d x + d y := by
  have h : ∀ x y : Fin 2, x ≠ y → (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by decide
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  rcases h x y hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact add_comm _ _

/- English proof (translation)
Establish `hp2` using `hp.two_le`. Establish `hp' : (2 : ℝ) ≤ p` using `by exact_mod_cast hp2`. Establish `hpos : (0 : ℝ) < (p : ℝ)⁻¹` using `by positivity`. Establish `hle : (p : ℝ)⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ (by linarith)`. Rewrite using `[map_sub, leadT_eq, MvPowerSeries.coeff_monomial]`.

Distinguish the cases in `hd : d = Finsupp.single x 1 + Finsupp.single y p`. Establish `hx : d x = (p ^ 2) ^ 0` using `by rw [hd]; simp [hxy.symm]`. Establish `hy : d y = p * (p ^ 2) ^ 0` using `by rw [hd]; simp [hxy]`. Rewrite using `[if_pos hd, coeff_AA_of K hp2 le_rfl hx hy]`. Simplify using `only [add_zero, zero_add, pow_one, sub_self, norm_zero]`.

Check the signs of the components of the expression. Rewrite using `[if_neg hd, sub_zero]`. Distinguish the cases in `h : MvPowerSeries.coeff d (AA K p x y) = 0`. Rewrite using `[h, norm_zero]`. Check the signs of the components of the expression.

Take `⟨i, j, hij, hx, hy⟩` from `coeff_AA_ne_zero h`. Establish `hj : 1 ≤ j`. Assume the negation of the conclusion as `hj`. Take `rfl : j = 0` from `by omega`. Take `rfl : i = 0` from `by omega`.

Apply `hd` to reduce the goal to its premises. Use extensionality with `z`. Break down `finset_fin_two_eq_cases x y hxy z with rfl | rfl` into its components or cases. Simplify using `[hx, hxy.symm]`. Simplify using `[hy, hxy]`.

Rewrite using `[coeff_AA_of K hp2 hij hx hy, norm_inv, norm_pow, hn, ← Real.rpow_natCast, ← Real.rpow_neg hpos.le]`. Use `Real.rpow_le_rpow_of_exponent_ge hpos hle ?_` and prove the remaining obligations. Establish `h1` using `(hT p i j hp2 hij).2 hj`. Establish `e` using `div_eq_mul_one_div (((p : ℝ) ^ 2) ^ i + p * ((p : ℝ) ^ 2) ^ j) ((p : ℝ) ^ 2 - 1)`. Rewrite using `[degree_fin_two_eq_add_of_ne hxy, hx, hy]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem wt_AA (hT : ValTable) {K : Type} [NormedField K] {p : ℕ} (hp : p.Prime)
    (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) {x y : Fin 2} (hxy : x ≠ y) (d : Fin 2 →₀ ℕ) :
    ‖MvPowerSeries.coeff d (AA K p x y - leadT K p x y)‖ ≤
      ((p : ℝ)⁻¹) ^ (1 / ((p : ℝ) - 1) - (d.degree : ℝ) * (1 / ((p : ℝ) ^ 2 - 1))) := by
  classical
  have hp2 := hp.two_le
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  have hle : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  rw [map_sub, leadT_eq, MvPowerSeries.coeff_monomial]
  by_cases hd : d = Finsupp.single x 1 + Finsupp.single y p
  · have hx : d x = (p ^ 2) ^ 0 := by rw [hd]; simp [hxy.symm]
    have hy : d y = p * (p ^ 2) ^ 0 := by rw [hd]; simp [hxy]
    rw [if_pos hd, coeff_AA_of K hp2 le_rfl hx hy]
    simp only [add_zero, zero_add, pow_one, sub_self, norm_zero]
    positivity
  · rw [if_neg hd, sub_zero]
    by_cases h : MvPowerSeries.coeff d (AA K p x y) = 0
    · rw [h, norm_zero]; positivity
    · obtain ⟨i, j, hij, hx, hy⟩ := coeff_AA_ne_zero h
      have hj : 1 ≤ j := by
        by_contra hj
        obtain rfl : j = 0 := by omega
        obtain rfl : i = 0 := by omega
        apply hd
        ext z
        rcases finset_fin_two_eq_cases x y hxy z with rfl | rfl
        · simp [hx, hxy.symm]
        · simp [hy, hxy]
      rw [coeff_AA_of K hp2 hij hx hy, norm_inv, norm_pow, hn, ← Real.rpow_natCast,
        ← Real.rpow_neg hpos.le]
      refine Real.rpow_le_rpow_of_exponent_ge hpos hle ?_
      have h1 := (hT p i j hp2 hij).2 hj
      have e := div_eq_mul_one_div (((p : ℝ) ^ 2) ^ i + p * ((p : ℝ) ^ 2) ^ j) ((p : ℝ) ^ 2 - 1)
      rw [degree_fin_two_eq_add_of_ne hxy, hx, hy]
      push_cast
      linarith

def G1 {K : Type} [Field K] (p : ℕ) (c c' : K) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.C c * (AA K p 0 1 - leadT K p 0 1) -
    MvPowerSeries.C c' * (AA K p 1 0 - leadT K p 1 0)

/- English proof (translation)
Introduce `d`. Unfold `MonoWtGe`. Rewrite using `[dot_const, G1, map_sub, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]`. Rewrite using `[sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) hc).trans (wt_AA hT hp hn (by decide) d)`. Rewrite using `[norm_neg, norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) hc').trans (wt_AA hT hp hn (by decide) d)`.
-/
theorem weight_ge_g_one (hT : ValTable) {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ}
    (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) {c c' : K} (hc : ‖c‖ ≤ 1) (hc' : ‖c'‖ ≤ 1) :
    WtGe ((p : ℝ)⁻¹) (fun _ : Fin 2 => 1 / ((p : ℝ) ^ 2 - 1)) (1 / ((p : ℝ) - 1))
      (G1 p c c') := by
  intro d
  unfold MonoWtGe
  rw [dot_const, G1, map_sub, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (wt_AA hT hp hn (by decide) d)
  · rw [norm_neg, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc').trans (wt_AA hT hp hn (by decide) d)

/- English proof (translation)
Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Assume the negation of the conclusion as `h`. Take `⟨i, j, _, hx, _⟩` from `coeff_AA_ne_zero h`. Establish `: 0 < (p ^ 2) ^ i` using `by positivity`. Simplify using `only [Finsupp.coe_zero, Pi.zero_apply] at hx`.

Use linear arithmetic over natural numbers and integers.
-/
theorem constantCoeff_AA (K : Type) [Field K] {p : ℕ} (hp : p ≠ 0) (x y : Fin 2) :
    MvPowerSeries.constantCoeff (AA K p x y) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  by_contra h
  obtain ⟨i, j, _, hx, _⟩ := coeff_AA_ne_zero h
  have : 0 < (p ^ 2) ^ i := by positivity
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hx
  omega

/- English proof (translation)
Simplify using `[G1, leadT, constantCoeff_AA K hp]`.
-/
theorem constant_coeff_g_one {K : Type} [Field K] {p : ℕ} (hp : p ≠ 0) (c c' : K) :
    MvPowerSeries.constantCoeff (G1 p c c') = 0 := by
  simp [G1, leadT, constantCoeff_AA K hp]

/- English proof (translation)
Rewrite using `[leadT, ← MvPowerSeries.coe_substAlgHom hs, map_mul, map_mul, map_pow, MvPowerSeries.substAlgHom_X, MvPowerSeries.substAlgHom_X]`. Use `congr 1`. Conclude with `(MvPowerSeries.substAlgHom hs).commutes _`.
-/
theorem subst_leadT {K τ : Type} [Field K] (p : ℕ) (x y : Fin 2) {a : Fin 2 → MvPowerSeries τ K}
    (hs : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (leadT K p x y) = MvPowerSeries.C ((p : K)⁻¹) * (a x * a y ^ p) := by
  rw [leadT, ← MvPowerSeries.coe_substAlgHom hs, map_mul, map_mul, map_pow,
    MvPowerSeries.substAlgHom_X, MvPowerSeries.substAlgHom_X]
  congr 1
  exact (MvPowerSeries.substAlgHom hs).commutes _

/- English proof (translation)
Establish `e : Gser p c c' = G1 p c c' + (MvPowerSeries.C c * leadT K p 0 1 - MvPowerSeries.C c' * leadT K p 1 0)`. Rewrite using `[Gser, G1, Aser_eq, Aser'_eq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hC : ∀ r : K, MvPowerSeries.substAlgHom hs (MvPowerSeries.C r) = MvPowerSeries.C r` using `fun r => (MvPowerSeries.substAlgHom hs).commutes r`. Establish `h1` using `subst_leadT p 0 1 hs`.

Establish `h2` using `subst_leadT p 1 0 hs`. Rewrite `h1`, `h2`, the goal using `[← MvPowerSeries.coe_substAlgHom hs]`. Rewrite using `[e, map_add, map_sub, map_mul, map_mul, hC, hC, h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem subst_g_series_eq {K τ : Type} [Field K] (p : ℕ) (c c' : K) {a : Fin 2 → MvPowerSeries τ K}
    (hs : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (Gser p c c') = MvPowerSeries.subst a (G1 p c c') +
      MvPowerSeries.C ((p : K)⁻¹) * (MvPowerSeries.C c * (a 0 * a 1 ^ p) -
        MvPowerSeries.C c' * (a 1 * a 0 ^ p)) := by
  have e : Gser p c c' = G1 p c c' +
      (MvPowerSeries.C c * leadT K p 0 1 - MvPowerSeries.C c' * leadT K p 1 0) := by
    rw [Gser, G1, Aser_eq, Aser'_eq]
    ring
  have hC : ∀ r : K, MvPowerSeries.substAlgHom hs (MvPowerSeries.C r) = MvPowerSeries.C r :=
    fun r => (MvPowerSeries.substAlgHom hs).commutes r
  have h1 := subst_leadT p 0 1 hs
  have h2 := subst_leadT p 1 0 hs
  rw [← MvPowerSeries.coe_substAlgHom hs] at h1 h2 ⊢
  rw [e, map_add, map_sub, map_mul, map_mul, hC, hC, h1, h2]
  ring

/- English proof (translation)
Simplify using `[hh1, map_sum, zero_pow hp]`.
-/
theorem constant_coeff_hh_zero {K E : Type} [Field K] [Fintype E] {p : ℕ} (hp : p ≠ 0) (c c' : K) :
    MvPowerSeries.constantCoeff (hh1 (E := E) p c c') = 0 := by
  simp [hh1, map_sum, zero_pow hp]

/- English proof (translation)
Establish `hp2` using `hp.two_le`. Establish `h1 : ‖ϖ‖ ^ (p ^ 2 - 1) = (p : ℝ)⁻¹` using `by rw [← norm_pow, hϖ, hn]`. Establish `hsq : 4 ≤ p ^ 2` using `by nlinarith`. Establish `hN : p ^ 2 - 1 ≠ 0` using `by omega`. Establish `h2` using `Real.pow_rpow_inv_natCast (norm_nonneg ϖ) hN`.

Establish `hcast : ((p ^ 2 - 1 : ℕ) : ℝ) = (p : ℝ) ^ 2 - 1`. Rewrite using `[Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[h1, hcast]`.

Rewrite using `[one_div, h2]`.
-/
theorem norm_unif {K : Type} [NormedField K] {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {ϖ : K} (hϖ : ϖ ^ (p ^ 2 - 1) = (p : K)) :
    ‖ϖ‖ = ((p : ℝ)⁻¹) ^ (1 / ((p : ℝ) ^ 2 - 1)) := by
  have hp2 := hp.two_le
  have h1 : ‖ϖ‖ ^ (p ^ 2 - 1) = (p : ℝ)⁻¹ := by rw [← norm_pow, hϖ, hn]
  have hsq : 4 ≤ p ^ 2 := by nlinarith
  have hN : p ^ 2 - 1 ≠ 0 := by omega
  have h2 := Real.pow_rpow_inv_natCast (norm_nonneg ϖ) hN
  have hcast : ((p ^ 2 - 1 : ℕ) : ℝ) = (p : ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [h1, hcast] at h2
  rw [one_div, h2]

/- English proof (translation)
Introduce `K E _ _ _ _ p c c' ϖ hp hn hϖ hc hc'`. Establish `hp' : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Establish `hpos : (0 : ℝ) < (p : ℝ)⁻¹` using `by positivity`. Establish `hlt : (p : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by linarith)`. Set `a : E → Fin 2 → MvPowerSeries (Bool × E) K` to `fun e z => MvPowerSeries.C ϖ * (MvPowerSeries.X (if z = 0 then (false, e) else (true, e)) : MvPowerSeries (Bool × E) K)`.

Establish `ha0 : ∀ e z, MvPowerSeries.constantCoeff (a e z) = 0` using `fun e z => by simp [a]`. Establish `hs : ∀ e, MvPowerSeries.HasSubst (a e)` using `fun e => MvPowerSeries.hasSubst_of_constantCoeff_zero (ha0 e)`. Establish `hG : Gtot (E` using `E) p c c' ϖ = MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hh1 (E := E) p c c' + ∑ e : E, MvPowerSeries.subst (a e) (G1 p c c') := by`. Unfold `Gtot hh1`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Use `(subst_g_series_eq p c c' (hs e)).trans ?_` and prove the remaining obligations. Establish `e1 : (MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) : MvPowerSeries (Bool × E) K) = MvPowerSeries.C ((p : K)⁻¹) * MvPowerSeries.C ϖ ^ (p + 1)`. Rewrite using `[← map_pow, ← map_mul, div_eq_inv_mul]`. Rewrite using `[e1]`.

Simplify using `only [a, if_true, Fin.isValue, one_ne_zero, if_false]`. Expand and normalize the polynomial expressions, which then agree. Establish `hR0 : MvPowerSeries.constantCoeff (∑ e : E, MvPowerSeries.subst (a e) (G1 p c c')) = 0`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun e _ => (low_one_iff _).1 (low_subst_of_low (ha0 e) ((low_one_iff _).2 (constant_coeff_g_one hp.ne_zero c c')))`.

Establish `hwa : ∀ e z, WtGe ((p : ℝ)⁻¹) (fun _ : Bool × E => (0 : ℝ)) (1 / ((p : ℝ) ^ 2 - 1)) (a e z)`. Introduce `e z m`. Unfold `MonoWtGe`. Rewrite using `[dot_const, mul_zero, sub_zero, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]`. Apply the tactic sequence `split_ifs <;> first`.

Consider the case `rw [mul_one, norm_unif hp hn hϖ]`. Consider the case `(rw [mul_zero, norm_zero]; positivity)`. Establish `hRn : ∀ n, ‖MvPowerSeries.coeff n (∑ e : E, MvPowerSeries.subst (a e) (G1 p c c'))‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))`. Introduce `n`. Rewrite using `[map_sum]`.

Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun e _ => ?_` and prove the remaining obligations. Establish `h` using `substitution_weight_bound K ((p : ℝ)⁻¹) hpos hlt (Fin 2) (Bool × E) (a e) (fun _ => 1 / ((p : ℝ) ^ 2 - 1)) (fun _ => 0) (1 / ((p : ℝ) - 1)) (G1 p c c') (ha0 e) (hwa e) (weight_ge_g_one hT hp hn hc hc') n`. Unfold `MonoWtGe at h`. Rewrite `h` using `[dot_const, mul_zero, sub_zero, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]`. Conclude with `h`.

Use `⟨mvExp (-(∑ e : E, MvPowerSeries.subst (a e) (G1 p c c'))), hE K _ p hp hn _ (by rw [map_neg, hR0, neg_zero]) (fun n => by rw [map_neg, norm_neg]; exact hRn n), ?_⟩` and prove the remaining obligations. Rewrite using `[hG, neg_add, mvExp_add (by rw [map_neg, map_mul, constant_coeff_hh_zero hp.ne_zero, mul_zero, neg_zero]) (by rw [map_neg, hR0, neg_zero])]`.
-/
theorem RescaleExact_of (hT : ValTable) (hE : ExpIntegral) : RescaleExact := by
  intro K E _ _ _ _ p c c' ϖ hp hn hϖ hc hc'
  classical
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  have hlt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  let a : E → Fin 2 → MvPowerSeries (Bool × E) K := fun e z => MvPowerSeries.C ϖ *
      (MvPowerSeries.X (if z = 0 then (false, e) else (true, e)) : MvPowerSeries (Bool × E) K)
  have ha0 : ∀ e z, MvPowerSeries.constantCoeff (a e z) = 0 := fun e z => by simp [a]
  have hs : ∀ e, MvPowerSeries.HasSubst (a e) := fun e =>
    MvPowerSeries.hasSubst_of_constantCoeff_zero (ha0 e)
  have hG : Gtot (E := E) p c c' ϖ =
      MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hh1 (E := E) p c c' +
        ∑ e : E, MvPowerSeries.subst (a e) (G1 p c c') := by
    unfold Gtot hh1
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    refine (subst_g_series_eq p c c' (hs e)).trans ?_
    have e1 : (MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) : MvPowerSeries (Bool × E) K) =
        MvPowerSeries.C ((p : K)⁻¹) * MvPowerSeries.C ϖ ^ (p + 1) := by
      rw [← map_pow, ← map_mul, div_eq_inv_mul]
    rw [e1]
    simp only [a, if_true, Fin.isValue, one_ne_zero, if_false]
    ring
  have hR0 : MvPowerSeries.constantCoeff (∑ e : E, MvPowerSeries.subst (a e) (G1 p c c')) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun e _ => (low_one_iff _).1
      (low_subst_of_low (ha0 e) ((low_one_iff _).2 (constant_coeff_g_one hp.ne_zero c c')))
  have hwa : ∀ e z, WtGe ((p : ℝ)⁻¹) (fun _ : Bool × E => (0 : ℝ)) (1 / ((p : ℝ) ^ 2 - 1))
      (a e z) := by
    intro e z m
    unfold MonoWtGe
    rw [dot_const, mul_zero, sub_zero, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
    split_ifs <;>
      first
        | rw [mul_one, norm_unif hp hn hϖ]
        | (rw [mul_zero, norm_zero]; positivity)
  have hRn : ∀ n, ‖MvPowerSeries.coeff n (∑ e : E, MvPowerSeries.subst (a e) (G1 p c c'))‖ ≤
      (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
    intro n
    rw [map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun e _ => ?_
    have h := substitution_weight_bound K ((p : ℝ)⁻¹) hpos hlt (Fin 2) (Bool × E) (a e)
      (fun _ => 1 / ((p : ℝ) ^ 2 - 1)) (fun _ => 0) (1 / ((p : ℝ) - 1)) (G1 p c c') (ha0 e)
      (hwa e) (weight_ge_g_one hT hp hn hc hc') n
    unfold MonoWtGe at h
    rw [dot_const, mul_zero, sub_zero, Real.inv_rpow (by positivity), ← Real.rpow_neg
      (by positivity)] at h
    exact h
  refine ⟨mvExp (-(∑ e : E, MvPowerSeries.subst (a e) (G1 p c c'))),
    hE K _ p hp hn _ (by rw [map_neg, hR0, neg_zero])
      (fun n => by rw [map_neg, norm_neg]; exact hRn n), ?_⟩
  rw [hG, neg_add, mvExp_add (by rw [map_neg, map_mul, constant_coeff_hh_zero hp.ne_zero, mul_zero,
    neg_zero]) (by rw [map_neg, hR0, neg_zero])]

/- English proof (translation)
Introduce `K E _ _ _ _ p c c' ϖ hp hn hϖ hc hc'`. Take `⟨V, hV, e⟩` from `hR K E p c c' ϖ hp hn hϖ hc hc'`. Establish `h0` using `constant_coeff_hh_zero (E := E) hp.ne_zero c c'`. Rewrite using `[e]`. Conclude with `hM K _ (p : K) _ _ V h0 hV (hC K _ p ϖ hp hn hϖ _ h0)`.
-/
theorem RescaleCore_of (hR : RescaleExact) (hC : ClassExp) (hM : ClassMul) : RescaleCore := by
  intro K E _ _ _ _ p c c' ϖ hp hn hϖ hc hc'
  obtain ⟨V, hV, e⟩ := hR K E p c c' ϖ hp hn hϖ hc hc'
  have h0 := constant_coeff_hh_zero (E := E) hp.ne_zero c c'
  rw [e]
  exact hM K _ (p : K) _ _ V h0 hV (hC K _ p ϖ hp hn hϖ _ h0)

end Formalism.InvariantFactorPaths.G7
