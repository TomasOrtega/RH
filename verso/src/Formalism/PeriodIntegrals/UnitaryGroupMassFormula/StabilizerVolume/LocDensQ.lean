import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensSt

noncomputable section

namespace PI.VolStabS

open NumberField IsDedekindDomain Filter Asymptotics
open scoped nonZeroDivisors

namespace LocalCountingSum

variable (K : Type) [Field K] [NumberField K]

def cnt (n : ℕ) : ℝ := (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `hE : IsEmpty {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ 0}`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨I, hI⟩`.

Establish `h0 : Ideal.absNorm (I : Ideal (𝓞 K)) = 0` using `Nat.le_zero.1 hI`. Rewrite `h0` using `[Ideal.absNorm_eq_zero_iff]`. Conclude with `(mem_nonZeroDivisors_iff_ne_zero.1 I.2) (by rw [h0]; rfl)`. Rewrite using `[Nat.card_of_isEmpty]`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Rewrite using `[Finset.sum_Icc_succ_top (by omega), ih]`. Use `haveI : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} := (Ideal.finite_setOf_absNorm_le₀ (S := 𝓞 K) n).to_subtype`. Use `haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n + 1} := (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) (n + 1)).to_subtype`. Establish `hnz : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n + 1 → I ∈ (Ideal (𝓞 K))⁰`.

Introduce `I hI`. Use `mem_nonZeroDivisors_iff_ne_zero.2 (fun h => ?_)` and prove the remaining obligations. Rewrite `hI` using `[h]`. Simplify using `at hI`. Set `e : {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n + 1} ≃ {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} ⊕ {I : Ideal (𝓞 K) // Ideal.absNorm I = n + 1}` to `{ toFun := fun x => if h : Ideal.absNorm (x.1 : Ideal (𝓞 K)) ≤ n then Sum.inl ⟨x.1, h⟩ else Sum.inr ⟨x.1.1, by have := x.2; omega⟩ invFun := fun y => match y with`.

Consider the case `Sum.inl z => ⟨z.1, Nat.le_succ_of_le z.2⟩`. Consider the case `Sum.inr z => ⟨⟨z.1, hnz z.1 z.2⟩, z.2.le⟩`. Use `left_inv := by`. Introduce `x`. Distinguish the cases in `h : Ideal.absNorm (x.1 : Ideal (𝓞 K)) ≤ n`.

Simplify using `only [dif_pos h]`. Simplify using `only [dif_neg h]`. Use `right_inv := by`. Introduce `y`. Break down `y with z | z` into its components or cases.

Simplify using `only [dif_pos z.2]`. Establish `hz : ¬ Ideal.absNorm z.1 ≤ n` using `by have := z.2; omega`. Simplify using `only [dif_neg hz] }`. Rewrite using `[Nat.card_congr e, Nat.card_sum]`. Unfold `cnt`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_cnt (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, cnt K k =
    (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) := by
  induction n with
  | zero =>
    have hE : IsEmpty {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ 0} := by
      constructor
      rintro ⟨I, hI⟩
      have h0 : Ideal.absNorm (I : Ideal (𝓞 K)) = 0 := Nat.le_zero.1 hI
      rw [Ideal.absNorm_eq_zero_iff] at h0
      exact (mem_nonZeroDivisors_iff_ne_zero.1 I.2) (by rw [h0]; rfl)
    rw [Nat.card_of_isEmpty]
    simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    haveI : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} := (Ideal.finite_setOf_absNorm_le₀ (S := 𝓞 K) n).to_subtype
    haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n + 1} :=
      (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) (n + 1)).to_subtype
    have hnz : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n + 1 → I ∈ (Ideal (𝓞 K))⁰ := by
      intro I hI
      refine mem_nonZeroDivisors_iff_ne_zero.2 (fun h => ?_)
      rw [h] at hI
      simp at hI
    let e : {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n + 1} ≃ {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} ⊕ {I : Ideal (𝓞 K) // Ideal.absNorm I = n + 1} :=
      { toFun := fun x => if h : Ideal.absNorm (x.1 : Ideal (𝓞 K)) ≤ n then Sum.inl ⟨x.1, h⟩
          else Sum.inr ⟨x.1.1, by have := x.2; omega⟩
        invFun := fun y => match y with
          | Sum.inl z => ⟨z.1, Nat.le_succ_of_le z.2⟩
          | Sum.inr z => ⟨⟨z.1, hnz z.1 z.2⟩, z.2.le⟩
        left_inv := by
          intro x
          by_cases h : Ideal.absNorm (x.1 : Ideal (𝓞 K)) ≤ n
          · simp only [dif_pos h]
          · simp only [dif_neg h]
        right_inv := by
          intro y
          rcases y with z | z
          · simp only [dif_pos z.2]
          · have hz : ¬ Ideal.absNorm z.1 ≤ n := by have := z.2; omega
            simp only [dif_neg hz] }
    rw [Nat.card_congr e, Nat.card_sum]
    unfold cnt
    push_cast
    ring

/- English proof (translation)
Establish `h2` using `(NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop`. Establish `hc : ∀ n : ℕ, (Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ (n : ℝ)} : ℝ) = (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ)`. Introduce `n`. Use `congr 1`. Conclude with `Nat.card_congr (Equiv.subtypeEquivRight (fun I => Nat.cast_le))`.

Simplify using `only [Real.rpow_one]`. Take `⟨L, hL⟩ : ∃ L, Tendsto ((fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, cnt K k) / fun n : ℕ => (n : ℝ)) atTop (nhds L)` from `⟨_, h2.congr (fun n => by simp only [Function.comp_apply, Pi.div_apply, hc n, sum_cnt K n])⟩`. Conclude with `Asymptotics.isBigO_of_div_tendsto_nhds (Filter.eventually_atTop.2 ⟨1, fun n hn h0 => absurd h0 (by positivity)⟩) L hL`.
-/
theorem sum_cnt_bigO :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, cnt K k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  have h2 := (NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop
  have hc : ∀ n : ℕ, (Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ (n : ℝ)} : ℝ) =
      (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) := by
    intro n
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun I => Nat.cast_le))
  simp only [Real.rpow_one]
  obtain ⟨L, hL⟩ : ∃ L, Tendsto ((fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, cnt K k) / fun n : ℕ => (n : ℝ))
      atTop (nhds L) :=
    ⟨_, h2.congr (fun n => by simp only [Function.comp_apply, Pi.div_apply, hc n, sum_cnt K n])⟩
  exact Asymptotics.isBigO_of_div_tendsto_nhds
    (Filter.eventually_atTop.2 ⟨1, fun n hn h0 => absurd h0 (by positivity)⟩) L hL

/- English proof (translation)
Establish `h` using `LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := cnt K) (r := 1) (s := 2) (sum_cnt_bigO K) (fun n => by unfold cnt; positivity) zero_le_one (by norm_num)`. Unfold `LSeriesSummable at h`. Establish `e : LSeries.term (fun n => ((cnt K n : ℝ) : ℂ)) 2 = fun n => ((cnt K n / (n : ℝ) ^ 2 : ℝ) : ℂ)`. Use function extensionality and compare the values at `n`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases.

Simplify using `[LSeries.term]`. Rewrite using `[LSeries.term_of_ne_zero hn.ne']`. Use `push_cast`. Use `congr 1`. Conclude with `Complex.cpow_natCast (n : ℂ) 2` after adjusting the coercions.

Rewrite `h` using `[e]`. Conclude with `Complex.summable_ofReal.1 h`.
-/
theorem cnt_summable : Summable fun n : ℕ ↦ cnt K n / (n : ℝ) ^ 2 := by
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := cnt K) (r := 1) (s := 2) (sum_cnt_bigO K)
    (fun n => by unfold cnt; positivity) zero_le_one (by norm_num)
  unfold LSeriesSummable at h
  have e : LSeries.term (fun n => ((cnt K n : ℝ) : ℂ)) 2 = fun n => ((cnt K n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn.ne']
      push_cast
      congr 1
      exact_mod_cast Complex.cpow_natCast (n : ℂ) 2
  rw [e] at h
  exact Complex.summable_ofReal.1 h

end LocalCountingSum

/- English proof (translation)
Unfold `qV`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
theorem qV_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    qV v = (Ideal.absNorm v.asIdeal : ℝ) := by
  unfold qV
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

/- English proof (translation)
Introduce `F _ _`. Use `haveI hfin : ∀ n : ℕ, Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} := fun n => (Ideal.finite_setOf_absNorm_eq (S := 𝓞 F) n).to_subtype`. Set `f : Ideal (𝓞 F) → ℝ` to `fun I => ((Ideal.absNorm I : ℝ))⁻¹ ^ 2`. Establish `hf0 : ∀ I, 0 ≤ f I` using `fun I => by positivity`. Establish `hsig : Summable (fun x : Σ n : ℕ, {I : Ideal (𝓞 F) // Ideal.absNorm I = n} => f x.2.1)`.

Rewrite using `[summable_sigma_of_nonneg (fun x => hf0 _)]`. Use `⟨fun n => Summable.of_finite, ?_⟩` and prove the remaining obligations. Establish `e2 : (fun n : ℕ => ∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}, f I.1) = fun n => LocalCountingSum.cnt F n / (n : ℝ) ^ 2`. Use function extensionality and compare the values at `n`. Establish `hc : ∀ I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}, f I.1 = ((n : ℝ))⁻¹ ^ 2`.

Introduce `I`. Simplify using `only [f, I.2]`. Rewrite using `[tsum_congr hc, tsum_const, nsmul_eq_mul]`. Unfold `LocalCountingSum.cnt`. Rewrite using `[inv_pow, div_eq_mul_inv]`.

Rewrite using `[e2]`. Conclude with `LocalCountingSum.cnt_summable F`. Establish `hI : Summable f` using `(Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)).summable_iff.1 hsig`. Establish `hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)` using `fun v w h => HeightOneSpectrum.ext h`. Use `(hI.comp_injective hinj).congr (fun v => ?_)` and prove the remaining obligations.

Simplify using `only [Function.comp_apply, f, qV_eq]`.
-/
theorem qvSum_holds : QvSum := by
  intro F _ _
  haveI hfin : ∀ n : ℕ, Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
    fun n => (Ideal.finite_setOf_absNorm_eq (S := 𝓞 F) n).to_subtype
  let f : Ideal (𝓞 F) → ℝ := fun I => ((Ideal.absNorm I : ℝ))⁻¹ ^ 2
  have hf0 : ∀ I, 0 ≤ f I := fun I => by positivity
  have hsig : Summable (fun x : Σ n : ℕ, {I : Ideal (𝓞 F) // Ideal.absNorm I = n} => f x.2.1) := by
    rw [summable_sigma_of_nonneg (fun x => hf0 _)]
    refine ⟨fun n => Summable.of_finite, ?_⟩
    have e2 : (fun n : ℕ => ∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}, f I.1) =
        fun n => LocalCountingSum.cnt F n / (n : ℝ) ^ 2 := by
      funext n
      have hc : ∀ I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}, f I.1 = ((n : ℝ))⁻¹ ^ 2 := by
        intro I
        simp only [f, I.2]
      rw [tsum_congr hc, tsum_const, nsmul_eq_mul]
      unfold LocalCountingSum.cnt
      rw [inv_pow, div_eq_mul_inv]
    rw [e2]
    exact LocalCountingSum.cnt_summable F
  have hI : Summable f := (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)).summable_iff.1 hsig
  have hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) :=
    fun v w h => HeightOneSpectrum.ext h
  refine (hI.comp_injective hinj).congr (fun v => ?_)
  simp only [Function.comp_apply, f, qV_eq]

end PI.VolStabS
