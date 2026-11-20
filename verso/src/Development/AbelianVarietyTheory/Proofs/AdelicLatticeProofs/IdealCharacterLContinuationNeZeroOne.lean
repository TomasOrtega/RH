import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EulerProductNeZeroOneOfEntire
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneSubRePosOfNormLeHalf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DedekindZetaEulerProductMulSubOneEntire

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
/- English proof (translation)
Establish `h0 : Ideal.absNorm P.asIdeal ≠ 0` using `Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot`. Establish `h1 : Ideal.absNorm P.asIdeal ≠ 1` using `Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top`. Use linear arithmetic over natural numbers and integers.
-/
private theorem two_le_absNorm_heightOneSpectrum {K : Type} [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm P.asIdeal := by
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top
  omega

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
/- English proof (translation)
Introduce `h`. Establish `h1 : c * (n : ℂ) ^ (-s) = 1` using `(sub_eq_zero.mp h).symm`. Establish `h2 : ‖(n : ℂ) ^ (-s)‖ < 1`. Rewrite using `[Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]`. Conclude with `Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < n)) (by linarith)`.

Establish `h3` using `congrArg norm h1`. Rewrite `h3` using `[norm_mul, norm_one]`. Use polynomial arithmetic with `[norm_nonneg c, norm_nonneg ((n : ℂ) ^ (-s))]`.
-/
private theorem one_sub_mul_natCast_cpow_neg_ne_zero {c : ℂ} (hc : ‖c‖ ≤ 1) {n : ℕ} (hn : 2 ≤ n)
    {s : ℂ} (hs : 0 < s.re) : 1 - c * (n : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : c * (n : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have h2 : ‖(n : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < n)) (by linarith)
  have h3 := congrArg norm h1
  rw [norm_mul, norm_one] at h3
  nlinarith [norm_nonneg c, norm_nonneg ((n : ℂ) ^ (-s))]

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in

/- English proof (translation)
Introduce `K _ _ m X φ hm hXbot hXmul hXnorm hXzero hφmul hφsmul hφsmooth hφnorm hXφ hJ c hc hcX`. Establish `hXtop : X ⊤ = 1`. Establish `h1` using `hXnorm ⊤ top_ne_bot (top_sup_eq m)`. Establish `h2 : X ⊤ = X ⊤ * X ⊤` using `by rw [← hXmul, Ideal.top_mul]`. Establish `h3 : X ⊤ ≠ 0` using `fun h => by rw [h, norm_zero] at h1; exact zero_ne_one h1`.

Conclude with `mul_left_cancel₀ h3 (by rw [mul_one]; exact h2.symm)`. Establish `hXle : ∀ I, ‖X I‖ ≤ 1`. Introduce `I`. Distinguish the cases in `hI : I = ⊥`. Rewrite using `[hI, hXbot, norm_zero]`.

Conclude with `zero_le_one`. Distinguish the cases in `hIm : I ⊔ m = ⊤`. Rewrite using `[hXnorm I hI hIm]`. Rewrite using `[hXzero I hIm, norm_zero]`. Conclude with `zero_le_one`.

Take `⟨Z, hZd, hZ, hZ1⟩` from `_root_.GlobalTheory.idealCharacter_LSeries_continuation K m X φ hm hXbot hXmul hXnorm hXzero hφmul hφsmul hφsmooth hφnorm hXφ`. Establish `hZ0` using `hZ1 hJ`. Set `LX : ℂ → ℂ` to `dslope Z 1`. Establish `hLXd : Differentiable ℂ LX`. Rewrite using `[← differentiableOn_univ]`.

Conclude with `(Complex.differentiableOn_dslope Filter.univ_mem).mpr hZd.differentiableOn`. Establish `hLX : ∀ s : ℂ, 1 < s.re → LX s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)))`. Introduce `s hs`. Establish `hs1 : s ≠ 1` using `fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl _ hs`. Establish `hs1' : s - 1 ≠ 0` using `sub_ne_zero.mpr hs1`.

Rewrite using `[← _root_.GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X hXbot hXtop hXmul hXle s hs]`. Simplify using `only [LX, dslope_of_ne _ hs1, slope_def_field, hZ s hs, hZ0, sub_zero]`. Clear the denominators using the available nonvanishing facts. Take `⟨Zζ, hZζd, hZζ⟩` from `_root_.GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire K`. Establish `hsum : ∀ σ : ℝ, 1 < σ → Summable fun P : HeightOneSpectrum (𝓞 K) => ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-σ)` using `fun σ hσ => ((_root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 σ hσ).2`.

Establish `hne : Nonempty (HeightOneSpectrum (𝓞 K))`. Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 K)`. Conclude with `⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩⟩`. Establish `hLX1 : LX 1 ≠ 0` using `_root_.GlobalTheory.eulerProduct_ne_zero_one_of_entire (HeightOneSpectrum (𝓞 K)) (fun P => Ideal.absNorm P.asIdeal) (fun P => X P.asIdeal) two_le_absNorm_heightOneSpectrum (fun P => hXle _) hsum hne Zζ LX hZζd hLXd hZζ hLX`. Establish `hfin : {P : HeightOneSpectrum (𝓞 K) | P.asIdeal ∣ m}.Finite` using `Ideal.finite_factors hm`.

Set `S` to `hfin.toFinset`. Establish `hmemS : ∀ P, P ∈ S ↔ m ≤ P.asIdeal` using `fun P => by simp [S, Ideal.dvd_iff_le]`. Establish `hfac : ∀ (P : HeightOneSpectrum (𝓞 K)) (s : ℂ), 0 < s.re → 1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s) ≠ 0` using `fun P s hs => one_sub_mul_natCast_cpow_neg_ne_zero (hc P) (two_le_absNorm_heightOneSpectrum P) hs`. Set `F : ℂ → ℂ` to `∏ P ∈ S, fun s => (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹`. Establish `hF : ∀ s, F s = ∏ P ∈ S, (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹` using `fun s => by simp [F, Finset.prod_apply]`.

Use `⟨fun s => LX s * F s, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `hLXd.differentiableOn.mul` to reduce the goal to its premises. Apply `DifferentiableOn.finset_prod` to reduce the goal to its premises. Introduce `P _`. Use `DifferentiableOn.inv ?_ (fun s hs => hfac P s hs)` and prove the remaining obligations.

Use `DifferentiableOn.const_sub ?_ _` and prove the remaining obligations. Use `DifferentiableOn.const_mul ?_ _` and prove the remaining obligations. Introduce `s _`. Use `DifferentiableAt.differentiableWithinAt ?_` and prove the remaining obligations. Conclude with `differentiableAt_id.neg.const_cpow (Or.inl (Nat.cast_ne_zero.mpr (by have := two_le_absNorm_heightOneSpectrum P; omega)))`.

Introduce `s hs`. Establish `hs0 : 0 < s.re` using `by linarith`. Take `⟨hsa, -⟩` from `(_root_.GlobalTheory.eulerProduct_eq_exp_and_pos (HeightOneSpectrum (𝓞 K)) (fun P => Ideal.absNorm P.asIdeal) (fun P => X P.asIdeal) two_le_absNorm_heightOneSpectrum (fun P => hXle _) hsum).1 s hs`. Establish `hsplit : ∀ P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)) = -Complex.log (1 - X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)) + (if P ∈ S then -Complex.log (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)) else 0)`. Introduce `P`.

Distinguish the cases in `hP : P ∈ S`. Rewrite using `[if_pos hP]`. Establish `hXP : X P.asIdeal = 0` using `hXzero _ (by`. Rewrite using `[sup_eq_left.mpr ((hmemS P).mp hP)]`. Conclude with `P.isPrime.ne_top)`.

Rewrite using `[hXP, zero_mul, sub_zero, Complex.log_one, neg_zero, zero_add]`. Rewrite using `[if_neg hP, add_zero, hcX P (fun h => hP ((hmemS P).mpr h))]`. Use `show LX s * F s = _`. Rewrite using `[tsum_congr hsplit, hsa.tsum_add (summable_of_ne_finset_zero (s := S) fun P hP => if_neg hP), tsum_eq_sum (s := S) (fun P hP => if_neg hP), Complex.exp_add, ← hLX s hs, hF, Complex.exp_sum]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun P hP => ?_` and prove the remaining obligations. Rewrite using `[if_pos hP, Complex.exp_neg, Complex.exp_log (hfac P s hs0)]`. Use `show LX 1 * F 1 ≠ 0`. Rewrite using `[hF]`. Conclude with `mul_ne_zero hLX1 (Finset.prod_ne_zero_iff.mpr fun P _ => inv_ne_zero (hfac P 1 (by simp)))`.
-/
theorem _root_.GlobalTheory.idealCharacterL_continuation_ne_zero_one :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ)
    (φ : mixedSpace K → ℂ), m ≠ ⊥ → X ⊥ = 0 → (∀ I J, X (I * J) = X I * X J) →
    (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) → (∀ I, I ⊔ m ≠ ⊤ → X I = 0) →
    (∀ x y, φ (x * y) = φ x * φ y) → (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) →
    ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} →
    (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) →
    (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = φ (mixedEmbedding K β)) →
    (∃ J, J ≠ ⊥ ∧ J ⊔ m = ⊤ ∧ X J ≠ 1) → ∀ c : HeightOneSpectrum (𝓞 K) → ℂ,
    (∀ P, ‖c P‖ ≤ 1) → (∀ P, ¬ m ≤ P.asIdeal → c P = X P.asIdeal) →
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L {s | 0 < s.re} ∧ (∀ s : ℂ, 1 < s.re →
      L s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)))) ∧ L 1 ≠ 0 := by
  intro K _ _ m X φ hm hXbot hXmul hXnorm hXzero hφmul hφsmul hφsmooth hφnorm hXφ hJ c hc hcX
  have hXtop : X ⊤ = 1 := by
    have h1 := hXnorm ⊤ top_ne_bot (top_sup_eq m)
    have h2 : X ⊤ = X ⊤ * X ⊤ := by rw [← hXmul, Ideal.top_mul]
    have h3 : X ⊤ ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact zero_ne_one h1
    exact mul_left_cancel₀ h3 (by rw [mul_one]; exact h2.symm)
  have hXle : ∀ I, ‖X I‖ ≤ 1 := by
    intro I
    by_cases hI : I = ⊥
    · rw [hI, hXbot, norm_zero]
      exact zero_le_one
    by_cases hIm : I ⊔ m = ⊤
    · rw [hXnorm I hI hIm]
    · rw [hXzero I hIm, norm_zero]
      exact zero_le_one
  obtain ⟨Z, hZd, hZ, hZ1⟩ := _root_.GlobalTheory.idealCharacter_LSeries_continuation K m X φ hm hXbot hXmul hXnorm
    hXzero hφmul hφsmul hφsmooth hφnorm hXφ
  have hZ0 := hZ1 hJ
  let LX : ℂ → ℂ := dslope Z 1
  have hLXd : Differentiable ℂ LX := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr hZd.differentiableOn
  have hLX : ∀ s : ℂ, 1 < s.re → LX s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Complex.log (1 - X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl _ hs
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [← _root_.GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X hXbot hXtop hXmul hXle s hs]
    simp only [LX, dslope_of_ne _ hs1, slope_def_field, hZ s hs, hZ0, sub_zero]
    field_simp
  obtain ⟨Zζ, hZζd, hZζ⟩ := _root_.GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire K
  have hsum : ∀ σ : ℝ, 1 < σ → Summable fun P : HeightOneSpectrum (𝓞 K) =>
      ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-σ) :=
    fun σ hσ => ((_root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 σ hσ).2
  have hne : Nonempty (HeightOneSpectrum (𝓞 K)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩⟩
  have hLX1 : LX 1 ≠ 0 := _root_.GlobalTheory.eulerProduct_ne_zero_one_of_entire (HeightOneSpectrum (𝓞 K))
    (fun P => Ideal.absNorm P.asIdeal) (fun P => X P.asIdeal) two_le_absNorm_heightOneSpectrum
    (fun P => hXle _) hsum hne Zζ LX hZζd hLXd hZζ hLX
  have hfin : {P : HeightOneSpectrum (𝓞 K) | P.asIdeal ∣ m}.Finite := Ideal.finite_factors hm
  let S := hfin.toFinset
  have hmemS : ∀ P, P ∈ S ↔ m ≤ P.asIdeal := fun P => by simp [S, Ideal.dvd_iff_le]
  have hfac : ∀ (P : HeightOneSpectrum (𝓞 K)) (s : ℂ), 0 < s.re →
      1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s) ≠ 0 :=
    fun P s hs => one_sub_mul_natCast_cpow_neg_ne_zero (hc P) (two_le_absNorm_heightOneSpectrum P) hs
  let F : ℂ → ℂ := ∏ P ∈ S, fun s => (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹
  have hF : ∀ s, F s = ∏ P ∈ S, (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ :=
    fun s => by simp [F, Finset.prod_apply]
  refine ⟨fun s => LX s * F s, ?_, ?_, ?_⟩
  · apply hLXd.differentiableOn.mul
    apply DifferentiableOn.finset_prod
    intro P _
    refine DifferentiableOn.inv ?_ (fun s hs => hfac P s hs)
    refine DifferentiableOn.const_sub ?_ _
    refine DifferentiableOn.const_mul ?_ _
    intro s _
    refine DifferentiableAt.differentiableWithinAt ?_
    exact differentiableAt_id.neg.const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr (by have := two_le_absNorm_heightOneSpectrum P; omega)))
  · intro s hs
    have hs0 : 0 < s.re := by linarith
    obtain ⟨hsa, -⟩ := (_root_.GlobalTheory.eulerProduct_eq_exp_and_pos (HeightOneSpectrum (𝓞 K))
      (fun P => Ideal.absNorm P.asIdeal) (fun P => X P.asIdeal) two_le_absNorm_heightOneSpectrum
      (fun P => hXle _) hsum).1 s hs
    have hsplit : ∀ P : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)) =
        -Complex.log (1 - X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)) +
        (if P ∈ S then -Complex.log (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))
          else 0) := by
      intro P
      by_cases hP : P ∈ S
      · rw [if_pos hP]
        have hXP : X P.asIdeal = 0 := hXzero _ (by
          rw [sup_eq_left.mpr ((hmemS P).mp hP)]
          exact P.isPrime.ne_top)
        rw [hXP, zero_mul, sub_zero, Complex.log_one, neg_zero, zero_add]
      · rw [if_neg hP, add_zero, hcX P (fun h => hP ((hmemS P).mpr h))]
    show LX s * F s = _
    rw [tsum_congr hsplit, hsa.tsum_add (summable_of_ne_finset_zero (s := S) fun P hP => if_neg hP),
      tsum_eq_sum (s := S) (fun P hP => if_neg hP), Complex.exp_add, ← hLX s hs, hF,
      Complex.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [if_pos hP, Complex.exp_neg, Complex.exp_log (hfac P s hs0)]
  · show LX 1 * F 1 ≠ 0
    rw [hF]
    exact mul_ne_zero hLX1 (Finset.prod_ne_zero_iff.mpr fun P _ => inv_ne_zero (hfac P 1 (by simp)))

end GlobalTheory
