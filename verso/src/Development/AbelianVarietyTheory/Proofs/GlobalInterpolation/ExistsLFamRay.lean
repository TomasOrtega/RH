import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteIdealsIn
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayCountThetaFibreCount
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumLamIdealLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConvRealChar
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberLeAbsDiscrOfFinrankEqTwo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralOfMemRayI
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsImagQuadIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassNumberBounds

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk

section

variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)

/- English proof (translation)
Establish `: idealsIn D g 0 = ∅`. Use extensionality with `I`. Simplify using `only [idealsIn, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨h1, -, h2, -⟩`. Conclude with `h1 (Ideal.absNorm_eq_zero_iff.1 h2)`.

Simplify using `[aRay, this]`.
-/
theorem aRay_norm_zero (g : D.G) : aRay D g 0 = 0 := by
  have : idealsIn D g 0 = ∅ := by
    ext I
    simp only [idealsIn, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, -, h2, -⟩
    exact h1 (Ideal.absNorm_eq_zero_iff.1 h2)
  simp [aRay, this]

/- English proof (translation)
Establish `: idealsIn D 1 1 = {⊤}`. Use extensionality with `I`. Simplify using `only [idealsIn, Set.mem_ofPred_eq, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, -, h2, -⟩`.

Conclude with `Ideal.absNorm_eq_one_iff.1 h2`. Introduce and unpack `rfl`. Use `⟨top_ne_bot, ?_, Ideal.absNorm_eq_one_iff.2 rfl, D.cls_top⟩` and prove the remaining obligations. Rewrite using `[← Ideal.one_eq_top]`. Conclude with `isCoprime_one_left`.

Simplify using `[aRay, this]`.
-/
theorem aRay_one_norm_one : aRay D 1 1 = 1 := by
  have : idealsIn D 1 1 = {⊤} := by
    ext I
    simp only [idealsIn, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, -, h2, -⟩
      exact Ideal.absNorm_eq_one_iff.1 h2
    · rintro rfl
      refine ⟨top_ne_bot, ?_, Ideal.absNorm_eq_one_iff.2 rfl, D.cls_top⟩
      rw [← Ideal.one_eq_top]; exact isCoprime_one_left
  simp [aRay, this]

/- English proof (translation)
Establish `: idealsIn D g 1 = ∅`. Use extensionality with `I`. Simplify using `only [idealsIn, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨-, -, h2, h3⟩`. Rewrite `h3` using `[Ideal.absNorm_eq_one_iff.1 h2, D.cls_top]`.

Conclude with `hg h3.symm`. Simplify using `[aRay, this]`.
-/
theorem aRay_norm_one_of_ne {g : D.G} (hg : g ≠ 1) : aRay D g 1 = 0 := by
  have : idealsIn D g 1 = ∅ := by
    ext I
    simp only [idealsIn, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, -, h2, h3⟩
    rw [Ideal.absNorm_eq_one_iff.1 h2, D.cls_top] at h3
    exact hg h3.symm
  simp [aRay, this]

/- English proof (translation)
Establish `h1` using `RayData.card_eq_rayNo K M hM D`. Establish `h2` using `(RayNo.rayNo_bounds K (Ideal.span {(M : 𝓞 K)}) (by simpa [Ideal.span_singleton_eq_bot] using hM)).2.1`. Establish `h3 : Ideal.absNorm (Ideal.span {(M : 𝓞 K)}) = M ^ 2`. Rewrite using `[Ideal.absNorm_span_singleton, show (M : 𝓞 K) = algebraMap ℤ (𝓞 K) M by simp, Algebra.norm_algebraMap, RingOfIntegers.rank, hK]`. Simplify using `[Int.natAbs_pow]`.

Establish `h4 : (classNumber K : ℝ) ≤ 4 * |(discr K : ℝ)|`. Conclude with `GlobalTheory.classNumber_le_four_mul_abs_discr K hK` after adjusting the coercions. Rewrite `h2` using `[h3, ← h1]`. Establish `h5 : (Fintype.card D.G : ℝ) ≤ (classNumber K : ℝ) * (M : ℝ) ^ 2` using `by exact_mod_cast h2`. Conclude with `h5.trans (mul_le_mul_of_nonneg_right h4 (by positivity))`.
-/
theorem card_ray_le (hK : Module.finrank ℚ K = 2) (hM : M ≠ 0) :
    (Fintype.card D.G : ℝ) ≤ 4 * |(discr K : ℝ)| * (M : ℝ) ^ 2 := by
  have h1 := RayData.card_eq_rayNo K M hM D
  have h2 := (RayNo.rayNo_bounds K (Ideal.span {(M : 𝓞 K)})
    (by simpa [Ideal.span_singleton_eq_bot] using hM)).2.1
  have h3 : Ideal.absNorm (Ideal.span {(M : 𝓞 K)}) = M ^ 2 := by
    rw [Ideal.absNorm_span_singleton, show (M : 𝓞 K) = algebraMap ℤ (𝓞 K) M by simp, Algebra.norm_algebraMap,
      RingOfIntegers.rank, hK]
    simp [Int.natAbs_pow]
  have h4 : (classNumber K : ℝ) ≤ 4 * |(discr K : ℝ)| := by
    exact_mod_cast GlobalTheory.classNumber_le_four_mul_abs_discr K hK
  rw [h3, ← h1] at h2
  have h5 : (Fintype.card D.G : ℝ) ≤ (classNumber K : ℝ) * (M : ℝ) ^ 2 := by exact_mod_cast h2
  exact h5.trans (mul_le_mul_of_nonneg_right h4 (by positivity))

end

/- English proof (translation)
Establish `: χ g * χ g = 1`. Rewrite using `[← AddChar.mul_apply, h, AddChar.one_apply]`. Conclude with `mul_self_eq_one_iff.1 this`.
-/
theorem addChar_eq_one_or_neg_one {G : Type} [AddCommGroup G] (χ : AddChar G ℂ) (h : χ * χ = 1) (g : G) :
    χ g = 1 ∨ χ g = -1 := by
  have : χ g * χ g = 1 := by
    rw [← AddChar.mul_apply, h, AddChar.one_apply]
  exact mul_self_eq_one_iff.1 this

/- English proof (translation)
Introduce `d M hd hd4 hd100 hM`. Take `⟨K, _, _, ω, -, hK, hdisc, hω, -, -⟩` from `GlobalTheory.Mem.ImagQuad.exists_imagQuad_integers d hd hd4`. Establish `hx : (((2 * ω - 1 : 𝓞 K) : K)) ^ 2 = -(d : K)`. Use `congrArg (algebraMap (𝓞 K) K) hω` as an intermediate fact. Simplify using `using this`.

Establish `hM0 : M ≠ 0` using `by omega`. Set `D : RayData K M` to `rayData K M hM0`. Establish `hc` using `GlobalTheory.Hk.rayCountTheta K d M _ hd hd4 hd100 hx hK hM D`. Establish `hl` using `GlobalTheory.Hk.LamRay.lamRay_props K d M _ hd hd4 hd100 hx hK hM D`. Establish `hcard` using `card_ray_le D hK hM0`.

Establish `hdR : (100 : ℝ) ≤ d` using `by exact_mod_cast hd100`. Establish `hMR : (3 : ℝ) ≤ M` using `by exact_mod_cast hM`. Establish `hM2 : (9 : ℝ) ≤ (M : ℝ) ^ 2` using `by nlinarith`. Establish `hs : (10 : ℝ) ≤ Real.sqrt d` using `Real.le_sqrt_of_sq_le (by linarith)`. Establish `hss : Real.sqrt d * Real.sqrt d = d` using `Real.mul_self_sqrt (by linarith)`.

Establish `hsd : Real.sqrt d ≤ d` using `by nlinarith`. Establish `hpi` using `Real.pi_gt_three`. Establish `hpi4` using `Real.pi_le_four`. Rewrite `hcard` using `[hdisc]`. Establish `habs : |(((-(d : ℤ) : ℤ)) : ℝ)| = d`.

Rewrite using `[Int.cast_neg, abs_neg, Int.cast_natCast, Nat.abs_cast]`. Rewrite `hcard` using `[habs]`. Use `⟨{ G := Additive D.G ft := D.fin B := 4 * (d : ℝ) * (M : ℝ) ^ 2 κ := 2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) a := fun g n => aRay D g.toMul n lam := fun g n => lamRay D g.toMul n B_ge := by nlinarith card_le := hcard κ_ge := by` and prove the remaining obligations. Rewrite using `[div_le_div_iff₀ (by positivity) (by positivity)]`. Establish `h1 : Real.sqrt d * (M : ℝ) ^ 2 ≤ d * (M : ℝ) ^ 2` using `mul_le_mul_of_nonneg_right hsd (by positivity)`.

Establish `h2 : (0 : ℝ) ≤ d * (M : ℝ) ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Use `κ_le := by`. Rewrite using `[div_le_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.

Use `a_nonneg := fun g n => Nat.cast_nonneg _`. Use `a_zero := fun g => aRay_norm_zero D _`. Use `a_one := aRay_one_norm_one D`. Use `a_one_ne := fun g hg => aRay_norm_one_of_ne D hg`. Use `count := fun g => (hc g.toMul).1`.

Use `theta := fun g => (hc g.toMul).2`. Use `lam_nonneg := fun g n => hl.1 _ n`. Use `lam_le := hl.2.1`. Use `conv := fun g n => GlobalTheory.Hk.aRay_mul_log K M (by omega) D g.toMul n`. Use `sq := fun χ hχ n => GlobalTheory.Hk.RaySq.conv_real_char K M (by omega) D (fun g => (χ (Additive.ofMul g)).re) (by simp) ?_ ?_ n }, rfl, hl.2.2⟩`.

Introduce `g h`. Rewrite using `[ofMul_mul, AddChar.map_add_eq_mul]`. Apply the tactic sequence `rcases addChar_eq_one_or_neg_one χ hχ (Additive.ofMul g) with h1 | h1 <;> simp [h1]`. Introduce `g`. Apply the tactic sequence `rcases addChar_eq_one_or_neg_one χ hχ (Additive.ofMul g) with h1 | h1 <;> simp [h1]`.
-/
theorem exists_lFam_ray : ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → ∃ 𝓕 : LFam, 𝓕.B = (4 * (d : ℝ) * (M : ℝ) ^ 2) ∧
    ∀ p : ℕ, p.Prime → 𝓕.lam 0 p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p := by
  intro d M hd hd4 hd100 hM
  obtain ⟨K, _, _, ω, -, hK, hdisc, hω, -, -⟩ := GlobalTheory.Mem.ImagQuad.exists_imagQuad_integers d hd hd4
  have hx : (((2 * ω - 1 : 𝓞 K) : K)) ^ 2 = -(d : K) := by
    have := congrArg (algebraMap (𝓞 K) K) hω
    simpa using this
  have hM0 : M ≠ 0 := by omega
  let D : RayData K M := rayData K M hM0
  have hc := GlobalTheory.Hk.rayCountTheta K d M _ hd hd4 hd100 hx hK hM D
  have hl := GlobalTheory.Hk.LamRay.lamRay_props K d M _ hd hd4 hd100 hx hK hM D
  have hcard := card_ray_le D hK hM0
  have hdR : (100 : ℝ) ≤ d := by exact_mod_cast hd100
  have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM2 : (9 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  have hs : (10 : ℝ) ≤ Real.sqrt d := Real.le_sqrt_of_sq_le (by linarith)
  have hss : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (by linarith)
  have hsd : Real.sqrt d ≤ d := by nlinarith
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  rw [hdisc] at hcard
  have habs : |(((-(d : ℤ) : ℤ)) : ℝ)| = d := by
    rw [Int.cast_neg, abs_neg, Int.cast_natCast, Nat.abs_cast]
  rw [habs] at hcard
  refine ⟨{
    G := Additive D.G
    ft := D.fin
    B := 4 * (d : ℝ) * (M : ℝ) ^ 2
    κ := 2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2)
    a := fun g n => aRay D g.toMul n
    lam := fun g n => lamRay D g.toMul n
    B_ge := by nlinarith
    card_le := hcard
    κ_ge := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : Real.sqrt d * (M : ℝ) ^ 2 ≤ d * (M : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hsd (by positivity)
      have h2 : (0 : ℝ) ≤ d * (M : ℝ) ^ 2 := by positivity
      nlinarith
    κ_le := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    a_nonneg := fun g n => Nat.cast_nonneg _
    a_zero := fun g => aRay_norm_zero D _
    a_one := aRay_one_norm_one D
    a_one_ne := fun g hg => aRay_norm_one_of_ne D hg
    count := fun g => (hc g.toMul).1
    theta := fun g => (hc g.toMul).2
    lam_nonneg := fun g n => hl.1 _ n
    lam_le := hl.2.1
    conv := fun g n => GlobalTheory.Hk.aRay_mul_log K M (by omega) D g.toMul n
    sq := fun χ hχ n => GlobalTheory.Hk.RaySq.conv_real_char K M (by omega) D (fun g => (χ (Additive.ofMul g)).re) (by simp) ?_ ?_ n }, rfl, hl.2.2⟩
  · intro g h
    rw [ofMul_mul, AddChar.map_add_eq_mul]
    rcases addChar_eq_one_or_neg_one χ hχ (Additive.ofMul g) with h1 | h1 <;> simp [h1]
  · intro g
    rcases addChar_eq_one_or_neg_one χ hχ (Additive.ofMul g) with h1 | h1 <;> simp [h1]

end GlobalTheory.Hk
