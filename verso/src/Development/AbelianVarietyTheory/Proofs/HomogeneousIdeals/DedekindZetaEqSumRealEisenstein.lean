import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.TendstoRealEisensteinSubPole
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsBasisEmbedding

open NumberField Module FractionalIdeal Filter Topology
open scoped nonZeroDivisors UpperHalfPlane Real

namespace GlobalTheory

open QuadraticZeta

namespace QuadraticZeta

/- English proof (translation)
Establish `hu` using `ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right`. Establish `hB` using `(Complex.continuous_ofReal.tendsto _).comp hA`. Establish `dL : HasDerivAt (fun s : ℝ => L s) (deriv L 1) 1` using `HasDerivAt.comp_ofReal (by simpa using hL.hasDerivAt)`. Establish `dG : HasDerivAt (fun s : ℝ => ((c ^ s / 2 : ℝ) : ℂ)) (c * Real.log c / 2 : ℝ) 1`. Simplify using `using ((Real.hasStrictDerivAt_const_rpow hc 1).hasDerivAt.div_const 2).ofReal_comp`.

Establish `hle : 𝓝[>] (1 : ℝ) ≤ 𝓝[≠] 1` using `nhdsWithin_mono _ fun _ h => ne_of_gt h`. Establish `cL` using `dL.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))`. Establish `cG` using `dG.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))`. Establish `sL` using `(hasDerivAt_iff_tendsto_slope.1 dL).mono_left hle`. Establish `sG` using `(hasDerivAt_iff_tendsto_slope.1 dG).mono_left hle`.

Establish `c0 : Tendsto (fun s : ℝ => (s - 1 : ℂ)) (𝓝[>] 1) (𝓝 0)`. Establish `: Continuous fun s : ℝ => (s - 1 : ℂ)` using `by fun_prop`. Simplify using `using (this.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))`. Establish `hne : ∀ s : ℝ, 1 < s → (s - 1 : ℂ) ≠ 0` using `fun s hs => by`. Conclude with `(sub_pos.2 hs).ne'` after adjusting the coercions.

Establish `e1 : L 1 = (c / 2 * a : ℝ)`. Use `tendsto_nhds_unique_of_eventuallyEq (((c0.mul hu).add_const 1).mul cL) (cG.mul ((c0.mul hB).add_const (a : ℂ))) (by filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)` as an intermediate fact. Establish `h1` using `h s hs`. Establish `h2` using `hne s hs`. Simplify using `only [Function.comp_apply]`.

Move the coercions through the operations in `at h1 ⊢`. Clear the denominators using the available nonvanishing facts. Take the linear combination `2 * (s - 1) * h1)`. Simplify using `using this`. Use `⟨e1, ?_⟩` and prove the remaining obligations.

Use `tendsto_nhds_unique_of_eventuallyEq ((hu.mul cL).add sL) ((cG.mul hB).add (sG.const_mul (a : ℂ))) (by filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)` as an intermediate fact. Establish `h1` using `h s hs`. Establish `h2` using `hne s hs`. Simplify using `only [Function.comp_apply, slope, vsub_eq_sub, Complex.real_smul, Complex.ofReal_one, e1, Real.rpow_one]`. Move the coercions through the operations in `at h1 ⊢`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `2 * (s - 1) * h1)`. Simplify using `only [Complex.ofReal_one, Real.rpow_one] at this`. Rewrite using `[this]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem compare_expansions {L : ℂ → ℂ} (hL : DifferentiableAt ℂ L 1) {A : ℝ → ℝ} {a C c : ℝ}
    (hc : 0 < c) (hA : Tendsto (fun s => A s - a / (s - 1)) (𝓝[>] 1) (𝓝 C))
    (h : ∀ s : ℝ, 1 < s → riemannZeta s * L s = (c ^ s / 2 * A s : ℝ)) :
    L 1 = (c / 2 * a : ℝ) ∧
      Real.eulerMascheroniConstant * L 1 + deriv L 1 = (c / 2 * (C + a * Real.log c) : ℝ) := by
  have hu := ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right
  have hB := (Complex.continuous_ofReal.tendsto _).comp hA
  have dL : HasDerivAt (fun s : ℝ => L s) (deriv L 1) 1 :=
    HasDerivAt.comp_ofReal (by simpa using hL.hasDerivAt)
  have dG : HasDerivAt (fun s : ℝ => ((c ^ s / 2 : ℝ) : ℂ)) (c * Real.log c / 2 : ℝ) 1 := by
    simpa using ((Real.hasStrictDerivAt_const_rpow hc 1).hasDerivAt.div_const 2).ofReal_comp
  have hle : 𝓝[>] (1 : ℝ) ≤ 𝓝[≠] 1 := nhdsWithin_mono _ fun _ h => ne_of_gt h
  have cL := dL.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  have cG := dG.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  have sL := (hasDerivAt_iff_tendsto_slope.1 dL).mono_left hle
  have sG := (hasDerivAt_iff_tendsto_slope.1 dG).mono_left hle
  have c0 : Tendsto (fun s : ℝ => (s - 1 : ℂ)) (𝓝[>] 1) (𝓝 0) := by
    have : Continuous fun s : ℝ => (s - 1 : ℂ) := by fun_prop
    simpa using (this.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  have hne : ∀ s : ℝ, 1 < s → (s - 1 : ℂ) ≠ 0 := fun s hs => by
    exact_mod_cast (sub_pos.2 hs).ne'
  have e1 : L 1 = (c / 2 * a : ℝ) := by
    have := tendsto_nhds_unique_of_eventuallyEq (((c0.mul hu).add_const 1).mul cL)
      (cG.mul ((c0.mul hB).add_const (a : ℂ))) (by
        filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
        have h1 := h s hs
        have h2 := hne s hs
        simp only [Function.comp_apply]
        push_cast at h1 ⊢
        field_simp
        linear_combination 2 * (s - 1) * h1)
    simpa using this
  refine ⟨e1, ?_⟩
  have := tendsto_nhds_unique_of_eventuallyEq ((hu.mul cL).add sL)
    ((cG.mul hB).add (sG.const_mul (a : ℂ))) (by
      filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      have h1 := h s hs
      have h2 := hne s hs
      simp only [Function.comp_apply, slope, vsub_eq_sub, Complex.real_smul, Complex.ofReal_one,
        e1, Real.rpow_one]
      push_cast at h1 ⊢
      field_simp
      linear_combination 2 * (s - 1) * h1)
  simp only [Complex.ofReal_one, Real.rpow_one] at this
  rw [this]
  push_cast
  ring

end QuadraticZeta

variable {K : Type*} [Field K] [NumberField K] {d : ℕ}

def IsIdealClassPoint (σ : K →+* ℂ) (c : ClassGroup (𝓞 K)) (τ : ℍ) : Prop :=
  ∃ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (ω : ℂ), ClassGroup.mk K 𝔞 = c ∧
    ∀ z, z ∈ σ '' 𝔞.1 ↔ ∃ m n : ℤ, ω * (m * (τ : ℂ) + n) = z

/- English proof (translation)
Take `⟨I, rfl⟩` from `ClassGroup.mk0_surjective c`. Take `⟨L, hL⟩` from `exists_periodPair h2 hD σ (FractionalIdeal.mk0 K I)`. Conclude with `⟨_, L, ClassGroup.mk_mk0 K I, hL⟩`.
-/
theorem exists_classRep_periodPair (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ)
    (c : ClassGroup (𝓞 K)) : ∃ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : PeriodPair),
      ClassGroup.mk K 𝔞 = c ∧ (L.lattice : Set ℂ) = σ '' 𝔞.1 := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  obtain ⟨L, hL⟩ := exists_periodPair h2 hD σ (FractionalIdeal.mk0 K I)
  exact ⟨_, L, ClassGroup.mk_mk0 K I, hL⟩

/- English proof (translation)
Take `⟨𝔞, L, h1, hL⟩` from `exists_classRep_periodPair h2 hD σ c`. Take `⟨ω, τ, -, h⟩` from `exists_lattice_eq_mul_tau L`. Conclude with `⟨τ, 𝔞, ω, h1, fun z => by rw [← hL, SetLike.mem_coe, h]⟩`.
-/
theorem exists_isIdealClassPoint (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ)
    (c : ClassGroup (𝓞 K)) : ∃ τ, IsIdealClassPoint σ c τ := by
  obtain ⟨𝔞, L, h1, hL⟩ := exists_classRep_periodPair h2 hD σ c
  obtain ⟨ω, τ, -, h⟩ := exists_lattice_eq_mul_tau L
  exact ⟨τ, 𝔞, ω, h1, fun z => by rw [← hL, SetLike.mem_coe, h]⟩

/- English proof (translation)
Use `choose 𝔞 ω hc h using hτ`. Establish `hs0 : -s ≠ 0` using `by linarith`. Establish `h1` using `(hasSum_sum fun c (_ : c ∈ Finset.univ) => hasSum_ideal_of_image h2 hD σ hd (𝔞 c) (h c) hs (summable_realEisenstein _ hs)).div_const 2`. Rewrite `h1` using `[← Finset.mul_sum, mul_div_right_comm]`. Establish `h3 : HasSum (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-s)) _` using `h1.congr_fun fun I => by`.

Break down `eq_or_ne I ⊥ with rfl | hI` into its components or cases. Simplify using `[Real.zero_rpow hs0]`. Establish `hI' : I ∈ (Ideal (𝓞 K))⁰` using `mem_nonZeroDivisors_of_ne_zero hI`. Establish `: ∀ c, ((I * 𝔞 c : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal ↔ (ClassGroup.mk0 ⟨I, hI'⟩)⁻¹ = c` using `fun c => by`. Rewrite using `[inv_eq_iff_mul_eq_one, ← ClassGroup.mk_mk0 K]`.

Use `conv_rhs => rw [← hc c, ← map_mul, ClassGroup.mk_eq_one_iff]`. Both sides reduce to the same expression. Simplify using `only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree. Establish `h4` using `Complex.hasSum_ofReal.2 (h3.tsum_fiberwise Ideal.absNorm)`.

Rewrite using `[dedekindZeta, LSeries]`. Use `HasSum.tsum_eq (h4.congr_fun fun n => ?_)` and prove the remaining obligations. Rewrite using `[tsum_congr (g := fun _ => (n : ℝ) ^ (-s)) fun I => by`. Rewrite using `[show Ideal.absNorm I.1 = n from I.2], tsum_const, nsmul_eq_mul]`. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases.

Simplify using `[Real.zero_rpow hs0]`. Rewrite using `[LSeries.term_of_ne_zero hn, Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.cpow_neg]`. Both sides reduce to the same expression.
-/
theorem dedekindZeta_eq_sum_realEisenstein (h2 : finrank ℚ K = 2) (hD : discr K = -d) (hd : 4 < d)
    (σ : K →+* ℂ) {τ : ClassGroup (𝓞 K) → ℍ} (hτ : ∀ c, IsIdealClassPoint σ c (τ c))
    {s : ℝ} (hs : 1 < s) :
    dedekindZeta K s = ((2 / √d) ^ s / 2 * ∑ c, ∑' p : {p : ℤ × ℤ // p ≠ 0},
      (τ c).im ^ s / ‖(p.1.1 * τ c + p.1.2 : ℂ)‖ ^ (2 * s) : ℝ) := by
  classical
  choose 𝔞 ω hc h using hτ
  have hs0 : -s ≠ 0 := by linarith
  have h1 := (hasSum_sum fun c (_ : c ∈ Finset.univ) => hasSum_ideal_of_image h2 hD σ hd (𝔞 c)
    (h c) hs (summable_realEisenstein _ hs)).div_const 2
  rw [← Finset.mul_sum, mul_div_right_comm] at h1
  have h3 : HasSum (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-s)) _ :=
    h1.congr_fun fun I => by
      rcases eq_or_ne I ⊥ with rfl | hI
      · simp [Real.zero_rpow hs0]
      have hI' : I ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hI
      have : ∀ c, ((I * 𝔞 c : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal ↔
          (ClassGroup.mk0 ⟨I, hI'⟩)⁻¹ = c := fun c => by
        rw [inv_eq_iff_mul_eq_one, ← ClassGroup.mk_mk0 K]
        conv_rhs => rw [← hc c, ← map_mul, ClassGroup.mk_eq_one_iff]
        rfl
      simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
  have h4 := Complex.hasSum_ofReal.2 (h3.tsum_fiberwise Ideal.absNorm)
  rw [dedekindZeta, LSeries]
  refine HasSum.tsum_eq (h4.congr_fun fun n => ?_)
  rw [tsum_congr (g := fun _ => (n : ℝ) ^ (-s)) fun I => by
    rw [show Ideal.absNorm I.1 = n from I.2], tsum_const, nsmul_eq_mul]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow hs0]
  · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg _),
      Complex.ofReal_neg, Complex.cpow_neg]
    rfl

/- English proof (translation)
Establish `hd0` using `discr_pos h2 hD`. Establish `hh : (0 : ℝ) < classNumber K` using `by exact_mod_cast classNumber_pos K`. Establish `hA` using `tendsto_finsetSum Finset.univ fun c _ => tendsto_realEisenstein_sub_pole (τ c)`. Use `replace hA := hA.congr (f₂ := fun s : ℝ => (∑ c, ∑' p : {p : ℤ × ℤ // p ≠ 0}, (τ c).im ^ s / ‖(p.1.1 * τ c + p.1.2 : ℂ)‖ ^ (2 * s)) - classNumber K * π / (s - 1)) fun s => by simp [classNumber, mul_div_assoc]`. Take `⟨e1, e2⟩` from `compare_expansions (χ.differentiableAt_LFunction 1 (Or.inr (hχ.ne_one (by omega)))) (show 0 < 2 / √(d : ℝ) by positivity) hA fun s hs => by`.

Rewrite using `[← dedekindZeta_eq_mul_LFunction h2 hD hχ (by simpa using hs), dedekindZeta_eq_sum_realEisenstein h2 hD hd σ hτ hs]`. Establish `e3 : ∑ c, (2 * π * (Real.eulerMascheroniConstant - Real.log 2) - π * Real.log (τ c).im - 2 * π * Real.log (‖ModularForm.eta (τ c)‖ ^ 2)) = classNumber K * (2 * π * (Real.eulerMascheroniConstant - Real.log 2)) - π * ∑ c, Real.log ((τ c).im * ‖ModularForm.eta (τ c)‖ ^ 4)`. Rewrite using `[Finset.mul_sum, classNumber, ← Finset.card_univ, ← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Real.log_mul (τ c).im_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 (ModularForm.eta_ne_zero (τ c).2))), Real.log_pow, Real.log_pow]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `e2` using `[e3]`. Use `⟨e1.trans (congrArg _ (by ring)), ?_⟩` and prove the remaining obligations. Rewrite using `[eq_sub_of_add_eq' e2, e1, ← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_div, ← Complex.ofReal_sub, Real.log_div two_ne_zero (by positivity), Real.log_mul two_ne_zero (by positivity)]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem LFunction_one_and_mean_log_eta [NeZero d] (h2 : finrank ℚ K = 2) (hD : discr K = -d)
    (hd : 4 < d) {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ)
    (σ : K →+* ℂ) {τ : ClassGroup (𝓞 K) → ℍ} (hτ : ∀ c, IsIdealClassPoint σ c (τ c)) :
    χ.LFunction 1 = (π * classNumber K / √d : ℝ) ∧
    (((∑ c, Real.log ((τ c).im * ‖ModularForm.eta (τ c)‖ ^ 4)) / classNumber K : ℝ) : ℂ)
      = (Real.eulerMascheroniConstant - Real.log (2 * √d) : ℝ)
        - deriv χ.LFunction 1 / χ.LFunction 1 := by
  have hd0 := discr_pos h2 hD
  have hh : (0 : ℝ) < classNumber K := by exact_mod_cast classNumber_pos K
  have hA := tendsto_finsetSum Finset.univ fun c _ => tendsto_realEisenstein_sub_pole (τ c)
  replace hA := hA.congr (f₂ := fun s : ℝ => (∑ c, ∑' p : {p : ℤ × ℤ // p ≠ 0},
      (τ c).im ^ s / ‖(p.1.1 * τ c + p.1.2 : ℂ)‖ ^ (2 * s)) - classNumber K * π / (s - 1))
    fun s => by simp [classNumber, mul_div_assoc]
  obtain ⟨e1, e2⟩ := compare_expansions
    (χ.differentiableAt_LFunction 1 (Or.inr (hχ.ne_one (by omega))))
    (show 0 < 2 / √(d : ℝ) by positivity) hA fun s hs => by
      rw [← dedekindZeta_eq_mul_LFunction h2 hD hχ (by simpa using hs),
        dedekindZeta_eq_sum_realEisenstein h2 hD hd σ hτ hs]
  have e3 : ∑ c, (2 * π * (Real.eulerMascheroniConstant - Real.log 2) - π * Real.log (τ c).im
        - 2 * π * Real.log (‖ModularForm.eta (τ c)‖ ^ 2))
      = classNumber K * (2 * π * (Real.eulerMascheroniConstant - Real.log 2))
        - π * ∑ c, Real.log ((τ c).im * ‖ModularForm.eta (τ c)‖ ^ 4) := by
    rw [Finset.mul_sum, classNumber, ← Finset.card_univ, ← nsmul_eq_mul, ← Finset.sum_const,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Real.log_mul (τ c).im_ne_zero
      (pow_ne_zero _ (norm_ne_zero_iff.2 (ModularForm.eta_ne_zero (τ c).2))), Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  rw [e3] at e2
  refine ⟨e1.trans (congrArg _ (by ring)), ?_⟩
  rw [eq_sub_of_add_eq' e2, e1, ← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_div,
    ← Complex.ofReal_sub, Real.log_div two_ne_zero (by positivity),
    Real.log_mul two_ne_zero (by positivity)]
  congr 1
  field_simp
  ring

/- English proof (translation)
Set `L' : PeriodPair` to `⟨a * τ, a, by`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t e`. Establish `e2 : (s * τ + t : ℂ) = 0` using `mul_left_cancel₀ ha (by`. Simplify using `only [Complex.real_smul] at e`.

Take the linear combination `e)`. Establish `e3 : s = 0` using `by simpa [τ.im_ne_zero] using congrArg Complex.im e2`. Conclude with `⟨e3, by simpa [e3] using e2⟩⟩`. Establish `e : L.lattice = L'.lattice`. Use extensionality with `x`.

Simplify using `only [h, PeriodPair.mem_lattice, L']`. Conclude with `exists₂_congr fun m n => by rw [show a * (m * τ + n) = m * (a * τ) + n * a by ring]`. Establish `hy` using `τ.im_pos`. Rewrite using `[e, ZLattice.covolume_eq_det_mul_measureReal _ _ L'.latticeBasis Complex.orthonormalBasisOneI.toBasis, MeasureTheory.measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _), MeasureTheory.Measure.real, OrthonormalBasis.coe_toBasis, Complex.orthonormalBasisOneI.volume_pa …`. Use `congr 1`.

Rewrite using `[Module.Basis.det_apply, Matrix.det_fin_two]`. Simplify using `[Module.Basis.toMatrix_apply, L', Complex.sq_norm, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem covolume_lattice_eq {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    ZLattice.covolume L.lattice = ‖a‖ ^ 2 * τ.im := by
  let L' : PeriodPair := ⟨a * τ, a, by
    rw [LinearIndependent.pair_iff]
    intro s t e
    have e2 : (s * τ + t : ℂ) = 0 := mul_left_cancel₀ ha (by
      simp only [Complex.real_smul] at e
      linear_combination e)
    have e3 : s = 0 := by simpa [τ.im_ne_zero] using congrArg Complex.im e2
    exact ⟨e3, by simpa [e3] using e2⟩⟩
  have e : L.lattice = L'.lattice := by
    ext x
    simp only [h, PeriodPair.mem_lattice, L']
    exact exists₂_congr fun m n => by rw [show a * (m * τ + n) = m * (a * τ) + n * a by ring]
  have hy := τ.im_pos
  rw [e, ZLattice.covolume_eq_det_mul_measureReal _ _ L'.latticeBasis
    Complex.orthonormalBasisOneI.toBasis,
    MeasureTheory.measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _),
    MeasureTheory.Measure.real, OrthonormalBasis.coe_toBasis,
    Complex.orthonormalBasisOneI.volume_parallelepiped, ENNReal.toReal_one, mul_one,
    ← abs_of_nonneg (show 0 ≤ ‖a‖ ^ 2 * τ.im by positivity), ← abs_neg (_ * _)]
  congr 1
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply, L', Complex.sq_norm, Complex.normSq_apply]
  ring

noncomputable def latticeLogPeriod (L : PeriodPair) : ℝ :=
  Real.log (ZLattice.covolume L.lattice / π) + Real.log ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖ / 6

/- English proof (translation)
Establish `h1` using `norm_ne_zero_iff.2 (ModularForm.eta_ne_zero τ.2)`. Establish `h2` using `norm_ne_zero_iff.2 ha`. Rewrite using `[← latticeCurve_Δ, latticeCurve_Δ_eq_discriminant ha h, ModularForm.discriminant, norm_mul, norm_pow, norm_pow, norm_div, show ‖(2 * π : ℂ)‖ = 2 * π by simp [Real.pi_pos.le], Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_div (by positivity) h2 …`. Evaluate the numerical expressions.
-/
theorem log_norm_lattice_discriminant {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    Real.log ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖ = 12 * (Real.log (2 * π) - Real.log ‖a‖)
      + 24 * Real.log ‖ModularForm.eta τ‖ := by
  have h1 := norm_ne_zero_iff.2 (ModularForm.eta_ne_zero τ.2)
  have h2 := norm_ne_zero_iff.2 ha
  rw [← latticeCurve_Δ, latticeCurve_Δ_eq_discriminant ha h, ModularForm.discriminant, norm_mul,
    norm_pow, norm_pow, norm_div, show ‖(2 * π : ℂ)‖ = 2 * π by simp [Real.pi_pos.le],
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_div (by positivity) h2]
  norm_num

/- English proof (translation)
Establish `h1` using `norm_ne_zero_iff.2 (ModularForm.eta_ne_zero τ.2)`. Establish `h2` using `norm_ne_zero_iff.2 ha`. Establish `hy` using `τ.im_pos`. Rewrite using `[latticeLogPeriod, covolume_lattice_eq ha h, log_norm_lattice_discriminant ha h, show (4 : ℝ) = 2 ^ 2 by norm_num]`. Simplify using `(disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem latticeLogPeriod_eq {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    latticeLogPeriod L = Real.log (4 * π * τ.im * ‖ModularForm.eta τ‖ ^ 4) := by
  have h1 := norm_ne_zero_iff.2 (ModularForm.eta_ne_zero τ.2)
  have h2 := norm_ne_zero_iff.2 ha
  have hy := τ.im_pos
  rw [latticeLogPeriod, covolume_lattice_eq ha h, log_norm_lattice_discriminant ha h,
    show (4 : ℝ) = 2 ^ 2 by norm_num]
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow]
  push_cast
  ring

section

variable [NeZero d] (h2 : finrank ℚ K = 2) (hD : discr K = -d) (hd : 4 < d)
  {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ) (σ : K →+* ℂ)
include h2 hD hd hχ

include σ in

/- English proof (translation)
Use `choose τ hτ using exists_isIdealClassPoint h2 hD σ`. Conclude with `(LFunction_one_and_mean_log_eta h2 hD hd hχ σ hτ).1`.
-/
theorem LFunction_one_eq_classNumber : χ.LFunction 1 = (π * classNumber K / √d : ℝ) := by
  choose τ hτ using exists_isIdealClassPoint h2 hD σ
  exact (LFunction_one_and_mean_log_eta h2 hD hd hχ σ hτ).1

/- English proof (translation)
Establish `h` using `(LFunction_one_and_mean_log_eta h2 hD hd hχ σ hτ).2`. Establish `hd0` using `discr_pos h2 hD`. Establish `hh : (0 : ℝ) < classNumber K` using `by exact_mod_cast classNumber_pos K`. Establish `e : ∀ c, Real.log (4 * π * (τ c).im * ‖ModularForm.eta (τ c)‖ ^ 4) = Real.log (4 * π) + Real.log ((τ c).im * ‖ModularForm.eta (τ c)‖ ^ 4)` using `fun c => by`. Establish `h1` using `norm_ne_zero_iff.2 (ModularForm.eta_ne_zero (τ c).2)`.

Establish `hy` using `(τ c).im_pos`. Rewrite using `[mul_assoc, Real.log_mul (by positivity) (by positivity)]`. Establish `e2 : Real.log (2 * π / √d) = Real.log (4 * π) - Real.log (2 * √d)`. Rewrite using `[← Real.log_div (by positivity) (by positivity)]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Evaluate the numerical expressions. Simplify using `only [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[add_div, show (Fintype.card (ClassGroup (𝓞 K)) : ℝ) = classNumber K from rfl, mul_div_cancel_left₀ _ hh.ne', Complex.ofReal_add, h, e2]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem chowla_selberg_eta {τ : ClassGroup (𝓞 K) → ℍ} (hτ : ∀ c, IsIdealClassPoint σ c (τ c)) :
    (((∑ c, Real.log (4 * π * (τ c).im * ‖ModularForm.eta (τ c)‖ ^ 4)) / classNumber K : ℝ) : ℂ)
      = (Real.eulerMascheroniConstant + Real.log (2 * π / √d) : ℝ)
        - deriv χ.LFunction 1 / χ.LFunction 1 := by
  have h := (LFunction_one_and_mean_log_eta h2 hD hd hχ σ hτ).2
  have hd0 := discr_pos h2 hD
  have hh : (0 : ℝ) < classNumber K := by exact_mod_cast classNumber_pos K
  have e : ∀ c, Real.log (4 * π * (τ c).im * ‖ModularForm.eta (τ c)‖ ^ 4)
      = Real.log (4 * π) + Real.log ((τ c).im * ‖ModularForm.eta (τ c)‖ ^ 4) := fun c => by
    have h1 := norm_ne_zero_iff.2 (ModularForm.eta_ne_zero (τ c).2)
    have hy := (τ c).im_pos
    rw [mul_assoc, Real.log_mul (by positivity) (by positivity)]
  have e2 : Real.log (2 * π / √d) = Real.log (4 * π) - Real.log (2 * √d) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
    norm_num
  simp only [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [add_div, show (Fintype.card (ClassGroup (𝓞 K)) : ℝ) = classNumber K from rfl,
    mul_div_cancel_left₀ _ hh.ne', Complex.ofReal_add, h, e2]
  push_cast
  ring

variable {𝔞 : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ}
  (h𝔞 : ∀ c, ClassGroup.mk K (𝔞 c) = c) {L : ClassGroup (𝓞 K) → PeriodPair}
  (hL : ∀ c, ((L c).lattice : Set ℂ) = σ '' (𝔞 c).1)
include h𝔞 hL

/- English proof (translation)
Use `choose a τ ha h using fun c => exists_lattice_eq_mul_tau (L c)`. Simplify using `only [fun c => latticeLogPeriod_eq (ha c) (h c)]`. Conclude with `chowla_selberg_eta h2 hD hd hχ σ fun c => ⟨𝔞 c, a c, h𝔞 c, fun z => by rw [← hL, SetLike.mem_coe, h]⟩`.
-/
theorem chowla_selberg_lattice :
    (((∑ c, latticeLogPeriod (L c)) / classNumber K : ℝ) : ℂ)
      = (Real.eulerMascheroniConstant + Real.log (2 * π / √d) : ℝ)
        - deriv χ.LFunction 1 / χ.LFunction 1 := by
  choose a τ ha h using fun c => exists_lattice_eq_mul_tau (L c)
  simp only [fun c => latticeLogPeriod_eq (ha c) (h c)]
  exact chowla_selberg_eta h2 hD hd hχ σ fun c =>
    ⟨𝔞 c, a c, h𝔞 c, fun z => by rw [← hL, SetLike.mem_coe, h]⟩

/- English proof (translation)
Establish `h0` using `chowla_selberg_lattice h2 hD hd hχ σ h𝔞 hL`. Establish `hd0` using `discr_pos h2 hD`. Establish `hh : (0 : ℝ) < classNumber K` using `by exact_mod_cast classNumber_pos K`. Establish `e : ∀ c, Real.log ((absNorm (𝔞 c).1 : ℝ) ^ 6 * ‖(L c).g₂ ^ 3 - 27 * (L c).g₃ ^ 2‖) = 6 * Real.log (2 * π / √d) + 6 * latticeLogPeriod (L c)` using `fun c => by`. Take `⟨a, τ, ha, h⟩` from `exists_lattice_eq_mul_tau (L c)`.

Establish `h1` using `norm_ne_zero_iff.2 (latticeCurve_Δ_ne_zero (L c))`. Establish `h3` using `norm_ne_zero_iff.2 ha`. Establish `hy` using `τ.im_pos`. Rewrite `h1` using `[latticeCurve_Δ]`. Rewrite using `[latticeLogPeriod, covolume_lattice_eq ha h, absNorm_eq_of_image h2 hD σ ha (τ := τ) fun z => by rw [← hL, SetLike.mem_coe, h]]`.

Simplify using `(disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : Real.log (2 * π / √d) = Real.log (2 * π) - Real.log d / 2`. Rewrite using `[Real.log_div (by positivity) (by positivity), Real.log_sqrt hd0.le]`.

Simplify using `only [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]`. Rewrite using `[add_div, show (Fintype.card (ClassGroup (𝓞 K)) : ℝ) = classNumber K from rfl, mul_div_cancel_left₀ _ hh.ne', mul_div_assoc 6, Complex.ofReal_add, Complex.ofReal_mul 6 (_ / _), h0, e2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chowla_selberg_discriminant :
    (((∑ c, Real.log ((absNorm (𝔞 c).1 : ℝ) ^ 6 * ‖(L c).g₂ ^ 3 - 27 * (L c).g₃ ^ 2‖))
        / classNumber K : ℝ) : ℂ)
      = (12 * Real.log (2 * π) - 6 * Real.log d + 6 * Real.eulerMascheroniConstant : ℝ)
        - 6 * (deriv χ.LFunction 1 / χ.LFunction 1) := by
  have h0 := chowla_selberg_lattice h2 hD hd hχ σ h𝔞 hL
  have hd0 := discr_pos h2 hD
  have hh : (0 : ℝ) < classNumber K := by exact_mod_cast classNumber_pos K
  have e : ∀ c, Real.log ((absNorm (𝔞 c).1 : ℝ) ^ 6 * ‖(L c).g₂ ^ 3 - 27 * (L c).g₃ ^ 2‖)
      = 6 * Real.log (2 * π / √d) + 6 * latticeLogPeriod (L c) := fun c => by
    obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau (L c)
    have h1 := norm_ne_zero_iff.2 (latticeCurve_Δ_ne_zero (L c))
    have h3 := norm_ne_zero_iff.2 ha
    have hy := τ.im_pos
    rw [latticeCurve_Δ] at h1
    rw [latticeLogPeriod, covolume_lattice_eq ha h, absNorm_eq_of_image h2 hD σ ha
      (τ := τ) fun z => by rw [← hL, SetLike.mem_coe, h]]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow]
    push_cast
    ring
  have e2 : Real.log (2 * π / √d) = Real.log (2 * π) - Real.log d / 2 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_sqrt hd0.le]
  simp only [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum]
  rw [add_div, show (Fintype.card (ClassGroup (𝓞 K)) : ℝ) = classNumber K from rfl,
    mul_div_cancel_left₀ _ hh.ne', mul_div_assoc 6, Complex.ofReal_add, Complex.ofReal_mul 6 (_ / _),
    h0, e2]
  push_cast
  ring

end

/- English proof (translation)
Take `⟨k, rfl⟩ : ∃ k, d = 4 * k + 3` from `⟨d / 4, by omega⟩`. Establish `hw : ((1 + r) / 2) ^ 2 - (1 + r) / 2 + (k + 1) = 0`. Move the coercions through the operations in `at hr`. Take the linear combination `hr / 4`. Establish `hi : IsIntegral ℤ ((1 + r) / 2)` using `⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k + 1 : ℤ), by monicity!, by simpa using hw⟩`.

Set `w : 𝓞 K` to `⟨_, hi⟩`. Establish `hw' : w ^ 2 - w + (k + 1) = 0` using `RingOfIntegers.coe_injective (by`. Simplify using `only [map_add, map_sub, map_pow, map_natCast, map_one, map_zero]`. Conclude with `hw)`. Take `⟨b, t, n, h0, hb, hD⟩` from `exists_basis h2`.

Establish `e` using `eq_coord b h0 w`. Generalize the expression as in `b.repr w 0 = x, b.repr w 1 = y at e`. Establish `e1` using `repr_coord b h0 (x ^ 2 - y ^ 2 * n - x + (k + 1)) (2 * x * y + y ^ 2 * t - y)`. Rewrite using `[show ((x ^ 2 - y ^ 2 * n - x + (k + 1) : ℤ) : 𝓞 K) + (2 * x * y + y ^ 2 * t - y : ℤ) * b 1 = 0 by`. Rewrite `hw'` using `[e]`.

Use `push_cast`. Take the linear combination `hw' - (y : 𝓞 K) ^ 2 * hb] at e1`. Simplify using `only [map_zero, Finsupp.zero_apply] at e1`. Take `⟨e1, e2⟩` from `e1`. Establish `hy : y ≠ 0`.

Introduce and unpack `rfl`. Use polynomial arithmetic with `[sq_nonneg (2 * x - 1), Int.natCast_nonneg k]`. Establish `e3 : 2 * x + y * t - 1 = 0` using `mul_left_cancel₀ hy (by linear_combination -e2)`. Establish `e4 : y * y * discr K = -(4 * k + 3 : ℕ)`. Rewrite using `[hD]`.

Use `push_cast`. Take the linear combination `(y * t - 2 * x + 1) * e3 - 4 * e1`. Establish `hu : IsUnit y` using `(Int.squarefree_natCast.2 hsq) y ⟨-discr K, by linear_combination e4⟩`. Apply the tactic sequence `rcases Int.isUnit_iff.1 hu with rfl | rfl <;> simpa using e4`.
-/
theorem discr_eq_neg_of_sq_eq (h2 : finrank ℚ K = 2) (hsq : Squarefree d) (hd : d % 4 = 3)
    {r : K} (hr : r ^ 2 = -d) : discr K = -d := by
  obtain ⟨k, rfl⟩ : ∃ k, d = 4 * k + 3 := ⟨d / 4, by omega⟩
  have hw : ((1 + r) / 2) ^ 2 - (1 + r) / 2 + (k + 1) = 0 := by
    push_cast at hr
    linear_combination hr / 4
  have hi : IsIntegral ℤ ((1 + r) / 2) :=
    ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k + 1 : ℤ), by monicity!, by simpa using hw⟩
  let w : 𝓞 K := ⟨_, hi⟩
  have hw' : w ^ 2 - w + (k + 1) = 0 := RingOfIntegers.coe_injective (by
    simp only [map_add, map_sub, map_pow, map_natCast, map_one, map_zero]
    exact hw)
  obtain ⟨b, t, n, h0, hb, hD⟩ := exists_basis h2
  have e := eq_coord b h0 w
  generalize b.repr w 0 = x, b.repr w 1 = y at e
  have e1 := repr_coord b h0 (x ^ 2 - y ^ 2 * n - x + (k + 1)) (2 * x * y + y ^ 2 * t - y)
  rw [show ((x ^ 2 - y ^ 2 * n - x + (k + 1) : ℤ) : 𝓞 K) + (2 * x * y + y ^ 2 * t - y : ℤ) * b 1
    = 0 by
      rw [e] at hw'
      push_cast
      linear_combination hw' - (y : 𝓞 K) ^ 2 * hb] at e1
  simp only [map_zero, Finsupp.zero_apply] at e1
  obtain ⟨e1, e2⟩ := e1
  have hy : y ≠ 0 := by
    rintro rfl
    nlinarith [sq_nonneg (2 * x - 1), Int.natCast_nonneg k]
  have e3 : 2 * x + y * t - 1 = 0 := mul_left_cancel₀ hy (by linear_combination -e2)
  have e4 : y * y * discr K = -(4 * k + 3 : ℕ) := by
    rw [hD]
    push_cast
    linear_combination (y * t - 2 * x + 1) * e3 - 4 * e1
  have hu : IsUnit y := (Int.squarefree_natCast.2 hsq) y ⟨-discr K, by linear_combination e4⟩
  rcases Int.isUnit_iff.1 hu with rfl | rfl <;> simpa using e4

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ hs => dedekindZeta_eq_mul_LFunction h2 hD hχ hs, LFunction_one_eq_classNumber h2 hD hd hχ σ, fun _ hτ => chowla_selberg_eta h2 hD hd hχ σ hτ, fun _ _ h𝔞 hL => ⟨chowla_selberg_lattice h2 hD hd hχ σ h𝔞 hL, chowla_selberg_discriminant h2 hD hd hχ σ h𝔞 hL⟩⟩`.
-/
theorem chowla_selberg [NeZero d] (h2 : finrank ℚ K = 2) (hD : discr K = -d) (hd : 4 < d)
    {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ) (σ : K →+* ℂ) :
    (∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s) ∧
    χ.LFunction 1 = (π * classNumber K / √d : ℝ) ∧
    (∀ τ : ClassGroup (𝓞 K) → ℍ, (∀ c, IsIdealClassPoint σ c (τ c)) →
      (((∑ c, Real.log (4 * π * (τ c).im * ‖ModularForm.eta (τ c)‖ ^ 4)) / classNumber K : ℝ) : ℂ)
        = (Real.eulerMascheroniConstant + Real.log (2 * π / √d) : ℝ)
          - deriv χ.LFunction 1 / χ.LFunction 1) ∧
    ∀ (𝔞 : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : ClassGroup (𝓞 K) → PeriodPair),
      (∀ c, ClassGroup.mk K (𝔞 c) = c) → (∀ c, ((L c).lattice : Set ℂ) = σ '' (𝔞 c).1) →
      (((∑ c, latticeLogPeriod (L c)) / classNumber K : ℝ) : ℂ)
        = (Real.eulerMascheroniConstant + Real.log (2 * π / √d) : ℝ)
          - deriv χ.LFunction 1 / χ.LFunction 1 ∧
      (((∑ c, Real.log ((absNorm (𝔞 c).1 : ℝ) ^ 6 * ‖(L c).g₂ ^ 3 - 27 * (L c).g₃ ^ 2‖))
          / classNumber K : ℝ) : ℂ)
        = (12 * Real.log (2 * π) - 6 * Real.log d + 6 * Real.eulerMascheroniConstant : ℝ)
          - 6 * (deriv χ.LFunction 1 / χ.LFunction 1) :=
  ⟨fun _ hs => dedekindZeta_eq_mul_LFunction h2 hD hχ hs,
    LFunction_one_eq_classNumber h2 hD hd hχ σ,
    fun _ hτ => chowla_selberg_eta h2 hD hd hχ σ hτ,
    fun _ _ h𝔞 hL => ⟨chowla_selberg_lattice h2 hD hd hχ σ h𝔞 hL,
      chowla_selberg_discriminant h2 hD hd hχ σ h𝔞 hL⟩⟩

/- English proof (translation)
Set `r : ℂ` to `√7 * Complex.I`. Establish `hr : r ^ 2 = -7`. Rewrite using `[mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]`. Simplify using the standard rewrite rules. Establish `hm : (Polynomial.X ^ 2 + Polynomial.C 7 : Polynomial ℚ).Monic` using `by monicity!`.

Establish `he : Polynomial.aeval r (Polynomial.X ^ 2 + Polynomial.C 7 : Polynomial ℚ) = 0`. Simplify using `[hr]`. Establish `hi : IsIntegral ℚ r` using `⟨_, hm, he⟩`. Establish `hfin` using `IntermediateField.adjoin.finiteDimensional hi`. Establish `hK : NumberField (IntermediateField.adjoin ℚ {r})` using `⟨⟩`.

Establish `h2 : finrank ℚ (IntermediateField.adjoin ℚ {r}) = 2`. Rewrite using `[IntermediateField.adjoin.finrank hi]`. Use `le_antisymm ((Polynomial.natDegree_le_natDegree (minpoly.min ℚ r hm he)).trans (by compute_degree)) ((minpoly.two_le_natDegree_iff hi).2 ?_)` and prove the remaining obligations. Introduce and unpack `⟨q, hq⟩`. Use `congrArg Complex.im hq` as an intermediate fact.

Simplify using `[r, eq_comm (a := (0 : ℝ))] at this`. Establish `hD : discr (IntermediateField.adjoin ℚ {r}) = -(7 : ℕ)` using `discr_eq_neg_of_sq_eq h2 (by norm_num : Nat.Prime 7).squarefree rfl (r := IntermediateField.AdjoinSimple.gen ℚ r) (Subtype.ext (by simp [hr]; rfl))`. Take `⟨χ, hχ⟩` from `exists_isKroneckerChar_of_discr h2 hD`. Conclude with `⟨_, hK, χ, h2, hD, hχ⟩`.
-/
theorem exists_field_discr_neg_seven : ∃ (K : IntermediateField ℚ ℂ) (_ : NumberField K)
    (χ : DirichletCharacter ℂ 7), finrank ℚ K = 2 ∧ discr K = -(7 : ℕ) ∧ IsKroneckerChar χ := by
  let r : ℂ := √7 * Complex.I
  have hr : r ^ 2 = -7 := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    simp
  have hm : (Polynomial.X ^ 2 + Polynomial.C 7 : Polynomial ℚ).Monic := by monicity!
  have he : Polynomial.aeval r (Polynomial.X ^ 2 + Polynomial.C 7 : Polynomial ℚ) = 0 := by
    simp [hr]
  have hi : IsIntegral ℚ r := ⟨_, hm, he⟩
  have hfin := IntermediateField.adjoin.finiteDimensional hi
  have hK : NumberField (IntermediateField.adjoin ℚ {r}) := ⟨⟩
  have h2 : finrank ℚ (IntermediateField.adjoin ℚ {r}) = 2 := by
    rw [IntermediateField.adjoin.finrank hi]
    refine le_antisymm ((Polynomial.natDegree_le_natDegree (minpoly.min ℚ r hm he)).trans
      (by compute_degree)) ((minpoly.two_le_natDegree_iff hi).2 ?_)
    rintro ⟨q, hq⟩
    have := congrArg Complex.im hq
    simp [r, eq_comm (a := (0 : ℝ))] at this
  have hD : discr (IntermediateField.adjoin ℚ {r}) = -(7 : ℕ) :=
    discr_eq_neg_of_sq_eq h2 (by norm_num : Nat.Prime 7).squarefree rfl
      (r := IntermediateField.AdjoinSimple.gen ℚ r) (Subtype.ext (by simp [hr]; rfl))
  obtain ⟨χ, hχ⟩ := exists_isKroneckerChar_of_discr h2 hD
  exact ⟨_, hK, χ, h2, hD, hχ⟩

end GlobalTheory
