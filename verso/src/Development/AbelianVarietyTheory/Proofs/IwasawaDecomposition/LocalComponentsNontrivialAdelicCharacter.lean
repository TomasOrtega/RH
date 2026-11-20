import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyRealStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.CharLoc

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Rewrite using `[psiV, psiV, h]`. Use `congrArg ψ₀ (Prod.ext (mul_zero _) ?_)` and prove the remaining obligations. Use `show algebraMap F (Af F) a * singleV F v y = singleV F v _`. Rewrite using `[mul_comm, GlobalTheory.SnMass.Inhab.single_mul, mul_comm]`. Both sides reduce to the same expression.
-/
theorem psiV_twist {ψ₀ ψ : AddChar (AF F) ℂ} {a : F} (h : ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x))
    (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    psiV F ψ v y = psiV F ψ₀ v (algebraMap F (Fv F v) a * y) := by
  rw [psiV, psiV, h]
  refine congrArg ψ₀ (Prod.ext (mul_zero _) ?_)
  show algebraMap F (Af F) a * singleV F v y = singleV F v _
  rw [mul_comm, GlobalTheory.SnMass.Inhab.single_mul, mul_comm]
  rfl

/- English proof (translation)
Rewrite using `[psiInf, psiInf, h]`. Conclude with `congrArg ψ₀ (Prod.ext rfl (mul_zero _))`.
-/
theorem psiInf_twist {ψ₀ ψ : AddChar (AF F) ℂ} {a : F} (h : ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x))
    (y : Ainf F) : psiInf F ψ y = psiInf F ψ₀ (algebraMap F (Ainf F) a * y) := by
  rw [psiInf, psiInf, h]
  exact congrArg ψ₀ (Prod.ext rfl (mul_zero _))

/- English proof (translation)
The claim follows from `(algebraMap F (Af F) a).2`.
-/
theorem eventually_integral (a : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) a).2

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Take `⟨d, hd, hd0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))`. Establish `hd1 : algebraMap F (Fv F v) (d : F) ≠ 0`. Rewrite using `[Ne, map_eq_zero]`.

Conclude with `hd0` after adjusting the coercions. Take `⟨z, hz⟩` from `HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp 1)`. Establish `h1` using `(hs (z * (algebraMap F (Fv F v) (d : F))⁻¹)).1 (fun y _ => hn _) d hd`. Rewrite `h1` using `[inv_mul_cancel_right₀ hd1, HeightOneSpectrum.mem_adicCompletionIntegers, hz, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem ne_one_of_stdAt {v : HeightOneSpectrum (𝓞 F)} {χ : Fv F v → ℂ} (hs : GlobalTheory.SnMass.StdAt v χ) :
    ∃ y, χ y ≠ 1 := by
  by_contra hn
  push Not at hn
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  have hd1 : algebraMap F (Fv F v) (d : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact_mod_cast hd0
  obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp 1)
  have h1 := (hs (z * (algebraMap F (Fv F v) (d : F))⁻¹)).1 (fun y _ => hn _) d hd
  rw [inv_mul_cancel_right₀ hd1, HeightOneSpectrum.mem_adicCompletionIntegers, hz, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at h1
  omega

/- English proof (translation)
Use function extensionality and compare the values at `w`. Assume the negation of the conclusion as `hw`. Establish `hw' : z w ≠ 0` using `hw`. Set `y : Ainf F` to `Pi.single w ((z w)⁻¹ * 2⁻¹)`. Establish `h1` using `hz y`.

Rewrite `h1` using `[h.2.1, Finset.sum_eq_single w]`. Establish `e : (z * y) w = 2⁻¹` using `by show z w * (Pi.single w ((z w)⁻¹ * 2⁻¹) : (v : InfinitePlace F) → v.Completion) w = _`. Rewrite using `[Pi.single_eq_same, mul_inv_cancel_left₀ hw']`. Rewrite `h1` using `[e, map_inv₀, map_ofNat]`. Establish `e2 : 2 * Real.pi * Complex.I * (((2⁻¹ : ℂ).re : ℝ) : ℂ) = Real.pi * Complex.I`.

Establish `: (2⁻¹ : ℂ).re = 2⁻¹` using `by simp`. Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[e2, Complex.exp_pi_mul_I]`.

Evaluate the numerical expressions using `at h1`. Introduce `u _ hu`. Establish `e : (z * y) u = 0` using `by show z u * (Pi.single w ((z w)⁻¹ * 2⁻¹) : (v : InfinitePlace F) → v.Completion) u = _`. Rewrite using `[Pi.single_eq_of_ne hu, mul_zero]`. Rewrite using `[e, map_zero, Complex.zero_re]`.

Introduce `hn`. Conclude with `absurd (Finset.mem_univ w) hn`.
-/
theorem eq_zero_of_std {ψ : AddChar (AF F) ℂ} (h : GlobalTheory.SnMass.IsStdChar F ψ) (z : Ainf F)
    (hz : ∀ y, psiInf F ψ (z * y) = 1) : z = 0 := by
  classical
  funext w
  by_contra hw
  have hw' : z w ≠ 0 := hw
  let y : Ainf F := Pi.single w ((z w)⁻¹ * 2⁻¹)
  have h1 := hz y
  rw [h.2.1, Finset.sum_eq_single w] at h1
  · have e : (z * y) w = 2⁻¹ := by
      show z w * (Pi.single w ((z w)⁻¹ * 2⁻¹) : (v : InfinitePlace F) → v.Completion) w = _
      rw [Pi.single_eq_same, mul_inv_cancel_left₀ hw']
    rw [e, map_inv₀, map_ofNat] at h1
    have e2 : 2 * Real.pi * Complex.I * (((2⁻¹ : ℂ).re : ℝ) : ℂ) = Real.pi * Complex.I := by
      have : (2⁻¹ : ℂ).re = 2⁻¹ := by simp
      rw [this]
      push_cast
      ring
    rw [e2, Complex.exp_pi_mul_I] at h1
    norm_num at h1
  · intro u _ hu
    have e : (z * y) u = 0 := by
      show z u * (Pi.single w ((z w)⁻¹ * 2⁻¹) : (v : InfinitePlace F) → v.Completion) u = _
      rw [Pi.single_eq_of_ne hu, mul_zero]
    rw [e, map_zero, Complex.zero_re]
  · intro hn
    exact absurd (Finset.mem_univ w) hn

/- English proof (translation)
Introduce `F _ _ _ ψ hψ`. Take `⟨ψ₀, h₀⟩` from `GlobalTheory.SnMass.Inhab.exists_isStdChar F`. Take `⟨a, ha, h⟩` from `GlobalTheory.T.exists_ne_zero_adele_char_eq_comp_mul_totally_real F ψ₀ ψ h₀.1 hψ`. Use `⟨fun v => ?_, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `ne_one_of_stdAt (h₀.2.2 v)`.

Use `⟨algebraMap F (Fv F v) a⁻¹ * y, ?_⟩` and prove the remaining obligations. Rewrite using `[psiV_twist h, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]` and apply the resulting hypothesis. Take `⟨d, hd, hd0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))`. Establish `hd1 : (d : F) ≠ 0` using `by exact_mod_cast hd0`. Use `filter_upwards [eventually_integral a, eventually_integral (a * d)⁻¹] with v h1 h2 y`.

Simplify using `only [psiV_twist h, ← mul_assoc]`. Use `(h₀.2.2 v _).trans ⟨fun hy => ?_, fun hy d' _ => ?_⟩` and prove the remaining obligations. Establish `h3` using `mul_mem (hy d hd) h2`. Rewrite `h3` using `[mul_right_comm _ y, ← map_mul, mul_right_comm, ← map_mul, mul_inv_cancel₀ (mul_ne_zero ha hd1), map_one, one_mul]`. Then use the resulting hypothesis. Conclude with `mul_mem (mul_mem h1 hy) (HeightOneSpectrum.coe_mem_adicCompletionIntegers v d')`.

Establish `h1` using `eq_zero_of_std h₀ (algebraMap F (Ainf F) a * x) fun y => by`. Rewrite using `[mul_assoc, ← psiInf_twist h, hx]`. Establish `h2` using `congrArg (algebraMap F (Ainf F) a⁻¹ * ·) h1`. Simplify `h2` using `only [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul, mul_zero]`.
-/
theorem char_local : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∀ v : HeightOneSpectrum (𝓞 F), ∃ y, psiV F ψ v y ≠ 1) ∧ (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ y : Fv F v, (∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (y * t) = 1) ↔ y ∈ v.adicCompletionIntegers F) ∧ ∀ x : Ainf F, (∀ y, psiInf F ψ (x * y) = 1) → x = 0 := by
  intro F _ _ _ ψ hψ
  obtain ⟨ψ₀, h₀⟩ := GlobalTheory.SnMass.Inhab.exists_isStdChar F
  obtain ⟨a, ha, h⟩ := GlobalTheory.T.exists_ne_zero_adele_char_eq_comp_mul_totally_real F ψ₀ ψ h₀.1 hψ
  refine ⟨fun v => ?_, ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := ne_one_of_stdAt (h₀.2.2 v)
    refine ⟨algebraMap F (Fv F v) a⁻¹ * y, ?_⟩
    rwa [psiV_twist h, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
  · obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
    have hd1 : (d : F) ≠ 0 := by exact_mod_cast hd0
    filter_upwards [eventually_integral a, eventually_integral (a * d)⁻¹] with v h1 h2 y
    simp only [psiV_twist h, ← mul_assoc]
    refine (h₀.2.2 v _).trans ⟨fun hy => ?_, fun hy d' _ => ?_⟩
    · have h3 := mul_mem (hy d hd) h2
      rwa [mul_right_comm _ y, ← map_mul, mul_right_comm, ← map_mul, mul_inv_cancel₀ (mul_ne_zero ha hd1),
        map_one, one_mul] at h3
    · exact mul_mem (mul_mem h1 hy) (HeightOneSpectrum.coe_mem_adicCompletionIntegers v d')
  · have h1 := eq_zero_of_std h₀ (algebraMap F (Ainf F) a * x) fun y => by
      rw [mul_assoc, ← psiInf_twist h, hx]
    have h2 := congrArg (algebraMap F (Ainf F) a⁻¹ * ·) h1
    simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul, mul_zero] using h2

end GlobalTheory.GaugeEx.CharLoc
