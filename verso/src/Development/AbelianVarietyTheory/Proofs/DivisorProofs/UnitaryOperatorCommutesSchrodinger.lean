import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFourierEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtThetaSumHeisenbergLine
import GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.AdelicSchur

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `htr : ∀ z : mixedEmbedding.mixedSpace F, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z = (∑ w, z.1 w) + ∑ w, 2 * (z.2 w).re`. Introduce `z`. Rewrite using `[Algebra.trace_prod_apply, GroundTheory.Global.SemiLocal.trace_pi, GroundTheory.Global.SemiLocal.trace_pi]`. Simplify using `[Algebra.trace_self_apply, Algebra.trace_complex_apply]`. Use `Prod.ext (funext fun w => ?_) (funext fun w => ?_)` and prove the remaining obligations.

Establish `h1` using `h (Pi.single w 1, 0)`. Rewrite `h1` using `[htr]`. Simplify `h1` using `[Pi.single_apply]`. Establish `h1` using `h (0, Pi.single w (star (u.2 w)))`. Rewrite `h1` using `[htr]`.

Simplify using `[Pi.single_apply, Complex.star_def] at h1`. Rewrite `h1` using `[Finset.sum_eq_single w (fun v _ hv => by simp [hv]) (by simp)]`. Simplify using `at h1`. Establish `ha : (u.2 w).re = 0` using `by nlinarith [mul_self_nonneg (u.2 w).re, mul_self_nonneg (u.2 w).im]`. Establish `hb : (u.2 w).im = 0` using `by nlinarith [mul_self_nonneg (u.2 w).re, mul_self_nonneg (u.2 w).im]`.

Conclude with `Complex.ext (by simpa using ha) (by simpa using hb)`.
-/
theorem mixed_eq_zero (u : mixedEmbedding.mixedSpace F)
    (h : ∀ s, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (u * s) = 0) : u = 0 := by
  classical
  have htr : ∀ z : mixedEmbedding.mixedSpace F, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z =
      (∑ w, z.1 w) + ∑ w, 2 * (z.2 w).re := by
    intro z
    rw [Algebra.trace_prod_apply, GroundTheory.Global.SemiLocal.trace_pi, GroundTheory.Global.SemiLocal.trace_pi]
    simp [Algebra.trace_self_apply, Algebra.trace_complex_apply]
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · have h1 := h (Pi.single w 1, 0)
    rw [htr] at h1
    simpa [Pi.single_apply] using h1
  · have h1 := h (0, Pi.single w (star (u.2 w)))
    rw [htr] at h1
    simp [Pi.single_apply, Complex.star_def] at h1
    rw [Finset.sum_eq_single w (fun v _ hv => by simp [hv]) (by simp)] at h1
    simp at h1
    have ha : (u.2 w).re = 0 := by nlinarith [mul_self_nonneg (u.2 w).re, mul_self_nonneg (u.2 w).im]
    have hb : (u.2 w).im = 0 := by nlinarith [mul_self_nonneg (u.2 w).re, mul_self_nonneg (u.2 w).im]
    exact Complex.ext (by simpa using ha) (by simpa using hb)

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, evalV F v a ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `ha (af_ext fun u => by rw [h u, map_zero])`. Take `⟨t, ht⟩` from `hψ v`.

Use `⟨singleFin v (t / evalV F v a), ?_⟩` and prove the remaining obligations. Establish `e : a * singleFin v (t / evalV F v a) = singleFin v t`. Apply `af_ext` to reduce the goal to its premises. Introduce `u`. Rewrite using `[map_mul]`.

Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality. Rewrite using `[evalV_singleFin_self, evalV_singleFin_self]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[evalV_singleFin_ne hu, evalV_singleFin_ne hu, mul_zero]`.

Rewrite using `[e]`. Conclude with `ht`.
-/
theorem fin_exists_ne_one (ψ : AddChar (AF F) ℂ) (hψ : ∀ w : Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) {a : Af F}
    (ha : a ≠ 0) : ∃ b : Af F, GlobalTheory.HeisSchA.finChar ψ (a * b) ≠ 1 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, evalV F v a ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha (af_ext fun u => by rw [h u, map_zero])
  obtain ⟨t, ht⟩ := hψ v
  refine ⟨singleFin v (t / evalV F v a), ?_⟩
  have e : a * singleFin v (t / evalV F v a) = singleFin v t := by
    apply af_ext
    intro u
    rw [map_mul]
    by_cases hu : u = v
    · subst hu
      rw [evalV_singleFin_self, evalV_singleFin_self]
      field_simp
    · rw [evalV_singleFin_ne hu, evalV_singleFin_ne hu, mul_zero]
  rw [e]
  exact ht

/- English proof (translation)
Establish `hone : ∀ i (c : AF F), ψ (x i * c) = 1` using `fun i c => by`. Use `hx (Pi.single i c)` as an intermediate fact. Rewrite `this` using `[dotProduct_single]`. Then use the resulting hypothesis. Use function extensionality and compare the values at `i`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Use `show (x i).1 = 0`. Apply `(InfiniteAdeleRing.ringEquiv_mixedSpace F).injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Apply `mixed_eq_zero` to reduce the goal to its premises. Introduce `s`.

Assume the negation of the conclusion as `hT`. Use `set e := InfiniteAdeleRing.ringEquiv_mixedSpace F`. Use `set T := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (e (x i).1 * s) with hTdef`. Establish `h1` using `hone i (GlobalTheory.HeisSchA.mk (e.symm (((2 * T)⁻¹ : ℝ) • s)) 0)`. Establish `hmul : x i * GlobalTheory.HeisSchA.mk (e.symm (((2 * T)⁻¹ : ℝ) • s)) 0 = GlobalTheory.HeisSchA.mk ((x i).1 * e.symm (((2 * T)⁻¹ : ℝ) • s)) 0` using `Prod.ext rfl (mul_zero _)`.

Rewrite `h1` using `[hmul, hψ.2.2 _ (GlobalTheory.HeisSchA.at_mk _)]`. Establish `htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (GlobalTheory.HeisSchA.mk ((x i).1 * e.symm (((2 * T)⁻¹ : ℝ) • s)) 0)) = 1 / 2` using `by show Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (e ((x i).1 * e.symm (((2 * T)⁻¹ : ℝ) • s))) = 1 / 2`. Rewrite using `[map_mul, RingEquiv.apply_symm_apply, mul_smul_comm, map_smul, ← hTdef, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite `h1` using `[htr]`.

Establish `h2 : -(2 * (Real.pi : ℂ) * Complex.I) * (((1 / 2 : ℝ)) : ℂ) = -((Real.pi : ℂ) * Complex.I)` using `by push_cast; ring`. Rewrite `h1` using `[h2, Complex.exp_neg, Complex.exp_pi_mul_I]`. Evaluate the numerical expressions using `at h1`. Use `show (x i).2 = 0`. Assume the negation of the conclusion as `hb`.

Take `⟨b, hb'⟩` from `fin_exists_ne_one ψ (GlobalTheory.PsiNontrivAt.exists_psiAt_ne_one ψ hψ) hb`. Apply `hb'` to reduce the goal to its premises. Rewrite using `[GlobalTheory.HeisSchA.finChar_apply]`. Use `hone i (GlobalTheory.HeisSchA.mk 0 b)` as an intermediate fact. Establish `hmul : x i * GlobalTheory.HeisSchA.mk 0 b = GlobalTheory.HeisSchA.mk 0 ((x i).2 * b)` using `Prod.ext (mul_zero _) rfl`.

Rewrite `this` using `[hmul]`. Then use the resulting hypothesis.
-/
theorem sep {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (x : κ → AF F)
    (hx : ∀ y : κ → AF F, ψ (x ⬝ᵥ y) = 1) : x = 0 := by
  classical
  have hone : ∀ i (c : AF F), ψ (x i * c) = 1 := fun i c => by
    have := hx (Pi.single i c)
    rwa [dotProduct_single] at this
  funext i
  refine Prod.ext ?_ ?_
  · show (x i).1 = 0
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
    rw [map_zero]
    apply mixed_eq_zero
    intro s
    by_contra hT
    set e := InfiniteAdeleRing.ringEquiv_mixedSpace F
    set T := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (e (x i).1 * s) with hTdef
    have h1 := hone i (GlobalTheory.HeisSchA.mk (e.symm (((2 * T)⁻¹ : ℝ) • s)) 0)
    have hmul : x i * GlobalTheory.HeisSchA.mk (e.symm (((2 * T)⁻¹ : ℝ) • s)) 0 =
        GlobalTheory.HeisSchA.mk ((x i).1 * e.symm (((2 * T)⁻¹ : ℝ) • s)) 0 :=
      Prod.ext rfl (mul_zero _)
    rw [hmul, hψ.2.2 _ (GlobalTheory.HeisSchA.at_mk _)] at h1
    have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (GlobalTheory.HeisSchA.mk ((x i).1 * e.symm (((2 * T)⁻¹ : ℝ) • s)) 0)) = 1 / 2 := by
      show Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (e ((x i).1 * e.symm (((2 * T)⁻¹ : ℝ) • s))) = 1 / 2
      rw [map_mul, RingEquiv.apply_symm_apply, mul_smul_comm, map_smul, ← hTdef, smul_eq_mul]
      field_simp
    rw [htr] at h1
    have h2 : -(2 * (Real.pi : ℂ) * Complex.I) * (((1 / 2 : ℝ)) : ℂ) = -((Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [h2, Complex.exp_neg, Complex.exp_pi_mul_I] at h1
    norm_num at h1
  · show (x i).2 = 0
    by_contra hb
    obtain ⟨b, hb'⟩ := fin_exists_ne_one ψ (GlobalTheory.PsiNontrivAt.exists_psiAt_ne_one ψ hψ) hb
    apply hb'
    rw [GlobalTheory.HeisSchA.finChar_apply]
    have := hone i (GlobalTheory.HeisSchA.mk 0 b)
    have hmul : x i * GlobalTheory.HeisSchA.mk 0 b = GlobalTheory.HeisSchA.mk 0 ((x i).2 * b) :=
      Prod.ext (mul_zero _) rfl
    rwa [hmul] at this

end GlobalTheory.AdelicSchur

namespace GlobalTheory.AdelicSchur

/- English proof (translation)
Establish `hs : ∀ c : ℂ, Complex.normSq (A + c * B) = Complex.normSq (A' + c * B')` using `fun c => by`. Rewrite using `[Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h c]`. Establish `h1` using `hs 1`. Establish `h2` using `hs (-1)`. Establish `h3` using `hs Complex.I`.

Establish `h4` using `hs (-Complex.I)`. Simplify using `only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at h1 h2 h3 h4`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]`. Take the linear combination `(h1 - h2) / 4`.

Simplify using `only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]`. Take the linear combination `(h4 - h3) / 4`.
-/
theorem conj_mul_eq {A B A' B' : ℂ} (h : ∀ c : ℂ, ‖A + c * B‖ = ‖A' + c * B'‖) :
    star A * B = star A' * B' := by
  have hs : ∀ c : ℂ, Complex.normSq (A + c * B) = Complex.normSq (A' + c * B') := fun c => by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h c]
  have h1 := hs 1
  have h2 := hs (-1)
  have h3 := hs Complex.I
  have h4 := hs (-Complex.I)
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at h1 h2 h3 h4
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    linear_combination (h1 - h2) / 4
  · simp only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    linear_combination (h4 - h3) / 4

/- English proof (translation)
Establish `hz' : z.re * z.re + z.im * z.im = 1`. Rewrite using `[← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz, one_pow]`. Rewrite using `[← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]`. Simplify using `only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im]`. Take the linear combination `(c.re * c.re + c.im * c.im) * hz'`.
-/
theorem norm_one_add_sq (c z : ℂ) (hz : ‖z‖ = 1) : ‖1 + c * z‖ ^ 2 = 1 + ‖c‖ ^ 2 + 2 * (c * z).re := by
  have hz' : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz, one_pow]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im]
  linear_combination (c.re * c.re + c.im * c.im) * hz'

/- English proof (translation)
Introduce `_ F _ _ κ _ ψ hψ M hpres hcomm hiso`. Use `letI : MeasurableSpace (κ → AF F) := borel _`. Use `haveI : BorelSpace (κ → AF F) := ⟨rfl⟩`. Use `haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Set `μ : Measure (κ → AF F)` to `Measure.addHaar`.

Use `haveI hμH : μ.IsAddHaarMeasure := by dsimp [μ]; infer_instance`. Establish `hL2 : ∀ φ ∈ schA F κ, MemLp φ 2 μ` using `fun φ hφ => GlobalTheory.WeilM.schA_memLp_two F κ μ hμH φ hφ`. Establish `hint : ∀ φ ∈ schA F κ, Integrable (fun x => ‖φ x‖ ^ 2) μ` using `fun φ hφ => (hL2 φ hφ).integrable_norm_pow two_ne_zero`. Establish `hnorm : ∀ φ ∈ schA F κ, ∫ x, ‖M φ x‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ`. Introduce `φ hφ`.

Establish `h` using `hiso μ hμH φ hφ`. Establish `e : ∀ g ∈ schA F κ, ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂μ)` using `fun g hg => by`. Rewrite using `[ofReal_integral_eq_lintegral_ofReal (hint g hg) (Filter.Eventually.of_forall fun x => by positivity)]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]`. Rewrite `h` using `[e _ (hpres φ hφ), e φ hφ]`. Conclude with `(ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => by positivity) (integral_nonneg fun x => by positivity)).1 h`. Establish `hψn : ∀ a, ‖ψ a‖ = 1` using `GlobalTheory.HeisLineTheta.norm_psi hψ`. Establish `hcy : ∀ y : κ → AF F, Continuous fun x : κ → AF F => ψ (x ⬝ᵥ y)` using `fun y => hψ.1.comp (continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const)`.

Establish `hschr0 : ∀ (y : κ → AF F) (f : (κ → AF F) → ℂ) x, schr ψ (0, y) f x = ψ (x ⬝ᵥ y) * f x`. Introduce `y f x`. Simplify using `[schr]`. Establish `hdiag : ∀ φ ∈ schA F κ, ∀ x, ‖M φ x‖ = ‖φ x‖`. Introduce `φ hφ`.

Establish `hMφ` using `hpres φ hφ`. Use `set D : (κ → AF F) → ℝ := fun x => ‖M φ x‖ ^ 2 - ‖φ x‖ ^ 2 with hD`. Establish `hDi : Integrable D μ` using `(hint _ hMφ).sub (hint φ hφ)`. Establish `hDc : Continuous D` using `((GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hMφ).norm.pow 2).sub ((GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hφ).norm.pow 2)`. Establish `hbi : ∀ (y : κ → AF F) (c : ℂ) (f : (κ → AF F) → ℂ), f ∈ schA F κ → Integrable (fun x => (c * ψ (x ⬝ᵥ y)).re * ‖f x‖ ^ 2) μ` using `fun y c f hf => (hint f hf).bdd_mul (Complex.continuous_re.comp (continuous_const.mul (hcy y))).aestronglyMeasurable (Filter.Eventually.of_forall fun x => by`.

Rewrite using `[Real.norm_eq_abs]`. Use `(Complex.abs_re_le_norm _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul, hψn, mul_one])`. Establish `hre : ∀ (y : κ → AF F) (c : ℂ), ∫ x, (c * ψ (x ⬝ᵥ y)).re * D x ∂μ = 0`. Introduce `y c`.

Establish `hg : φ + c • schr ψ (0, y) φ ∈ schA F κ` using `(schA F κ).add_mem hφ ((schA F κ).smul_mem c (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ))`. Establish `hMg : M (φ + c • schr ψ (0, y) φ) = M φ + c • schr ψ (0, y) (M φ)`. Rewrite using `[map_add, map_smul, hcomm _ φ hφ]`. Establish `h1` using `hnorm _ hg`. Rewrite `h1` using `[hMg]`.

Establish `hpt : ∀ f : (κ → AF F) → ℂ, (fun x => ‖(f + c • schr ψ (0, y) f) x‖ ^ 2) = fun x => (1 + ‖c‖ ^ 2) * ‖f x‖ ^ 2 + 2 * ((c * ψ (x ⬝ᵥ y)).re * ‖f x‖ ^ 2)`. Introduce `f`. Use function extensionality and compare the values at `x`. Rewrite using `[Pi.add_apply, Pi.smul_apply, hschr0, smul_eq_mul, show f x + c * (ψ (x ⬝ᵥ y) * f x) = (1 + c * ψ (x ⬝ᵥ y)) * f x by ring, norm_mul, mul_pow, norm_one_add_sq c _ (hψn _)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h1` using `[hpt, hpt, integral_add ((hint _ hMφ).const_mul _) ((hbi y c _ hMφ).const_mul _), integral_add ((hint _ hφ).const_mul _) ((hbi y c _ hφ).const_mul _), integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, hnorm φ hφ]`. Establish `h2 : ∫ x, (c * ψ (x ⬝ᵥ y)).re * ‖M φ x‖ ^ 2 ∂μ = ∫ x, (c * ψ (x ⬝ᵥ y)).re * ‖φ x‖ ^ 2 ∂μ`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : (fun x => (c * ψ (x ⬝ᵥ y)).re * D x) = fun x => (c * ψ (x ⬝ᵥ y)).re * ‖M φ x‖ ^ 2 - (c * ψ (x ⬝ᵥ y)).re * ‖φ x‖ ^ 2`. Use function extensionality and compare the values at `x`.

Simplify using `only [hD]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, integral_sub (hbi y c _ hMφ) (hbi y c _ hφ), h2, sub_self]`. Establish `hF : ∀ y : κ → AF F, ∫ x, ψ (x ⬝ᵥ y) * (D x : ℂ) ∂μ = 0`. Introduce `y`.

Establish `hI : Integrable (fun x => ψ (x ⬝ᵥ y) * (D x : ℂ)) μ` using `hDi.ofReal.bdd_mul (hcy y).aestronglyMeasurable (Filter.Eventually.of_forall fun x => (hψn _).le)`. Apply `Complex.ext` to reduce the goal to its premises. Rewrite using `[Complex.zero_re, ← RCLike.re_to_complex, ← integral_re hI]`. Establish `e : (fun x => RCLike.re (ψ (x ⬝ᵥ y) * (D x : ℂ))) = fun x => ((1 : ℂ) * ψ (x ⬝ᵥ y)).re * D x`. Use function extensionality and compare the values at `x`.

Simplify using `[Complex.mul_re]`. Rewrite using `[e]`. Conclude with `hre y 1`. Rewrite using `[Complex.zero_im, ← RCLike.im_to_complex, ← integral_im hI]`. Establish `e : (fun x => RCLike.im (ψ (x ⬝ᵥ y) * (D x : ℂ))) = fun x => ((-Complex.I) * ψ (x ⬝ᵥ y)).re * D x`.

Use function extensionality and compare the values at `x`. Simplify using `[Complex.mul_re, Complex.mul_im]`. Rewrite using `[e]`. Conclude with `hre y (-Complex.I)`. Establish `hD0` using `GlobalTheory.CharFourierInj.real_eq_zero (G := κ → AF F) (A := κ → AF F) (fun y x => ψ (x ⬝ᵥ y)) hcy (fun y x x' => by simp only [add_dotProduct, AddChar.map_add_eq_mul]) (fun y y' x => by simp only [dotProduct_add, AddChar.map_add_eq_mul]) (fun x => by simp only [dotProduct_zero …`.

Introduce `x`. Use `congrFun hD0 x` as an intermediate fact. Simplify using `only [hD, Pi.zero_apply, sub_eq_zero] at this`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this`. Establish `htwo : ∀ φ ∈ schA F κ, ∀ φ' ∈ schA F κ, ∀ x a, star (M φ x) * M φ' (x + a) = star (φ x) * φ' (x + a)`.

Introduce `φ hφ φ' hφ' x a`. Apply `conj_mul_eq` to reduce the goal to its premises. Introduce `c`. Establish `hg : φ + c • schr ψ (a, 0) φ' ∈ schA F κ` using `(schA F κ).add_mem hφ ((schA F κ).smul_mem c (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ' hφ'))`. Establish `h1` using `hdiag _ hg x`.

Rewrite `h1` using `[map_add, map_smul, hcomm _ φ' hφ']`. Simplify `h1` using `[schr]`. Distinguish the cases in `h0 : ∃ φ₀ ∈ schA F κ, ∃ x₀, φ₀ x₀ ≠ 0`. Take `⟨φ₀, hφ₀, x₀, hx₀⟩` from `h0`. Establish `hn1 : ‖M φ₀ x₀‖ = ‖φ₀ x₀‖` using `hdiag φ₀ hφ₀ x₀`.

Establish `hs : star (M φ₀ x₀) ≠ 0`. Rewrite using `[star_ne_zero, ← norm_ne_zero_iff, hn1, norm_ne_zero_iff]`. Conclude with `hx₀`. Use `⟨star (φ₀ x₀) / star (M φ₀ x₀), fun φ hφ => funext fun x => ?_⟩` and prove the remaining obligations. Establish `h2` using `htwo φ₀ hφ₀ φ hφ x₀ (x - x₀)`.

Rewrite `h2` using `[add_sub_cancel]`. Rewrite using `[Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs]`. Conclude with `(mul_comm _ _).trans h2`. Use `push_neg at h0`. Use `⟨0, fun φ hφ => ?_⟩` and prove the remaining obligations.

Establish `: φ = 0` using `funext fun x => h0 φ hφ x`. Rewrite using `[this, map_zero, smul_zero]`.
-/
theorem schur : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ M : Module.End ℂ ((κ → AF F) → ℂ), (∀ φ ∈ schA F κ, M φ ∈ schA F κ) →
    (∀ w : (κ → AF F) × (κ → AF F), ∀ φ ∈ schA F κ, M (schr ψ w φ) = schr ψ w (M φ)) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖M φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∃ z : ℂ, ∀ φ ∈ schA F κ, M φ = z • φ := by
  intro _ F _ _ κ _ ψ hψ M hpres hcomm hiso
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  let μ : Measure (κ → AF F) := Measure.addHaar
  haveI hμH : μ.IsAddHaarMeasure := by dsimp [μ]; infer_instance
  have hL2 : ∀ φ ∈ schA F κ, MemLp φ 2 μ := fun φ hφ =>
    GlobalTheory.WeilM.schA_memLp_two F κ μ hμH φ hφ
  have hint : ∀ φ ∈ schA F κ, Integrable (fun x => ‖φ x‖ ^ 2) μ := fun φ hφ =>
    (hL2 φ hφ).integrable_norm_pow two_ne_zero
  have hnorm : ∀ φ ∈ schA F κ, ∫ x, ‖M φ x‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ := by
    intro φ hφ
    have h := hiso μ hμH φ hφ
    have e : ∀ g ∈ schA F κ, ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂μ) := fun g hg => by
      rw [ofReal_integral_eq_lintegral_ofReal (hint g hg) (Filter.Eventually.of_forall fun x => by positivity)]
      congr 1
      funext x
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rw [e _ (hpres φ hφ), e φ hφ] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => by positivity)
      (integral_nonneg fun x => by positivity)).1 h
  have hψn : ∀ a, ‖ψ a‖ = 1 := GlobalTheory.HeisLineTheta.norm_psi hψ
  have hcy : ∀ y : κ → AF F, Continuous fun x : κ → AF F => ψ (x ⬝ᵥ y) := fun y =>
    hψ.1.comp (continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const)
  have hschr0 : ∀ (y : κ → AF F) (f : (κ → AF F) → ℂ) x, schr ψ (0, y) f x = ψ (x ⬝ᵥ y) * f x := by
    intro y f x
    simp [schr]
  have hdiag : ∀ φ ∈ schA F κ, ∀ x, ‖M φ x‖ = ‖φ x‖ := by
    intro φ hφ
    have hMφ := hpres φ hφ
    set D : (κ → AF F) → ℝ := fun x => ‖M φ x‖ ^ 2 - ‖φ x‖ ^ 2 with hD
    have hDi : Integrable D μ := (hint _ hMφ).sub (hint φ hφ)
    have hDc : Continuous D :=
      ((GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hMφ).norm.pow 2).sub
        ((GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hφ).norm.pow 2)
    have hbi : ∀ (y : κ → AF F) (c : ℂ) (f : (κ → AF F) → ℂ), f ∈ schA F κ →
        Integrable (fun x => (c * ψ (x ⬝ᵥ y)).re * ‖f x‖ ^ 2) μ := fun y c f hf =>
      (hint f hf).bdd_mul (Complex.continuous_re.comp (continuous_const.mul (hcy y))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]
          refine (Complex.abs_re_le_norm _).trans ?_
          rw [norm_mul, hψn, mul_one])
    have hre : ∀ (y : κ → AF F) (c : ℂ), ∫ x, (c * ψ (x ⬝ᵥ y)).re * D x ∂μ = 0 := by
      intro y c
      have hg : φ + c • schr ψ (0, y) φ ∈ schA F κ :=
        (schA F κ).add_mem hφ ((schA F κ).smul_mem c (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ))
      have hMg : M (φ + c • schr ψ (0, y) φ) = M φ + c • schr ψ (0, y) (M φ) := by
        rw [map_add, map_smul, hcomm _ φ hφ]
      have h1 := hnorm _ hg
      rw [hMg] at h1
      have hpt : ∀ f : (κ → AF F) → ℂ, (fun x => ‖(f + c • schr ψ (0, y) f) x‖ ^ 2) =
          fun x => (1 + ‖c‖ ^ 2) * ‖f x‖ ^ 2 + 2 * ((c * ψ (x ⬝ᵥ y)).re * ‖f x‖ ^ 2) := by
        intro f
        funext x
        rw [Pi.add_apply, Pi.smul_apply, hschr0, smul_eq_mul,
          show f x + c * (ψ (x ⬝ᵥ y) * f x) = (1 + c * ψ (x ⬝ᵥ y)) * f x by ring, norm_mul, mul_pow,
          norm_one_add_sq c _ (hψn _)]
        ring
      rw [hpt, hpt, integral_add ((hint _ hMφ).const_mul _) ((hbi y c _ hMφ).const_mul _),
        integral_add ((hint _ hφ).const_mul _) ((hbi y c _ hφ).const_mul _),
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, hnorm φ hφ] at h1
      have h2 : ∫ x, (c * ψ (x ⬝ᵥ y)).re * ‖M φ x‖ ^ 2 ∂μ = ∫ x, (c * ψ (x ⬝ᵥ y)).re * ‖φ x‖ ^ 2 ∂μ := by
        linarith
      have e : (fun x => (c * ψ (x ⬝ᵥ y)).re * D x) =
          fun x => (c * ψ (x ⬝ᵥ y)).re * ‖M φ x‖ ^ 2 - (c * ψ (x ⬝ᵥ y)).re * ‖φ x‖ ^ 2 := by
        funext x
        simp only [hD]
        ring
      rw [e, integral_sub (hbi y c _ hMφ) (hbi y c _ hφ), h2, sub_self]
    have hF : ∀ y : κ → AF F, ∫ x, ψ (x ⬝ᵥ y) * (D x : ℂ) ∂μ = 0 := by
      intro y
      have hI : Integrable (fun x => ψ (x ⬝ᵥ y) * (D x : ℂ)) μ :=
        hDi.ofReal.bdd_mul (hcy y).aestronglyMeasurable (Filter.Eventually.of_forall fun x => (hψn _).le)
      apply Complex.ext
      · rw [Complex.zero_re, ← RCLike.re_to_complex, ← integral_re hI]
        have e : (fun x => RCLike.re (ψ (x ⬝ᵥ y) * (D x : ℂ))) = fun x => ((1 : ℂ) * ψ (x ⬝ᵥ y)).re * D x := by
          funext x
          simp [Complex.mul_re]
        rw [e]
        exact hre y 1
      · rw [Complex.zero_im, ← RCLike.im_to_complex, ← integral_im hI]
        have e : (fun x => RCLike.im (ψ (x ⬝ᵥ y) * (D x : ℂ))) = fun x => ((-Complex.I) * ψ (x ⬝ᵥ y)).re * D x := by
          funext x
          simp [Complex.mul_re, Complex.mul_im]
        rw [e]
        exact hre y (-Complex.I)
    have hD0 := GlobalTheory.CharFourierInj.real_eq_zero (G := κ → AF F) (A := κ → AF F) (fun y x => ψ (x ⬝ᵥ y)) hcy
      (fun y x x' => by simp only [add_dotProduct, AddChar.map_add_eq_mul])
      (fun y y' x => by simp only [dotProduct_add, AddChar.map_add_eq_mul])
      (fun x => by simp only [dotProduct_zero, AddChar.map_zero_eq_one])
      (fun y x => hψn _) (fun x hx => GlobalTheory.AdelicSchur.sep ψ hψ x hx) μ D hDc hDi hF
    intro x
    have := congrFun hD0 x
    simp only [hD, Pi.zero_apply, sub_eq_zero] at this
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  have htwo : ∀ φ ∈ schA F κ, ∀ φ' ∈ schA F κ, ∀ x a,
      star (M φ x) * M φ' (x + a) = star (φ x) * φ' (x + a) := by
    intro φ hφ φ' hφ' x a
    apply conj_mul_eq
    intro c
    have hg : φ + c • schr ψ (a, 0) φ' ∈ schA F κ :=
      (schA F κ).add_mem hφ ((schA F κ).smul_mem c (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ' hφ'))
    have h1 := hdiag _ hg x
    rw [map_add, map_smul, hcomm _ φ' hφ'] at h1
    simpa [schr] using h1
  by_cases h0 : ∃ φ₀ ∈ schA F κ, ∃ x₀, φ₀ x₀ ≠ 0
  · obtain ⟨φ₀, hφ₀, x₀, hx₀⟩ := h0
    have hn1 : ‖M φ₀ x₀‖ = ‖φ₀ x₀‖ := hdiag φ₀ hφ₀ x₀
    have hs : star (M φ₀ x₀) ≠ 0 := by
      rw [star_ne_zero, ← norm_ne_zero_iff, hn1, norm_ne_zero_iff]
      exact hx₀
    refine ⟨star (φ₀ x₀) / star (M φ₀ x₀), fun φ hφ => funext fun x => ?_⟩
    have h2 := htwo φ₀ hφ₀ φ hφ x₀ (x - x₀)
    rw [add_sub_cancel] at h2
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs]
    exact (mul_comm _ _).trans h2
  · push_neg at h0
    refine ⟨0, fun φ hφ => ?_⟩
    have : φ = 0 := funext fun x => h0 φ hφ x
    rw [this, map_zero, smul_zero]

end GlobalTheory.AdelicSchur
