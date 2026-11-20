import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.NormInvMulSelf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitDict
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilThetadictRelReal

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
/- English proof (translation)
Introduce `w`. Use `set τ := (d.B.emb w).1 with hτ`. Use `set a := τ η with ha`. Use `set c := cW d.B η w with hc`. Establish `hθ1 : ∀ x : E, θ w ((1 : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) ⊗ₜ[F] x) = star (τ x)` using `fun x => by`.

Use `th w ((1 : AF F) ⊗ₜ[F] x)` as an intermediate fact. Rewrite `this` using `[Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, piInf_one]`. Conclude with `this`. Establish `hmat : (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η)).map (θ w) = a • d.A.J.map τ`. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply, HeckeCharacterZeroLocus.SiegelWeilU.JR, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, HeckeCharacterZeroLocus.SiegelWeilU.inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct …`. Rewrite using `[← hcm.2.2.2, herm, map_mul]`. Establish `hcs : star c = c` using `Complex.conj_ofReal _`. Establish `hfrH : ((fr w).1)ᴴ = c • ((R.fr w).1)ᵀ`. Rewrite using `[frc w, Matrix.conjTranspose_smul]`.

Express the relevant statement in the definitionally equal form `star c • _ = _`. Rewrite using `[hcs]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply]`.

Establish `hζ : R.ζ ≠ 0`. Apply the tactic sequence `rcases hηζ with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> simp`. Establish `hfr' : (R.fr w).1ᵀ * d.A.J.map τ * (R.fr w).1.map star = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • 1`. Use `congrArg (fun M => R.ζ⁻¹ • M) (R.hfr w)` as an intermediate fact. Simplify using `only [smul_smul, inv_mul_cancel₀ hζ, one_smul] at this`.

Rewrite using `[this]`. Establish `ha0 : a ≠ 0` using `(map_ne_zero τ).2 hη`. Establish `hapos : 0 < ‖a‖` using `norm_pos_iff.2 ha0`. Establish `hcc : c * c = ((‖a‖⁻¹ : ℝ) : ℂ)`. Rewrite using `[hc, cW, ← Complex.ofReal_mul, ← Real.rpow_add hapos]`.

Evaluate the numerical expressions using `[Real.rpow_neg_one]`. Use `set z := a / R.ζ * ((R.sg w : ℤ) : ℂ) with hz`. Establish `hsg : ‖((R.sg w : ℤ) : ℂ)‖ = 1`. Apply the tactic sequence `rcases Int.units_eq_one_or (R.sg w) with h | h <;> rw [h] <;> simp`. Establish `hsg0 : ((R.sg w : ℤ) : ℂ) ≠ 0`.

Introduce `h`. Rewrite `hsg` using `[h]`. Simplify using `at hsg`. Establish `hsgim : (((R.sg w : ℤ) : ℂ)).im = 0` using `by simp`. Establish `hz0 : z ≠ 0` using `mul_ne_zero (div_ne_zero ha0 hζ) hsg0`.

Establish `hzn : ‖z‖ = ‖a‖`. Rewrite using `[hz, norm_mul, norm_div, hsg]`. Apply the tactic sequence `rcases hηζ with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> simp`. Establish `hzim : z.im = 0`. Establish `hconj` using `hcm.2.2.2 τ η`.

Break down `hηζ with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases. Rewrite `hconj` using `[h1]`. Establish `him : a.im = 0`. Use `congrArg Complex.im hconj` as an intermediate fact. Express the relevant statement in the definitionally equal form `a.im = (star a).im at this`.

Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hz, h2, div_one, Complex.mul_im, him, hsgim]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hconj` using `[h1, map_neg]`.

Establish `hre : a.re = 0`. Use `congrArg Complex.re hconj` as an intermediate fact. Express the relevant statement in the definitionally equal form `(-a).re = (star a).re at this`. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hz, h2, Complex.div_I, Complex.mul_im, hsgim]`. Simplify using `[Complex.mul_im, hre]`. Establish `key : (fr w).1ᴴ * (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η)).map (θ w) * (fr w).1 = (((‖z‖⁻¹ : ℝ) : ℂ) * z) • (1 : Matrix (Fin d.m) (Fin d.m) ℂ)`. Rewrite using `[hfrH, hmat, frc w, show ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = c from rfl]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]`.

Rewrite using `[hfr', smul_smul, hzn, ← hcc, hz]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Express the relevant statement in the definitionally equal form `(fr w).1ᴴ * (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η)).map (θ w) * (fr w).1 = _`. Rewrite using `[key, norm_inv_mul_self hz0 hzim]`.

Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.εsW_k, sgn, hz, ha, hτ]`. Simplify using `[hij]`.
-/
theorem isFrames_of'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (η : E) (hη : η ≠ 0) (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ)
    (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) (hηζ : (σ η = η ∧ R.ζ = 1) ∨ (σ η = -η ∧ R.ζ = Complex.I))
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ))
    (th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y))
    (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star) :
    Gen.IsFrames (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) θ (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.εsW_k R η) fr := by
  intro w
  set τ := (d.B.emb w).1 with hτ
  set a := τ η with ha
  set c := cW d.B η w with hc
  have hθ1 : ∀ x : E, θ w ((1 : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) ⊗ₜ[F] x) = star (τ x) := fun x => by
    have := th w ((1 : AF F) ⊗ₜ[F] x)
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, piInf_one] at this
    exact this
  have hmat : (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η)).map (θ w) = a • d.A.J.map τ := by
    ext i j
    simp only [Matrix.map_apply, HeckeCharacterZeroLocus.SiegelWeilU.JR, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
      HeckeCharacterZeroLocus.SiegelWeilU.inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, hθ1]
    rw [← hcm.2.2.2, herm, map_mul]
  have hcs : star c = c := Complex.conj_ofReal _
  have hfrH : ((fr w).1)ᴴ = c • ((R.fr w).1)ᵀ := by
    rw [frc w, Matrix.conjTranspose_smul]
    change star c • _ = _
    rw [hcs]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hζ : R.ζ ≠ 0 := by
    rcases hηζ with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> simp
  have hfr' : (R.fr w).1ᵀ * d.A.J.map τ * (R.fr w).1.map star = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • 1 := by
    have := congrArg (fun M => R.ζ⁻¹ • M) (R.hfr w)
    simp only [smul_smul, inv_mul_cancel₀ hζ, one_smul] at this
    rw [this]
  have ha0 : a ≠ 0 := (map_ne_zero τ).2 hη
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hcc : c * c = ((‖a‖⁻¹ : ℝ) : ℂ) := by
    rw [hc, cW, ← Complex.ofReal_mul, ← Real.rpow_add hapos]
    norm_num [Real.rpow_neg_one]
  set z := a / R.ζ * ((R.sg w : ℤ) : ℂ) with hz
  have hsg : ‖((R.sg w : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or (R.sg w) with h | h <;> rw [h] <;> simp
  have hsg0 : ((R.sg w : ℤ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hsg; simp at hsg
  have hsgim : (((R.sg w : ℤ) : ℂ)).im = 0 := by simp
  have hz0 : z ≠ 0 := mul_ne_zero (div_ne_zero ha0 hζ) hsg0
  have hzn : ‖z‖ = ‖a‖ := by
    rw [hz, norm_mul, norm_div, hsg]
    rcases hηζ with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> simp
  have hzim : z.im = 0 := by
    have hconj := hcm.2.2.2 τ η
    rcases hηζ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at hconj
      have him : a.im = 0 := by
        have := congrArg Complex.im hconj
        change a.im = (star a).im at this
        simp at this; linarith
      rw [hz, h2, div_one, Complex.mul_im, him, hsgim]; ring
    · rw [h1, map_neg] at hconj
      have hre : a.re = 0 := by
        have := congrArg Complex.re hconj
        change (-a).re = (star a).re at this
        simp at this; linarith
      rw [hz, h2, Complex.div_I, Complex.mul_im, hsgim]
      simp [Complex.mul_im, hre]
  have key : (fr w).1ᴴ * (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η)).map (θ w) * (fr w).1 =
      (((‖z‖⁻¹ : ℝ) : ℂ) * z) • (1 : Matrix (Fin d.m) (Fin d.m) ℂ) := by
    rw [hfrH, hmat, frc w, show ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = c from rfl]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hfr', smul_smul, hzn, ← hcc, hz]
    congr 1
    field_simp
  change (fr w).1ᴴ * (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η)).map (θ w) * (fr w).1 = _
  rw [key, norm_inv_mul_self hz0 hzim]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.εsW_k, sgn, hz, ha, hτ]
  · simp [hij]
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
