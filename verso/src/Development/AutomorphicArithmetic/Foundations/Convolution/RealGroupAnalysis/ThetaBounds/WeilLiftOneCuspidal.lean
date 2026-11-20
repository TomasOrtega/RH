import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThMeas
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.HatMaj
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ZpowLeAbs
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.CuspZero
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Imports
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D W M π f hf φ x`. Establish `hL` using `(UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f hf).1`. Establish `hW` using `UpperTheory.ConvolutionTheory.R2.Pp.wfBasic F f.1 hL`. Establish `hWc : Continuous fun g : G1 F => Wf f.1 (gl g * x)` using `hW.1.comp (UpperTheory.ConvolutionTheory.R2.continuous_gl.mul continuous_const)`. Establish `hm : ∀ φ : S4 F, Measurable fun g => Wf f.1 (gl g * x) * hat (W.Om g φ).1 ![0, 1, 1, 0]` using `fun φ => hWc.measurable.mul ((thMeas F E D W φ).2.2.2.2 _)`.

Use `⟨hm φ, ?_, ?_⟩` and prove the remaining obligations. Introduce `b g`. Establish `h1 : Wf f.1 (gl (nU b * g) * x) = ψ (-b) * Wf f.1 (gl g * x)`. Rewrite using `[UpperTheory.ConvolutionTheory.R2.gl_mul, mul_assoc]`. Conclude with `hW.2.1 b _`.

Establish `h2 : hat (W.Om (nU b * g) φ).1 ![0, 1, 1, 0] = ψ b * hat (W.Om g φ).1 ![0, 1, 1, 0]`. Rewrite using `[map_mul, Module.End.mul_apply, (hatSt F E D W).n b (W.Om g φ) ![0, 1, 1, 0]]`. Establish `e : Function.update ![(0 : A F), 1, 1, 0] 1 (![(0 : A F), 1, 1, 0] 1 + b * ![(0 : A F), 1, 1, 0] 0) = ![0, 1, 1, 0]`. Apply the tactic sequence `ext i; fin_cases i <;> simp`. Rewrite using `[e]`.

Simplify using the standard rewrite rules. Rewrite using `[h1, h2]`. Establish `h3 : ψ (-b) * ψ b = 1`. Rewrite using `[UpperTheory.ConvolutionTheory.R2.ψ_neg]`. Conclude with `inv_mul_cancel₀ (UpperTheory.ConvolutionTheory.R2.ψ_ne_zero b)`.

Combine the equalities or inequalities in the displayed calculation. Introduce `hφ y hy`. Take `⟨N, hN⟩` from `wtId F`. Take `⟨K, hK, hB'⟩` from `hatMaj F E D W φ hφ y hy`. Take `⟨B', hB'⟩` from `hB' N`.

Take `⟨B, hB⟩` from `UpperTheory.ConvolutionTheory.R2.Pp.bdd F π f hf {x} isCompact_singleton`. Use `M.prob` as an intermediate fact. Establish `hI` using `(hN K hK).comp_fst M.κ`. Establish `hmaj : Integrable (fun p : IdeleGroup F × G1 F => (B * B') * ((ab p.1)⁻¹ * wt K N ![0, ((p.1⁻¹ : (A F)ˣ) : A F), (p.1 : A F), 0])) M.ν` using `hI.const_mul _`. Use `hmaj.mono' ?_ ?_` and prove the remaining obligations.

Establish `hc : Continuous fun p : IdeleGroup F × G1 F => mD p.1 * p.2` using `(UpperTheory.ConvolutionTheory.R2.continuous_mD.comp continuous_fst).mul continuous_snd`. Establish `hab : Continuous fun p : IdeleGroup F × G1 F => ab p.1` using `UpperTheory.ConvolutionTheory.R2.continuous_ab.comp continuous_fst`. Establish `hmm : Measurable (iw fun g => Wf f.1 (gl g * x) * hat (W.Om g (W.L (infGL E 2 y) φ)).1 ![0, 1, 1, 0])` using `(Complex.continuous_ofReal.comp ((hab.inv₀ fun p => UpperTheory.ConvolutionTheory.R2.ab_ne_zero _).pow 2)).measurable.mul ((hm (W.L (infGL E 2 y) φ)).comp hc.measurable)`. Conclude with `hmm.aestronglyMeasurable`. Establish `hk : ∀ᵐ p ∂M.ν, p.2 ∈ KK F` using `Measure.quasiMeasurePreserving_snd.ae (by`.

Use `M.supp` as an intermediate fact. Conclude with `measure_eq_zero_iff_ae_notMem.1 (by simpa using this) |>.mono (fun k hk => by simpa using hk))`. Use `filter_upwards [hk] with p hp`. Take `⟨a, k⟩` from `p`. Establish `hk' : k ∈ KK F` using `hp`.

Establish `h1` using `(hB (mD a * k) x rfl).2`. Establish `h2` using `hB' 0 a k hk' 1 1 0`. Rewrite `h2` using `[UpperTheory.ConvolutionTheory.R2.nU_zero, one_mul, mul_one, mul_one, mul_zero]`. Establish `hpos : 0 < ab a` using `UpperTheory.ConvolutionTheory.R2.ab_pos a`. Establish `hB0 : 0 ≤ B` using `(norm_nonneg _).trans h1`.

Simplify using `only [iw, norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Rewrite using `[abs_of_pos (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.weilLift_one_cuspidal :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), UnfoldedThetaIntegralConvergesSimilitudeOne W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ x
  have hL := (UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f hf).1
  have hW := UpperTheory.ConvolutionTheory.R2.Pp.wfBasic F f.1 hL
  have hWc : Continuous fun g : G1 F => Wf f.1 (gl g * x) :=
    hW.1.comp (UpperTheory.ConvolutionTheory.R2.continuous_gl.mul continuous_const)
  have hm : ∀ φ : S4 F, Measurable fun g => Wf f.1 (gl g * x) * hat (W.Om g φ).1 ![0, 1, 1, 0] := fun φ =>
    hWc.measurable.mul ((thMeas F E D W φ).2.2.2.2 _)
  refine ⟨hm φ, ?_, ?_⟩
  · intro b g
    have h1 : Wf f.1 (gl (nU b * g) * x) = ψ (-b) * Wf f.1 (gl g * x) := by
      rw [UpperTheory.ConvolutionTheory.R2.gl_mul, mul_assoc]
      exact hW.2.1 b _
    have h2 : hat (W.Om (nU b * g) φ).1 ![0, 1, 1, 0] = ψ b * hat (W.Om g φ).1 ![0, 1, 1, 0] := by
      rw [map_mul, Module.End.mul_apply, (hatSt F E D W).n b (W.Om g φ) ![0, 1, 1, 0]]
      have e : Function.update ![(0 : A F), 1, 1, 0] 1 (![(0 : A F), 1, 1, 0] 1 + b * ![(0 : A F), 1, 1, 0] 0) = ![0, 1, 1, 0] := by
        ext i; fin_cases i <;> simp
      rw [e]
      simp
    rw [h1, h2]
    have h3 : ψ (-b) * ψ b = 1 := by
      rw [UpperTheory.ConvolutionTheory.R2.ψ_neg]; exact inv_mul_cancel₀ (UpperTheory.ConvolutionTheory.R2.ψ_ne_zero b)
    calc _ = (ψ (-b) * ψ b) * (Wf f.1 (gl g * x) * hat (W.Om g φ).1 ![0, 1, 1, 0]) := by ring
      _ = _ := by rw [h3, one_mul]
  · intro hφ y hy
    obtain ⟨N, hN⟩ := wtId F
    obtain ⟨K, hK, hB'⟩ := hatMaj F E D W φ hφ y hy
    obtain ⟨B', hB'⟩ := hB' N
    obtain ⟨B, hB⟩ := UpperTheory.ConvolutionTheory.R2.Pp.bdd F π f hf {x} isCompact_singleton
    have := M.prob
    have hI := (hN K hK).comp_fst M.κ
    have hmaj : Integrable (fun p : IdeleGroup F × G1 F => (B * B') * ((ab p.1)⁻¹ * wt K N ![0, ((p.1⁻¹ : (A F)ˣ) : A F), (p.1 : A F), 0])) M.ν :=
      hI.const_mul _
    refine hmaj.mono' ?_ ?_
    · have hc : Continuous fun p : IdeleGroup F × G1 F => mD p.1 * p.2 :=
        (UpperTheory.ConvolutionTheory.R2.continuous_mD.comp continuous_fst).mul continuous_snd
      have hab : Continuous fun p : IdeleGroup F × G1 F => ab p.1 :=
        UpperTheory.ConvolutionTheory.R2.continuous_ab.comp continuous_fst
      have hmm : Measurable (iw fun g => Wf f.1 (gl g * x) * hat (W.Om g (W.L (infGL E 2 y) φ)).1 ![0, 1, 1, 0]) :=
        (Complex.continuous_ofReal.comp ((hab.inv₀ fun p => UpperTheory.ConvolutionTheory.R2.ab_ne_zero _).pow 2)).measurable.mul
          ((hm (W.L (infGL E 2 y) φ)).comp hc.measurable)
      exact hmm.aestronglyMeasurable
    · have hk : ∀ᵐ p ∂M.ν, p.2 ∈ KK F := Measure.quasiMeasurePreserving_snd.ae (by
        have := M.supp
        exact measure_eq_zero_iff_ae_notMem.1 (by simpa using this) |>.mono (fun k hk => by simpa using hk))
      filter_upwards [hk] with p hp
      obtain ⟨a, k⟩ := p
      have hk' : k ∈ KK F := hp
      have h1 := (hB (mD a * k) x rfl).2
      have h2 := hB' 0 a k hk' 1 1 0
      rw [UpperTheory.ConvolutionTheory.R2.nU_zero, one_mul, mul_one, mul_one, mul_zero] at h2
      have hpos : 0 < ab a := UpperTheory.ConvolutionTheory.R2.ab_pos a
      have hB0 : 0 ≤ B := (norm_nonneg _).trans h1
      simp only [iw, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      calc ((ab a)⁻¹ ^ 2) * (‖Wf f.1 (gl (mD a * k) * x)‖ * ‖hat (W.Om (mD a * k) (W.L (infGL E 2 y) φ)).1 ![0, 1, 1, 0]‖)
          ≤ ((ab a)⁻¹ ^ 2) * (B * (B' * ab a * wt K N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0])) := by
            gcongr
        _ = _ := by field_simp
