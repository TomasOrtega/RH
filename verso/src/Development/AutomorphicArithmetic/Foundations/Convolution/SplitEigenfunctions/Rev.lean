import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

/- English proof (translation)
Introduce and unpack `hE hC hF hD hB hP E _ _ _ D W M N P ⟨φ, hφ, h, hne⟩`. Choose the witnesses or unpack the hypotheses as in `⟨ph, hph, h0⟩ : ∃ ph ∈ Fock D.δ, f0 W N ph φ.1 ≠ 0 := by`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Use `hne (hP E D W M N P φ hφ (fun ph hph => ?_) h)` and prove the remaining obligations.

Establish `h1` using `hC E D W M N P ph hph φ hφ (qr D.δ X0) 1`. Rewrite `h1` using `[← hE E D W M N P ph hph φ hφ, hn ph hph]`. Establish `hδ : qr D.δ X0 ≠ 0`. Use `D.neg (Rat.castHom ℝ)` as an intermediate fact. Simplify using `only [qr, X0, eq_ratCast, Rat.cast_lt_zero] at this ⊢`.

Simplify using `using this.ne`. Establish `e : {ξ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = qr D.δ X0} = {ξ | qr D.δ ξ = qr D.δ X0}` using `Set.ext fun ξ => ⟨fun h => h.2, fun h => ⟨(show qr D.δ ξ = _ from h) ▸ hδ, h⟩⟩`. Rewrite `h1` using `[e]`. Simplify using `only [Pi.zero_apply, zero_mul, integral_zero] at h1`. Use `(mul_eq_zero.1 h1.symm).resolve_left ?_` and prove the remaining obligations.

Simplify using `[Measure.real, adeleMeasure_fundamentalSet]`. Take `⟨π, hπ, f, hf, h2⟩` from `hD M _ (hF E D W M N P ph hph φ hφ) h0`. Conclude with `⟨π, hπ, f, hf, ph, hph, φ, hφ, hB E D W M N P ph hph φ hφ π f hf ▸ h2⟩`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.rev :
    ThetaLiftEqAnisotropicPart → Coef → ThetaLiftIsBoundedCuspidal → Dens → Fub → CoefPer → Rev := by
  rintro hE hC hF hD hB hP E _ _ _ D W M N P ⟨φ, hφ, h, hne⟩
  obtain ⟨ph, hph, h0⟩ : ∃ ph ∈ Fock D.δ, f0 W N ph φ.1 ≠ 0 := by
    by_contra hn
    push Not at hn
    refine hne (hP E D W M N P φ hφ (fun ph hph => ?_) h)
    have h1 := hC E D W M N P ph hph φ hφ (qr D.δ X0) 1
    rw [← hE E D W M N P ph hph φ hφ, hn ph hph] at h1
    have hδ : qr D.δ X0 ≠ 0 := by
      have := D.neg (Rat.castHom ℝ)
      simp only [qr, X0, eq_ratCast, Rat.cast_lt_zero] at this ⊢
      simpa using this.ne
    have e : {ξ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = qr D.δ X0} = {ξ | qr D.δ ξ = qr D.δ X0} :=
      Set.ext fun ξ => ⟨fun h => h.2, fun h => ⟨(show qr D.δ ξ = _ from h) ▸ hδ, h⟩⟩
    rw [e] at h1
    simp only [Pi.zero_apply, zero_mul, integral_zero] at h1
    refine (mul_eq_zero.1 h1.symm).resolve_left ?_
    simp [Measure.real, adeleMeasure_fundamentalSet]
  obtain ⟨π, hπ, f, hf, h2⟩ := hD M _ (hF E D W M N P ph hph φ hφ) h0
  exact ⟨π, hπ, f, hf, ph, hph, φ, hφ, hB E D W M N P ph hph φ hφ π f hf ▸ h2⟩
