import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.QuadLiftUnr
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.NormRam

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Published UpperTheory.CBC

/- English proof (translation)
Establish `e : normV v = Ideal.absNorm v.asIdeal`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression. Rewrite using `[e]`. Establish `a` using `Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot`.

Establish `b` using `Ideal.absNorm_eq_one_iff.not.2 v.isPrime.ne_top`. Use linear arithmetic over natural numbers and integers.
-/
private theorem normV_two_le {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ normV v := by
  have e : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [e]
  have a := Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
  have b := Ideal.absNorm_eq_one_iff.not.2 v.isPrime.ne_top
  omega

/- English proof (translation)
Introduce `hR K M _ _ _ _ _ _ _ h2 a ha π hw`. Take `⟨P, hP⟩` from `UpperTheory.ConvolutionTheory.Sph.quadLiftUnr K M h2 a ha π hw`. Establish `hp : (Module.finrank K M).Prime` using `h2 ▸ Nat.prime_two`. Use `haveI : Algebra.IsQuadraticExtension K M := { finrank_eq_two' := h2 }`. Use `haveI : IsGalois K M := Algebra.IsQuadraticExtension.isGalois K M`.

Use `⟨P, ⟨fun w f B hf hB => ?_, hP.inf, hP.loc⟩⟩` and prove the remaining obligations. Distinguish the cases in `hu : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal`. Conclude with `hP.sat w f B hu hf hB`. Establish `h1` using `(UpperTheory.ConvolutionTheory.Sph.normRam K M hp w hu).1`. Establish `hf1 : f = 1`.

Establish `h3 : normV (w.under (𝓞 K)) ^ 1 = normV (w.under (𝓞 K)) ^ f` using `by rw [pow_one, ← hf, h1]`. Conclude with `(Nat.pow_right_injective (normV_two_le _) h3).symm`. Substitute `hf1` using the available equality. Establish `e : B.map (· ^ 1) = B` using `by simp`. Rewrite using `[e]`.

Conclude with `hR K M hp a ha π P hP.weak w hu B hB`.
-/
theorem UpperTheory.ConvolutionTheory.Sph.quadLiftOf :
    UpperTheory.ConvolutionTheory.Sph.RamSph → GlobalTheory.GalCut.QuadLift := by
  intro hR K M _ _ _ _ _ _ _ h2 a ha π hw
  obtain ⟨P, hP⟩ := UpperTheory.ConvolutionTheory.Sph.quadLiftUnr K M h2 a ha π hw
  have hp : (Module.finrank K M).Prime := h2 ▸ Nat.prime_two
  haveI : Algebra.IsQuadraticExtension K M := { finrank_eq_two' := h2 }
  haveI : IsGalois K M := Algebra.IsQuadraticExtension.isGalois K M
  refine ⟨P, ⟨fun w f B hf hB => ?_, hP.inf, hP.loc⟩⟩
  by_cases hu : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal
  · exact hP.sat w f B hu hf hB
  · have h1 := (UpperTheory.ConvolutionTheory.Sph.normRam K M hp w hu).1
    have hf1 : f = 1 := by
      have h3 : normV (w.under (𝓞 K)) ^ 1 = normV (w.under (𝓞 K)) ^ f := by rw [pow_one, ← hf, h1]
      exact (Nat.pow_right_injective (normV_two_le _) h3).symm
    subst hf1
    have e : B.map (· ^ 1) = B := by simp
    rw [e]
    exact hR K M hp a ha π P hP.weak w hu B hB
