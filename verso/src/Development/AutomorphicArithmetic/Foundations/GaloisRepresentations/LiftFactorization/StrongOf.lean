import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LiftFactorization.RamLiftOf
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.NormRam
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatFamOfIsDiscrete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.GalCut GlobalTheory.RealGal GlobalTheory.UnitaryBC UpperTheory.V.Published UpperTheory.Gal.UnramifiedFromSplittingCriterion UpperTheory.ConvolutionTheory.Sph

/- English proof (translation)
Introduce `hL hR K M _ _ _ _ _ _ _ _ hp a ha π hη`. Establish `hno : ∀ η : HChar K, IsNormChar M η → (CG.mk π).twist η ≠ CG.mk π`. Introduce `η hn he`. Use `hη η hn ?_` and prove the remaining obligations. Establish `h1` using `(GlobalTheory.ResW.exists_satFam_of_isDiscrete K a).1 π`.

Establish `h2 : ∀ᶠ v in Filter.cofinite, η.UnrAt v` using `Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified η)`. Use `filter_upwards [h1, h2] with v hv hu`. Take `⟨B, hB⟩` from `hv`. Use `⟨hu, B, hB, ?_⟩` and prove the remaining obligations. Establish `h3` using `CG.HasSat.twist hB hu`.

Rewrite `h3` using `[he]`. Conclude with `CG.HasSat.unique h3 hB`. Take `⟨P, hP⟩` from `hL K M hp a ha π hno`. Use `⟨P, ?_⟩` and prove the remaining obligations. Use `⟨fun w f B hf hB => ?_, hP.inf, hP.loc⟩` and prove the remaining obligations.

Distinguish the cases in `hu : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal`. Conclude with `hP.sat w f B hu hf hB`. Establish `h1 : (CG.mk P).HasSat w B` using `hR K M hp a ha π P hP.weak w hu B hB`. Establish `h2` using `(UpperTheory.ConvolutionTheory.Sph.normRam K M hp w hu).1`. Establish `h3 : 2 ≤ normV (w.under (𝓞 K))` using `GlobalTheory.WeilDeligne.one_lt_normV _`.

Establish `h4 : f = 1` using `Nat.pow_right_injective h3 (by simpa [← h2] using hf.symm)`. Substitute `h4` using the available equality. Simplify using `using h1`.
-/
theorem UpperTheory.Gal.AbelianGaloisNormality.strongOf :
    UpperTheory.Gal.AbelianGaloisNormality.StrongOf := by
  intro hL hR K M _ _ _ _ _ _ _ _ hp a ha π hη
  have hno : ∀ η : HChar K, IsNormChar M η → (CG.mk π).twist η ≠ CG.mk π := by
    intro η hn he
    refine hη η hn ?_
    have h1 := (GlobalTheory.ResW.exists_satFam_of_isDiscrete K a).1 π
    have h2 : ∀ᶠ v in Filter.cofinite, η.UnrAt v :=
      Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified η)
    filter_upwards [h1, h2] with v hv hu
    obtain ⟨B, hB⟩ := hv
    refine ⟨hu, B, hB, ?_⟩
    have h3 := CG.HasSat.twist hB hu
    rw [he] at h3
    exact CG.HasSat.unique h3 hB
  obtain ⟨P, hP⟩ := hL K M hp a ha π hno
  refine ⟨P, ?_⟩
  refine ⟨fun w f B hf hB => ?_, hP.inf, hP.loc⟩
  by_cases hu : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal
  · exact hP.sat w f B hu hf hB
  · have h1 : (CG.mk P).HasSat w B := hR K M hp a ha π P hP.weak w hu B hB
    have h2 := (UpperTheory.ConvolutionTheory.Sph.normRam K M hp w hu).1
    have h3 : 2 ≤ normV (w.under (𝓞 K)) := GlobalTheory.WeilDeligne.one_lt_normV _
    have h4 : f = 1 := Nat.pow_right_injective h3 (by simpa [← h2] using hf.symm)
    subst h4
    simpa using h1
