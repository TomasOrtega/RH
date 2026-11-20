import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtFrob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

/- English proof (translation)
Introduce `K _ _ S hS c`. Set `Ω` to `AlgebraicClosure K`. Take `⟨v, hvS, hdeg, B, hB, -, σ, hσ, hres⟩` from `GlobalTheory.Published.chebotarevDegreeOne' K Ω (GroundTheory.Global.hilbertClassField K Ω) (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω c) S hS`. Use `⟨v, hvS, ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified K).1 v).mpr hdeg, ?_⟩` and prove the remaining obligations. Rewrite using `[← artFrob K Ω B v σ hB hσ]`.

Use `show (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm (AlgEquiv.restrictNormalHom (GroundTheory.Global.hilbertClassField K Ω) σ) = c`. Rewrite using `[hres]`. Conclude with `MulEquiv.symm_apply_apply _ _`.
-/
theorem UpperTheory.V.Stick.degOne :
    ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ∀ c : ClassGroup (𝓞 K),
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ (Ideal.absNorm v.asIdeal).Prime ∧ primeCl v = c := by
  intro K _ _ S hS c
  let Ω := AlgebraicClosure K
  obtain ⟨v, hvS, hdeg, B, hB, -, σ, hσ, hres⟩ :=
    GlobalTheory.Published.chebotarevDegreeOne' K Ω (GroundTheory.Global.hilbertClassField K Ω)
      (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω c) S hS
  refine ⟨v, hvS, ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified K).1 v).mpr hdeg, ?_⟩
  rw [← artFrob K Ω B v σ hB hσ]
  show (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm
      (AlgEquiv.restrictNormalHom (GroundTheory.Global.hilbertClassField K Ω) σ) = c
  rw [hres]
  exact MulEquiv.symm_apply_apply _ _
