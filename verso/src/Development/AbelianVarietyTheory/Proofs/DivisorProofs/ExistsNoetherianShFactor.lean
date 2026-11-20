import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFactorStrictHenselisation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOfEtaleOfIsIndEtale
open GlobalTheory.EtC IsLocalRing

namespace GlobalTheory.NoethSHFactor

/- English proof (translation)
Introduce `R A _ _ _ hA b`. Take `⟨hH, hsep⟩` from `hA`. Set `p : Ideal R` to `(maximalIdeal A).comap b`. Use `haveI : p.IsPrime := Ideal.comap_isPrime _ _`. Set `Rp` to `Localization.AtPrime p`.

Establish `hunit : ∀ y : p.primeCompl, IsUnit (b y)`. Introduce `y`. Assume the negation of the conclusion as `h`. Conclude with `y.2 ((mem_maximalIdeal _).2 h)`. Set `b' : Rp →+* A` to `IsLocalization.lift (M := p.primeCompl) hunit`.

Establish `hb' : b'.comp (algebraMap R Rp) = b` using `IsLocalization.lift_comp hunit`. Use `letI : Algebra Rp A := b'.toAlgebra`. Use `haveI hloc : IsLocalHom (algebraMap Rp A) := by`. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨⟨r, s⟩, rfl⟩` from `IsLocalization.mk'_surjective p.primeCompl x`.

Rewrite using `[IsLocalization.AtPrime.isUnit_mk'_iff]`. Introduce `hr`. Establish `h1 : IsLocalization.mk' Rp r s * algebraMap R Rp s = algebraMap R Rp r` using `IsLocalization.mk'_spec Rp r s`. Establish `h2 : IsUnit (b r)`. Rewrite using `[← hb', RingHom.comp_apply, ← h1, map_mul]`.

Conclude with `hx.mul (by rw [← RingHom.comp_apply, hb']; exact hunit s)`. Conclude with `(mem_maximalIdeal _).1 hr h2`. Take `⟨D, _, _, _, c, w, hwc, P, _, φ, hφ, hφc, -⟩` from `GlobalTheory.StrictHensFactor.exists_factor_strictHenselisation Rp Rp A (Algebra.ofId Rp A)`. Use `haveI : IsNoetherianRing Rp := IsLocalization.isNoetherianRing p.primeCompl Rp inferInstance`. Use `haveI : IsNoetherianRing (Localization.AtPrime P) := IsLocalization.isNoetherianRing P.primeCompl _ inferInstance`.

Use `letI : Algebra (Localization.AtPrime P) D := φ.toAlgebra`. Establish `hD : IsNoetherianRing D` using `GlobalTheory.StalkNoeth.isNoetherianRing_of_indEt (Localization.AtPrime P) D hφ.2.2.2`. Use `⟨D, inferInstance, hD, ⟨hφ.1, hφ.2.1⟩, (c : Rp →+* D).comp (algebraMap R Rp), (w : D →+* A), ?_⟩` and prove the remaining obligations. Rewrite using `[← RingHom.comp_assoc]`. Establish `: (w : D →+* A).comp (c : Rp →+* D) = b'`.

Use extensionality with `x`. Conclude with `DFunLike.congr_fun hwc x`. Rewrite using `[this, hb']`.
-/
theorem exists_noetherian_sh_factor : ∀ (R A : Type) [CommRing R] [IsNoetherianRing R] [CommRing A], SH A →
    ∀ b : R →+* A, ∃ (C : Type) (_ : CommRing C), IsNoetherianRing C ∧ SH C ∧
      ∃ (f : R →+* C) (g : C →+* A), g.comp f = b := by
  intro R A _ _ _ hA b
  obtain ⟨hH, hsep⟩ := hA
  let p : Ideal R := (maximalIdeal A).comap b
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let Rp := Localization.AtPrime p
  have hunit : ∀ y : p.primeCompl, IsUnit (b y) := by
    intro y
    by_contra h
    exact y.2 ((mem_maximalIdeal _).2 h)
  let b' : Rp →+* A := IsLocalization.lift (M := p.primeCompl) hunit
  have hb' : b'.comp (algebraMap R Rp) = b := IsLocalization.lift_comp hunit
  letI : Algebra Rp A := b'.toAlgebra
  haveI hloc : IsLocalHom (algebraMap Rp A) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff]
    intro hr
    have h1 : IsLocalization.mk' Rp r s * algebraMap R Rp s = algebraMap R Rp r :=
      IsLocalization.mk'_spec Rp r s
    have h2 : IsUnit (b r) := by
      rw [← hb', RingHom.comp_apply, ← h1, map_mul]
      exact hx.mul (by rw [← RingHom.comp_apply, hb']; exact hunit s)
    exact (mem_maximalIdeal _).1 hr h2
  obtain ⟨D, _, _, _, c, w, hwc, P, _, φ, hφ, hφc, -⟩ :=
    GlobalTheory.StrictHensFactor.exists_factor_strictHenselisation Rp Rp A (Algebra.ofId Rp A)
  haveI : IsNoetherianRing Rp := IsLocalization.isNoetherianRing p.primeCompl Rp inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  letI : Algebra (Localization.AtPrime P) D := φ.toAlgebra
  have hD : IsNoetherianRing D :=
    GlobalTheory.StalkNoeth.isNoetherianRing_of_indEt (Localization.AtPrime P) D hφ.2.2.2
  refine ⟨D, inferInstance, hD, ⟨hφ.1, hφ.2.1⟩, (c : Rp →+* D).comp (algebraMap R Rp), (w : D →+* A), ?_⟩
  rw [← RingHom.comp_assoc]
  have : (w : D →+* A).comp (c : Rp →+* D) = b' := by
    ext x
    exact DFunLike.congr_fun hwc x
  rw [this, hb']

end GlobalTheory.NoethSHFactor
