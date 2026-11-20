import Mathlib
open TensorProduct

namespace GlobalTheory.CompanionTheory.KerLocal

/- English proof (translation)
Introduce `R Q P _ _ _ _ _ d g hfin hproj hrk p _`. Establish `hflat : Module.Flat R (Localization.AtPrime p)` using `IsLocalization.flat (Localization.AtPrime p) p.primeCompl`. Set `e1 : Localization.AtPrime p ⊗[R] LinearMap.ker d ≃ₗ[Localization.AtPrime p] LinearMap.ker (d.baseChange (Localization.AtPrime p))` to `LinearMap.tensorKerEquiv (Localization.AtPrime p) (Localization.AtPrime p) d`. Set `e2 : Localization.AtPrime p ⊗[R] LinearMap.ker d ≃ₗ[Localization.AtPrime p] LocalizedModule p.primeCompl (LinearMap.ker d)` to `(IsLocalizedModule.isBaseChange p.primeCompl (Localization.AtPrime p) (LocalizedModule.mkLinearMap p.primeCompl (LinearMap.ker d))).equiv`. Establish `hfree : Module.Free (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] LinearMap.ker d)` using `Module.free_of_flat_of_isLocalRing`.

Use `⟨Module.Free.of_equiv e1, Module.Finite.equiv e1, ?_⟩` and prove the remaining obligations. Rewrite using `[← e1.finrank_eq, e2.finrank_eq]`. Conclude with `hrk ⟨p, inferInstance⟩`.
-/
theorem ker_baseChange_localization_free :
    ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P]
      (d : Q →ₗ[R] P) (g : ℕ), Module.Finite R (LinearMap.ker d) →
      Module.Projective R (LinearMap.ker d) →
      (∀ p : PrimeSpectrum R, Module.rankAtStalk (LinearMap.ker d) p = g) →
      ∀ (p : Ideal R) [p.IsPrime],
        Module.Free (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧
        Module.Finite (Localization.AtPrime p)
          (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧
        Module.finrank (Localization.AtPrime p)
          (LinearMap.ker (d.baseChange (Localization.AtPrime p))) = g := by
  intro R Q P _ _ _ _ _ d g hfin hproj hrk p _
  have hflat : Module.Flat R (Localization.AtPrime p) :=
    IsLocalization.flat (Localization.AtPrime p) p.primeCompl
  let e1 : Localization.AtPrime p ⊗[R] LinearMap.ker d ≃ₗ[Localization.AtPrime p]
      LinearMap.ker (d.baseChange (Localization.AtPrime p)) :=
    LinearMap.tensorKerEquiv (Localization.AtPrime p) (Localization.AtPrime p) d
  let e2 : Localization.AtPrime p ⊗[R] LinearMap.ker d ≃ₗ[Localization.AtPrime p]
      LocalizedModule p.primeCompl (LinearMap.ker d) :=
    (IsLocalizedModule.isBaseChange p.primeCompl (Localization.AtPrime p)
      (LocalizedModule.mkLinearMap p.primeCompl (LinearMap.ker d))).equiv
  have hfree : Module.Free (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[R] LinearMap.ker d) := Module.free_of_flat_of_isLocalRing
  refine ⟨Module.Free.of_equiv e1, Module.Finite.equiv e1, ?_⟩
  rw [← e1.finrank_eq, e2.finrank_eq]
  exact hrk ⟨p, inferInstance⟩

end GlobalTheory.CompanionTheory.KerLocal
