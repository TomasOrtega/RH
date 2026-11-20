import Mathlib
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LocFreeProj

/- English proof (translation)
Introduce `R _ M _ _ h`. Set `s : Set R` to `{r | ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F) (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F) (_ : Module.Finite (Localization.Away r) F) (_ : Module.Free (Localization.Away r) F) (ϕ : M →ₗ[R] F), IsLocalizedModule (Submonoid.powers r) …`. Establish `hs : Ideal.span s = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨m, hm, hsm⟩` from `Ideal.exists_le_maximal _ hne`.

Take `⟨r, hr, hP⟩` from `h ⟨m, hm.isPrime⟩`. Conclude with `hr (hsm (Ideal.subset_span hP))`. Establish `hg : ∀ g : s, g.1 ∈ s` using `fun g => g.2`. Use `choose F iA iM iL iT iFin iFree ϕ hϕ using hg`. Use `letI := iA`.

Use `letI := iM`. Use `letI := iL`. Use `haveI := iT`. Use `haveI := iFin`. Use `haveI := iFree`.

Use `haveI := hϕ`. Use `haveI (g : s) : Module.Flat R (F g) := by haveI : Module.Flat R (Localization.Away g.1) := IsLocalization.flat _ (Submonoid.powers g.1)`. Conclude with `Module.Flat.trans R (Localization.Away g.1) (F g)`. Use `haveI hfp : Module.FinitePresentation R M := Module.FinitePresentation.of_localizationSpan' s hs (Mₚ := F) (Rₚ := fun g : s => Localization.Away g.1) ϕ fun _ => Module.finitePresentation_of_projective _ _`. Use `haveI : Module.Flat R M := Module.flat_of_isLocalized_span R M s hs F ϕ fun _ => inferInstance`.

Conclude with `⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩`.
-/
theorem finite_projective_of_locally_free : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M], (∀ q : PrimeSpectrum R, ∃ r : R, r ∉ q.asIdeal ∧ ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F) (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F) (_ : Module.Finite (Localization.Away r) F) (_ : Module.Free (Localization.Away r) F) (ϕ : M →ₗ[R] F), IsLocalizedModule (Submonoid.powers r) ϕ) → Module.Finite R M ∧ Module.Projective R M := by
  intro R _ M _ _ h
  let s : Set R := {r | ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F)
    (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F)
    (_ : Module.Finite (Localization.Away r) F) (_ : Module.Free (Localization.Away r) F)
    (ϕ : M →ₗ[R] F), IsLocalizedModule (Submonoid.powers r) ϕ}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hP⟩ := h ⟨m, hm.isPrime⟩
    exact hr (hsm (Ideal.subset_span hP))
  have hg : ∀ g : s, g.1 ∈ s := fun g => g.2
  choose F iA iM iL iT iFin iFree ϕ hϕ using hg
  letI := iA
  letI := iM
  letI := iL
  haveI := iT
  haveI := iFin
  haveI := iFree
  haveI := hϕ
  haveI (g : s) : Module.Flat R (F g) := by
    haveI : Module.Flat R (Localization.Away g.1) :=
      IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans R (Localization.Away g.1) (F g)
  haveI hfp : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s hs (Mₚ := F)
      (Rₚ := fun g : s => Localization.Away g.1) ϕ
      fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat R M :=
    Module.flat_of_isLocalized_span R M s hs F ϕ fun _ => inferInstance
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.LocFreeProj
