import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProjDimSpread
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open CategoryTheory

variable {R : Type} [CommRing R]

noncomputable def ProjDimSpread.localizedModuleEquiv (M : ModuleCat.{0} R) (S : Submonoid R) :
    M.localizedModule S ≃ₗ[Localization S] LocalizedModule S M :=
  LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
    (IsLocalizedModule.linearEquiv S (M.localizedModuleMkLinearMap S)
      (LocalizedModule.mkLinearMap S M))

/- English proof (translation)
Rewrite using `[HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective]`. Conclude with `⟨fun _ ↦ Module.Projective.of_equiv (localizedModuleEquiv M S), fun _ ↦ Module.Projective.of_equiv (localizedModuleEquiv M S).symm⟩`.
-/
theorem ProjDimSpread.hasProjectiveDimensionLE_zero_iff (M : ModuleCat.{0} R) (S : Submonoid R) :
    HasProjectiveDimensionLE (M.localizedModule S) 0 ↔
      Module.Projective (Localization S) (LocalizedModule S M) := by
  rw [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one,
    ← IsProjective.iff_projective]
  exact ⟨fun _ ↦ Module.Projective.of_equiv (localizedModuleEquiv M S),
    fun _ ↦ Module.Projective.of_equiv (localizedModuleEquiv M S).symm⟩

/- English proof (translation)
Rewrite `h` using `[hasProjectiveDimensionLE_zero_iff]`. Establish `: Module.FinitePresentation R M` using `Module.finitePresentation_of_finite R M`. Establish `: Module.Flat (Localization.AtPrime P) (LocalizedModule P.primeCompl M)` using `Module.Flat.of_projective`. Establish `hfree : Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl M)` using `Module.free_of_flat_of_isLocalRing`. Establish `hP : (⟨P, inferInstance⟩ : PrimeSpectrum R) ∈ Module.freeLocus R M` using `Module.mem_freeLocus.mpr hfree`.

Take `⟨_, ⟨g, rfl⟩, hPg, hsub⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hP Module.isOpen_freeLocus`. Use `⟨g, (PrimeSpectrum.mem_basicOpen g _).mp hPg, fun Q _ hQ ↦ ?_⟩` and prove the remaining obligations. Establish `: Module.Free (Localization.AtPrime Q) (LocalizedModule Q.primeCompl M)` using `Module.mem_freeLocus.mp (hsub ((PrimeSpectrum.mem_basicOpen g ⟨Q, inferInstance⟩).mpr hQ))`. Conclude with `(hasProjectiveDimensionLE_zero_iff M Q.primeCompl).mpr Module.Projective.of_free`.
-/
theorem ProjDimSpread.spread_zero [IsNoetherianRing R] (P : Ideal R) [P.IsPrime]
    (M : ModuleCat.{0} R) [Module.Finite R M]
    (h : HasProjectiveDimensionLE (M.localizedModule P.primeCompl) 0) :
    ∃ g : R, g ∉ P ∧ ∀ (Q : Ideal R) [Q.IsPrime], g ∉ Q →
      HasProjectiveDimensionLE (M.localizedModule Q.primeCompl) 0 := by
  rw [hasProjectiveDimensionLE_zero_iff] at h
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  have : Module.Flat (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
    Module.Flat.of_projective
  have hfree : Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  have hP : (⟨P, inferInstance⟩ : PrimeSpectrum R) ∈ Module.freeLocus R M :=
    Module.mem_freeLocus.mpr hfree
  obtain ⟨_, ⟨g, rfl⟩, hPg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hP
      Module.isOpen_freeLocus
  refine ⟨g, (PrimeSpectrum.mem_basicOpen g _).mp hPg, fun Q _ hQ ↦ ?_⟩
  have : Module.Free (Localization.AtPrime Q) (LocalizedModule Q.primeCompl M) :=
    Module.mem_freeLocus.mp (hsub ((PrimeSpectrum.mem_basicOpen g ⟨Q, inferInstance⟩).mpr hQ))
  exact (hasProjectiveDimensionLE_zero_iff M Q.primeCompl).mpr Module.Projective.of_free

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact fun M _ h ↦ spread_zero P M h`. Consider the case `succ n ih`. Introduce `M _ h`. Break down `Module.exists_finite_presentation R M with ⟨F, _, _, _, _, f, surjf⟩` into its components or cases.

Set `S` to `f.shortComplexKer`. Establish `S_exact` using `LinearMap.shortExact_shortComplexKer surjf`. Establish `proj` using `ModuleCat.projective_of_categoryTheory_projective S.X₂`. Establish `Sp_exact (T : Submonoid R) : (S.map (ModuleCat.localizedModuleFunctor T)).ShortExact` using `S_exact.map_of_exact (ModuleCat.localizedModuleFunctor T)`. Establish `projp (T : Submonoid R) : Projective (S.map (ModuleCat.localizedModuleFunctor T)).X₂` using `(ModuleCat.localizedModuleFunctor.{0} T).projective_obj_of_projective proj`.

Establish `hK : HasProjectiveDimensionLE ((ModuleCat.of R (LinearMap.ker f)).localizedModule P.primeCompl) n` using `((Sp_exact P.primeCompl).hasProjectiveDimensionLT_X₃_iff n (projp _)).mp h`. Take `⟨g, hg, hQ⟩` from `ih (ModuleCat.of R (LinearMap.ker f)) hK`. Conclude with `⟨g, hg, fun Q _ hgQ ↦ ((Sp_exact Q.primeCompl).hasProjectiveDimensionLT_X₃_iff n (projp _)).mpr (hQ Q hgQ)⟩`.
-/
theorem ProjDimSpread.spread [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] (n : ℕ) :
    ∀ (M : ModuleCat.{0} R) [Module.Finite R M],
      HasProjectiveDimensionLE (M.localizedModule P.primeCompl) n →
      ∃ g : R, g ∉ P ∧ ∀ (Q : Ideal R) [Q.IsPrime], g ∉ Q →
        HasProjectiveDimensionLE (M.localizedModule Q.primeCompl) n := by
  induction n with
  | zero => exact fun M _ h ↦ spread_zero P M h
  | succ n ih =>
    intro M _ h
    rcases Module.exists_finite_presentation R M with ⟨F, _, _, _, _, f, surjf⟩
    let S := f.shortComplexKer
    have S_exact := LinearMap.shortExact_shortComplexKer surjf
    have proj := ModuleCat.projective_of_categoryTheory_projective S.X₂
    have Sp_exact (T : Submonoid R) : (S.map (ModuleCat.localizedModuleFunctor T)).ShortExact :=
      S_exact.map_of_exact (ModuleCat.localizedModuleFunctor T)
    have projp (T : Submonoid R) : Projective (S.map (ModuleCat.localizedModuleFunctor T)).X₂ :=
      (ModuleCat.localizedModuleFunctor.{0} T).projective_obj_of_projective proj
    have hK : HasProjectiveDimensionLE
        ((ModuleCat.of R (LinearMap.ker f)).localizedModule P.primeCompl) n :=
      ((Sp_exact P.primeCompl).hasProjectiveDimensionLT_X₃_iff n (projp _)).mp h
    obtain ⟨g, hg, hQ⟩ := ih (ModuleCat.of R (LinearMap.ker f)) hK
    exact ⟨g, hg, fun Q _ hgQ ↦
      ((Sp_exact Q.primeCompl).hasProjectiveDimensionLT_X₃_iff n (projp _)).mpr (hQ Q hgQ)⟩

noncomputable def ProjDimSpread.quotientEquiv (I Q : Ideal R) [Q.IsPrime] :
    (ModuleCat.of R (R ⧸ I)).localizedModule Q.primeCompl ≃ₗ[Localization.AtPrime Q]
      (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) :=
  ((ProjDimSpread.localizedModuleEquiv (ModuleCat.of R (R ⧸ I)) Q.primeCompl).trans
    (LinearEquiv.extendScalarsOfIsLocalization Q.primeCompl (Localization.AtPrime Q)
      (IsLocalizedModule.linearEquiv Q.primeCompl (LocalizedModule.mkLinearMap Q.primeCompl (R ⧸ I))
        (I.toLocalizedQuotient' (Localization.AtPrime Q) Q.primeCompl
          (Algebra.linearMap R (Localization.AtPrime Q)))))).trans
    (Submodule.quotEquivOfEq _ _
      (Ideal.localized'_eq_map (Localization.AtPrime Q) Q.primeCompl I))

/- English proof (translation)
Introduce `R _ _ I P _ ℓ h`. Establish `e : ∀ (Q : Ideal R) [Q.IsPrime], (ModuleCat.of R (R ⧸ I)).localizedModule Q.primeCompl ≅ ModuleCat.of (Localization.AtPrime Q) (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q)))` using `fun Q _ ↦ (ProjDimSpread.quotientEquiv I Q).toModuleIso`. Establish `hP : HasProjectiveDimensionLE ((ModuleCat.of R (R ⧸ I)).localizedModule P.primeCompl) ℓ` using `hasProjectiveDimensionLT_of_iso (e P).symm (ℓ + 1)`. Take `⟨g, hg, hQ⟩` from `ProjDimSpread.spread P ℓ (ModuleCat.of R (R ⧸ I)) hP`. Use `⟨g, hg, fun Q _ hgQ ↦ ?_⟩` and prove the remaining obligations.

Use `hQ Q hgQ` as an intermediate fact. Conclude with `hasProjectiveDimensionLT_of_iso (e Q) (ℓ + 1)`.
-/
theorem ProjDimSpread.proof : ProjDimSpread.Statement := by
  intro R _ _ I P _ ℓ h
  have e : ∀ (Q : Ideal R) [Q.IsPrime], (ModuleCat.of R (R ⧸ I)).localizedModule Q.primeCompl ≅
      ModuleCat.of (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) :=
    fun Q _ ↦ (ProjDimSpread.quotientEquiv I Q).toModuleIso
  have hP : HasProjectiveDimensionLE
      ((ModuleCat.of R (R ⧸ I)).localizedModule P.primeCompl) ℓ :=
    hasProjectiveDimensionLT_of_iso (e P).symm (ℓ + 1)
  obtain ⟨g, hg, hQ⟩ := ProjDimSpread.spread P ℓ (ModuleCat.of R (R ⧸ I)) hP
  refine ⟨g, hg, fun Q _ hgQ ↦ ?_⟩
  have := hQ Q hgQ
  exact hasProjectiveDimensionLT_of_iso (e Q) (ℓ + 1)

end GroundTheory.Heights₂.Heights
