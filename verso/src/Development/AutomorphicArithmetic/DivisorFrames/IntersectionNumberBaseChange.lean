import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIntersectionNumberGroundFieldChange
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

/- English proof (translation)
Introduce `k K _ _ ψ X s hdeg hs`. Use `letI := ψ.toAlgebra`. Establish `hfin : Module.Finite k K` using `Module.finite_of_finrank_pos hdeg`. Use `⟨?_, fun d L _ ↦ ?_⟩` and prove the remaining obligations. Take `⟨hp, hL⟩` from `(isProjOver_iff_isProper_and_exists_isAmpleLB s).1 hs`.

Establish `hf : IsFinite (spMap ψ)` using `(IsFinite.SpecMap_iff _).2 hfin`. Conclude with `(isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨inferInstance, hL⟩`. Use `letI := algebraΓOfHom (s ≫ spMap ψ)`. Use `letI := algebraΓOfHom s`. Use `haveI : IsScalarTower k K Γ(X, ⊤) := by`.

Use `IsScalarTower.of_algebraMap_eq fun r ↦ ?_` and prove the remaining obligations. Establish `h` using `Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)`. Establish `h2` using `congrArg (fun g ↦ s.appTop.hom (g.hom r)) h`. Conclude with `h2.symm`. Conclude with `GroundFieldChange.interNum_fieldChange k K X (GlobalTheory.structureModule X) L`.
-/
theorem UpperTheory.intersection_number_base_change :
    ∀ (k K : Type) [Field k] [Field K] (ψ : k →+* K) (X : Scheme.{0}) (s : X ⟶ Sp K), 0 < embDeg ψ → IsProjOver s → IsProjOver (s ≫ spMap ψ) ∧ ∀ (d : ℕ) (L : Fin d → LB X), (∀ i, (L i).IsLB) → (letI := algebraΓOfHom (s ≫ spMap ψ); interNum k (GlobalTheory.structureModule X) L) = (embDeg ψ : ℤ) * (letI := algebraΓOfHom s; interNum K (GlobalTheory.structureModule X) L) := by
  intro k K _ _ ψ X s hdeg hs
  letI := ψ.toAlgebra
  have hfin : Module.Finite k K := Module.finite_of_finrank_pos hdeg
  refine ⟨?_, fun d L _ ↦ ?_⟩
  · obtain ⟨hp, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB s).1 hs
    have hf : IsFinite (spMap ψ) := (IsFinite.SpecMap_iff _).2 hfin
    exact (isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨inferInstance, hL⟩
  · letI := algebraΓOfHom (s ≫ spMap ψ)
    letI := algebraΓOfHom s
    haveI : IsScalarTower k K Γ(X, ⊤) := by
      refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
      have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)
      have h2 := congrArg (fun g ↦ s.appTop.hom (g.hom r)) h
      exact h2.symm
    exact GroundFieldChange.interNum_fieldChange k K X (GlobalTheory.structureModule X) L
