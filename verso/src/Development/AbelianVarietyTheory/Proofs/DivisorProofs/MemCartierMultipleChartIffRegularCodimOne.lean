import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfRegularAtCodimOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.ChartHartogs

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsLocalization.isDomain_of_le_nonZeroDivisors (R := R) (M := p.asIdeal.primeCompl) (S := (Spec.structureSheaf R).presheaf.stalk p) (hM := p.asIdeal.primeCompl_le_nonZeroDivisors), isIntegrallyClosed_of_isLocalization _ p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors …`.
-/
theorem stalk_normal (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (p : PrimeSpectrum R) :
    IsDomain ((Spec.structureSheaf R).presheaf.stalk p) ∧ IsIntegrallyClosed ((Spec.structureSheaf R).presheaf.stalk p) :=
  ⟨IsLocalization.isDomain_of_le_nonZeroDivisors (R := R) (M := p.asIdeal.primeCompl) (S := (Spec.structureSheaf R).presheaf.stalk p) (hM := p.asIdeal.primeCompl_le_nonZeroDivisors),
    isIntegrallyClosed_of_isLocalization _ p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors⟩

/- English proof (translation)
Establish `hs : Smooth (σ.C x).G.hom` using `(σ.C x).semi.smooth`. Take `⟨h1, h2⟩` from `GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (σ.C x).R`. Use `⟨LocallyOfFiniteType.isLocallyNoetherian (σ.C x).G.hom, fun z => ?_⟩` and prove the remaining obligations. Use `(stalk_normal (σ.C x).R ((σ.C x).G.hom z)).1` as an intermediate fact. Use `(stalk_normal (σ.C x).R ((σ.C x).G.hom z)).2` as an intermediate fact.

Conclude with `(GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_of_smooth (σ.C x).G.hom z).2`.
-/
theorem chart_normal (σ : Setup) (x : Sp σ.R) :
    IsLocallyNoetherian (σ.C x).G.left ∧ ∀ z : (σ.C x).G.left, IsIntegrallyClosed ((σ.C x).G.left.presheaf.stalk z) := by
  have hs : Smooth (σ.C x).G.hom := (σ.C x).semi.smooth
  obtain ⟨h1, h2⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (σ.C x).R
  refine ⟨LocallyOfFiniteType.isLocallyNoetherian (σ.C x).G.hom, fun z => ?_⟩
  have := (stalk_normal (σ.C x).R ((σ.C x).G.hom z)).1
  have := (stalk_normal (σ.C x).R ((σ.C x).G.hom z)).2
  exact (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_of_smooth (σ.C x).G.hom z).2

/- English proof (translation)
Introduce `σ x k v`. Establish `hV1 : ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → (k • σ.D₁ x).IsEqn z 1` using `fun z hz => by`. Simplify using `using (σ.noVert x z hz).nsmul k`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `⟨fun z => h _, fun z hz => ?_⟩` and prove the remaining obligations. Use `(hV1 z hz).regularAt_iff.1 (h z)` as an intermediate fact. Simplify using `using this`. Introduce and unpack `⟨h1, h2⟩ y`. Take `⟨hLN, hN⟩` from `chart_normal σ x`.

Take `⟨g, hg⟩` from `(k • σ.D₁ x).exists_isEqn y`. Take `⟨U, hyU, hU⟩` from `hg.exists_nhds`. Use `hg.regularAt_iff.2 (GlobalTheory.Hartogs.regAt_of_forall_dvr _ hN _ y fun z hzy hdvr => ?_)` and prove the remaining obligations. Establish `hgz` using `hU z (hzy.mem_open U.isOpen hyU)`. Distinguish the cases in `hzV : z ∈ σ.V x`.

Use `h1 ⟨z, hzV⟩` as an intermediate fact. Rewrite `this` using `[Scheme.Opens.ι_apply]`. Conclude with `hgz.regularAt_iff.1 this`. Establish `hv : Vert (σ.C x).G.hom (σ.ρ x σ.f) z` using `⟨IsDiscreteValuationRing.ringKrullDim_eq_one _, not_not.1 fun h => hzV ((σ.hV x z).2 h)⟩`. Conclude with `hgz.regularAt_iff.1 ((hV1 z hv).regularAt_iff.2 (by simpa using h2 z hv))`.
-/
theorem mem_sec_iff : ∀ (σ : Setup) (x : Sp σ.R) (k : ℕ) (v : (σ.C x).G.left.functionField), v ∈ Sec (σ.D₁ x) k ↔ (∀ z : (σ.V x).toScheme, (k • σ.D₁ x).RegularAt ((σ.V x).ι z) v) ∧ ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → RegAt z v := by
  intro σ x k v
  have hV1 : ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → (k • σ.D₁ x).IsEqn z 1 := fun z hz => by
    simpa using (σ.noVert x z hz).nsmul k
  constructor
  · intro h
    refine ⟨fun z => h _, fun z hz => ?_⟩
    have := (hV1 z hz).regularAt_iff.1 (h z)
    simpa using this
  · rintro ⟨h1, h2⟩ y
    obtain ⟨hLN, hN⟩ := chart_normal σ x
    obtain ⟨g, hg⟩ := (k • σ.D₁ x).exists_isEqn y
    obtain ⟨U, hyU, hU⟩ := hg.exists_nhds
    refine hg.regularAt_iff.2 (GlobalTheory.Hartogs.regAt_of_forall_dvr _ hN _ y fun z hzy hdvr => ?_)
    have hgz := hU z (hzy.mem_open U.isOpen hyU)
    by_cases hzV : z ∈ σ.V x
    · have := h1 ⟨z, hzV⟩
      rw [Scheme.Opens.ι_apply] at this
      exact hgz.regularAt_iff.1 this
    · have hv : Vert (σ.C x).G.hom (σ.ρ x σ.f) z :=
        ⟨IsDiscreteValuationRing.ringKrullDim_eq_one _, not_not.1 fun h => hzV ((σ.hV x z).2 h)⟩
      exact hgz.regularAt_iff.1 ((hV1 z hv).regularAt_iff.2 (by simpa using h2 z hv))

end GlobalTheory.Desc.ChartHartogs
