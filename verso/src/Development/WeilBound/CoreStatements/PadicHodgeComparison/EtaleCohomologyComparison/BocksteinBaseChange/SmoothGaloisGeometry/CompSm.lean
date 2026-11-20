import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.ConnectedSpacePullbackOfIsIntegral
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsStrictlySemistableCompOpenImmersion
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

/- English proof (translation)
Take `⟨⟨N, i, hi, hcomp⟩, ϖ, hϖ, hss⟩` from `hM`. Establish `: IsClosedImmersion U.ι` using `.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hU)`. Use `⟨⟨N, U.ι ≫ i, inferInstance, by rw [Category.assoc, hcomp]⟩, ϖ, hϖ, ?_⟩` and prove the remaining obligations. Conclude with `isStrictlySemistable_comp_openImmersion ϖ M.p hss U.ι`.
-/
theorem Model.good_sub (M : Model l K) (hM : M.Good) (U : M.X.Opens) (hU : IsClosed (U : Set M.X)) :
    (M.sub U).Good := by
  obtain ⟨⟨N, i, hi, hcomp⟩, ϖ, hϖ, hss⟩ := hM
  have : IsClosedImmersion U.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hU)
  refine ⟨⟨N, U.ι ≫ i, inferInstance, by rw [Category.assoc, hcomp]⟩, ϖ, hϖ, ?_⟩
  exact isStrictlySemistable_comp_openImmersion ϖ M.p hss U.ι

/- English proof (translation)
Use `hM.2` as an intermediate fact. Conclude with `⟨M.good_sub hM.1 U hU, inferInstanceAs (Smooth (U.ι ≫ M.p))⟩`.
-/
theorem Model.sm_sub (M : Model l K) (hM : M.Sm) (U : M.X.Opens) (hU : IsClosed (U : Set M.X)) :
    (M.sub U).Sm := by
  have := hM.2
  exact ⟨M.good_sub hM.1 U hU, inferInstanceAs (Smooth (U.ι ≫ M.p))⟩

/- English proof (translation)
Use `OK_dvr (l := l) (K := K)` as an intermediate fact. Take `⟨⟨N, i, hi, hcomp⟩, -⟩` from `hM`. Establish `: IsProper (PSpace.str (OK l K) N)` using `isProper_str _ N`. Establish `: IsLocallyNoetherian M.X`. Conclude with `LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str (OK l K) N)`.

Establish `: CompactSpace M.X`. Conclude with `QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str (OK l K) N)`. Establish `: IsNoetherian M.X` using `{}`. Use `infer_instance`.
-/
theorem Model.noetherianSpace [FiniteDimensional ℚ_[l] K] (M : Model l K) (hM : M.Good) :
    NoetherianSpace M.X := by
  have := OK_dvr (l := l) (K := K)
  obtain ⟨⟨N, i, hi, hcomp⟩, -⟩ := hM
  have : IsProper (PSpace.str (OK l K) N) := isProper_str _ N
  have : IsLocallyNoetherian M.X := by
    exact LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str (OK l K) N)
  have : CompactSpace M.X := by
    exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str (OK l K) N)
  have : IsNoetherian M.X := {}
  infer_instance

/- English proof (translation)
Use `OK_dvr (l := l) (K := K)` as an intermediate fact. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (OK l K)`. Use `OK_away hϖ` as an intermediate fact. Conclude with `IsOpenImmersion.of_isLocalization (S := K) ϖ`.
-/
theorem isOpenImmersion_gen [FiniteDimensional ℚ_[l] K] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (OK l K).subtype)) := by
  have := OK_dvr (l := l) (K := K)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (OK l K)
  have := OK_away hϖ
  exact IsOpenImmersion.of_isLocalization (S := K) ϖ

/- English proof (translation)
Introduce `l _ K _`. Use `OK_dvr (l := l) (K := K)` as an intermediate fact. Use `compM_of _ isOpenImmersion_gen (fun M hM U hU ↦ M.sm_sub hM U hU) (fun M hM ↦ M.noetherianSpace hM.1) ?_` and prove the remaining obligations. Introduce `M hM`. Use `hM.2` as an intermediate fact.

Establish `hS : GlobalTheory.IsNormalScheme (Spec (CommRingCat.of (OK l K)))` using `inferInstance`. Use `⟨GlobalTheory.isNormalScheme_of_smooth M.p, LocallyOfFiniteType.isLocallyNoetherian M.p, Flat.generalizingMap M.p, inferInstance⟩` and prove the remaining obligations.
-/
theorem compSm : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
    CompM (Model.Sm (l := l) (K := K)) := by
  intro l _ K _
  have := OK_dvr (l := l) (K := K)
  refine compM_of _ isOpenImmersion_gen (fun M hM U hU ↦ M.sm_sub hM U hU) (fun M hM ↦ M.noetherianSpace hM.1) ?_
  intro M hM
  have := hM.2
  have hS : GlobalTheory.IsNormalScheme (Spec (CommRingCat.of (OK l K))) := inferInstance
  refine ⟨GlobalTheory.isNormalScheme_of_smooth M.p, LocallyOfFiniteType.isLocallyNoetherian M.p,
    Flat.generalizingMap M.p, inferInstance⟩

end CrystallineSemistableComparison
