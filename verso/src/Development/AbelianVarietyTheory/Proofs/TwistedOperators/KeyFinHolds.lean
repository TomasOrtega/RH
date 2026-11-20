import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowEx

/- English proof (translation)
Introduce `P Ξ hΞ`. Set `U : Key P` to `{p | p.1 ∈ Ξ ∧ {w | ¬ p.1.UnrAt w}.Finite ∧ ∀ w ∈ p.2, ¬ p.1.UnrAt w}`. Establish `hU : U.Finite`. Use `(hΞ.biUnion (t := fun ξ => {p ∈ U | p.1 = ξ}) fun ξ _ => ?_).subset fun p hp => Set.mem_biUnion hp.1 ⟨hp, rfl⟩` and prove the remaining obligations. Distinguish the cases in `hf : {w | ¬ ξ.UnrAt w}.Finite`.

Use `((hf.toFinset.powerset.finite_toSet).image fun Q => (ξ, Q)).subset ?_` and prove the remaining obligations. Introduce and unpack `⟨a, Q⟩ ⟨h, rfl⟩`. Conclude with `⟨Q, Finset.mem_coe.2 (Finset.mem_powerset.2 fun w hw => hf.mem_toFinset.2 (h.2.2 w hw)), rfl⟩`. Use `Set.finite_empty.subset ?_` and prove the remaining obligations. Introduce and unpack `⟨a, Q⟩ ⟨h, rfl⟩`.

Conclude with `hf h.2.1`. Use `⟨{κ | κ ⊆ U}, hU.finite_subsets, ?_⟩` and prove the remaining obligations. Introduce and unpack `X T L μ₀ rfl hL h`. Use `⟨keyOf L, ?_, HEq.rfl⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨t, rfl⟩`.

Take `⟨ξ, h1, h2⟩` from `h t`. Use `⟨by rw [← eq_of_heq h2] at h1; exact h1, ?_, fun w hw => (hL.Q_ram t w).2 (Or.inl hw)⟩` and prove the remaining obligations. Use `((L.Q t).finite_toSet.union ((L.Q t).finite_toSet.image Formalism.DivisionValues.conjPl)).subset fun w hw => ?_` and prove the remaining obligations. Break down `(hL.Q_ram t w).1 hw with h | ⟨w', h, h'⟩` into its components or cases. Conclude with `Or.inl h`.

Conclude with `Or.inr ⟨w', h, (GlobalTheory.GoodPrimes.isConjPl_iff.1 h').symm⟩`.
-/
theorem keyFin_holds : KeyFin := by
  classical
  intro P Ξ hΞ
  let U : Key P := {p | p.1 ∈ Ξ ∧ {w | ¬ p.1.UnrAt w}.Finite ∧ ∀ w ∈ p.2, ¬ p.1.UnrAt w}
  have hU : U.Finite := by
    refine (hΞ.biUnion (t := fun ξ => {p ∈ U | p.1 = ξ}) fun ξ _ => ?_).subset fun p hp => Set.mem_biUnion hp.1 ⟨hp, rfl⟩
    by_cases hf : {w | ¬ ξ.UnrAt w}.Finite
    · refine ((hf.toFinset.powerset.finite_toSet).image fun Q => (ξ, Q)).subset ?_
      rintro ⟨a, Q⟩ ⟨h, rfl⟩
      exact ⟨Q, Finset.mem_coe.2 (Finset.mem_powerset.2 fun w hw => hf.mem_toFinset.2 (h.2.2 w hw)), rfl⟩
    · refine Set.finite_empty.subset ?_
      rintro ⟨a, Q⟩ ⟨h, rfl⟩
      exact hf h.2.1
  refine ⟨{κ | κ ⊆ U}, hU.finite_subsets, ?_⟩
  rintro X T L μ₀ rfl hL h
  refine ⟨keyOf L, ?_, HEq.rfl⟩
  rintro _ ⟨t, rfl⟩
  obtain ⟨ξ, h1, h2⟩ := h t
  refine ⟨by rw [← eq_of_heq h2] at h1; exact h1, ?_, fun w hw => (hL.Q_ram t w).2 (Or.inl hw)⟩
  refine ((L.Q t).finite_toSet.union ((L.Q t).finite_toSet.image Formalism.DivisionValues.conjPl)).subset fun w hw => ?_
  rcases (hL.Q_ram t w).1 hw with h | ⟨w', h, h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨w', h, (GlobalTheory.GoodPrimes.isConjPl_iff.1 h').symm⟩

end GlobalTheory.RowEx
