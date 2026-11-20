import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleDegreeCountAlongFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePrimeValuationSumEqLogGapFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagonalRamifiedBoundAlongFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonnegConstDiscriminantTermLeBudgetFamilyAStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimesLossLogSumAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleOffTypeFamilyBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePrimeSizesLeBudgetFamilyStatement

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `eps Fm h0 h1 hT hG`. Take `⟨Cdeg, xd, -, hdeg⟩` from `GlobalTheory.T.exists_degreeCountBound_of_eps_lt_one_div_52 Fm h0 h1`. Take `⟨Cg, xg, hCg, hsz⟩` from `GlobalTheory.T.typePrime_sizes_le_budget_family Fm h0 h1 hG Cdeg`. Take `⟨CT, xT, -, hoT⟩` from `GlobalTheory.T.admissible_off_type_family_bound Fm h0 h1 hT`. Take `⟨CG, xG, -, hoG⟩` from `GlobalTheory.T.exists_const_stabiliserLog_bound_along_family Fm h0 h1 hT hG`.

Take `⟨Cd, xD, -, hoD⟩` from `GlobalTheory.T.offDiagonalRamified_bound_along_family' Fm h0 h1`. Take `⟨CI, xI, -, hoI⟩` from `GlobalTheory.T.inertPrimeLossBound_eventually Fm h0 h1`. Use `⟨Cdeg, Cg, CT, CG, Cd, CI, max xd (max xg (max xT (max xG (max xD xI)))), hCg, ?_⟩` and prove the remaining obligations. Introduce `x hx0 hx i`. Establish `a1 : xd ≤ x` using `(le_max_left _ _).trans hx0`.

Establish `r1` using `(le_max_right _ _).trans hx0`. Establish `a2 : xg ≤ x` using `(le_max_left _ _).trans r1`. Establish `r2` using `(le_max_right _ _).trans r1`. Establish `a3 : xT ≤ x` using `(le_max_left _ _).trans r2`. Establish `r3` using `(le_max_right _ _).trans r2`.

Establish `a4 : xG ≤ x` using `(le_max_left _ _).trans r3`. Establish `r4` using `(le_max_right _ _).trans r3`. Establish `a5 : xD ≤ x` using `(le_max_left _ _).trans r4`. Establish `a6 : xI ≤ x` using `(le_max_right _ _).trans r4`. Conclude with `⟨fun u j h => (Fm.D x i).T_ne_g u j h.symm, GlobalTheory.T.normDecompositionCond_famP Fm x hx i, hdeg x a1 hx i, hsz x a2 hx i, hoT x a3 hx i, hoG x a4 hx i, hoD x a5 hx i, hoI x a6 hx i⟩`.
-/
theorem familySecondComplementInputs_of_tuSize_of_dGamSize : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → DGamSize Fm →
    Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm := by
  intro eps Fm h0 h1 hT hG
  obtain ⟨Cdeg, xd, -, hdeg⟩ := GlobalTheory.T.exists_degreeCountBound_of_eps_lt_one_div_52 Fm h0 h1
  obtain ⟨Cg, xg, hCg, hsz⟩ := GlobalTheory.T.typePrime_sizes_le_budget_family Fm h0 h1 hG Cdeg
  obtain ⟨CT, xT, -, hoT⟩ := GlobalTheory.T.admissible_off_type_family_bound Fm h0 h1 hT
  obtain ⟨CG, xG, -, hoG⟩ := GlobalTheory.T.exists_const_stabiliserLog_bound_along_family Fm h0 h1 hT hG
  obtain ⟨Cd, xD, -, hoD⟩ := GlobalTheory.T.offDiagonalRamified_bound_along_family' Fm h0 h1
  obtain ⟨CI, xI, -, hoI⟩ := GlobalTheory.T.inertPrimeLossBound_eventually Fm h0 h1
  refine ⟨Cdeg, Cg, CT, CG, Cd, CI, max xd (max xg (max xT (max xG (max xD xI)))), hCg, ?_⟩
  intro x hx0 hx i
  have a1 : xd ≤ x := (le_max_left _ _).trans hx0
  have r1 := (le_max_right _ _).trans hx0
  have a2 : xg ≤ x := (le_max_left _ _).trans r1
  have r2 := (le_max_right _ _).trans r1
  have a3 : xT ≤ x := (le_max_left _ _).trans r2
  have r3 := (le_max_right _ _).trans r2
  have a4 : xG ≤ x := (le_max_left _ _).trans r3
  have r4 := (le_max_right _ _).trans r3
  have a5 : xD ≤ x := (le_max_left _ _).trans r4
  have a6 : xI ≤ x := (le_max_right _ _).trans r4
  exact ⟨fun u j h => (Fm.D x i).T_ne_g u j h.symm, GlobalTheory.T.normDecompositionCond_famP Fm x hx i, hdeg x a1 hx i, hsz x a2 hx i,
    hoT x a3 hx i, hoG x a4 hx i, hoD x a5 hx i, hoI x a6 hx i⟩

end GlobalTheory
