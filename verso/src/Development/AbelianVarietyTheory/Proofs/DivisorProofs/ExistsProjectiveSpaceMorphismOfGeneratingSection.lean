import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionQuotientsTranscendenceBasisBasepointFreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotientSubfieldEqMulRankOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceOrderArithVarietyFubiniStudyDegreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithCharZeroFunctionFieldInjectiveConstantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismProjSpaceBasepointFreeSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapGenericPointEqOfAlgIndependentQuotientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericPointEqFinrankQuotientsStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

/- English proof (translation)
Introduce `k _ X _ p D hX P hA e x hg`. Take `⟨hx, hind, hfin⟩` from `GlobalTheory.T.sectionQuotients_transcendenceBasis_basepointFree k X p D hX P hA e x hg`. Take `⟨hK, hι⟩` from `GlobalTheory.T.projArith_charZero_functionField_injective_constants k X p D hX`. Use `haveI := hX.isDomain`. Use `haveI := hX.finite`.

Use `haveI : CharZero k := ⟨fun a b h => Nat.cast_injective (R := X.functionField) (by`. Use `congrArg (GlobalTheory.toFunctionField p) h` as an intermediate fact. Simplify `this)⟩` using `only [map_natCast]`. Take `⟨hP, -, -⟩` from `GlobalTheory.T.projectiveSpace_order_arithVariety_fubiniStudyDegree k D`. Use `haveI : IsIntegral (PSpace k D) := hP.isIntegral`.

Take `⟨hdeg, hev⟩` from `GlobalTheory.T.finrank_quotientSubfield_eq_mul_rank_order k X.functionField (GlobalTheory.toFunctionField p) D x hι hind`. Take `⟨π, hπ, hc, hiso⟩` from `GlobalTheory.T.exists_morphism_projSpace_basepointFreeSections k X p D hX P e x hg (hx 0)`. Establish `hgen` using `GlobalTheory.T.map_genericPoint_eq_of_algIndependent_quotients k X p D π hπ x (hx 0) hc hev`. Establish `hr` using `GlobalTheory.T.residueDegree_genericPoint_eq_finrank_quotients k X p D π hπ x (hx 0) hc hgen`. Use `⟨inferInstance, π, hπ, hgen, ?_, ?_, hiso⟩` and prove the remaining obligations.

Rewrite using `[hr]`. Introduce `h0`. Use `haveI := hfin`. Establish `: 0 < Module.finrank (ratF x) X.functionField` using `Module.finrank_pos`. Rewrite `this` using `[hdeg, h0, zero_mul]`.

Conclude with `lt_irrefl _ this`. Rewrite using `[hr, hdeg]`.
-/
theorem toProj_gens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ (_ : IsIntegral (PSpace k D)) (π : X ⟶ PSpace k D) (hπ : π ≫ PSpace.str k D = p), π (genericPoint X) = genericPoint (PSpace k D) ∧ π.residueDegree (genericPoint X) ≠ 0 ∧ π.residueDegree (genericPoint X) * Module.finrank ℤ k = Module.finrank (ratF x) X.functionField ∧ ∀ u : SmFn p, IsCan P e 1 x u → ((up P.L u).pow e).Isometric ((ProjSpace.hermitianTwistingSheaf k D).pull π hπ) := by
  intro k _ X _ p D hX P hA e x hg
  obtain ⟨hx, hind, hfin⟩ := GlobalTheory.T.sectionQuotients_transcendenceBasis_basepointFree k X p D hX P hA e x hg
  obtain ⟨hK, hι⟩ := GlobalTheory.T.projArith_charZero_functionField_injective_constants k X p D hX
  haveI := hX.isDomain
  haveI := hX.finite
  haveI : CharZero k := ⟨fun a b h => Nat.cast_injective (R := X.functionField) (by
    have := congrArg (GlobalTheory.toFunctionField p) h
    simpa only [map_natCast] using this)⟩
  obtain ⟨hP, -, -⟩ := GlobalTheory.T.projectiveSpace_order_arithVariety_fubiniStudyDegree k D
  haveI : IsIntegral (PSpace k D) := hP.isIntegral
  obtain ⟨hdeg, hev⟩ := GlobalTheory.T.finrank_quotientSubfield_eq_mul_rank_order k X.functionField (GlobalTheory.toFunctionField p) D x hι hind
  obtain ⟨π, hπ, hc, hiso⟩ := GlobalTheory.T.exists_morphism_projSpace_basepointFreeSections k X p D hX P e x hg (hx 0)
  have hgen := GlobalTheory.T.map_genericPoint_eq_of_algIndependent_quotients k X p D π hπ x (hx 0) hc hev
  have hr := GlobalTheory.T.residueDegree_genericPoint_eq_finrank_quotients k X p D π hπ x (hx 0) hc hgen
  refine ⟨inferInstance, π, hπ, hgen, ?_, ?_, hiso⟩
  · rw [hr]
    intro h0
    haveI := hfin
    have : 0 < Module.finrank (ratF x) X.functionField := Module.finrank_pos
    rw [hdeg, h0, zero_mul] at this
    exact lt_irrefl _ this
  · rw [hr, hdeg]

end GlobalTheory.HSAmp
