import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTransStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumKeepsAdmissibleFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumIsUnitaryAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportedWeilDatumAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSchroedingerModelSiegelRuleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePlaceVacuumAnyDarbouxCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUnitaryAdelicIsoMapHaarAndFundamentalDo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxCoordinatesTensorHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTauEOverRealPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNegConjMemberHermitianLatticeSpaceData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareSkewSumSpaceIsSkewHermitianSelfDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameCoordsMemSelfDualLatticeCoordsIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieAlgebrasAtPlaceActFockVectorsByFockOperators
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterUnramifiedOffBad
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosedSubgroupOfLocalStabilizerPairs
import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.ExistsHaarFundDom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAtCofinitelyManyPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedPlaceOfUnramifiedOnePrimeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyAlgHomCompletionOfSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsWeilDatumCompGroupSwappingSymplecticEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivConjOfGramTransposeEqNegStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivInvTransposeOfGramInvStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTransposeGramCoordinateHomeomorphSymplectiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticHomTransposeGramDarbouxStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TripleDarboux

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model SplitsFully Chars HasExp)

/- English proof (translation)
Use `{ cm := GlobalTheory.AdelicU.isCMExt_host D galois := D.host.hostE_isGalois unram := GlobalTheory.InertOfConj.unram D std := GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ inert := ?_ psiP := fun v hv => GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ v fun hle => hP v hv (Ideal …` and prove the remaining obligations. Introduce `v w hw`. Establish `hns : ¬ Formalism.MainNotions.KudlaSiegelWeil.Split D v`. Introduce and unpack `⟨w1, w2, hne, h1, h2⟩`. Apply `hne` to reduce the goal to its premises.

Establish `key : ∀ u : HeightOneSpectrum (𝓞 D.host.E), Formalism.MainNotions.KudlaSiegelWeil.Over D u v → u = w` using `fun u hu => by`. Establish `hle : w.asIdeal ≤ u.asIdeal`. Rewrite using `[← hw]`. Conclude with `Ideal.map_le_iff_le_comap.2 (le_of_eq hu.symm)`. Conclude with `HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top hle).symm`.

Rewrite using `[key w1 h1, key w2 h2]`. Take `⟨h2, h3, hd, -⟩` from `Formalism.MainNotions.KudlaSiegelWeil.inert_conditions_hold D v hns`. Conclude with `⟨h2, h3, GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ v hd⟩`.
-/
theorem base_isGood {D : D7} (B : Base D.host.F D.host.E) (hψ : IsStdChar D B.ψ (-1))
    (hP : ∀ v ∈ B.P, ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) : B.IsGood D.sp.cm.sig := by
  refine { cm := GlobalTheory.AdelicU.isCMExt_host D
           galois := D.host.hostE_isGalois
           unram := GlobalTheory.InertOfConj.unram D
           std := GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ
           inert := ?_
           psiP := fun v hv => GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ v fun hle => hP v hv (Ideal.dvd_iff_le.2 hle) }
  intro v w hw
  have hns : ¬ Formalism.MainNotions.KudlaSiegelWeil.Split D v := by
    rintro ⟨w1, w2, hne, h1, h2⟩
    apply hne
    have key : ∀ u : HeightOneSpectrum (𝓞 D.host.E), Formalism.MainNotions.KudlaSiegelWeil.Over D u v → u = w := fun u hu => by
      have hle : w.asIdeal ≤ u.asIdeal := by
        rw [← hw]
        exact Ideal.map_le_iff_le_comap.2 (le_of_eq hu.symm)
      exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top hle).symm
    rw [key w1 h1, key w2 h2]
  obtain ⟨h2, h3, hd, -⟩ := Formalism.MainNotions.KudlaSiegelWeil.inert_conditions_hold D v hns
  exact ⟨h2, h3, GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ v hd⟩

/- English proof (translation)
Establish `hn : D.host.QS ≠ 0` using `D.host.QS_pos.ne'`. Establish `hq : D.host.q ≠ 0` using `D.host.hyp.1.ne_zero`. Establish `hd : D.host.d ≠ 0` using `D.host.hyp.2.1.ne_zero`. Establish `hm : D.host.QS * D.host.q * D.host.d ≠ 0` using `mul_ne_zero (mul_ne_zero hn hq) hd`. Take `⟨p, hp, hlt, hc⟩` from `Nat.exists_prime_gt_modEq_one (∑ u ∈ S, Ideal.absNorm u.asIdeal) hm`.

Take `⟨h1, -, -⟩` from `GlobalTheory.HostSplit.split_completely_of_modEq_one D.R D.host p hp hc`. Establish `h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E`. Rewrite using `[← GlobalTheory.HostSplit.ncard_placesOver _ hp]`. Conclude with `h1`. Take `⟨v, hv⟩` from `GlobalTheory.SplitChoice.exists_place_over D.host.F hp`.

Use `⟨v, fun hu => ?_, ?_, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.SplitChoice.natCast_notMem_of_absNorm_lt v hp ?_ hv` and prove the remaining obligations. Use `Finset.single_le_sum (f := fun u : HeightOneSpectrum (𝓞 D.host.F) => Ideal.absNorm u.asIdeal) (fun _ _ => Nat.zero_le _) hu` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hmax : (Ideal.span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible`.

Establish `hle : Ideal.span {(p : ℤ)} ≤ v.asIdeal.under ℤ`. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]`. Simplify using `using hv`. Establish `hunder : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)}` using `(hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle).symm`. Unfold `SplitsFully`.

Rewrite using `[hunder]`. Conclude with `h`. Rewrite using `[GlobalTheory.AdelicU.nonempty_split_iff (GlobalTheory.AdelicU.isCMExt_host D)]`. Conclude with `GlobalTheory.GoodPlace.ncard_primesOver_eq_two (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 hp h v hv`.
-/
theorem exists_good_place (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∃ v₁ : HeightOneSpectrum (𝓞 D.host.F), v₁ ∉ S ∧ SplitsFully D.host.E v₁ ∧
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v₁) := by
  classical
  have hn : D.host.QS ≠ 0 := D.host.QS_pos.ne'
  have hq : D.host.q ≠ 0 := D.host.hyp.1.ne_zero
  have hd : D.host.d ≠ 0 := D.host.hyp.2.1.ne_zero
  have hm : D.host.QS * D.host.q * D.host.d ≠ 0 := mul_ne_zero (mul_ne_zero hn hq) hd
  obtain ⟨p, hp, hlt, hc⟩ := Nat.exists_prime_gt_modEq_one (∑ u ∈ S, Ideal.absNorm u.asIdeal) hm
  obtain ⟨h1, -, -⟩ := GlobalTheory.HostSplit.split_completely_of_modEq_one D.R D.host p hp hc
  have h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E := by
    rw [← GlobalTheory.HostSplit.ncard_placesOver _ hp]
    exact h1
  obtain ⟨v, hv⟩ := GlobalTheory.SplitChoice.exists_place_over D.host.F hp
  refine ⟨v, fun hu => ?_, ?_, ?_⟩
  · refine GlobalTheory.SplitChoice.natCast_notMem_of_absNorm_lt v hp ?_ hv
    have := Finset.single_le_sum (f := fun u : HeightOneSpectrum (𝓞 D.host.F) => Ideal.absNorm u.asIdeal)
      (fun _ _ => Nat.zero_le _) hu
    omega
  · have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
    have hle : Ideal.span {(p : ℤ)} ≤ v.asIdeal.under ℤ := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
      simpa using hv
    have hunder : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} :=
      (hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle).symm
    unfold SplitsFully
    rw [hunder]
    exact h
  · rw [GlobalTheory.AdelicU.nonempty_split_iff (GlobalTheory.AdelicU.isCMExt_host D)]
    exact GlobalTheory.GoodPlace.ncard_primesOver_eq_two (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 hp h v hv

end GlobalTheory.TripleDarboux

end
