import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomEqOnAdjoinSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaConjUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfConjOnFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGalConjEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaAtOfIsEtaConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiOfOverK
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharFiniteOrderOfTrivialAtInfinity
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResFinEqOneOfAway
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResEtaHasInfExpOfIsEtaConj
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAdjointScalarParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CircleEqOneIffOfConj
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionDeterminantRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaCharacterUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrAtEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormIntegrality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolShapeOfOverK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingConjugateOscillatorFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCHLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormGaloisEquivariance
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormScalarExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFockVacuumProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorFockVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorMaximalCompactBasisSubstitut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeilRepresentationSixth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorTorusAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientConjugateThetaForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilMaximalCompactFockSubstitutionCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOfLowSmoothLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorsHolomorphicModelUniqueUpToPhaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeilRepresentationFifth
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingConjugateOscillatorEighth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormRationality
import Formalism.LocalToGlobal.ProjectiveLattices.FnDefC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingConjugateOscillatorNinth
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemLatGHat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormNonvanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevMemCuspA
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormHeckeEigen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilVacuumFiniteSelfDualLatticeSplittingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumStabilizerSplittingCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeilRepresentationSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFourth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeilRepresentationThird
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReframeVStdOfPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasis
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.TransformIndicator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InverseSelfDualFrameStandardSpaceIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDualFamilySelfDualHermitianSpace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeOfOddExponentSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfHeckeCharUnramifi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointSmulIntegralOfFourierCoeffNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubIdempotentSmulMemLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentSumConjSumOrthogonalDvdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicMatrixMemLatticeOfColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenMapTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointSmulIntegralOfFourierCoeffNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinTensAlgebraMap
import Development.AbelianVarietyTheory.Definitions.Divisors.ConstantUniqueOfEqProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormSignExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignForWeilModelFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanDetSetIffAdelicLatticeValuationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumeratorIdealOfAntiInvariantDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicCharacterEqProdUnramifiedValueZpowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIdempotentComponentsConjValuationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotIsOfFinOrderUnitQuot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FgOfSmulLe
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThirdStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormPeriodRelation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormSqOfMulConjEqDifferentIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingConjugateOscillatorSixth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormSignIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapTypingsEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoprimeScalarForEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoprimeScalarCentralElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfIsVacO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeMarkingAdmissible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreDictionaryGoodAtGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicShapeIntegralWeightGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ActLevAndActBC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkingRootsDilationCoprimeLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsWeightCompat

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `T _ _ _ _ _ _ fw _ σ` and use `overK_iff_good_of_pins T fw.alg_eq fw.laws.pins σ`.
-/
theorem overK_iff_good_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ ↔ GoodEmb T.Q.c (res T σ) :=
  fun T _ _ _ _ _ _ fw _ σ => overK_iff_good_of_pins T fw.alg_eq fw.laws.pins σ

end GlobalTheory.GalLift

end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjCharUnique

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F _ i σ`. Use `⟨fun μ' μ'' h g => eq_of_conj_on_finite (σ := σ) (μ := R.mu0 ((i : ℕ) + 1)) h.1 g.1 (fun x hx => (h.2.2.2.1 x hx).elim fun y hy => ⟨_, hy⟩) (fun x hx => (g.2.2.2.1 x hx).elim fun y hy => ⟨_, hy⟩), fun η' η'' h g => GlobalTheory.UnramCharUnique.isEtaConj_unique D σ R.eta η' η'' h …` and prove the remaining obligations.
-/
theorem conjChar_unique_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), (∀ μ' μ'', ChiAt R i σ μ' → ChiAt R i σ μ'' → μ' = μ'') ∧ ∀ η' η'', IsEtaConj σ R.eta η' → IsEtaConj σ R.eta η'' → η' = η'' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F _ i σ
  refine ⟨fun μ' μ'' h g => eq_of_conj_on_finite (σ := σ) (μ := R.mu0 ((i : ℕ) + 1)) h.1 g.1
    (fun x hx => (h.2.2.2.1 x hx).elim fun y hy => ⟨_, hy⟩) (fun x hx => (g.2.2.2.1 x hx).elim fun y hy => ⟨_, hy⟩),
    fun η' η'' h g => GlobalTheory.UnramCharUnique.isEtaConj_unique D σ R.eta η' η'' h g⟩

end GlobalTheory.ConjCharUnique

end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaConjType

open Formalism.L2.Host Formalism.L2.JoinChr

section General

variable {E : Type} [Field E] [NumberField E]

variable {L : Type} [Field L] (ι σ : L →+* ℂ) {χ χ' : HChar E} (hu : ∀ P, χ.UnrAt P) (hu' : ∀ P, χ'.UnrAt P)
  (y : HeightOneSpectrum (𝓞 E) → L) (hy : ∀ P, ι (y P) = ((χ.val P : ℂˣ) : ℂ) * (rt P : ℂ))
  (hy' : ∀ P, σ (y P) = ((χ'.val P : ℂˣ) : ℂ) * (rt P : ℂ))

include hu hu' hy hy'

end General

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hR _ σ hσ η' hη`. Take `⟨χ', hc⟩` from `GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D η' hη.1`. Establish `h` using `isEtaT_of_conj hσ hR.lev.eta hc R.C.isEta hη`. Establish `he` using `GlobalTheory.Mem.EtaTilde.isEta_res D η' χ' hc h`. Use `⟨⟨⟨_, he⟩, fun η hη' a => ?_⟩, fun τ => ⟨1, by norm_num, ?_, fun θ hθ x hx hx' => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique hη' he, pow_one, MonoidHom.comp_apply]`. Take `⟨⟨θ', hθ'⟩, -⟩` from `GlobalTheory.Member.infiniteAdele_bijective D`. Conclude with `⟨fun τ => θ' (tauE D τ), fun τ => hθ' _⟩`. Rewrite using `[GlobalTheory.Mem.EtaTilde.val_infinite D η' χ' hc h.unr _ h.inf θ hθ x hx, Finset.prod_eq_single τ (fun τ' _ hτ => by rw [hx' τ' hτ]; simp) (by simp)]`.
-/
theorem resEta_hasInfExp_of_isEtaConj_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ η', IsEtaConj σ R.eta η' → ResEta D η' 1 ∧ ∀ ρ, HasInfExp D η' ρ (1 / 2) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR _ σ hσ η' hη
  obtain ⟨χ', hc⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D η' hη.1
  have h := isEtaT_of_conj hσ hR.lev.eta hc R.C.isEta hη
  have he := GlobalTheory.Mem.EtaTilde.isEta_res D η' χ' hc h
  refine ⟨⟨⟨_, he⟩, fun η hη' a => ?_⟩, fun τ => ⟨1, by norm_num, ?_, fun θ hθ x hx hx' => ?_⟩⟩
  · rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique hη' he, pow_one, MonoidHom.comp_apply]
  · obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
    exact ⟨fun τ => θ' (tauE D τ), fun τ => hθ' _⟩
  · rw [GlobalTheory.Mem.EtaTilde.val_infinite D η' χ' hc h.unr _ h.inf θ hθ x hx,
      Finset.prod_eq_single τ (fun τ' _ hτ => by rw [hx' τ' hτ]; simp) (by simp)]

end GlobalTheory.EtaConjType

end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ hb hat`. Use `⟨logHookSum_of_bijective i _ hb, fun μ' η' hμ hη hres hinf => ?_⟩` and prove the remaining obligations. Conclude with `{ vpos := hC.models.vpos i sig := fun ρ => D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _ lab_bij := hb lab_at := hat par := fun ρ => if_pos (hat ρ) gap := fun ρ n hn => GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents.gap (D.hc (lab σ ρ)) i hn mu_res := ⟨hres. …`.
-/
theorem hypConj_of_chars_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), Function.Bijective (lab (D := D) σ) → (∀ ρ, labE σ (lab σ ρ) = tauE D ρ) → logHookSum i (lab σ) = logHookSum i id ∧ ∀ (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → ResEta D η' 1 → (∀ ρ, HasInfExp D η' ρ (1 / 2)) → HypConj R i σ μ' η' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ hb hat
  refine ⟨logHookSum_of_bijective i _ hb, fun μ' η' hμ hη hres hinf => ?_⟩
  exact
    { vpos := hC.models.vpos i
      sig := fun ρ => D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
      lab_bij := hb
      lab_at := hat
      par := fun ρ => if_pos (hat ρ)
      gap := fun ρ n hn => GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents.gap (D.hc (lab σ ρ)) i hn
      mu_res := ⟨hres.1, fun η _ a => (hμ.2.1 a).trans (pow_zero _).symm⟩
      mu_inf := hμ.2.2.1
      mu_cond := fun x hx => (hμ.2.2.2.1 x hx.1).elim fun y hy =>
        circle_eq_one_iff_of_conj D.what₂.embLL σ _ _ y hy.1 hy.2
      eta_res := hres
      eta_unr := hη.2.1
      eta_inf := hinf }

end GlobalTheory.GalLift

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F h i`. Establish `hL` using `h.lev`. Establish `hW` using `h.thP.ωP i A.μ0`. Establish `hr : Odd D.R.r`. Use `D.R.m_add_three_le_k` as an intermediate fact.

Take `⟨a, ha⟩` from `D.R.k_even`. Take `⟨b, hb⟩` from `D.R.m_even`. Conclude with `⟨a + b - 1, by simp only [Ranks.r]; omega⟩`. Establish `rV : (Vc D i).rank = D.R.r + D.R.t` using `D.sp.V_rank _ (Nat.le_add_left _ _) i.2`. Establish `rW : (Wc D i).rank = D.R.r` using `D.sp.W_rank _ (Nat.le_add_left _ _) i.2`.

Establish `hev : Even (Vc D i).rank` using `rV ▸ hr.add_odd D.R.t_odd`. Use `⟨GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hL.eta R.C.isEta _ _ _ hW.resS hW.resT (hev.add_odd (rW ▸ hr)), MonoidHom.ext fun x => GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0) x, Finset.eq_empty_of_forall_notMem fun P hP => (hL.Q_ram A …` and prove the remaining obligations. Take `⟨-, e, ⟨⟨es, hes, -⟩, -⟩, -⟩` from `h.thP.vP i t`. Establish `key` using `fun P (hP : P.under (𝓞 D.host.F) = v) => (GlobalTheory.levCh_unramified_places D T0 R.toLevCh A.μ0 hL t).2.2.2 P fun PP hPP => by`. Rewrite using `[hP]`.

Conclude with `GlobalTheory.AdTh.RecPair.under_ne (hes PP (Finset.mem_union.2 hPP)) hv`. Establish `u1` using `GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.mu0 i) v ε hv.1 fun P hP => (key P hP).2 i`. Establish `u2` using `GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.xi t) v ε hv.1 fun P hP => (key P hP).1`. Establish `u3` using `GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ hL.eta v ε hv.1 fun P _ => R.C.isEta.unr P`. Establish `u4 : GlobalTheory.WeilParts.UnramAt ε (R.toLevCh.mu t ((i : ℕ) + 1))` using `fun x a b c => by show R.mu0 ((i : ℕ) + 1) x * R.xi t x = 1`.

Rewrite using `[u1 x a b c, u2 x a b c, one_mul]`. Use `⟨u4, fun x a b c => ?_⟩` and prove the remaining obligations. Use `show R.toLevCh.mu t ((i : ℕ) + 1) x * (R.eta x)⁻¹ = 1`. Rewrite using `[u4 x a b c, u3 x a b c, inv_one, one_mul]`.
-/
theorem chars_of_lift_ofFive : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), IsEtaTilde D R.eta ∧ R.xi A.μ0 = 1 ∧ R.Q A.μ0 = ∅ ∧ ∀ t v ε, NonSplitAt D v ε → UnramAt ε (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 ∧ UnramAt ε (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i
  classical
  have hL := h.lev
  have hW := h.thP.ωP i A.μ0
  have hr : Odd D.R.r := by
    have := D.R.m_add_three_le_k
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hev : Even (Vc D i).rank := rV ▸ hr.add_odd D.R.t_odd
  refine ⟨GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hL.eta R.C.isEta _ _ _ hW.resS hW.resT (hev.add_odd (rW ▸ hr)),
    MonoidHom.ext fun x => GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0) x,
    Finset.eq_empty_of_forall_notMem fun P hP =>
      (hL.Q_ram A.μ0 P).2 (Or.inl hP) (by rw [hL.xi_base]; exact fun _ _ => rfl), fun t v ε hv => ?_⟩
  obtain ⟨-, e, ⟨⟨es, hes, -⟩, -⟩, -⟩ := h.thP.vP i t
  have key := fun P (hP : P.under (𝓞 D.host.F) = v) =>
    (GlobalTheory.levCh_unramified_places D T0 R.toLevCh A.μ0 hL t).2.2.2 P fun PP hPP => by
      rw [hP]
      exact GlobalTheory.AdTh.RecPair.under_ne (hes PP (Finset.mem_union.2 hPP)) hv
  have u1 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.mu0 i) v ε hv.1 fun P hP => (key P hP).2 i
  have u2 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.xi t) v ε hv.1 fun P hP => (key P hP).1
  have u3 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ hL.eta v ε hv.1 fun P _ => R.C.isEta.unr P
  have u4 : GlobalTheory.WeilParts.UnramAt ε (R.toLevCh.mu t ((i : ℕ) + 1)) := fun x a b c => by
    show R.mu0 ((i : ℕ) + 1) x * R.xi t x = 1
    rw [u1 x a b c, u2 x a b c, one_mul]
  refine ⟨u4, fun x a b c => ?_⟩
  show R.toLevCh.mu t ((i : ℕ) + 1) x * (R.eta x)⁻¹ = 1
  rw [u4 x a b c, u3 x a b c, inv_one, one_mul]

end GlobalTheory.OneMapRef

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.Facts

/- English proof (translation)
Establish `hc` using `chars_of_lift_ofFive D G Pl0 T0 A Ks R F hR i`. Establish `u1 : UnramAt ε μ'` using `fun x a b c => by`. Establish `h0 : R.mu0 ((i : ℕ) + 1) x * R.xi A.μ0 x = 1` using `(hc.2.2.2 A.μ0 v ε hv).1 x a b c`. Rewrite `h0` using `[hc.2.1, MonoidHom.one_apply, mul_one]`. Conclude with `(hμ.2.2.2.1 x (infPart_eq_one hv.1 a)).elim fun y hy => (circle_eq_one_iff_of_conj D.what₂.embLL σ _ _ y hy.1 hy.2).2 h0`.

Use `⟨u1, fun x a b c => ?_⟩` and prove the remaining obligations. Use `show μ' x * (η' x)⁻¹ = 1`. Rewrite using `[u1 x a b c, hη.2.1 x (infPart_eq_one hv.1 a) b c, inv_one, one_mul]`.
-/
theorem unramAt_conj_ofFive {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (hR : GlobalTheory.Core5 R F)
    (i : Fin D.R.m) {σ : D.what₂.LL →+* ℂ} {μ' η' : (AE D)ˣ →* Circle} (hμ : ChiAt R i σ μ') (hη : IsEtaConj σ R.eta η')
    {v ε} (hv : NonSplitAt D v ε) : UnramAt ε μ' ∧ UnramAt ε (μ' * η'⁻¹) := by
  have hc := chars_of_lift_ofFive D G Pl0 T0 A Ks R F hR i
  have u1 : UnramAt ε μ' := fun x a b c => by
    have h0 : R.mu0 ((i : ℕ) + 1) x * R.xi A.μ0 x = 1 := (hc.2.2.2 A.μ0 v ε hv).1 x a b c
    rw [hc.2.1, MonoidHom.one_apply, mul_one] at h0
    exact (hμ.2.2.2.1 x (infPart_eq_one hv.1 a)).elim fun y hy =>
      (circle_eq_one_iff_of_conj D.what₂.embLL σ _ _ y hy.1 hy.2).2 h0
  refine ⟨u1, fun x a b c => ?_⟩
  show μ' x * (η' x)⁻¹ = 1
  rw [u1 x a b c, hη.2.1 x (infPart_eq_one hv.1 a) b c, inv_one, one_mul]

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ hR tie i O hP σ σ' hσ' hK`. Establish `hin : InR D ((i : ℕ) + 1)` using `inR i`. Establish `hf : (inC O.c').comp O.jL = D.what₂.embLL` using `hP.lift.field`. Establish `e0 : res T D.what₂.embLL = T.σ₀` using `res_embLL T tie.alg_eq tie.laws.pins.2.2.1`. Establish `hj : ∀ x, O.jL (algebraMap T.Q.c.F D.what₂.LL x) = incF T.Q.c O.c' O.hle x` using `fun x => (inC O.c').injective ((RingHom.congr_fun hf _).trans (RingHom.congr_fun e0 x))`.

Establish `hs : res T σ = sOf O σ'` using `RingHom.ext fun x => (RingHom.congr_fun hσ' _).symm.trans (congrArg σ' (hj x))`. Establish `hg : GoodEmb T.Q.c (res T σ)` using `(overK_iff_good_ofFive T R F κ v₀ hR tie i σ).1 hK`. Establish `hg' : GoodEmb T.Q.c (sOf O σ')` using `hs ▸ hg`. Establish `hsig : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1)` using `fun ρ => D.sp.W_sigval _ hin.1 hin.2 _`. Establish `hq` using `(tie.laws.pins.2.2.2 _ hin).2.1`.

Establish `hpq : (D.R.sigW ((i : ℕ) + 1)).1 + (T.Q.Dw ((i : ℕ) + 1)).q = (Wc D i).rank`. Rewrite using `[hq]`. Conclude with `sigW_add i`. Establish `hε : ∀ τ a, (R.MW i σ).ε τ a = decide ((a : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1)` using `fun τ a => by`. Rewrite using `[signs_of_overK R i hK τ a, hsig]`.

Establish `hl` using `(labels_overK σ).1 hK`. Use `⟨hs, hg', hg', signs_of_overK R i hK, FactsLat.isONeg_x0Mat _ hpq hε, FactsLat.cart_eq_cartZ _ hpq hε, ?_, fun ρ => ?_, fun μ' η' hμ hη => ⟨fun hV => ?_, fun v ε hv => unramAt_conj_ofFive R F hR i hμ hη hv, ?_⟩⟩` and prove the remaining obligations. Establish `h : IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) (res T σ))` using `tie.x0 i σ hg`. Rewrite `h` using `[hs]`. Conclude with `h`.

Use `Eq.trans ?_ (hl.2 ρ)` and prove the remaining obligations. Unfold `relab labE`. Rewrite using `[← embV_eq_embF O.c' O.jL hf, ← hσ']`. Both sides reduce to the same expression. Establish `h : ChiAt R i σ (T.chiW ((i : ℕ) + 1) (res T σ))` using `tie.chiR i σ hg`.

Rewrite `h` using `[hs]`. Rewrite using `[(GlobalTheory.ConjCharUnique.conjChar_unique_ofFive R F hR i σ).1 _ _ hμ h]`. Conclude with `FactsLat.muVal_cast hV (tie.laws.muVal _ hin _ hg')`. Establish `h` using `GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_ofFive R F hR i σ hK η' hη`. Conclude with `(hypConj_of_chars_ofFive R F hR i σ hl.1 hl.2).2 μ' η' hμ hη h.1 h.2`.
-/
theorem factsAt_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → FWTie T R κ v₀ → ∀ (i : Fin D.R.m) (O : OM T R i), Pinned κ v₀ O → ∀ (σ : D.what₂.LL →+* ℂ) (σ' : O.c'.F →+* ℂ), σ'.comp O.jL = σ → OverK σ → FactsAt O σ σ' := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR tie i O hP σ σ' hσ' hK
  have hin : InR D ((i : ℕ) + 1) := inR i
  have hf : (inC O.c').comp O.jL = D.what₂.embLL := hP.lift.field
  have e0 : res T D.what₂.embLL = T.σ₀ := res_embLL T tie.alg_eq tie.laws.pins.2.2.1
  have hj : ∀ x, O.jL (algebraMap T.Q.c.F D.what₂.LL x) = incF T.Q.c O.c' O.hle x := fun x =>
    (inC O.c').injective ((RingHom.congr_fun hf _).trans (RingHom.congr_fun e0 x))
  have hs : res T σ = sOf O σ' := RingHom.ext fun x =>
    (RingHom.congr_fun hσ' _).symm.trans (congrArg σ' (hj x))
  have hg : GoodEmb T.Q.c (res T σ) := (overK_iff_good_ofFive T R F κ v₀ hR tie i σ).1 hK
  have hg' : GoodEmb T.Q.c (sOf O σ') := hs ▸ hg
  have hsig : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := fun ρ => D.sp.W_sigval _ hin.1 hin.2 _
  have hq := (tie.laws.pins.2.2.2 _ hin).2.1
  have hpq : (D.R.sigW ((i : ℕ) + 1)).1 + (T.Q.Dw ((i : ℕ) + 1)).q = (Wc D i).rank := by
    rw [hq]; exact sigW_add i
  have hε : ∀ τ a, (R.MW i σ).ε τ a = decide ((a : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1) := fun τ a => by
    rw [signs_of_overK R i hK τ a, hsig]
  have hl := (labels_overK σ).1 hK
  refine ⟨hs, hg', hg', signs_of_overK R i hK, FactsLat.isONeg_x0Mat _ hpq hε, FactsLat.cart_eq_cartZ _ hpq hε, ?_,
    fun ρ => ?_, fun μ' η' hμ hη => ⟨fun hV => ?_, fun v ε hv => unramAt_conj_ofFive R F hR i hμ hη hv, ?_⟩⟩
  · have h : IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) (res T σ)) := tie.x0 i σ hg
    rw [hs] at h
    exact h
  · refine Eq.trans ?_ (hl.2 ρ)
    unfold relab labE
    rw [← embV_eq_embF O.c' O.jL hf, ← hσ']
    rfl
  · have h : ChiAt R i σ (T.chiW ((i : ℕ) + 1) (res T σ)) := tie.chiR i σ hg
    rw [hs] at h
    rw [(GlobalTheory.ConjCharUnique.conjChar_unique_ofFive R F hR i σ).1 _ _ hμ h]
    exact FactsLat.muVal_cast hV (tie.laws.muVal _ hin _ hg')
  · have h := GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_ofFive R F hR i σ hK η' hη
    exact (hypConj_of_chars_ofFive R F hR i σ hl.1 hl.2).2 μ' η' hμ hη h.1 h.2

end GlobalTheory.GalOne.Facts

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.FactsLat

variable {D : D7}

section Model

variable {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {p q : ℕ} (hpq : p + q = V.rank)
  (hε : ∀ τ a, M.ε τ a = decide ((a : ℕ) < p))
include hpq hε

end Model

/- English proof (translation)
Introduce and unpack `D G _ _ Pl0 T0 A T _ R F κ v₀ hR ⟨tie⟩ i Tp tup O hP`. Establish `hsg : sg0 D A = D.what₂.embLL` using `sgAt_mk _ R.hv0`. Establish `hin : InR D ((i : ℕ) + 1)` using `⟨Nat.le_add_left _ _, i.2⟩`. Establish `hrV : (Vc D i).rank = D.R.nV` using `D.sp.V_rank _ hin.1 hin.2`. Establish `hV0` using `selfDual_frame_level_one_lattice_eq_standard (hR.lev.βV i)`.

Establish `hW0` using `selfDual_frame_level_one_lattice_eq_standard (hR.lev.βW i)`. Establish `hVs` using `GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ (hR.lev.βV i)`. Establish `hWs` using `GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ (hR.lev.βW i)`. Establish `hmv` using `GlobalTheory.MovedLat.moved_lattices D _ _ _ _ hV0 hW0 hVs hWs 1`. Establish `hV1 : Bridge.hLat (Vc D i) 1 = R.ΛV i` using `(hmv 1).2.2.2.2.1`.

Establish `hW1 : Bridge.hLat (Wc D i) 1 = R.ΛW i` using `(hmv 1).2.2.2.2.2`. Take `⟨hp, hq, -⟩` from `tie.laws.pins.2.2.2 _ hin`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hi` using `i.2`. Establish `hpq : (D.R.sigW ((i : ℕ) + 1)).1 + (T.Q.Dw ((i : ℕ) + 1)).q = (Wc D i).rank`.

Rewrite using `[hq, rank_Wc]`. Simplify using `only [Ranks.sigW, Ranks.r]`. Use linear arithmetic over natural numbers and integers. Establish `hε : ∀ τ a, (R.MW i (sg0 D A)).ε τ a = decide ((a : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1)` using `fun τ a => by`. Rewrite using `[hR.models.order i τ a, D.sp.W_sigval _ hin.1 hin.2]`.

Establish `hs : D.what₂.embLL.comp (algebraMap T.Q.c.F D.what₂.LL) = O.s0`. Use `IsFractionRing.ringHom_ext (A := 𝓞 T.Q.c.F) fun x => ?_` and prove the remaining obligations. Conclude with `(congrArg D.what₂.embLL (tie.alg_eq x)).trans (tie.laws.pins.2.2.1 x)`. Establish `hg : GoodEmb T.Q.c O.s0` using `T.toCore.good_σ₀`. Establish `hTau : Nonempty D.what₂.Tau` using `⟨D.eTau.symm 1⟩`.

Use `⟨hsg, hP.lift.std.1, ?_, ?_, ?_, hVs, hWs, isONeg_x0Mat _ hpq hε, cart_eq_cartZ _ hpq hε, ?_, ?_, ?_, ?_, ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[hrV]`. Establish `h1` using `D.R.k_even`. Establish `h2` using `D.R.m_even`. Establish `h3` using `D.R.t_odd`.

Simplify using `only [Ranks.nV, Ranks.r]`. Rewrite `*` using `[Nat.even_iff]`. Rewrite `h3` using `[Nat.odd_iff]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hrV]`.

Conclude with `(tie.kap i (Classical.choice hTau)).2.2`. Rewrite using `[← hV1, hP.lift.std.2, pi_eq_stdL]`. Use `tie.x0 i (sg0 D A) (by rw [hsg, hs]; exact hg)` as an intermediate fact. Rewrite `this` using `[show (sg0 D A).comp (algebraMap T.Q.c.F D.what₂.LL) = O.s0 by rw [hsg, hs]]`. Conclude with `this`.

Establish `h1` using `(tie.chiR i D.what₂.embLL (by rw [hs]; exact hg)).2.2.2.2 rfl`. Rewrite `h1` using `[hs]`. Rewrite using `[← h1]`. Conclude with `muVal_cast O.hV (tie.laws.muVal _ hin _ hg)`. Rewrite using `[hp, hq]`.

Simplify using `only [Ranks.sigW]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Ranks.r]`. Use linear arithmetic over natural numbers and integers. Take `⟨hr, g, e, F', ik, φ, th, h1, -⟩` from `tie.laws.adPin _ hin _ hg`.

Conclude with `latEmb_cast O.hV hr (rank_Wc i) _ h1`. Take `⟨-, h2, h3, h4, -⟩` from `hmv h`. Establish `e1 : FWT.fin (Vc D i) 1 = 1` using `map_one (finHom (Vc D i)).rangeRestrict`. Rewrite `h3` using `[e1, hV1]`. Use `⟨_, h2, ?_, ?_, h3⟩` and prove the remaining obligations.

Rewrite using `[h4]`. Conclude with `isAA_span _`. Rewrite using `[← hW1]`. Conclude with `isMov_hLat _ h`.
-/
theorem facts_lat_ofFive : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → sg0 D A = D.what₂.embLL ∧ (Vc D i).gram = 1 ∧ Even (Vc D i).rank ∧ (κ i).n = (Vc D i).rank ∧ R.ΛV i = stdL D.host.E (Vc D i).rank ∧ IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ IsONeg (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).q (baseZ R i) ∧ cart (R.MW i (sg0 D A)) = cartZ (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).q (baseZ R i) ∧ (∀ ρ, T.x₀ ((i : ℕ) + 1) O.s0 (tauE D ρ) = Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) (baseZ R i ρ)) ∧ MuVal (Wc D i) (R.mu0 ((i : ℕ) + 1)) O.mu ∧ (T.Q.Dw ((i : ℕ) + 1)).p ≠ (T.Q.Dw ((i : ℕ) + 1)).q ∧ 1 ≤ D.R.r ∧ LatEmb (Wc D i) (iotaW T i) ∧ ∀ h : GA D (Wc D i), ∃ LT : Lt D.host.E (Wc D i).rank, IsSelfDualC (Wc D i) LT ∧ GlobalTheory.Ker.IsAA (latG (Wc D i) h) LT ∧ GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt (Wc D i) h) (R.ΛW i) LT ∧ ∀ u : WO (Vc D i) (Wc D i), u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i : Set _) (LT : Set _) fun _ => True) ↔ ∃ u₀ ∈ (latO (Vc D i) (Wc D i) (R.ΛV i : Set _) (R.ΛW i : Set _) fun _ => True), u = actO (Vc D i) (Wc D i) 1 h u₀ := by
  rintro D G _ _ Pl0 T0 A T _ R F κ v₀ hR ⟨tie⟩ i Tp tup O hP
  have hsg : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hin : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hrV : (Vc D i).rank = D.R.nV := D.sp.V_rank _ hin.1 hin.2
  have hV0 := selfDual_frame_level_one_lattice_eq_standard (hR.lev.βV i)
  have hW0 := selfDual_frame_level_one_lattice_eq_standard (hR.lev.βW i)
  have hVs := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ (hR.lev.βV i)
  have hWs := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ (hR.lev.βW i)
  have hmv := GlobalTheory.MovedLat.moved_lattices D _ _ _ _ hV0 hW0 hVs hWs 1
  have hV1 : Bridge.hLat (Vc D i) 1 = R.ΛV i := (hmv 1).2.2.2.2.1
  have hW1 : Bridge.hLat (Wc D i) 1 = R.ΛW i := (hmv 1).2.2.2.2.2
  obtain ⟨hp, hq, -⟩ := tie.laws.pins.2.2.2 _ hin
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  have hpq : (D.R.sigW ((i : ℕ) + 1)).1 + (T.Q.Dw ((i : ℕ) + 1)).q = (Wc D i).rank := by
    rw [hq, rank_Wc]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hε : ∀ τ a, (R.MW i (sg0 D A)).ε τ a = decide ((a : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1) := fun τ a => by
    rw [hR.models.order i τ a, D.sp.W_sigval _ hin.1 hin.2]
  have hs : D.what₂.embLL.comp (algebraMap T.Q.c.F D.what₂.LL) = O.s0 := by
    refine IsFractionRing.ringHom_ext (A := 𝓞 T.Q.c.F) fun x => ?_
    exact (congrArg D.what₂.embLL (tie.alg_eq x)).trans (tie.laws.pins.2.2.1 x)
  have hg : GoodEmb T.Q.c O.s0 := T.toCore.good_σ₀
  have hTau : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  refine ⟨hsg, hP.lift.std.1, ?_, ?_, ?_, hVs, hWs, isONeg_x0Mat _ hpq hε, cart_eq_cartZ _ hpq hε, ?_, ?_, ?_, ?_, ?_,
    fun h => ?_⟩
  · rw [hrV]
    have h1 := D.R.k_even
    have h2 := D.R.m_even
    have h3 := D.R.t_odd
    simp only [Ranks.nV, Ranks.r]
    rw [Nat.even_iff] at *
    rw [Nat.odd_iff] at h3
    omega
  · rw [hrV]
    exact (tie.kap i (Classical.choice hTau)).2.2
  · rw [← hV1, hP.lift.std.2, pi_eq_stdL]
  · have := tie.x0 i (sg0 D A) (by rw [hsg, hs]; exact hg)
    rw [show (sg0 D A).comp (algebraMap T.Q.c.F D.what₂.LL) = O.s0 by rw [hsg, hs]] at this
    exact this
  · have h1 := (tie.chiR i D.what₂.embLL (by rw [hs]; exact hg)).2.2.2.2 rfl
    rw [hs] at h1
    rw [← h1]
    exact muVal_cast O.hV (tie.laws.muVal _ hin _ hg)
  · rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  · simp only [Ranks.r]
    omega
  · obtain ⟨hr, g, e, F', ik, φ, th, h1, -⟩ := tie.laws.adPin _ hin _ hg
    exact latEmb_cast O.hV hr (rank_Wc i) _ h1
  · obtain ⟨-, h2, h3, h4, -⟩ := hmv h
    have e1 : FWT.fin (Vc D i) 1 = 1 := map_one (finHom (Vc D i)).rangeRestrict
    rw [e1, hV1] at h3
    refine ⟨_, h2, ?_, ?_, h3⟩
    · rw [h4]; exact isAA_span _
    · rw [← hW1]; exact isMov_hLat _ h

end GlobalTheory.OneMapRef.FactsLat

end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ hC tie i O hP σ σ' hj' hK hV h`. Take `⟨-, hg1, hev, hn, -, -, -, -, -, -, -, -, hr1, -, -⟩` from `GlobalTheory.OneMapRef.FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hC ⟨tie⟩ i Unit _ O hP`. Take `⟨-, hσ, hσ', -, -, -, hx0, -, -⟩` from `GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hC tie i O hP σ σ' hj' hK`. Establish `L` using `tie.laws`. Establish `hj : InR D ((i : ℕ) + 1)` using `⟨Nat.le_add_left _ _, i.2⟩`.

Establish `hU` using `L.unf _ hj _ hσ`. Establish `hU'` using `(Formalism.L2.PjFree.isUnf_ofPj _).2 hU`. Take `⟨hm, hdom, hun, g₀, e₀, F₀, ik, φ, th, hth, hD⟩` from `laws_cast L hj hσ hV (rank_Wc i)`. Take `⟨γ, hγ, -, hlat, hfr, hmk⟩` from `GlobalTheory.T.dictionary_rational_element_analytic_point D _ _ _ _ _ (sOf O σ') (Wc D i) _ (rank_Wc i) (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV) (iotaW T i) g₀ e₀ F₀ ik φ th _ R.θ (zAt R i σ) hσ hU hr1 hC.models.inf hth hD hx0 h`. Take `⟨W⟩` from `nonempty_uw hU'`.

Take `⟨hκ, hsd, -⟩` from `uw_lattice _ _ _ _ _ _ _ _ _ hσ hU' hr1 W (dictS hV h).1`. Take `⟨hp0, hΨ⟩` from `hU.2.1 (dictS hV h).1`. Take `⟨eT, heT⟩` from `exists_type_equiv T.Q L.pins.1 _ hΨ`. Take `⟨Dc, hDe, -⟩` from `exists_dic _ _ (T.Q.Dw ((i : ℕ) + 1)) _ O.c' σ' _ W.g (Vc D i).rank (xS hV h) (wtA (κ i)) W.e hσ' hU.1 hp0 hΨ hsd (hn ▸ dom_wtA (κ i))`. Establish `hM : Matched T.Q.c (sOf O σ') (xS hV h) Dc.idx Dc.e` using `⟨Dc.per_eq, Dc.ty_eq⟩`.

Use `⟨γ, hγ, W.g, eT, Dc, hdom h, ⟨(hC.thP.ωP i A.μ0).std, hC.models.inf, hg1, hev, hm _, ?_, heT, Dc.sympl⟩, hM, hp0, hsd, hlat, hfr eT heT, ?_, fun g' bas idx e hs hM' => hmk (hdom h) g' bas idx e hs hM'⟩` and prove the remaining obligations. Use `hκ.trans ?_` and prove the remaining obligations. Use `(hm (dictS hV h).1).2` as an intermediate fact. Express the relevant statement in the definitionally equal form `2 * (xS hV h).ξ0 = _`. Rewrite using `[this, mul_neg]`.

Rewrite `hM`, the goal using `[hDe]`. Take `⟨A₀, -, θ, h1, h2⟩` from `uw_anFib _ _ _ _ _ _ _ _ _ hσ hU' hr1 W (dictS hV h).1 Dc.bas Dc.idx Dc.sympl hM.1 hM.2 ⟨(dictS hV h).2, hdom h⟩ (hun h)`. Conclude with `⟨A₀, θ, h1, h2⟩`.
-/
theorem framed_point_at_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → FWTie T R κ v₀ → ∀ (i : Fin D.R.m) (O : OM T R i), Pinned κ v₀ O → ∀ (σ : D.what₂.LL →+* ℂ) (σ' : O.c'.F →+* ℂ), σ'.comp O.jL = σ → OverK σ → ∀ hV : T.V ((i : ℕ) + 1) (sOf O σ') = Wc D i, ∀ h, PointAt κ O σ σ' hV h := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC tie i O hP σ σ' hj' hK hV h
  obtain ⟨-, hg1, hev, hn, -, -, -, -, -, -, -, -, hr1, -, -⟩ :=
    GlobalTheory.OneMapRef.FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hC ⟨tie⟩ i Unit _ O hP
  obtain ⟨-, hσ, hσ', -, -, -, hx0, -, -⟩ := GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hC tie i O hP σ σ' hj' hK
  have L := tie.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hU := L.unf _ hj _ hσ
  have hU' := (Formalism.L2.PjFree.isUnf_ofPj _).2 hU
  obtain ⟨hm, hdom, hun, g₀, e₀, F₀, ik, φ, th, hth, hD⟩ := laws_cast L hj hσ hV (rank_Wc i)
  obtain ⟨γ, hγ, -, hlat, hfr, hmk⟩ := GlobalTheory.T.dictionary_rational_element_analytic_point D _ _ _ _ _ (sOf O σ') (Wc D i) _ (rank_Wc i)
    (T.U ((i : ℕ) + 1) (sOf O σ'))
    (dictS hV) (iotaW T i) g₀ e₀ F₀ ik φ th _ R.θ (zAt R i σ) hσ hU hr1 hC.models.inf hth hD hx0 h
  obtain ⟨W⟩ := nonempty_uw hU'
  obtain ⟨hκ, hsd, -⟩ := uw_lattice _ _ _ _ _ _ _ _ _ hσ hU' hr1 W (dictS hV h).1
  obtain ⟨hp0, hΨ⟩ := hU.2.1 (dictS hV h).1
  obtain ⟨eT, heT⟩ := exists_type_equiv T.Q L.pins.1 _ hΨ
  obtain ⟨Dc, hDe, -⟩ := exists_dic _ _ (T.Q.Dw ((i : ℕ) + 1)) _ O.c' σ' _ W.g (Vc D i).rank
    (xS hV h) (wtA (κ i)) W.e hσ' hU.1 hp0 hΨ hsd (hn ▸ dom_wtA (κ i))
  have hM : Matched T.Q.c (sOf O σ') (xS hV h) Dc.idx Dc.e := ⟨Dc.per_eq, Dc.ty_eq⟩
  refine ⟨γ, hγ, W.g, eT, Dc, hdom h, ⟨(hC.thP.ωP i A.μ0).std, hC.models.inf, hg1, hev, hm _, ?_, heT, Dc.sympl⟩, hM,
    hp0, hsd, hlat, hfr eT heT, ?_, fun g' bas idx e hs hM' => hmk (hdom h) g' bas idx e hs hM'⟩
  · refine hκ.trans ?_
    have := (hm (dictS hV h).1).2
    change 2 * (xS hV h).ξ0 = _
    rw [this, mul_neg]
  · rw [hDe] at hM ⊢
    obtain ⟨A₀, -, θ, h1, h2⟩ := uw_anFib _ _ _ _ _ _ _ _ _ hσ hU' hr1 W (dictS hV h).1 Dc.bas Dc.idx Dc.sympl hM.1 hM.2
      ⟨(dictS hV h).2, hdom h⟩ (hun h)
    exact ⟨A₀, θ, h1, h2⟩

end GlobalTheory.GalOne

end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.FrameConst

open GlobalTheory.OneMapRef.FrameConst

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ hR tie i O hP σ σ' hσ' μ' η' ω f₀ f hC hV`. Take `⟨-, -, -, -, hΛ, dS, dT, -, -, -, -, -, hr1, -, hlat⟩` from `FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hR ⟨tie⟩ i Unit _ O hP`. Take `⟨hη, -, -, -⟩` from `chars_of_lift_ofFive D G Pl0 T0 A _ R F hR i`. Take `⟨hK, hchi, heta, hW, hvec, -⟩` from `hC`. Take `⟨-, hσ, -, -, hZ, hcart, -, -, hch⟩` from `GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ' hK`.

Take `⟨hmu, hun, -⟩` from `hch μ' η' hchi heta`. Establish `hin : InR D ((i : ℕ) + 1)` using `⟨Nat.le_add_left _ _, i.2⟩`. Establish `hf` using `hvec.1`. Establish `hu` using `tie.laws.muUnit _ hin _ hσ`. Rewrite `dS`, `hlat`, `hf` using `[hΛ]`.

Rewrite `hf` using `[hcart]`. Use `exists_frConst (D.sp.V_sig _) (D.sp.W_sig _) hW ⟨_, hη⟩ hun hZ dS dT hf (hmu hV) (mu_rat_cast hV fun γ hγ h => by rw [hu.1, hu.2.2.1 γ hγ, one_mul]) (fun h => (hlat h).imp fun _ h' => h'.2) _ hσ (tie.laws.unf _ hin _ hσ) hr1 tie.laws.pins.2.1.2 (t := 2 * xiR D) (fun k τ => congrA …` and prove the remaining obligations. Take `⟨γ, hγ, g, eT, Dc, hx, h1, h2, h3, h4, h5, h6, h7, -⟩` from `GlobalTheory.GalOne.framed_point_at_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ' hK hV h`. Conclude with `⟨γ, hγ, g, eT, Dc.bas, Dc.idx, Dc.e, hx, h1, h2, h3, h4, h5, h6, h7⟩`.
-/
theorem exists_frAtEmb_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → FWTie T R κ v₀ → ∀ (i : Fin D.R.m) (O : OM T R i), Pinned κ v₀ O → ∀ (σ : D.what₂.LL →+* ℂ) (σ' : O.c'.F →+* ℂ), σ'.comp O.jL = σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ), ConjW R i σ μ' η' ω f₀ f → ∀ hV : T.V ((i : ℕ) + 1) (sOf O σ') = Wc D i, ∃ cc, CUnit cc ∧ FrAtEmb O σ σ' hV ω f₀ cc := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR tie i O hP σ σ' hσ' μ' η' ω f₀ f hC hV
  obtain ⟨-, -, -, -, hΛ, dS, dT, -, -, -, -, -, hr1, -, hlat⟩ :=
    FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hR ⟨tie⟩ i Unit _ O hP
  obtain ⟨hη, -, -, -⟩ := chars_of_lift_ofFive D G Pl0 T0 A _ R F hR i
  obtain ⟨hK, hchi, heta, hW, hvec, -⟩ := hC
  obtain ⟨-, hσ, -, -, hZ, hcart, -, -, hch⟩ := GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ' hK
  obtain ⟨hmu, hun, -⟩ := hch μ' η' hchi heta
  have hin : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hf := hvec.1
  have hu := tie.laws.muUnit _ hin _ hσ
  rw [hΛ] at dS hlat hf
  rw [hcart] at hf
  refine exists_frConst (D.sp.V_sig _) (D.sp.W_sig _) hW ⟨_, hη⟩ hun hZ dS dT hf (hmu hV)
    (mu_rat_cast hV fun γ hγ h => by rw [hu.1, hu.2.2.1 γ hγ, one_mul])
    (fun h => (hlat h).imp fun _ h' => h'.2) _ hσ (tie.laws.unf _ hin _ hσ) hr1 tie.laws.pins.2.1.2 (t := 2 * xiR D)
    (fun k τ => congrArg (2 * ·) (tie.laws.xiAbs _ hin _ hσ k τ.1)) _ fun h => ?_
  obtain ⟨γ, hγ, g, eT, Dc, hx, h1, h2, h3, h4, h5, h6, h7, -⟩ :=
    GlobalTheory.GalOne.framed_point_at_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ' hK hV h
  exact ⟨γ, hγ, g, eT, Dc.bas, Dc.idx, Dc.e, hx, h1, h2, h3, h4, h5, h6, h7⟩

end GlobalTheory.GalOne.FrameConst

end

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.VecConj

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ μ' η' ω f₀ f h`. Establish `hK` using `h.1`. Establish `hμ` using `h.2.1`. Establish `hη` using `h.2.2.1`. Establish `hW` using `h.2.2.2.1`.

Establish `hvec` using `h.2.2.2.2.1`. Establish `hf` using `h.2.2.2.2.2`. Establish `hM` using `hC.models`. Establish `hv` using `GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hvec hf`. Establish `hne : f ≠ 0` using `GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)) (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)) ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) hvec`.

Establish `hl` using `(labels_overK σ).1 hK`. Establish `he` using `GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_ofFive R F hC i σ hK η' hη`. Establish `hH : HypConj R i σ μ' η'` using `(hypConj_of_chars_ofFive R F hC i σ hl.1 hl.2).2 μ' η' hμ hη he.1 he.2`. Establish `hr : Odd D.R.r`. Use `D.R.m_add_three_le_k` as an intermediate fact.

Take `⟨a, ha⟩` from `D.R.k_even`. Take `⟨b, hb⟩` from `D.R.m_even`. Conclude with `⟨a + b - 1, by simp only [Ranks.r]; omega⟩`. Establish `rV : (Vc D i).rank = D.R.r + D.R.t` using `D.sp.V_rank _ (Nat.le_add_left _ _) i.2`. Establish `rW : (Wc D i).rank = D.R.r` using `D.sp.W_rank _ (Nat.le_add_left _ _) i.2`.

Establish `hev : Even (Vc D i).rank` using `rV ▸ hr.add_odd D.R.t_odd`. Establish `hexp : ∀ τ, ∃ a : ℤ, HasInfExp D μ' τ a` using `fun τ => by`. Take `⟨z, hz⟩` from `(D.hc (lab σ τ)).e_int i`. Establish `h3` using `hH.mu_inf τ`. Rewrite `h3` using `[hz, ← Int.cast_neg]`.

Conclude with `⟨-z, h3⟩`. Use `⟨hne, hv, fun ρ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ ρ _ (Facts.signs_of_overK R i hK ρ), fun B hB => ?_, hH, fun h1 => ⟨hW, hM.inf, h1, hev, D.sp.V_sig _, D.sp.W_sig _, hexp, fun τ => ?_, fun v ε hv => Facts.unramAt_conj_ofFive R F hC i hμ hη hv, ⟨η', hη.1, hη.2.1, he.1, …` and prove the remaining obligations. Conclude with `GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ _ _ hW.std hM.inf _ _ _ _ _ _ (fun τ => VecP.isCartanInv_one_of_onb (hM.BV i τ)) (GlobalTheory.AdTh.VecFock.isCartanInv_cart _) (hM.BV i) hB (D.sp.V_sig _) (D.sp.W_sig _) f hf hv hne`. Take `⟨a, ha⟩` from `hexp τ`. Take `⟨s, hs⟩` from `hr`.

Use `⟨a - s - 1, ?_⟩` and prove the remaining obligations. Establish `h3` using `GlobalTheory.Mem.HeckeExp.hasInfExp_mul ha (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (he.2 τ))`. Establish `e : ((a - s - 1 : ℤ) : ℚ) + ((Wc D i).rank : ℚ) / 2 = (a : ℚ) + -(1 / 2)`. Rewrite using `[rW, hs]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h3`.
-/
theorem vec_conj_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), ∀ (μ' η' : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ), ConjW R i σ μ' η' ω f₀ f → f ≠ 0 ∧ (∀ ρ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ ρ (cplxO 1 (cart (R.MW i σ) ρ)) f) ∧ (∀ ρ, IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (onb (R.MW i σ) ρ) (pW D i ρ)) ∧ (∀ (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), (∀ ρ, IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (B ρ) (pW D i ρ)) → Function.Injective (ptAt R i σ B f)) ∧ HypConj R i σ μ' η' ∧ ((Vc D i).gram = 1 → GlobalTheory.AdTh.IsPair R.ψ R.θ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ μ' η' ω f₀ f h
  have hK := h.1
  have hμ := h.2.1
  have hη := h.2.2.1
  have hW := h.2.2.2.1
  have hvec := h.2.2.2.2.1
  have hf := h.2.2.2.2.2
  have hM := hC.models
  have hv := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hvec hf
  have hne : f ≠ 0 :=
    GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i))
      (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i))
      ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) hvec
  have hl := (labels_overK σ).1 hK
  have he := GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_ofFive R F hC i σ hK η' hη
  have hH : HypConj R i σ μ' η' := (hypConj_of_chars_ofFive R F hC i σ hl.1 hl.2).2 μ' η' hμ hη he.1 he.2
  have hr : Odd D.R.r := by
    have := D.R.m_add_three_le_k
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hev : Even (Vc D i).rank := rV ▸ hr.add_odd D.R.t_odd
  have hexp : ∀ τ, ∃ a : ℤ, HasInfExp D μ' τ a := fun τ => by
    obtain ⟨z, hz⟩ := (D.hc (lab σ τ)).e_int i
    have h3 := hH.mu_inf τ
    rw [hz, ← Int.cast_neg] at h3
    exact ⟨-z, h3⟩
  refine ⟨hne, hv, fun ρ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ ρ _ (Facts.signs_of_overK R i hK ρ), fun B hB => ?_, hH,
    fun h1 => ⟨hW, hM.inf, h1, hev, D.sp.V_sig _, D.sp.W_sig _, hexp, fun τ => ?_,
      fun v ε hv => Facts.unramAt_conj_ofFive R F hC i hμ hη hv, ⟨η', hη.1, hη.2.1, he.1, he.2⟩⟩⟩
  · exact GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ _ _ hW.std hM.inf _ _ _ _ _ _
      (fun τ => VecP.isCartanInv_one_of_onb (hM.BV i τ)) (GlobalTheory.AdTh.VecFock.isCartanInv_cart _) (hM.BV i) hB
      (D.sp.V_sig _) (D.sp.W_sig _) f hf hv hne
  · obtain ⟨a, ha⟩ := hexp τ
    obtain ⟨s, hs⟩ := hr
    refine ⟨a - s - 1, ?_⟩
    have h3 := GlobalTheory.Mem.HeckeExp.hasInfExp_mul ha (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (he.2 τ))
    have e : ((a - s - 1 : ℤ) : ℚ) + ((Wc D i).rank : ℚ) / 2 = (a : ℚ) + -(1 / 2) := by
      rw [rW, hs]; push_cast; ring
    rw [e]
    exact h3

end GlobalTheory.GalOne.VecConj

end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.Rebase

open GlobalTheory.ConjLiftUnique

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ μ' η' ω f₀ f hW B hB c io hio`. Establish `hvec` using `GlobalTheory.GalOne.VecConj.vec_conj_ofFive R F hC i σ μ' η' ω f₀ f hW`. Establish `hlow` using `GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ _ (GlobalTheory.GalLift.ProjLift.holShape_of_overK R i hW.1)`. Conclude with `rebase_gen hW.2.2.2.1 hC.models.inf (D.sp.V_sig _) (D.sp.W_sig _) (fun τ => GlobalTheory.GalLift.Vec.isCartanInv_one (hC.models.BV i τ)) hlow.1 hlow.2 hW.2.2.2.2.2 hvec.2.1 hB hvec.2.2.1 (hvec.2.2.2.1 _ hvec.2.2.1) hio`.
-/
theorem rebase_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), ∀ (μ' η' : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ), ConjW R i σ μ' η' ω f₀ f → ∀ (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), (∀ ρ, IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (B ρ) (pW D i ρ)) → ∀ (c : CoefA (Vc D i)) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ B f) (deltaConj i σ) io → ∃ io' : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank, IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ (onb (R.MW i σ)) f) (deltaConj i σ) io' ∧ ∀ x w, ptAt R i σ B f (io x w) = ptAt R i σ (onb (R.MW i σ)) f (io' x w) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ μ' η' ω f₀ f hW B hB c io hio
  have hvec := GlobalTheory.GalOne.VecConj.vec_conj_ofFive R F hC i σ μ' η' ω f₀ f hW
  have hlow := GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ _ (GlobalTheory.GalLift.ProjLift.holShape_of_overK R i hW.1)
  exact rebase_gen hW.2.2.2.1 hC.models.inf (D.sp.V_sig _) (D.sp.W_sig _)
    (fun τ => GlobalTheory.GalLift.Vec.isCartanInv_one (hC.models.BV i τ)) hlow.1 hlow.2 hW.2.2.2.2.2 hvec.2.1 hB hvec.2.2.1
    (hvec.2.2.2.1 _ hvec.2.2.1) hio

end GlobalTheory.GalOne.Rebase

end

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.MinorWeight

open GlobalTheory.JointHarm GlobalTheory.AdTh.MinorWeight GlobalTheory.AdTh
open scoped Classical

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F h i σ μ' η' ω f₀ f hc τ a`. Establish `hvec` using `GlobalTheory.GalOne.VecConj.vec_conj_ofFive R F h i σ μ' η' ω f₀ f hc`. Establish `hv` using `hvec.2.1`. Establish `hH` using `hvec.2.2.2.2.1`. Establish `hθ` using `h.models.inf`.

Establish `hω` using `hc.2.2.2.1`. Establish `hth` using `hc.2.2.2.2.2`. Establish `hw` using `fun ρ => GlobalTheory.MovedWeights.weights_label D i (lab σ ρ) (pW D i ρ) (qW D i ρ) (congrArg Prod.fst ((hH.sig ρ).trans (hH.sig _).symm)) (congrArg Prod.snd ((hH.sig ρ).trans (hH.sig _).symm)) ((R.MW i σ).lam ρ) ((R.MW i σ).ε ρ) (by have := (R.MW i σ).enum ρ; rw [hH.par ρ] at t …`. Use `choose x₁ x₂ x₃ hx₁ hx₂ hx₃ hK hU hpq hε hap ham using hw`. Establish `hmn : (Wc D i).rank ≤ (Vc D i).rank` using `(D.sp.W_rank _ (Nat.le_add_left _ _) i.2).le.trans (r_le_V i)`.

Establish `hB : ∀ ρ, (R.BV i ρ)ᴴ * gramAt D (Vc D i) ρ * R.BV i ρ = 1` using `fun ρ => onb_eq_one (h.models.BV i ρ)`. Establish `hBi : ∀ ρ, (R.BV i ρ)⁻¹ * R.BV i ρ = 1` using `fun ρ => Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_left_inverse (hB ρ))`. Establish `ha` using `hH.mu_inf`. Establish `hb` using `fun τ => GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hH.mu_inf τ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hH.eta_inf τ))`. Use `clear hvec hc hH`.

Unfold `ptAt deltaConj`. Generalize the expression as in `R.MW i σ = M at hε hK hv ⊢`. Establish `h1 : ∀ ρ, M.fr ρ * (M.fr ρ)⁻¹ = 1` using `fun ρ => Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ))`. Establish `hKd` using `diag_mem (ε := M.ε τ) a`. Take `⟨a1, a2, a3⟩` from `GlobalTheory.PointAtPlaceHom.atTau_spec hθ (Wc D i) τ (conj_mem M τ hKd)`.

Generalize the expression as in `atTau R.θ (Wc D i) τ _ = g at a1 a2 a3 ⊢`. Set `θs : D.what₂.Tau → Fin (Wc D i).rank → ℝ` to `fun ρ => if ρ = τ then a else 0`. Establish `hg : ∀ ρ, M.fr ρ * compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i) g) * (M.fr ρ)⁻¹ = diagonal fun j => Complex.exp ((θs ρ j : ℂ) * Complex.I)` using `fun ρ => by`. Distinguish the cases in `e : ρ = τ`. Substitute `e` using the available equality.

Rewrite using `[show compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i) g) = _ from a2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]`. Simplify using `only [θs, if_true]`. Rewrite using `[show compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i) g) = _ from a3 ρ e, Matrix.mul_one, h1]`. Simplify using `[θs, e]`. Establish `e1 : ∀ ρ, (R.BV i ρ)⁻¹ * compAt R.θ ρ (Formalism.L2.Theta.mt (Vc D i) 1) * R.BV i ρ = 1` using `fun ρ => by`.

Rewrite using `[show compAt R.θ ρ (Formalism.L2.Theta.mt (Vc D i) 1) = 1 from GlobalTheory.PointAtPlaceHom.infMat_one _ _, Matrix.mul_one, hBi]`. Establish `key` using `(GlobalTheory.T.weil_maximalCompact_fock_substitution_character D R.ψ R.θ _ _ _ _ _ _ M (R.BV i) hω hθ (D.sp.V_sig _) (D.sp.W_sig _) hB _ _ hpq hε _ _ ha hb x₁ x₂ x₃ hx₁ hx₂ hx₃ _ hth hv 1 (one_mem _) g a1 (fun ρ => hg ρ ▸ diag_mem _)).2 (delta (pW D i) (qW D i) (fun ρ => aPl D i …`. Simplify using `only [hg, e1] at key`. Use `key.trans ?_` and prove the remaining obligations. Rewrite using `[fact_diagonal M.ε _ _ _ _ x₁ x₂ x₃ hmn hpq hε hap ham _ (fun _ _ => Complex.exp_ne_zero _), map_smul]`.

Use `congr 1`. Rewrite using `[Finset.prod_eq_single τ (fun ρ _ e => by simp [θs, e]) (fun e => (e (Finset.mem_univ _)).elim), Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hr` using `revNeg_shape (Nat.le.intro (hpq τ)) (hε τ) j`. Establish `hj` using `j.2`.

Rewrite using `[extWt, hK τ, ← Complex.exp_int_mul, wtK, hr]`. Use `congr 1`. Distinguish the cases in `hp : (j : ℕ) < pW D i τ`. Simplify using `[θs, hp, mul_assoc]`. Rewrite using `[if_neg hp, if_neg hp, if_neg (by have := hpq τ; omega), show (Wc D i).rank - 1 - ((Wc D i).rank - 1 - (j - pW D i τ)) = j - pW D i τ by omega]`.

Simplify using `[θs, mul_assoc]`.
-/
theorem deltaConj_extremal_weight_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), ∀ (μ' η' : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ), ConjW R i σ μ' η' ω f₀ f → ∀ (τ : D.what₂.Tau) (a : Fin (Wc D i).rank → ℝ), ω (1, atTau R.θ (Wc D i) τ (((R.MW i σ).fr τ)⁻¹ * Matrix.diagonal (fun j => Complex.exp ((a j : ℂ) * Complex.I)) * (R.MW i σ).fr τ)) (ptAt R i σ (onb (R.MW i σ)) f (deltaConj i σ)) = Complex.exp (((∑ j, extWt (R.MW i σ) τ j * a j : ℝ) : ℂ) * Complex.I) • ptAt R i σ (onb (R.MW i σ)) f (deltaConj i σ) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i σ μ' η' ω f₀ f hc τ a
  have hvec := GlobalTheory.GalOne.VecConj.vec_conj_ofFive R F h i σ μ' η' ω f₀ f hc
  have hv := hvec.2.1
  have hH := hvec.2.2.2.2.1
  have hθ := h.models.inf
  have hω := hc.2.2.2.1
  have hth := hc.2.2.2.2.2
  have hw := fun ρ => GlobalTheory.MovedWeights.weights_label D i (lab σ ρ) (pW D i ρ) (qW D i ρ)
    (congrArg Prod.fst ((hH.sig ρ).trans (hH.sig _).symm)) (congrArg Prod.snd ((hH.sig ρ).trans (hH.sig _).symm))
    ((R.MW i σ).lam ρ) ((R.MW i σ).ε ρ) (by have := (R.MW i σ).enum ρ; rw [hH.par ρ] at this; exact this)
  choose x₁ x₂ x₃ hx₁ hx₂ hx₃ hK hU hpq hε hap ham using hw
  have hmn : (Wc D i).rank ≤ (Vc D i).rank := (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).le.trans (r_le_V i)
  have hB : ∀ ρ, (R.BV i ρ)ᴴ * gramAt D (Vc D i) ρ * R.BV i ρ = 1 := fun ρ => onb_eq_one (h.models.BV i ρ)
  have hBi : ∀ ρ, (R.BV i ρ)⁻¹ * R.BV i ρ = 1 := fun ρ =>
    Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_left_inverse (hB ρ))
  have ha := hH.mu_inf
  have hb := fun τ => GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hH.mu_inf τ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hH.eta_inf τ))
  clear hvec hc hH
  unfold ptAt deltaConj
  generalize R.MW i σ = M at hε hK hv ⊢
  have h1 : ∀ ρ, M.fr ρ * (M.fr ρ)⁻¹ = 1 := fun ρ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ))
  have hKd := diag_mem (ε := M.ε τ) a
  obtain ⟨a1, a2, a3⟩ := GlobalTheory.PointAtPlaceHom.atTau_spec hθ (Wc D i) τ (conj_mem M τ hKd)
  generalize atTau R.θ (Wc D i) τ _ = g at a1 a2 a3 ⊢
  let θs : D.what₂.Tau → Fin (Wc D i).rank → ℝ := fun ρ => if ρ = τ then a else 0
  have hg : ∀ ρ, M.fr ρ * compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i) g) * (M.fr ρ)⁻¹ =
      diagonal fun j => Complex.exp ((θs ρ j : ℂ) * Complex.I) := fun ρ => by
    by_cases e : ρ = τ
    · subst e
      rw [show compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i) g) = _ from a2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1,
        Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
      simp only [θs, if_true]
    · rw [show compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i) g) = _ from a3 ρ e, Matrix.mul_one, h1]
      simp [θs, e]
  have e1 : ∀ ρ, (R.BV i ρ)⁻¹ * compAt R.θ ρ (Formalism.L2.Theta.mt (Vc D i) 1) * R.BV i ρ = 1 := fun ρ => by
    rw [show compAt R.θ ρ (Formalism.L2.Theta.mt (Vc D i) 1) = 1 from GlobalTheory.PointAtPlaceHom.infMat_one _ _, Matrix.mul_one, hBi]
  have key := (GlobalTheory.T.weil_maximalCompact_fock_substitution_character D R.ψ R.θ _ _ _ _ _ _ M (R.BV i) hω hθ (D.sp.V_sig _) (D.sp.W_sig _) hB _ _ hpq hε
    _ _ ha hb x₁ x₂ x₃ hx₁ hx₂ hx₃ _ hth hv 1 (one_mem _) g a1 (fun ρ => hg ρ ▸ diag_mem _)).2
    (delta (pW D i) (qW D i) (fun ρ => aPl D i (pW D i ρ) (lab σ ρ)) (fun ρ => aMi D i (pW D i ρ) (qW D i ρ) (lab σ ρ)))
  simp only [hg, e1] at key
  refine key.trans ?_
  rw [fact_diagonal M.ε _ _ _ _ x₁ x₂ x₃ hmn hpq hε hap ham _ (fun _ _ => Complex.exp_ne_zero _), map_smul]
  congr 1
  rw [Finset.prod_eq_single τ (fun ρ _ e => by simp [θs, e]) (fun e => (e (Finset.mem_univ _)).elim), Complex.ofReal_sum,
    Finset.sum_mul, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hr := revNeg_shape (Nat.le.intro (hpq τ)) (hε τ) j
  have hj := j.2
  rw [extWt, hK τ, ← Complex.exp_int_mul, wtK, hr]
  congr 1
  by_cases hp : (j : ℕ) < pW D i τ
  · simp [θs, hp, mul_assoc]
  · rw [if_neg hp, if_neg hp, if_neg (by have := hpq τ; omega),
      show (Wc D i).rank - 1 - ((Wc D i).rank - 1 - (j - pW D i τ)) = j - pW D i τ by omega]
    simp [θs, mul_assoc]

end GlobalTheory.GalOne.MinorWeight

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.IoExtConj

open GlobalTheory.AdTh.IoExtPf
open scoped Classical

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hR i σ μ' η' ω f₀ f hC c io hio v hv`. Establish `hH` using `GlobalTheory.GalLift.ProjLift.holShape_of_overK R i hC.1`. Establish `hvec` using `GlobalTheory.GalOne.VecConj.vec_conj_ofFive R F hR i σ μ' η' ω f₀ f hC`. Establish `hinj` using `hvec.2.2.2.1 _ hvec.2.2.1`. Set `pt` to `pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) (onb (R.MW i σ)) f`.

Conclude with `exists_unit_of_isIoW R.θ (R.MW i σ) (GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ _ hH).1 (GlobalTheory.T.extremal_vectors_holomorphic_model_unique_up_to_phase D _ _ _ hH) c ω pt (deltaConj i σ) (fun h => deltaConj_ne i σ (hinj (h.trans (map_zero pt).symm))) (GlobalTheory.GalOn …`.
-/
theorem ioExt_conj_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), ∀ (μ' η' : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ), ConjW R i σ μ' η' ω f₀ f → ∀ (c : CoefA (Vc D i)) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ (onb (R.MW i σ)) f) (deltaConj i σ) io → ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, IsExtVec (R.MW i σ) (fun ρ => v ρ) → ∃ w : c.W, ‖w‖ = 1 ∧ io (PiTensorProduct.tprod ℂ v) w = deltaConj i σ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i σ μ' η' ω f₀ f hC c io hio v hv
  have hH := GlobalTheory.GalLift.ProjLift.holShape_of_overK R i hC.1
  have hvec := GlobalTheory.GalOne.VecConj.vec_conj_ofFive R F hR i σ μ' η' ω f₀ f hC
  have hinj := hvec.2.2.2.1 _ hvec.2.2.1
  let pt := pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) (onb (R.MW i σ)) f
  exact exists_unit_of_isIoW R.θ (R.MW i σ) (GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ _ hH).1 (GlobalTheory.T.extremal_vectors_holomorphic_model_unique_up_to_phase D _ _ _ hH) c ω pt
    (deltaConj i σ) (fun h => deltaConj_ne i σ (hinj (h.trans (map_zero pt).symm)))
    (GlobalTheory.GalOne.MinorWeight.deltaConj_extremal_weight_ofFive R F hR i σ μ' η' ω f₀ f hC) io hio v hv

end GlobalTheory.GalOne.IoExtConj

end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VecFock

open scoped ComplexOrder

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F h i t hV`. Establish `hθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t)`. Use `h.thP.pt_theta i t 1` as an intermediate fact. Unfold `RealDat.ptP pureTensorO at this`. Rewrite `this` using `[pureTensorL_one]`. Then use the resulting hypothesis.

Use `⟨hθ, GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (h.thP.vP i t) hθ, isCartanInv_cart _, fun τ => ?_, fun τ => isONBasis_onb _ τ _ (h.models.order i τ)⟩` and prove the remaining obligations. Establish `: gramAt D (Vc D i) τ = 1`. Unfold `gramAt`. Rewrite using `[hV.1]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.

Rewrite using `[this]`. Conclude with `⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩`.
-/
theorem vec_fock_ofFive' : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (t : T0), VStd D i → IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) ∧ (∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) (R.vP i t)) ∧ (∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ)) ∧ (∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1) ∧ ∀ τ, IsONBasis (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) (onb (R.MW i (sg0 D A)) τ) ((Wc D i).sig (tauE D τ)).1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i t hV
  have hθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := h.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [pureTensorL_one] at this
  refine ⟨hθ, GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (h.thP.vP i t) hθ,
    isCartanInv_cart _, fun τ => ?_, fun τ => isONBasis_onb _ τ _ (h.models.order i τ)⟩
  have : gramAt D (Vc D i) τ = 1 := by
    unfold gramAt
    rw [hV.1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [this]
  exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩

end GlobalTheory.AdTh.VecFock

end

section

noncomputable section

namespace GlobalTheory.GalOne.PhaseAt

section General

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

end General

section Letters

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
open GlobalTheory.AdTh.PhaseMap
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {m n : ℕ} {l : Geo.Tor.Level H} (c : Coeff l)
  (φ : c.F →+* ℂ) {e : D.what₂.Tau → D.what₂.Tau}

variable {lt : LtN Dw n → FVar D m n}

end Letters

end GlobalTheory.GalOne.PhaseAt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.PhaseAt

open GlobalTheory.AdTh GlobalTheory.AdTh.PhaseMap

set_option maxHeartbeats 3200000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT i O hO σ σ' hσ μ' η' ω f₀ f hW c c₁ hc₁ Λ hio hex₀`. Establish `hstd` using `hO.lift.std`. Establish `hθ : IsInfFam R.θ` using `hR.models.inf`. Establish `hc : c.Is` using `hc₁.coef`. Establish `hvec` using `GlobalTheory.GalOne.VecConj.vec_conj_ofFive R F hR i σ μ' η' ω f₀ f hW`.

Establish `hfac` using `GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hR hT i O hO σ σ' hσ hW.1`. Establish `hP` using `hvec.2.2.2.2.2 hstd.1`. Establish `hψ` using `hP.weil.std`. Establish `f1 : IsThetaFunO R.ψ (Vc D i) (Wc D i) f` using `hW.2.2.2.2.2`. Establish `f2` using `hvec.2.1`.

Establish `f3` using `GlobalTheory.AdTh.VecFock.isCartanInv_cart (R.MW i σ)`. Establish `f4` using `(GlobalTheory.AdTh.VecFock.vec_fock_ofFive' D G Pl0 T0 A _ R F hR i A.μ0 hstd).2.2.2.1`. Establish `f5` using `hvec.2.2.1`. Establish `he : Function.Bijective (lab (D` using `D) σ) := hvec.2.2.2.2.1.lab_bij`. Establish `hrel` using `GlobalTheory.Relab.relab_good _ _ _ O.c' σ' hfac.2.2.1`.

Establish `e1 : ∀ ρ, relab O.c' σ' (tauE D (lab σ ρ)) = tauE D ρ` using `hfac.2.2.2.2.2.2.2.1`. Establish `e2 : ∀ ρ, relab O.c' σ' (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (tauE D (lab σ ρ))) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (tauE D ρ)` using `fun ρ => (hrel.2.2.1 _).trans (congrArg _ (e1 ρ))`. Establish `hlt : ∀ lt, IsLtAt O σ' lt → IsLt (mv (lab σ) lt)` using `fun lt hl ℓ => ⟨(hl ℓ).1, (hl ℓ).2.imp (fun h => ⟨hrel.1.1 (h.1.trans (e1 _).symm), h.2⟩) fun h => ⟨hrel.1.1 (h.1.trans (e2 _).symm), h.2⟩⟩`. Set `v₁ : VsV D i D.what₂.LL` to `⟨Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal D.what₂.LL _ (lamV D i τ), GlobalTheory.Proof.TensorMapDescent.ten_mem _ _ fun τ => Formalism.GradedWeylDivisibility.hwMem _ _ _ le_rfl _ (Formalism.L2.DIV.natW_antitone _)⟩`. Establish `hv : CoefExt.up O.jL (lamV D i) v₁ = O.hw`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `hw` using `hO.io.1`. Unfold `hwOK at hw`. Use `Eq.trans ?_ hw.symm` and prove the remaining obligations. Use `show MvPolynomial.map O.jL (Formalism.L2.DIV.ten _) = _`.

Rewrite using `[GlobalTheory.Proof.TensorMapDescent.map_ten]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Conclude with `Formalism.L2.DIV.map_extremal _ _ _`. Establish `n1 : ‖c₁ v₁‖ = 1`.

Establish `hn` using `GlobalTheory.StdFrame.neg_eq_false_of_vStd D i hstd`. Establish `hG : gramV D i = 1`. Rewrite using `[gramV, hn, if_neg Bool.false_ne_true]`. Conclude with `hstd.1`. Establish `hi` using `inner_of_int (lamV D i) σ c₁ _ hc₁.pair v₁ v₁ (∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℤ τ (Formalism.BasicNotions.extremal ℤ _ (lamV D i τ))) (by show Formalism.L2.DIV.ten _ = _`.

Unfold `Formalism.L2.DIV.ten`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[fk_map_blockEmb, Formalism.L2.DIV.map_extremal])`. Rewrite `hi` using `[hG]`.

Use `replace hi := hi.trans ((congrArg σ (CoefExt.pairVr_extremal (labLL D) v₁ rfl)).trans (map_one _))`. Rewrite `hi` using `[inner_self_eq_norm_sq_to_K]`. Establish `h4 : ‖c₁ v₁‖ ^ 2 = 1`. Establish `h5` using `congrArg norm hi`. Simplify using `using h5`.

Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4`. Establish `n2 : ∀ (γE : GL (Fin (Vc D i).rank) D.host.E) (v : VsV D i D.what₂.LL), CoefExt.up O.jL (lamV D i) (rhoVr (labLL D) (lamV D i) γE v) = rhoM O.c' (fun τ => embF O.c' (tauE D τ)) (lamV D i) (γE : Matrix _ _ D.host.E) (CoefExt.up O.jL (lamV D i) v)` using `fun γE v => by`. Establish `hu : IsUnit (γE.val).det` using `(Matrix.isUnit_iff_isUnit_det γE.val).1 γE.isUnit`. Establish `hγE : Matrix.nonsingInvUnit γE.val hu = γE` using `Units.ext rfl`. Establish `hemb : (fun τ => embF O.c' (tauE D τ)) = fun τ => O.jL.comp (labLL D τ)`.

Use function extensionality and compare the values at `fun τ => (embV_eq_embF O.c' O.jL hO.lift.field τ).symm`. Rewrite using `[rhoM, dif_pos hu, hγE, hemb]`. Conclude with `CoefExt.up_rhoVr O.jL (lamV D i) (labLL D) γE v`. Establish `hid : ∀ v, c₁ (CoefExt.up (RingHom.id _) (lamV D i) v) = c₁ v` using `fun v => congrArg c₁ (up_id _ v)`. Establish `n3 : Submodule.span ℂ (Set.range c₁) = ⊤` using `CoefExt.span_top (W := c.W) hid hc₁.span`.

Establish `n4 : ∀ (m : ℕ) (b : Fin m → VsV D i D.what₂.LL), LinearIndependent D.what₂.LL b → LinearIndependent ℂ (fun j => c₁ (b j))` using `fun m b hb => CoefExt.linearIndependent (W := c.W) hid hc₁.indep b hb`. Take `⟨r1, r2, -⟩` from `GlobalTheory.RatGen.rational_points_generate D (Vc D i) c (hR.models.vpos i) hP.sigV hc`. Take `⟨-, -, w1, w2, w3⟩` from `GlobalTheory.WeightExponents.weight_exponents D T.Q hT.laws.pins _ (inR i) (κ i)`. Establish `hty : IsTyp D T.Q.H` using `⟨w1, w2⟩`. Take `⟨d1, d2, -⟩` from `hT.laws.pins.2.2.2 _ (inR i)`.

Establish `hsig : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1)` using `fun τ => D.sp.W_sigval _ (inR i).1 (inR i).2 _`. Take `⟨-, cga, i1, i2, -, i3, -, -, i4, -⟩` from `hO.io`. Take `⟨w₀, hw₀, hΔ⟩` from `hex₀`. Establish `hBV : ∀ τ, (R.BV i τ)ᴴ * R.BV i τ = 1` using `fun τ => by`. Take `⟨ε, hε, h1, -⟩` from `hR.models.BV i τ`.

Rewrite `h1` using `[gramAt_one hP.std, Matrix.mul_one]`. Rewrite using `[h1, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Break down `hε a with h | h` into its components or cases.

Rewrite using `[h.1]`. Both sides reduce to the same expression. Conclude with `absurd a.2 (not_lt.2 h.2)`. Establish `hon : ∀ τ, IsONBasis (gramAt D (Vc D i) τ) 1 1 (Vc D i).rank` using `fun τ => ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, by simp [gramAt_one hP.std], by simp⟩`. Set `PT` to `pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (fun _ => 1) (onb (R.MW i σ)) f`.

Establish `hsub : ∀ (U : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ), (∀ τ, (U τ)ᴴ * U τ = 1) → ∀ P, pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) U (onb (R.MW i σ)) f P = PT (PhaseMap.sub (fun τ => ((Wc D i).sig (tauE D τ)).1) U P)` using `fun U hU P => by`. Establish `h` using `GlobalTheory.AdTh.SourceBasis.pureTensorO_mul_source D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ (fun _ => 1) U _ _ _ f5 (fun τ => (trace_parity (f5 τ)).1) (fun τ => by simp) (fun τ => PhaseMap.det_ne_zero (hU τ)) _ f1 P`. Simplify using `only [Matrix.one_mul] at h`. Conclude with `h`. Establish `hinj : Function.Injective PT` using `GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ _ _ _ _ _ _ f4 f3 hon f5 hP.sigV hP.sigW _ f1 f2 hvec.1`.

Take `⟨g, hg, hgB⟩ : ∃ g ∈ GinfC (Vc D i), ∀ τ, compAt R.θ τ (Formalism.L2.Theta.mt (Vc D i) g) = R.BV i τ` from `(GlobalTheory.SmoothForms.RealPts.glue R.θ hθ (Vc D i)).2 (R.BV i) fun τ => by show (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = gramAt D (Vc D i) τ`. Rewrite using `[gramAt_one hP.std, Matrix.mul_one, hBV]`. Take `⟨χ, hχ, hχg⟩` from `om_real hP f4 f3 f5 f1 f2 hg`. Rewrite `hχg` using `[funext hgB]`. Set `A₀ : c.W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)` to `pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) (onb (R.MW i σ)) f ∘ₗ Λ`.

Establish `hA₀ : ∀ a ∈ GinfC (Vc D i), ∀ w, A₀ (c.ρ a w) = ω (a, 1) (A₀ w)` using `fun a ha w => (hio a ha w).symm`. Establish `hw₁ : A₀ (c.ρ g⁻¹ (χ • w₀)) = PT (deltaConj i σ)`. Establish `h1 : A₀ (χ • w₀) = ω (g, 1) (PT (deltaConj i σ))`. Rewrite using `[map_smul, hχg, ← hΔ]`. Both sides reduce to the same expression.

Rewrite using `[hA₀ _ (inv_mem hg), h1, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one]`. Conclude with `congrArg (fun T : Module.End ℂ _ => T _) (map_one ω)`. Establish `hn₁ : ‖c.ρ g⁻¹ (χ • w₀)‖ = 1`. Rewrite using `[norm_eq_sqrt_re_inner (𝕜 := ℂ), hc.2.1, ← norm_eq_sqrt_re_inner, norm_smul, hχ, hw₀, mul_one]`. Use `haveI := hc.2.2.2.1`.

Use `haveI : FiniteDimensional D.what₂.LL (VsV D i D.what₂.LL) := Module.Finite.of_basis (Formalism.L2.DIV.bVV D.what₂.LL (lamV D i))`. Establish `main : ∀ lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank, IsLt (mv (lab σ) lt) → ∃ a : ℂ, a • c.ρ g⁻¹ (χ • w₀) = c₁ v₁ ∧ ∀ v, A₀ (c₁ v) = a • PT (toG O.c' σ' lt (O.io (CoefExt.up O.jL (lamV D i) v)))` using `fun lt hl => by`. Establish `hsm : ∀ (a : O.c'.F) P, toG O.c' σ' lt (a • P) = σ' a • toG O.c' σ' lt P` using `fun a P => by`. Rewrite using `[MvPolynomial.smul_eq_C_mul, map_mul, toG_C, MvPolynomial.smul_eq_C_mul]`. Take `⟨B₀, hB₀⟩` from `GlobalTheory.AdTh.PhaseMap.exists_ext c₁ n4 { toFun := fun v => toG O.c' σ' lt (O.io (CoefExt.up O.jL (lamV D i) v)) map_add' := fun v w => by rw [up_add, map_add, map_add] map_smul' := fun a v => by rw [up_smul, map_smul, hsm, ← RingHom.congr_fun hσ a]; rfl }`.

Use `replace hB₀ : ∀ v, B₀ (c₁ v) = toG O.c' σ' lt (O.io (CoefExt.up O.jL (lamV D i) v)) := hB₀`. Establish `hpG : toG O.c' σ' lt (O.io O.hw) = deltaConj i σ`. Rewrite using `[i4]`. Use `toG_pG O.c' σ' he hl hty i1 _ _ _ _ _ (fun τ => by rw [pW, hsig, d1]) (fun τ => by rw [qW, hsig, d2]) (fun τ k hk => ?_) fun τ k hk => ?_` and prove the remaining obligations. Rewrite `hk` using `[d1]`.

Use `(w3 _ k).1.trans ((dif_pos hk).trans (((hT.kap i _).1 ⟨k, hk⟩).trans ?_))` and prove the remaining obligations. Rewrite using `[pW, hsig, hsig]`. Rewrite `hk` using `[d2]`. Use `(w3 _ k).2.trans ((dif_pos hk).trans (((hT.kap i _).2.1 ⟨k, hk⟩).trans ?_))` and prove the remaining obligations. Rewrite using `[pW, qW, hsig, hsig]`.

Take `⟨a, ha, ha'⟩` from `proportional (c.ρ.comp (GQ (Vc D i)).subtype) _ r1 (fun γ hγ => hγ) r2 A₀ (PT ∘ₗ B₀) (fun γ => by`. Take `⟨γE, a, k, h1, h2, h3, h4, h5, h6⟩` from `rat_parts hθ hP.std γ`. Take `⟨x, hx, hxa⟩` from `om_real hP f4 f3 f5 f1 f2 h2`. Establish `hx0 : x ≠ 0` using `fun h => by simp [h] at hx`. Establish `h7 : c.ρ γ = c.ρ a` using `by rw [h4, map_mul, hc.1 k h3, mul_one]`.

Use `⟨ω (a, 1), σ' (cga γE.val) * x⁻¹, fun w => ?_, fun w => ?_⟩` and prove the remaining obligations. Use `show A₀ (c.ρ γ w) = _`. Rewrite using `[h7, hA₀ a h2]`. Establish `h8 : (PT ∘ₗ B₀) ∘ₗ c.ρ γ = (σ' (cga γE.val) * x⁻¹) • (ω (a, 1) ∘ₗ (PT ∘ₗ B₀))`. Use `LinearMap.ext_on_range n3 fun v => ?_` and prove the remaining obligations.

Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply]`. Rewrite using `[← hc₁.act γ γE h1, hB₀, hB₀, n2, i3 _ h5, hsm, hxa, hsub _ (compAt_unitary hθ hP.std a), smul_smul, inv_mul_cancel_right₀ hx0, map_smul, toG_gaStar O.c' σ' he.1 hl hty e1 e2 (fun τ => ((Wc D i).sig (tauE D τ)).1) (fun τ => by rw [hsig, d1]) _ _ h6]`. Conclude with `LinearMap.congr_fun h8 w)`. Use the proof step `(c.ρ g⁻¹ (χ • w₀)) (c₁ v₁) (by rw [hw₁, LinearMap.comp_apply, hB₀, hv, hpG])`. Use the proof step `(fun h => by`.

Rewrite `h` using `[LinearMap.comp_apply, hB₀, map_eq_zero_iff _ hinj, map_eq_zero_iff _ (toG_injective O.c' σ' hl hty), map_eq_zero_iff _ i2]`. Establish `h0 : v₁ = 0` using `Subtype.ext (MvPolynomial.map_injective _ O.jL.injective ((congrArg Subtype.val h).trans (map_zero _).symm))`. Rewrite `n1` using `[h0, map_zero, norm_zero]`. Conclude with `zero_ne_one n1)`. Conclude with `⟨a, ha', fun v => (ha _).trans (congrArg (fun P => a • PT P) (hB₀ v))⟩`.

Distinguish the cases in `hex : ∃ lt, IsLtAt O σ' lt`. Take `⟨lt₀, hl₀⟩` from `hex`. Take `⟨a, ha, -⟩` from `main lt₀ (hlt _ hl₀)`. Use `⟨a, ?_, fun lt hl x x' hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← n1, ← ha, norm_smul, hn₁, mul_one]`.

Take `⟨b, hb, hb'⟩` from `main lt (hlt _ hl)`. Take `rfl : a = b` from `smul_left_injective ℂ (fun h => by simp [h] at hn₁) (ha.trans hb.symm)`. Take `rfl : x' = CoefExt.up O.jL (lamV D i) x` from `Subtype.ext hx`. Conclude with `hb' x`. Conclude with `⟨1, norm_one, fun lt hl => absurd ⟨lt, hl⟩ hex⟩`.
-/
theorem io_eq_phase_smul_at_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → FWTie T R κ v₀ → ∀ (i : Fin D.R.m) (O : OM T R i), Pinned κ v₀ O → ∀ (σ : D.what₂.LL →+* ℂ) (σ' : O.c'.F →+* ℂ), σ'.comp O.jL = σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ), ConjW R i σ μ' η' ω f₀ f → ∀ (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ → ∀ (Λ : c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ u ∈ GinfC (Vc D i), ∀ w, ω (u, 1) (ptAt R i σ (onb (R.MW i σ)) f (Λ w)) = ptAt R i σ (onb (R.MW i σ)) f (Λ (c.ρ u w))) → (∃ w : c.W, ‖w‖ = 1 ∧ Λ w = deltaConj i σ) → ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∀ lt, IsLtAt O σ' lt → ∀ x x', IsUp O x x' → ptAt R i σ (onb (R.MW i σ)) f (Λ (c₁ x)) = ka • pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (fun _ => 1) (onb (R.MW i σ)) f (MvPolynomial.rename lt (MvPolynomial.map σ' (O.io x'))) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT i O hO σ σ' hσ μ' η' ω f₀ f hW c c₁ hc₁ Λ hio hex₀
  have hstd := hO.lift.std
  have hθ : IsInfFam R.θ := hR.models.inf
  have hc : c.Is := hc₁.coef
  have hvec := GlobalTheory.GalOne.VecConj.vec_conj_ofFive R F hR i σ μ' η' ω f₀ f hW
  have hfac := GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hR hT i O hO σ σ' hσ hW.1
  have hP := hvec.2.2.2.2.2 hstd.1
  have hψ := hP.weil.std
  have f1 : IsThetaFunO R.ψ (Vc D i) (Wc D i) f := hW.2.2.2.2.2
  have f2 := hvec.2.1
  have f3 := GlobalTheory.AdTh.VecFock.isCartanInv_cart (R.MW i σ)
  have f4 := (GlobalTheory.AdTh.VecFock.vec_fock_ofFive' D G Pl0 T0 A _ R F hR i A.μ0 hstd).2.2.2.1
  have f5 := hvec.2.2.1
  have he : Function.Bijective (lab (D := D) σ) := hvec.2.2.2.2.1.lab_bij
  have hrel := GlobalTheory.Relab.relab_good _ _ _ O.c' σ' hfac.2.2.1
  have e1 : ∀ ρ, relab O.c' σ' (tauE D (lab σ ρ)) = tauE D ρ := hfac.2.2.2.2.2.2.2.1
  have e2 : ∀ ρ, relab O.c' σ' (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (tauE D (lab σ ρ))) =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (tauE D ρ) := fun ρ => (hrel.2.2.1 _).trans (congrArg _ (e1 ρ))
  have hlt : ∀ lt, IsLtAt O σ' lt → IsLt (mv (lab σ) lt) := fun lt hl ℓ =>
    ⟨(hl ℓ).1, (hl ℓ).2.imp (fun h => ⟨hrel.1.1 (h.1.trans (e1 _).symm), h.2⟩)
      fun h => ⟨hrel.1.1 (h.1.trans (e2 _).symm), h.2⟩⟩
  let v₁ : VsV D i D.what₂.LL := ⟨Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal D.what₂.LL _ (lamV D i τ),
    GlobalTheory.Proof.TensorMapDescent.ten_mem _ _ fun τ => Formalism.GradedWeylDivisibility.hwMem _ _ _ le_rfl _ (Formalism.L2.DIV.natW_antitone _)⟩
  have hv : CoefExt.up O.jL (lamV D i) v₁ = O.hw := by
    apply Subtype.ext
    have hw := hO.io.1
    unfold hwOK at hw
    refine Eq.trans ?_ hw.symm
    show MvPolynomial.map O.jL (Formalism.L2.DIV.ten _) = _
    rw [GlobalTheory.Proof.TensorMapDescent.map_ten]
    congr 1
    funext τ
    exact Formalism.L2.DIV.map_extremal _ _ _
  have n1 : ‖c₁ v₁‖ = 1 := by
    have hn := GlobalTheory.StdFrame.neg_eq_false_of_vStd D i hstd
    have hG : gramV D i = 1 := by
      rw [gramV, hn, if_neg Bool.false_ne_true]
      exact hstd.1
    have hi := inner_of_int (lamV D i) σ c₁ _ hc₁.pair v₁ v₁ (∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℤ τ (Formalism.BasicNotions.extremal ℤ _ (lamV D i τ))) (by
      show Formalism.L2.DIV.ten _ = _
      unfold Formalism.L2.DIV.ten
      rw [map_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [fk_map_blockEmb, Formalism.L2.DIV.map_extremal])
    rw [hG] at hi
    replace hi := hi.trans ((congrArg σ (CoefExt.pairVr_extremal (labLL D) v₁ rfl)).trans (map_one _))
    rw [inner_self_eq_norm_sq_to_K] at hi
    have h4 : ‖c₁ v₁‖ ^ 2 = 1 := by
      have h5 := congrArg norm hi
      simpa using h5
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  have n2 : ∀ (γE : GL (Fin (Vc D i).rank) D.host.E) (v : VsV D i D.what₂.LL),
      CoefExt.up O.jL (lamV D i) (rhoVr (labLL D) (lamV D i) γE v) =
        rhoM O.c' (fun τ => embF O.c' (tauE D τ)) (lamV D i) (γE : Matrix _ _ D.host.E)
          (CoefExt.up O.jL (lamV D i) v) := fun γE v => by
    have hu : IsUnit (γE.val).det := (Matrix.isUnit_iff_isUnit_det γE.val).1 γE.isUnit
    have hγE : Matrix.nonsingInvUnit γE.val hu = γE := Units.ext rfl
    have hemb : (fun τ => embF O.c' (tauE D τ)) = fun τ => O.jL.comp (labLL D τ) :=
      funext fun τ => (embV_eq_embF O.c' O.jL hO.lift.field τ).symm
    rw [rhoM, dif_pos hu, hγE, hemb]
    exact CoefExt.up_rhoVr O.jL (lamV D i) (labLL D) γE v
  have hid : ∀ v, c₁ (CoefExt.up (RingHom.id _) (lamV D i) v) = c₁ v := fun v => congrArg c₁ (up_id _ v)
  have n3 : Submodule.span ℂ (Set.range c₁) = ⊤ := CoefExt.span_top (W := c.W) hid hc₁.span
  have n4 : ∀ (m : ℕ) (b : Fin m → VsV D i D.what₂.LL), LinearIndependent D.what₂.LL b →
      LinearIndependent ℂ (fun j => c₁ (b j)) := fun m b hb => CoefExt.linearIndependent (W := c.W) hid hc₁.indep b hb
  obtain ⟨r1, r2, -⟩ := GlobalTheory.RatGen.rational_points_generate D (Vc D i) c (hR.models.vpos i) hP.sigV hc
  obtain ⟨-, -, w1, w2, w3⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hT.laws.pins _ (inR i) (κ i)
  have hty : IsTyp D T.Q.H := ⟨w1, w2⟩
  obtain ⟨d1, d2, -⟩ := hT.laws.pins.2.2.2 _ (inR i)
  have hsig : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := fun τ => D.sp.W_sigval _ (inR i).1 (inR i).2 _
  obtain ⟨-, cga, i1, i2, -, i3, -, -, i4, -⟩ := hO.io
  obtain ⟨w₀, hw₀, hΔ⟩ := hex₀
  have hBV : ∀ τ, (R.BV i τ)ᴴ * R.BV i τ = 1 := fun τ => by
    obtain ⟨ε, hε, h1, -⟩ := hR.models.BV i τ
    rw [gramAt_one hP.std, Matrix.mul_one] at h1
    rw [h1, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with h | h
    · rw [h.1]; rfl
    · exact absurd a.2 (not_lt.2 h.2)
  have hon : ∀ τ, IsONBasis (gramAt D (Vc D i) τ) 1 1 (Vc D i).rank := fun τ =>
    ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, by simp [gramAt_one hP.std], by simp⟩
  let PT := pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (fun _ => 1) (onb (R.MW i σ)) f
  have hsub : ∀ (U : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ), (∀ τ, (U τ)ᴴ * U τ = 1) → ∀ P,
      pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) U (onb (R.MW i σ)) f P =
        PT (PhaseMap.sub (fun τ => ((Wc D i).sig (tauE D τ)).1) U P) := fun U hU P => by
    have h := GlobalTheory.AdTh.SourceBasis.pureTensorO_mul_source D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ (fun _ => 1) U _ _ _ f5
      (fun τ => (trace_parity (f5 τ)).1) (fun τ => by simp) (fun τ => PhaseMap.det_ne_zero (hU τ)) _ f1 P
    simp only [Matrix.one_mul] at h
    exact h
  have hinj : Function.Injective PT :=
    GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ _ _ _ _ _ _ f4 f3 hon f5 hP.sigV hP.sigW _ f1 f2
      hvec.1
  obtain ⟨g, hg, hgB⟩ : ∃ g ∈ GinfC (Vc D i), ∀ τ, compAt R.θ τ (Formalism.L2.Theta.mt (Vc D i) g) = R.BV i τ :=
    (GlobalTheory.SmoothForms.RealPts.glue R.θ hθ (Vc D i)).2 (R.BV i) fun τ => by
      show (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = gramAt D (Vc D i) τ
      rw [gramAt_one hP.std, Matrix.mul_one, hBV]
  obtain ⟨χ, hχ, hχg⟩ := om_real hP f4 f3 f5 f1 f2 hg
  rw [funext hgB] at hχg
  let A₀ : c.W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) :=
    pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) (onb (R.MW i σ)) f ∘ₗ Λ
  have hA₀ : ∀ a ∈ GinfC (Vc D i), ∀ w, A₀ (c.ρ a w) = ω (a, 1) (A₀ w) := fun a ha w => (hio a ha w).symm
  have hw₁ : A₀ (c.ρ g⁻¹ (χ • w₀)) = PT (deltaConj i σ) := by
    have h1 : A₀ (χ • w₀) = ω (g, 1) (PT (deltaConj i σ)) := by
      rw [map_smul, hχg, ← hΔ]
      rfl
    rw [hA₀ _ (inv_mem hg), h1, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one]
    exact congrArg (fun T : Module.End ℂ _ => T _) (map_one ω)
  have hn₁ : ‖c.ρ g⁻¹ (χ • w₀)‖ = 1 := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), hc.2.1, ← norm_eq_sqrt_re_inner, norm_smul, hχ, hw₀, mul_one]
  haveI := hc.2.2.2.1
  haveI : FiniteDimensional D.what₂.LL (VsV D i D.what₂.LL) := Module.Finite.of_basis (Formalism.L2.DIV.bVV D.what₂.LL (lamV D i))
  have main : ∀ lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank, IsLt (mv (lab σ) lt) →
      ∃ a : ℂ, a • c.ρ g⁻¹ (χ • w₀) = c₁ v₁ ∧ ∀ v, A₀ (c₁ v) =
        a • PT (toG O.c' σ' lt (O.io (CoefExt.up O.jL (lamV D i) v))) := fun lt hl => by
    have hsm : ∀ (a : O.c'.F) P, toG O.c' σ' lt (a • P) = σ' a • toG O.c' σ' lt P := fun a P => by
      rw [MvPolynomial.smul_eq_C_mul, map_mul, toG_C, MvPolynomial.smul_eq_C_mul]
    obtain ⟨B₀, hB₀⟩ := GlobalTheory.AdTh.PhaseMap.exists_ext c₁ n4
      { toFun := fun v => toG O.c' σ' lt (O.io (CoefExt.up O.jL (lamV D i) v))
        map_add' := fun v w => by rw [up_add, map_add, map_add]
        map_smul' := fun a v => by rw [up_smul, map_smul, hsm, ← RingHom.congr_fun hσ a]; rfl }
    replace hB₀ : ∀ v, B₀ (c₁ v) = toG O.c' σ' lt (O.io (CoefExt.up O.jL (lamV D i) v)) := hB₀
    have hpG : toG O.c' σ' lt (O.io O.hw) = deltaConj i σ := by
      rw [i4]
      refine toG_pG O.c' σ' he hl hty i1 _ _ _ _ _ (fun τ => by rw [pW, hsig, d1]) (fun τ => by rw [qW, hsig, d2])
        (fun τ k hk => ?_) fun τ k hk => ?_
      · rw [d1] at hk
        refine (w3 _ k).1.trans ((dif_pos hk).trans (((hT.kap i _).1 ⟨k, hk⟩).trans ?_))
        rw [pW, hsig, hsig]
      · rw [d2] at hk
        refine (w3 _ k).2.trans ((dif_pos hk).trans (((hT.kap i _).2.1 ⟨k, hk⟩).trans ?_))
        rw [pW, qW, hsig, hsig]
    obtain ⟨a, ha, ha'⟩ := proportional (c.ρ.comp (GQ (Vc D i)).subtype) _ r1 (fun γ hγ => hγ) r2 A₀ (PT ∘ₗ B₀)
      (fun γ => by
        obtain ⟨γE, a, k, h1, h2, h3, h4, h5, h6⟩ := rat_parts hθ hP.std γ
        obtain ⟨x, hx, hxa⟩ := om_real hP f4 f3 f5 f1 f2 h2
        have hx0 : x ≠ 0 := fun h => by simp [h] at hx
        have h7 : c.ρ γ = c.ρ a := by rw [h4, map_mul, hc.1 k h3, mul_one]
        refine ⟨ω (a, 1), σ' (cga γE.val) * x⁻¹, fun w => ?_, fun w => ?_⟩
        · show A₀ (c.ρ γ w) = _
          rw [h7, hA₀ a h2]
        · have h8 : (PT ∘ₗ B₀) ∘ₗ c.ρ γ = (σ' (cga γE.val) * x⁻¹) • (ω (a, 1) ∘ₗ (PT ∘ₗ B₀)) := by
            refine LinearMap.ext_on_range n3 fun v => ?_
            simp only [LinearMap.comp_apply, LinearMap.smul_apply]
            rw [← hc₁.act γ γE h1, hB₀, hB₀, n2, i3 _ h5, hsm, hxa, hsub _ (compAt_unitary hθ hP.std a), smul_smul,
              inv_mul_cancel_right₀ hx0, map_smul,
              toG_gaStar O.c' σ' he.1 hl hty e1 e2 (fun τ => ((Wc D i).sig (tauE D τ)).1) (fun τ => by rw [hsig, d1]) _ _ h6]
          exact LinearMap.congr_fun h8 w)
      (c.ρ g⁻¹ (χ • w₀)) (c₁ v₁) (by rw [hw₁, LinearMap.comp_apply, hB₀, hv, hpG])
      (fun h => by
        rw [LinearMap.comp_apply, hB₀, map_eq_zero_iff _ hinj, map_eq_zero_iff _ (toG_injective O.c' σ' hl hty),
          map_eq_zero_iff _ i2] at h
        have h0 : v₁ = 0 := Subtype.ext (MvPolynomial.map_injective _ O.jL.injective
          ((congrArg Subtype.val h).trans (map_zero _).symm))
        rw [h0, map_zero, norm_zero] at n1
        exact zero_ne_one n1)
    exact ⟨a, ha', fun v => (ha _).trans (congrArg (fun P => a • PT P) (hB₀ v))⟩
  by_cases hex : ∃ lt, IsLtAt O σ' lt
  · obtain ⟨lt₀, hl₀⟩ := hex
    obtain ⟨a, ha, -⟩ := main lt₀ (hlt _ hl₀)
    refine ⟨a, ?_, fun lt hl x x' hx => ?_⟩
    · rw [← n1, ← ha, norm_smul, hn₁, mul_one]
    · obtain ⟨b, hb, hb'⟩ := main lt (hlt _ hl)
      obtain rfl : a = b := smul_left_injective ℂ (fun h => by simp [h] at hn₁) (ha.trans hb.symm)
      obtain rfl : x' = CoefExt.up O.jL (lamV D i) x := Subtype.ext hx
      exact hb' x
  · exact ⟨1, norm_one, fun lt hl => absurd ⟨lt, hl⟩ hex⟩

end GlobalTheory.GalOne.PhaseAt

end

end

section

noncomputable section

namespace GlobalTheory.GalOne.IoCmp

section Letters

open NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

end Letters

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne
open GlobalTheory.OneMapRef.IoCmp

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ hR t i O hO σ σ' hσ μ' η' ω f₀ f hW cf c₁ hc₁ B hB io hio0 v hv`. Establish `hfa` using `GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hR t i O hO σ σ' hσ hW.1`. Establish `hgood : GoodEmb O.c' σ'` using `hfa.2.2.1`. Establish `hord` using `hfa.2.2.2.1`. Establish `hcart` using `hfa.2.2.2.2.2.1`.

Establish `hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f` using `hW.2.2.2.2.2`. Use `(GlobalTheory.GalOne.Rebase.rebase_ofFive R F hR i σ μ' η' ω f₀ f hW B hB cf io hio0).elim fun io' hio' => ?_` and prove the remaining obligations. Establish `hext : IsExtVec (R.MW i σ) (fun ρ => v ρ)`. Establish `h` using `(t.hv₀ i σ).1`. Rewrite `h` using `[← hv]`.

Conclude with `h`. Establish `hw` using `GlobalTheory.GalOne.IoExtConj.ioExt_conj_ofFive R F hR i σ μ' η' ω f₀ f hW cf io' hio'.1 v hext`. Use `(GlobalTheory.GalOne.PhaseAt.io_eq_phase_smul_at_ofFive T R F κ v₀ hR t i O hO σ σ' hσ μ' η' ω f₀ f hW cf c₁ hc₁ (io' (PiTensorProduct.tprod ℂ v)) (fun u hu w => hio'.1.1 u hu _ w) hw).elim fun ka hka' => ?_` and prove the remaining obligations. Establish `hka` using `hka'.1`. Establish `hio` using `hka'.2`.

Take `⟨-, -, w1, w2, -⟩` from `GlobalTheory.WeightExponents.weight_exponents D T.Q t.laws.pins _ (inR i) (κ i)`. Use `replace w1 : ∀ τ, InPsi T.Q.H τ ↔ ∃ t, τ = tauE D t := w1`. Use `replace w2 : ∀ τ, ¬ InPsi T.Q.H τ ↔ ∃ t, τ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (tauE D t) := w2`. Establish `hrl : ∀ τ, InPsi T.Q.H (relab O.c' σ' τ) ↔ InPsi T.Q.H τ` using `fun τ => Formalism.L2.Pj.relab_rt_iff O.c' σ' hgood τ`. Take `⟨d1, d2, -⟩` from `t.laws.pins.2.2.2 _ (inR i)`.

Take `⟨-, -, -, hx, -, -, hpq⟩` from `GlobalTheory.PinNum.numerics_of_pins D T.Q t.laws.pins`. Use `replace hpq := (hpq _ (inR i)).1`. Establish `hr` using `rank_Wc (D := D) i`. Establish `hsig : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1)` using `fun τ => D.sp.W_sigval _ (inR i).1 (inR i).2 _`. Establish `hneg : ∀ ρ, nNeg ((R.MW i σ).ε ρ) = (T.Q.Dw ((i : ℕ) + 1)).q` using `fun ρ => by`.

Establish `h` using `nNeg_shape (ε := (R.MW i σ).ε ρ) (p := (T.Q.Dw ((i : ℕ) + 1)).p) (by omega) (fun a => by rw [hord ρ a, hsig, d1])`. Use linear arithmetic over natural numbers and integers. Establish `hθ : IsInfFam R.θ` using `hR.models.inf`. Establish `hψ` using `(hR.thP.ωP i A.μ0).std`. Establish `hcj : ∀ a b : D.host.E →+* ℂ, ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb a = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb b → a = b` using `fun a b h => by`.

Use extensionality with `x`. Conclude with `star_injective (RingHom.congr_fun h x)`. Establish `hex : ∀ ℓ : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank, ∃ (ρ : D.what₂.Tau) (c : Fin (Wc D i).rank), (relab O.c' σ' ℓ.1 = tauE D ρ ∧ (c : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).q + ℓ.2.1 ∧ (ℓ.2.1 : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p) ∨ (relab O.c' σ' ℓ.1 = ReciprocityTheory.ChartRestriction.G.Geo. …` using `fun ℓ => by`. Distinguish the cases in `h : InPsi T.Q.H ℓ.1`. Take `⟨ρ, hρ⟩` from `(w1 _).1 ((hrl _).2 h)`.

Establish `h3 : (ℓ.2.1 : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p` using `lt_of_lt_of_eq ℓ.2.1.2 (if_pos h)`. Conclude with `⟨ρ, ⟨(T.Q.Dw ((i : ℕ) + 1)).q + ℓ.2.1, by omega⟩, Or.inl ⟨hρ, rfl, h3⟩⟩`. Take `⟨ρ, hρ⟩` from `(w2 _).1 (fun h' => h ((hrl _).1 h'))`. Establish `h3 : (ℓ.2.1 : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).q` using `lt_of_lt_of_eq ℓ.2.1.2 (if_neg h)`. Conclude with `⟨ρ, ⟨(T.Q.Dw ((i : ℕ) + 1)).q - 1 - ℓ.2.1, by omega⟩, Or.inr ⟨hρ, rfl, h3⟩⟩`.

Use `choose ρ c hc using hex`. Set `lt' : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank` to `fun ℓ => (ρ ℓ, c ℓ, ℓ.2.2)`. Set `lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank` to `fun ℓ => (ρ ℓ, arr (T.Q.Dw ((i : ℕ) + 1)).q (c ℓ), ℓ.2.2)`. Use `replace hio := hio lt (fun ℓ => ⟨rfl, by`. Break down `hc ℓ with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩` into its components or cases.

Use `Or.inl ⟨h1, ?_⟩ show ((arr (T.Q.Dw ((i : ℕ) + 1)).q (c ℓ) : Fin _) : ℕ) = _` and prove the remaining obligations. Rewrite using `[arr, dif_neg (by omega)]`. Use `show (c ℓ : ℕ) - _ = _`. Use linear arithmetic over natural numbers and integers. Use `Or.inr ⟨h1, ?_⟩ show ((arr (T.Q.Dw ((i : ℕ) + 1)).q (c ℓ) : Fin _) : ℕ) = _` and prove the remaining obligations.

Rewrite using `[arr, dif_pos (by omega)]`. Use `show (Wc D i).rank - 1 - (c ℓ : ℕ) = _`. Use the proof step `omega⟩)`. Establish `hBV : ∀ τ, (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = 1` using `fun τ => by`. Take `⟨ε, hε, h1, -⟩` from `hR.models.BV i τ`.

Rewrite using `[h1, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Break down `hε a with h | h` into its components or cases. Rewrite using `[h.1]`.

Both sides reduce to the same expression. Conclude with `absurd a.2 (not_lt.2 h.2)`. Establish `hka0 : ka ≠ 0` using `fun h => by simp [h] at hka`. Use `⟨ka⁻¹, by rw [norm_inv, hka, inv_one], fun x x' hxx => ⟨ka • MvPolynomial.rename lt' (MvPolynomial.map σ' (O.io x')), ?_, fun X eT g Dc heT => ?_⟩⟩` and prove the remaining obligations. Use `(hio'.2 _ _).trans ((hio x x' hxx).trans ?_)` and prove the remaining obligations.

Rewrite using `[fv, ← hcart, map_smul]`. Use `congrArg (fun y => ka • y) ?_` and prove the remaining obligations. Conclude with `pureTensorO_rename hψ hθ (fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBV τ)) (GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MW i σ)) hf _ _ _ (fun τ => arr (T.Q.Dw ((i : ℕ) + 1)).q) (fun τ => by rw [zAt, x0Mat, hneg]) ρ c (fun ℓ => ℓ.2.2) _`. Take `⟨-, cga, -, -, i3, -⟩` from `hO.io`. Establish `hhom` using `(isHomogeneous_of_span _ _ _ _ _ _ (i3 ▸ LinearMap.mem_range_self O.io x')).map σ'`.

Establish `hp0` using `Dc.hr`. Establish `hm : ∀ τ, relab O.c' σ' τ ∉ X.Ψ → (T.Q.Dw ((i : ℕ) + 1)).mult τ ≤ X.p0` using `fun τ hτ => by`. Establish `h : ¬ InPsi T.Q.H τ` using `fun h => by`. Take `⟨s, hs⟩` from `(w1 _).1 ((hrl τ).2 h)`. Conclude with `hτ (by rw [hs, ← heT s]; exact (eT s).2)`.

Establish `h2 : (T.Q.Dw ((i : ℕ) + 1)).mult τ = (T.Q.Dw ((i : ℕ) + 1)).q` using `if_neg h`. Use linear arithmetic over natural numbers and integers. Establish `hne : ∀ (s : D.what₂.Tau) (t : X.Ψ), tauE D s ≠ ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb t.1` using `fun s t e => (w2 _).2 ⟨eT.symm t, by rw [e, ← heT, Equiv.apply_symm_apply]⟩ ((w1 _).2 ⟨s, rfl⟩)`. Establish `heL : ∀ ℓ, (eT (ρ ℓ), (rowIdx Dc.hr).symm (Fin.cast (rank_Wc i) (c ℓ)), ℓ.2.2) = Dc.eL ℓ` using `fun ℓ => by`. Take `⟨h1, h2⟩` from `letter_relab Dc hm ℓ`.

Use `replace h2 : (∃ k, (Dc.eL ℓ).2.1 = Sum.inl k ∧ relab O.c' σ' ℓ.1 = (Dc.eL ℓ).1.1 ∧ (k : ℕ) = ℓ.2.1) ∨ (∃ k, (Dc.eL ℓ).2.1 = Sum.inr k ∧ relab O.c' σ' ℓ.1 = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (Dc.eL ℓ).1.1 ∧ (k : ℕ) = ℓ.2.1) := h2`. Establish `key : (eT (ρ ℓ)).1 = (Dc.eL ℓ).1.1 ∧ (c ℓ : ℕ) = rowIdx Dc.hr (Dc.eL ℓ).2.1`. Apply the tactic sequence `rcases h2 with ⟨k, e1, e2, e3⟩ | ⟨k, e1, e2, e3⟩ <;> rcases hc ℓ with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩`. Conclude with `⟨by rw [heT, ← g1, e2], by rw [e1, rowIdx_inl]; omega⟩`. Use `absurd ?_ (hne (eT.symm (Dc.eL ℓ).1) (eT (ρ ℓ)))` and prove the remaining obligations.

Rewrite using `[← heT, Equiv.apply_symm_apply, heT, ← g1, e2]`. Conclude with `absurd (g1.symm.trans e2) (hne _ _)`. Conclude with `⟨by rw [heT]; exact hcj _ _ (g1.symm.trans e2), by rw [e1, rowIdx_inr]; omega⟩`. Use `Prod.ext (Subtype.ext key.1) (Prod.ext ?_ h1.symm)` and prove the remaining obligations. Conclude with `(Equiv.symm_apply_eq _).2 (Fin.ext key.2)`.

Rewrite using `[map_smul, ← MvPolynomial.C_mul', ← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hka0, MvPolynomial.C_1, one_mul, toP, MvPolynomial.aeval_rename, lieFac_eq_pow _ hx, Complex.ofReal_pow, ← aeval_scale _ _ hhom]`. Use `congr 2`. Use function extensionality and compare the values at `ℓ`. Simplify using `only [Function.comp_apply, lt', two_div_fockScale, heL]`.
-/
theorem ioAt_of_conj_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → FWTie T R κ v₀ → ∀ (i : Fin D.R.m) (O : OM T R i), Pinned κ v₀ O → ∀ (σ : D.what₂.LL →+* ℂ) (σ' : O.c'.F →+* ℂ), σ'.comp O.jL = σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ), ConjW R i σ μ' η' ω f₀ f → ∀ (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ → ∀ (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), (∀ ρ, IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (B ρ) (pW D i ρ)) → ∀ (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ B f) (deltaConj i σ) io → ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (fun ρ => (v ρ : (R.MW i σ).sm ρ)) = v₀ i σ → ∃ ph : ℂ, ‖ph‖ = 1 ∧ IoAt κ O σ σ' c₁ f (fun w => ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ph := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR t i O hO σ σ' hσ μ' η' ω f₀ f hW cf c₁ hc₁ B hB io hio0 v hv
  classical
  have hfa := GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hR t i O hO σ σ' hσ hW.1
  have hgood : GoodEmb O.c' σ' := hfa.2.2.1
  have hord := hfa.2.2.2.1
  have hcart := hfa.2.2.2.2.2.1
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f := hW.2.2.2.2.2
  refine (GlobalTheory.GalOne.Rebase.rebase_ofFive R F hR i σ μ' η' ω f₀ f hW B hB cf io hio0).elim fun io' hio' => ?_
  have hext : IsExtVec (R.MW i σ) (fun ρ => v ρ) := by
    have h := (t.hv₀ i σ).1
    rw [← hv] at h
    exact h
  have hw := GlobalTheory.GalOne.IoExtConj.ioExt_conj_ofFive R F hR i σ μ' η' ω f₀ f hW cf io' hio'.1 v hext
  refine (GlobalTheory.GalOne.PhaseAt.io_eq_phase_smul_at_ofFive T R F κ v₀ hR t i O hO σ σ' hσ μ' η' ω f₀ f hW cf c₁ hc₁ (io' (PiTensorProduct.tprod ℂ v))
    (fun u hu w => hio'.1.1 u hu _ w) hw).elim fun ka hka' => ?_
  have hka := hka'.1
  have hio := hka'.2
  obtain ⟨-, -, w1, w2, -⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q t.laws.pins _ (inR i) (κ i)
  replace w1 : ∀ τ, InPsi T.Q.H τ ↔ ∃ t, τ = tauE D t := w1
  replace w2 : ∀ τ, ¬ InPsi T.Q.H τ ↔ ∃ t, τ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (tauE D t) := w2
  have hrl : ∀ τ, InPsi T.Q.H (relab O.c' σ' τ) ↔ InPsi T.Q.H τ := fun τ => Formalism.L2.Pj.relab_rt_iff O.c' σ' hgood τ
  obtain ⟨d1, d2, -⟩ := t.laws.pins.2.2.2 _ (inR i)
  obtain ⟨-, -, -, hx, -, -, hpq⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q t.laws.pins
  replace hpq := (hpq _ (inR i)).1
  have hr := rank_Wc (D := D) i
  have hsig : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := fun τ => D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have hneg : ∀ ρ, nNeg ((R.MW i σ).ε ρ) = (T.Q.Dw ((i : ℕ) + 1)).q := fun ρ => by
    have h := nNeg_shape (ε := (R.MW i σ).ε ρ) (p := (T.Q.Dw ((i : ℕ) + 1)).p) (by omega)
      (fun a => by rw [hord ρ a, hsig, d1])
    omega
  have hθ : IsInfFam R.θ := hR.models.inf
  have hψ := (hR.thP.ωP i A.μ0).std
  have hcj : ∀ a b : D.host.E →+* ℂ, ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb a = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb b → a = b := fun a b h => by
    ext x
    exact star_injective (RingHom.congr_fun h x)
  have hex : ∀ ℓ : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank, ∃ (ρ : D.what₂.Tau) (c : Fin (Wc D i).rank),
      (relab O.c' σ' ℓ.1 = tauE D ρ ∧ (c : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).q + ℓ.2.1 ∧ (ℓ.2.1 : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p) ∨
      (relab O.c' σ' ℓ.1 = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (tauE D ρ) ∧ (c : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).q - 1 - ℓ.2.1 ∧
        (ℓ.2.1 : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).q) := fun ℓ => by
    by_cases h : InPsi T.Q.H ℓ.1
    · obtain ⟨ρ, hρ⟩ := (w1 _).1 ((hrl _).2 h)
      have h3 : (ℓ.2.1 : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p := lt_of_lt_of_eq ℓ.2.1.2 (if_pos h)
      exact ⟨ρ, ⟨(T.Q.Dw ((i : ℕ) + 1)).q + ℓ.2.1, by omega⟩, Or.inl ⟨hρ, rfl, h3⟩⟩
    · obtain ⟨ρ, hρ⟩ := (w2 _).1 (fun h' => h ((hrl _).1 h'))
      have h3 : (ℓ.2.1 : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).q := lt_of_lt_of_eq ℓ.2.1.2 (if_neg h)
      exact ⟨ρ, ⟨(T.Q.Dw ((i : ℕ) + 1)).q - 1 - ℓ.2.1, by omega⟩, Or.inr ⟨hρ, rfl, h3⟩⟩
  choose ρ c hc using hex
  let lt' : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank := fun ℓ => (ρ ℓ, c ℓ, ℓ.2.2)
  let lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank :=
    fun ℓ => (ρ ℓ, arr (T.Q.Dw ((i : ℕ) + 1)).q (c ℓ), ℓ.2.2)
  replace hio := hio lt (fun ℓ => ⟨rfl, by
    rcases hc ℓ with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · refine Or.inl ⟨h1, ?_⟩
      show ((arr (T.Q.Dw ((i : ℕ) + 1)).q (c ℓ) : Fin _) : ℕ) = _
      rw [arr, dif_neg (by omega)]
      show (c ℓ : ℕ) - _ = _
      omega
    · refine Or.inr ⟨h1, ?_⟩
      show ((arr (T.Q.Dw ((i : ℕ) + 1)).q (c ℓ) : Fin _) : ℕ) = _
      rw [arr, dif_pos (by omega)]
      show (Wc D i).rank - 1 - (c ℓ : ℕ) = _
      omega⟩)
  have hBV : ∀ τ, (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = 1 := fun τ => by
    obtain ⟨ε, hε, h1, -⟩ := hR.models.BV i τ
    rw [h1, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with h | h
    · rw [h.1]; rfl
    · exact absurd a.2 (not_lt.2 h.2)
  have hka0 : ka ≠ 0 := fun h => by simp [h] at hka
  refine ⟨ka⁻¹, by rw [norm_inv, hka, inv_one], fun x x' hxx =>
    ⟨ka • MvPolynomial.rename lt' (MvPolynomial.map σ' (O.io x')), ?_, fun X eT g Dc heT => ?_⟩⟩
  · refine (hio'.2 _ _).trans ((hio x x' hxx).trans ?_)
    rw [fv, ← hcart, map_smul]
    refine congrArg (fun y => ka • y) ?_
    exact pureTensorO_rename hψ hθ (fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBV τ))
      (GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MW i σ)) hf _ _ _ (fun τ => arr (T.Q.Dw ((i : ℕ) + 1)).q)
      (fun τ => by rw [zAt, x0Mat, hneg]) ρ c (fun ℓ => ℓ.2.2) _
  · obtain ⟨-, cga, -, -, i3, -⟩ := hO.io
    have hhom := (isHomogeneous_of_span _ _ _ _ _ _ (i3 ▸ LinearMap.mem_range_self O.io x')).map σ'
    have hp0 := Dc.hr
    have hm : ∀ τ, relab O.c' σ' τ ∉ X.Ψ → (T.Q.Dw ((i : ℕ) + 1)).mult τ ≤ X.p0 := fun τ hτ => by
      have h : ¬ InPsi T.Q.H τ := fun h => by
        obtain ⟨s, hs⟩ := (w1 _).1 ((hrl τ).2 h)
        exact hτ (by rw [hs, ← heT s]; exact (eT s).2)
      have h2 : (T.Q.Dw ((i : ℕ) + 1)).mult τ = (T.Q.Dw ((i : ℕ) + 1)).q := if_neg h
      omega
    have hne : ∀ (s : D.what₂.Tau) (t : X.Ψ), tauE D s ≠ ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb t.1 := fun s t e =>
      (w2 _).2 ⟨eT.symm t, by rw [e, ← heT, Equiv.apply_symm_apply]⟩ ((w1 _).2 ⟨s, rfl⟩)
    have heL : ∀ ℓ, (eT (ρ ℓ), (rowIdx Dc.hr).symm (Fin.cast (rank_Wc i) (c ℓ)), ℓ.2.2) = Dc.eL ℓ := fun ℓ => by
      obtain ⟨h1, h2⟩ := letter_relab Dc hm ℓ
      replace h2 : (∃ k, (Dc.eL ℓ).2.1 = Sum.inl k ∧ relab O.c' σ' ℓ.1 = (Dc.eL ℓ).1.1 ∧ (k : ℕ) = ℓ.2.1) ∨
        (∃ k, (Dc.eL ℓ).2.1 = Sum.inr k ∧ relab O.c' σ' ℓ.1 = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (Dc.eL ℓ).1.1 ∧
          (k : ℕ) = ℓ.2.1) := h2
      have key : (eT (ρ ℓ)).1 = (Dc.eL ℓ).1.1 ∧ (c ℓ : ℕ) = rowIdx Dc.hr (Dc.eL ℓ).2.1 := by
        rcases h2 with ⟨k, e1, e2, e3⟩ | ⟨k, e1, e2, e3⟩ <;> rcases hc ℓ with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩
        · exact ⟨by rw [heT, ← g1, e2], by rw [e1, rowIdx_inl]; omega⟩
        · refine absurd ?_ (hne (eT.symm (Dc.eL ℓ).1) (eT (ρ ℓ)))
          rw [← heT, Equiv.apply_symm_apply, heT, ← g1, e2]
        · exact absurd (g1.symm.trans e2) (hne _ _)
        · exact ⟨by rw [heT]; exact hcj _ _ (g1.symm.trans e2), by rw [e1, rowIdx_inr]; omega⟩
      refine Prod.ext (Subtype.ext key.1) (Prod.ext ?_ h1.symm)
      exact (Equiv.symm_apply_eq _).2 (Fin.ext key.2)
    rw [map_smul, ← MvPolynomial.C_mul', ← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hka0, MvPolynomial.C_1, one_mul,
      toP, MvPolynomial.aeval_rename, lieFac_eq_pow _ hx, Complex.ofReal_pow, ← aeval_scale _ _ hhom]
    congr 2
    funext ℓ
    simp only [Function.comp_apply, lt', two_div_fockScale, heL]

end GlobalTheory.GalOne.IoCmp

end

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.Lift

variable {D : D7}

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ hR ⟨tie⟩ i Tp tup O hO ⟨t⟩`. Establish `hT` using `tie.laws`. Establish `hL` using `hR.lev`. Establish `hβ` using `hL.βW i`. Establish `hι` using `GlobalTheory.LevelAction.latEmb_iotaW T hT i`.

Establish `hMb : T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal` using `(hO.tuple t).half.1`. Establish `hp : T.Q.l.Mb * Mfr T.Q.l = Ideal.span {((T.Q.l.M : ℕ) : 𝓞 D.host.E)}` using `T.Q.l.prod`. Establish `hp' : (∏ PP ∈ R.Pg, PP.asIdeal) * Mfr T.Q.l = Ideal.span {((T.Q.l.M : ℕ) : 𝓞 D.host.E)}` using `by rw [← hMb]; exact hp`. Establish `hM0 : 0 < T.Q.l.M` using `lt_of_lt_of_le (by norm_num) T.Q.l.three_le`. Use `⟨fun g k hk => ⟨hk.1, isMov_of_mem_St hβ (parLev_St hk.2.1), ?_, fun h => ?_⟩, fun ε => ?_⟩` and prove the remaining obligations.

Take `⟨a, b, s, s', hb, hs, hs', hin, hout⟩` from `GlobalTheory.GeoLevel.exists_half_elements T.Q.l R.Pg (fun P => by rw [hMb]; exact mem_iff_prod_le _ P)`. Establish `hM : T.Q.l.M = D.host.g 0 * D.host.g 1` using `hT.pins.2.1.1`. Take `⟨x, hx, hroot, hval⟩` from `GlobalTheory.GeoLevel.exists_root_char (L := R.datWp i R.triv) (rank_Wc i).symm hk (hL.mu0 i) (R.C.isMu0 i).tame T.Q.l.M (fun P hP => (R.C.isMu0 i).unr P fun n hn => hP (by`. Establish `hn' : ((D.host.g n : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal` using `hn`. Rewrite using `[hM, Nat.cast_mul]`.

Use `fin_cases n`. Conclude with `Ideal.mul_mem_right _ _ hn'`. Conclude with `Ideal.mul_mem_left _ _ hn'))`. Use the proof step `(fun P => (R.chi ((i : ℕ) + 1) P)⁻¹) (hL.chi i) a b s s' hb hs hs' hin hout`. Establish `hc : T.chiW ((i : ℕ) + 1) O.s0 = R.mu0 ((i : ℕ) + 1)` using `chiTie_of_chiR T R tie.alg_eq hT.pins.2.2.1 tie.chiR i`.

Establish `h1 : O.mu k = ((T.chiW ((i : ℕ) + 1) O.s0 x : Circle) : ℂ)` using `mu_cast O.hV (hT.muVal _ (inR i) O.s0 T.toCore.good_σ₀) hroot`. Rewrite using `[h1, hc, hval]`. Conclude with `Finset.prod_mul_distrib.symm.trans (Finset.prod_eq_one fun P _ => Units.mul_inv _)`. Establish `hmv` using `(GlobalTheory.Member.latG_move D (Wc D i)).2.2.1 1 h k (GlobalTheory.LevelAction.finCong_of_mem_St hβ (parLev_St hk.2.1))`. Use `⟨hmv.1, fun mk hmk a ha => ?_⟩` and prove the remaining obligations.

Take `⟨k', hk', hf⟩` from `hO.lift.lev g`. Establish `hr` using `GlobalTheory.LevelUnique.redFn_eq_of_lift (L := R.datWp i R.triv) (rank_Wc i) hk' hk`. Take `⟨w₃, hw₃, e₃⟩` from `cong_on_half hι (fun b hb => GlobalTheory.LevelUnique.exists_cong (b := b) hβ R.Pg hp' (parLev_St hk'.2.1) (parLev_St hk.2.1) hr hb) a ha`. Take `⟨w₂, hw₂, e₂⟩` from `hf a ha`. Establish `ha' : O.lev g a ∈ Mfr T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La)` using `Submodule.smul_mono le_rfl le_top ((Submodule.map_smul'' _ _ (O.lev g)).le (Submodule.mem_map_of_mem ha))`.

Take `⟨w₁, hw₁, e₁⟩` from `hmk _ ha'`. Use `⟨w₁ + (finHom (Wc D i) h).1 *ᵥ (w₂ + w₃), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hmv.2]`. Conclude with `add_mem hw₁ ((GlobalTheory.Member.LatMove.mem_hat_iff _ h _).2 ⟨_, add_mem hw₂ hw₃, rfl⟩)`. Rewrite using `[GlobalTheory.Member.LatMove.fin_mul]`.

Conclude with `mark_calc e₁ e₂ e₃`. Take `⟨z, hz⟩` from `R.eG.surjective fun P => sgnGL D.R.r _ ε`. Use `⟨z, Subgroup.mem_center_iff.2 fun g => R.eG.injective ?_, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[R.eG.map_mul, R.eG.map_mul, hz]`. Use function extensionality and compare the values at `P`.

Conclude with `sgnGL_comm ε (R.eG g P)`. Take `⟨k, hk, hf⟩` from `hO.lift.lev z`. Establish `hr` using `redFn_sign (L := R.datWp i R.triv) (rank_Wc i) hk ε (congrFun hz)`. Take `⟨w₃, hw₃, e₃⟩` from `cong_on_half hι (fun b hb => exists_cong_sign (b := b) hβ R.Pg hp' (parLev_St hk.2.1) ε hr hb) a ha`. Take `⟨w₂, hw₂, e₂⟩` from `hf a ha`.

Conclude with `sign_div hι hM0 (add_mem hw₂ hw₃) (sign_calc e₂ e₃)`.
-/
theorem lift_laws_ofFive : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → Nonempty Tp → (∀ (g : G) (k : GA D (Wc D i)), Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → k ∈ GfC (Wc D i) ∧ GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt (Wc D i) k) (R.ΛW i) (R.ΛW i) ∧ (∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ)) * O.mu k = 1 ∧ ∀ h : GA D (Wc D i), latG (Wc D i) (h * k) = latG (Wc D i) h ∧ ∀ mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), MarkAd (rank_Wc i) T.Q.l (iotaW T i) h mk → MarkAd (rank_Wc i) T.Q.l (iotaW T i) (h * k) (mk ∘ₗ O.lev g)) ∧ ∀ ε : ℤˣ, ∃ z ∈ Subgroup.center G, ∀ a ∈ Mfr T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La), ∃ b : (T.Q.Dw ((i : ℕ) + 1)).La, O.lev z a = (ε : ℤ) • a + T.Q.l.M • b := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR ⟨tie⟩ i Tp tup O hO ⟨t⟩
  have hT := tie.laws
  have hL := hR.lev
  have hβ := hL.βW i
  have hι := GlobalTheory.LevelAction.latEmb_iotaW T hT i
  have hMb : T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal := (hO.tuple t).half.1
  have hp : T.Q.l.Mb * Mfr T.Q.l = Ideal.span {((T.Q.l.M : ℕ) : 𝓞 D.host.E)} := T.Q.l.prod
  have hp' : (∏ PP ∈ R.Pg, PP.asIdeal) * Mfr T.Q.l = Ideal.span {((T.Q.l.M : ℕ) : 𝓞 D.host.E)} := by rw [← hMb]; exact hp
  have hM0 : 0 < T.Q.l.M := lt_of_lt_of_le (by norm_num) T.Q.l.three_le
  refine ⟨fun g k hk => ⟨hk.1, isMov_of_mem_St hβ (parLev_St hk.2.1), ?_, fun h => ?_⟩, fun ε => ?_⟩
  · obtain ⟨a, b, s, s', hb, hs, hs', hin, hout⟩ := GlobalTheory.GeoLevel.exists_half_elements T.Q.l R.Pg
      (fun P => by rw [hMb]; exact mem_iff_prod_le _ P)
    have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := hT.pins.2.1.1
    obtain ⟨x, hx, hroot, hval⟩ := GlobalTheory.GeoLevel.exists_root_char (L := R.datWp i R.triv) (rank_Wc i).symm hk (hL.mu0 i)
      (R.C.isMu0 i).tame T.Q.l.M (fun P hP => (R.C.isMu0 i).unr P fun n hn => hP (by
        have hn' : ((D.host.g n : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hn
        rw [hM, Nat.cast_mul]
        fin_cases n
        · exact Ideal.mul_mem_right _ _ hn'
        · exact Ideal.mul_mem_left _ _ hn'))
      (fun P => (R.chi ((i : ℕ) + 1) P)⁻¹) (hL.chi i) a b s s' hb hs hs' hin hout
    have hc : T.chiW ((i : ℕ) + 1) O.s0 = R.mu0 ((i : ℕ) + 1) := chiTie_of_chiR T R tie.alg_eq hT.pins.2.2.1 tie.chiR i
    have h1 : O.mu k = ((T.chiW ((i : ℕ) + 1) O.s0 x : Circle) : ℂ) :=
      mu_cast O.hV (hT.muVal _ (inR i) O.s0 T.toCore.good_σ₀) hroot
    rw [h1, hc, hval]
    exact Finset.prod_mul_distrib.symm.trans (Finset.prod_eq_one fun P _ => Units.mul_inv _)
  · have hmv := (GlobalTheory.Member.latG_move D (Wc D i)).2.2.1 1 h k
      (GlobalTheory.LevelAction.finCong_of_mem_St hβ (parLev_St hk.2.1))
    refine ⟨hmv.1, fun mk hmk a ha => ?_⟩
    obtain ⟨k', hk', hf⟩ := hO.lift.lev g
    have hr := GlobalTheory.LevelUnique.redFn_eq_of_lift (L := R.datWp i R.triv) (rank_Wc i) hk' hk
    obtain ⟨w₃, hw₃, e₃⟩ := cong_on_half hι (fun b hb => GlobalTheory.LevelUnique.exists_cong (b := b) hβ R.Pg hp'
      (parLev_St hk'.2.1) (parLev_St hk.2.1) hr hb) a ha
    obtain ⟨w₂, hw₂, e₂⟩ := hf a ha
    have ha' : O.lev g a ∈ Mfr T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La) :=
      Submodule.smul_mono le_rfl le_top ((Submodule.map_smul'' _ _ (O.lev g)).le (Submodule.mem_map_of_mem ha))
    obtain ⟨w₁, hw₁, e₁⟩ := hmk _ ha'
    refine ⟨w₁ + (finHom (Wc D i) h).1 *ᵥ (w₂ + w₃), ?_, ?_⟩
    · rw [hmv.2]
      exact add_mem hw₁ ((GlobalTheory.Member.LatMove.mem_hat_iff _ h _).2 ⟨_, add_mem hw₂ hw₃, rfl⟩)
    · rw [GlobalTheory.Member.LatMove.fin_mul]
      exact mark_calc e₁ e₂ e₃
  · obtain ⟨z, hz⟩ := R.eG.surjective fun P => sgnGL D.R.r _ ε
    refine ⟨z, Subgroup.mem_center_iff.2 fun g => R.eG.injective ?_, fun a ha => ?_⟩
    · rw [R.eG.map_mul, R.eG.map_mul, hz]
      funext P
      exact sgnGL_comm ε (R.eG g P)
    · obtain ⟨k, hk, hf⟩ := hO.lift.lev z
      have hr := redFn_sign (L := R.datWp i R.triv) (rank_Wc i) hk ε (congrFun hz)
      obtain ⟨w₃, hw₃, e₃⟩ := cong_on_half hι (fun b hb => exists_cong_sign (b := b) hβ R.Pg hp'
        (parLev_St hk.2.1) ε hr hb) a ha
      obtain ⟨w₂, hw₂, e₂⟩ := hf a ha
      exact sign_div hι hM0 (add_mem hw₂ hw₃) (sign_calc e₂ e₃)

end GlobalTheory.OneMapRef.Lift

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.Equivar

open GlobalTheory.OneMapRef.Equivar

open scoped ComplexOrder in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ hC Comparison₂ i O hP σ σ' hσ μ' η' ω f₀ f₁ hW hV cc hcc`. Take `⟨hK, hμ, hη, ho, ⟨hv, -⟩, -⟩` from `hW`. Establish `hT : Nonempty (FWTie T R κ v₀)` using `⟨Comparison₂⟩`. Establish `hJ` using `Comparison₂.laws`. Establish `hj : InR D ((i : ℕ) + 1)` using `⟨by omega, by have := i.2; omega⟩`.

Establish `ht : TieIn T R κ v₀` using `⟨Comparison₂.laws, Comparison₂.alg_eq, Comparison₂.kap, Comparison₂.hv₀, Comparison₂.chiR, Comparison₂.x0⟩`. Establish `hpb : T.pb = R.C.P.pb` using `GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R hJ.toLawsM hC.lev (hP.tuple ()).half`. Take `⟨-, hgood, -, -, f8, f9, -, -, hch⟩` from `GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hC Comparison₂ i O hP σ σ' hσ hK`. Take `⟨f11, c4, -⟩` from `hch μ' η' hμ hη`. Use `replace f11 := f11 hV`.

Use `(GlobalTheory.GeoLevel.eqAt_iff hC.lev ht hpb O hP.act.1 hgood hV cc).2 fun g k hk f hf h => ?_` and prove the remaining obligations. Establish `hmuU` using `hJ.muUnit _ hj _ hgood`. Establish `hs` using `((mem_cusp _ _ _ _ _ _).1 hf).1`. Establish `hA : T.Q.l.A = 1` using `hJ.toLawsM.pins.2.1.2`. Take `⟨-, -, -, f4, -, f6, f7, -, -, -, -, -, -, f14, -⟩` from `GlobalTheory.OneMapRef.FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hC hT i Unit _ O hP`.

Take `⟨c1, -⟩` from `GlobalTheory.OneMapRef.chars_of_lift_ofFive D G Pl0 T0 A _ R F hC i`. Take `⟨l1, l2, -, l4⟩` from `(GlobalTheory.OneMapRef.Lift.lift_laws_ofFive D G Pl0 T0 A T R F κ v₀ hC hT i Unit _ O hP ⟨()⟩).1 g k hk`. Take `⟨γ, hγ, n, eT, Dc, hx, p1, p2, p3, p4, p5, p6, ⟨A₀, th, p7, p8⟩, p9⟩` from `GlobalTheory.GalOne.framed_point_at_ofFive T R F κ v₀ hC Comparison₂ i O hP σ σ' hσ hK hV h`. Take `⟨γ', hγ', n', eT', Dc', hx', q1, q2, q3, q4, q5, q6, ⟨A', th', q7, -⟩, q9⟩` from `GlobalTheory.GalOne.framed_point_at_ofFive T R F κ v₀ hC Comparison₂ i O hP σ σ' hσ hK hV (h * k)`. Use `letI : Algebra T.Q.c.F ℂ := (sOf O σ').toAlgebra`.

Take `⟨mk, m1, m2⟩` from `(GlobalTheory.OneMapRef.markAd_laws D _ _ _ _ (rank_Wc i) _ f14 _ _ p5 T.Q.l).1`. Take `⟨mk', m1', m2'⟩` from `(GlobalTheory.OneMapRef.markAd_laws D _ _ _ _ (rank_Wc i) _ f14 _ _ q5 T.Q.l).1`. Establish `hZ` using `p3 ▸ f8`. Establish `hfr` using `GlobalTheory.OneMapRef.oneg_frames D _ _ _ _ _ _ _ _ eT Dc.bas Dc.idx p1 _ hZ`. Establish `hmv` using `mvPt_spec hP.act.1.total g (ptC (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV h).1 ⟨(dictS hV h).2, hx⟩)`.

Establish `hev` using `evalAt_actL hP.act.1 (hJ.toLawsM.evalWD _ hj) frMap_trans_id g hs.1 (ptC (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV h).1 ⟨(dictS hV h).2, hx⟩)`. Take `⟨A₁, a1, a2⟩` from `GlobalTheory.Dict.FibreMove.anFib_levR_id _ _ _ _ _ _ _ _ _ Dc.bas Dc.idx Dc.e _ _ Dc.sympl hx p4 (O.lev g) _ _ hmv A₀`. Establish `ed : γ * γ'⁻¹ * (γ' * (h * k)) = γ * h * k` using `by group`. Take `⟨lam, z1, z2⟩` from `compare hA f14 p1 q1 p2 q2 (q3.trans p3.symm) p4 q4 (δ := γ * γ'⁻¹) (a' := γ' * (h * k)) (mul_mem hγ (inv_mem hγ')) (by rw [ed, (l4 _).1, p5]) q5 hZ hx hx' (by rw [ed, (hfr.2.2.2.2 k).2.2.1, (hfr.2.2.2.2 k).2.2.2.1 l1]; exact p6) q6 _ _ A₁ A' th th' (a1 th p7) q7 (mk ∘ₗ O.lev g) …`. Take `⟨u, u1, u2⟩` from `GlobalTheory.LatticeUnitRoot.exists_finUnit_isDetRoot D _ _ f7 k l1 l2`.

Establish `hone : GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt (Vc D i) 1) (R.ΛV i) (R.ΛV i)`. Establish `e : Formalism.L2.Theta.mt (Vc D i) 1 = 1` using `by rw [Formalism.L2.Theta.mt, map_one, Units.val_one]`. Introduce `u`. Rewrite using `[GlobalTheory.Ker.fmt, e, Matrix.map_one _ (map_zero _) (map_one _)]`. Simplify using the standard rewrite rules.

Establish `hi : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D` using `AddSubgroup.subset_closure ⟨1, fun v => one_mem _, 1, rfl⟩`. Establish `hvac` using `GlobalTheory.T.weil_vacuum_finite_selfDualLattice_splitting D (Vc D i) (Wc D i) R.ψ R.θ p1.2.1 (D.sp.V_sig _) (D.sp.W_sig _) _ _ _ ho ⟨_, c1⟩ c4 (fun _ => 1) (cart (R.MW i σ)) (fun τ => ⟨Matrix.mul_one _, by simp, by`. Establish `: gramAt D (Vc D i) τ = 1`. Rewrite using `[gramAt, p1.2.2.1]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.

Rewrite using `[this, Matrix.mul_one]`. Conclude with `Matrix.PosDef.one⟩)`. Use the proof step `(by rw [f9, ← p3]; exact hfr.2.2.2.1) _ _ f6 f7 _ hv 1 (one_mem _) k l1 hone l2 1 u`. Use the proof step `⟨map_one _, by simpa using hi, by simpa using hi⟩ u1 (by simp [IsDetRoot]) u2`. Establish `hmu : ((((μ' * η'⁻¹) 1)⁻¹ * μ' u : Circle) : ℂ) = muS hV k`.

Rewrite using `[map_one, inv_one, one_mul, f11.2 k u u2]`. Rewrite `hvac` using `[hmu]`. Take `⟨w, hw, hne⟩` from `exists_real_ne_zero p1 Dc.idx hx p8`. Take `⟨w', hw', z3, z4⟩` from `z2 w hw`. Establish `e1` using `hcc h γ hγ n eT Dc.bas Dc.idx Dc.e p1 p2 p6 hx A₀ th p7 w hw`.

Establish `e2` using `hcc (h * k) γ' hγ' n' eT' Dc'.bas Dc'.idx Dc'.e q1 q2 q6 hx' A' th' q7 w' hw'`. Establish `e3` using `z4 _ _ _ ho _ hv.2.theta`. Establish `e4 : ((1, γ * h * k) : GA D (Vc D i) × GA D (Wc D i)) = (1, γ * h) * (1, k)` using `by rw [Prod.mk_mul_mk, one_mul]`. Rewrite `e3` using `[ed, e4, map_mul, Module.End.mul_apply, hvac, map_smul, Pi.smul_apply, smul_eq_mul, e1, e2, z3]`. Establish `e5 : muS hV k * (cc (dictS hV h).1 * muS hV h) = cc (dictS hV (h * k)).1 * muS hV (h * k) * lam ^ (Vc D i).rank` using `mul_right_cancel₀ hne (by linear_combination e3)`.

Establish `hm : muS hV (h * k) = muS hV h * muS hV k` using `GlobalTheory.GeoLevel.castDict_mu_mul hmuU.1 hV h k`. Establish `h0 : muS hV (h * k) ≠ 0` using `norm_ne_zero_iff.1 ((hmuU.2.1 _).trans_ne one_ne_zero)`. Establish `e7 : cc (dictS hV h).1 = cc (dictS hV (h * k)).1 * lam ^ (Vc D i).rank` using `mul_right_cancel₀ h0 (by rw [hm] at e5 ⊢; linear_combination e5)`. Establish `e6` using `z1 _ _ f hs`. Rewrite `e6` using `[f4]`.

Use `show cc (dictS hV h).1 * rdU _ _ (dictS hV h).1 (dictS hV h).2 = cc (dictS hV (h * k)).1 * rdU _ _ (dictS hV (h * k)).1 (dictS hV (h * k)).2`. Rewrite using `[rdU_eq _ _ _ hx, rdU_eq _ _ _ hx', e6, e7, mul_assoc]`. Conclude with `congrArg _ (congrArg _ hev)`.
-/
theorem eqAt_of_frAtEmb_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → FWTie T R κ v₀ → ∀ (i : Fin D.R.m) (O : OM T R i), Pinned κ v₀ O → ∀ (σ : D.what₂.LL →+* ℂ) (σ' : O.c'.F →+* ℂ), σ'.comp O.jL = σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ), ConjW R i σ μ' η' ω f₀ f → ∀ hV : T.V ((i : ℕ) + 1) (sOf O σ') = Wc D i, ∀ cc, FrAtEmb O σ σ' hV ω f₀ cc → EqAt T R κ O (sOf O σ') hV cc := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC Comparison₂ i O hP σ σ' hσ μ' η' ω f₀ f₁ hW hV cc hcc
  obtain ⟨hK, hμ, hη, ho, ⟨hv, -⟩, -⟩ := hW
  have hT : Nonempty (FWTie T R κ v₀) := ⟨Comparison₂⟩
  have hJ := Comparison₂.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, by have := i.2; omega⟩
  have ht : TieIn T R κ v₀ := ⟨Comparison₂.laws, Comparison₂.alg_eq, Comparison₂.kap, Comparison₂.hv₀, Comparison₂.chiR, Comparison₂.x0⟩
  have hpb : T.pb = R.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R hJ.toLawsM hC.lev (hP.tuple ()).half
  obtain ⟨-, hgood, -, -, f8, f9, -, -, hch⟩ := GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hC Comparison₂ i O hP σ σ' hσ hK
  obtain ⟨f11, c4, -⟩ := hch μ' η' hμ hη
  replace f11 := f11 hV
  refine (GlobalTheory.GeoLevel.eqAt_iff hC.lev ht hpb O hP.act.1 hgood hV cc).2 fun g k hk f hf h => ?_
  have hmuU := hJ.muUnit _ hj _ hgood
  have hs := ((mem_cusp _ _ _ _ _ _).1 hf).1
  have hA : T.Q.l.A = 1 := hJ.toLawsM.pins.2.1.2
  obtain ⟨-, -, -, f4, -, f6, f7, -, -, -, -, -, -, f14, -⟩ :=
    GlobalTheory.OneMapRef.FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hC hT i Unit _ O hP
  obtain ⟨c1, -⟩ := GlobalTheory.OneMapRef.chars_of_lift_ofFive D G Pl0 T0 A _ R F hC i
  obtain ⟨l1, l2, -, l4⟩ := (GlobalTheory.OneMapRef.Lift.lift_laws_ofFive D G Pl0 T0 A T R F κ v₀ hC hT i Unit _ O hP ⟨()⟩).1 g k hk
  obtain ⟨γ, hγ, n, eT, Dc, hx, p1, p2, p3, p4, p5, p6, ⟨A₀, th, p7, p8⟩, p9⟩ :=
    GlobalTheory.GalOne.framed_point_at_ofFive T R F κ v₀ hC Comparison₂ i O hP σ σ' hσ hK hV h
  obtain ⟨γ', hγ', n', eT', Dc', hx', q1, q2, q3, q4, q5, q6, ⟨A', th', q7, -⟩, q9⟩ :=
    GlobalTheory.GalOne.framed_point_at_ofFive T R F κ v₀ hC Comparison₂ i O hP σ σ' hσ hK hV (h * k)
  letI : Algebra T.Q.c.F ℂ := (sOf O σ').toAlgebra
  obtain ⟨mk, m1, m2⟩ := (GlobalTheory.OneMapRef.markAd_laws D _ _ _ _ (rank_Wc i) _ f14 _ _ p5 T.Q.l).1
  obtain ⟨mk', m1', m2'⟩ := (GlobalTheory.OneMapRef.markAd_laws D _ _ _ _ (rank_Wc i) _ f14 _ _ q5 T.Q.l).1
  have hZ := p3 ▸ f8
  have hfr := GlobalTheory.OneMapRef.oneg_frames D _ _ _ _ _ _ _ _ eT Dc.bas Dc.idx p1 _ hZ
  have hmv := mvPt_spec hP.act.1.total g (ptC (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV h).1 ⟨(dictS hV h).2, hx⟩)
  have hev := evalAt_actL hP.act.1 (hJ.toLawsM.evalWD _ hj) frMap_trans_id g hs.1
    (ptC (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV h).1 ⟨(dictS hV h).2, hx⟩)
  obtain ⟨A₁, a1, a2⟩ := GlobalTheory.Dict.FibreMove.anFib_levR_id _ _ _ _ _ _ _ _ _ Dc.bas Dc.idx Dc.e _ _ Dc.sympl hx p4
    (O.lev g) _ _ hmv A₀
  have ed : γ * γ'⁻¹ * (γ' * (h * k)) = γ * h * k := by group
  obtain ⟨lam, z1, z2⟩ := compare hA f14 p1 q1 p2 q2 (q3.trans p3.symm) p4 q4 (δ := γ * γ'⁻¹) (a' := γ' * (h * k))
    (mul_mem hγ (inv_mem hγ')) (by rw [ed, (l4 _).1, p5]) q5 hZ hx hx'
    (by rw [ed, (hfr.2.2.2.2 k).2.2.1, (hfr.2.2.2.2 k).2.2.2.1 l1]; exact p6) q6 _ _ A₁ A' th th' (a1 th p7) q7
    (mk ∘ₗ O.lev g) mk' (fun a => m1 _) m1' (by rw [ed]; exact (l4 _).2 mk m2) m2'
    (a2 mk (p9 _ _ _ _ Dc.sympl p2 A₀ mk m1 m2)) (q9 _ _ _ _ Dc'.sympl q2 A' mk' m1' m2')
  obtain ⟨u, u1, u2⟩ := GlobalTheory.LatticeUnitRoot.exists_finUnit_isDetRoot D _ _ f7 k l1 l2
  have hone : GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt (Vc D i) 1) (R.ΛV i) (R.ΛV i) := by
    have e : Formalism.L2.Theta.mt (Vc D i) 1 = 1 := by rw [Formalism.L2.Theta.mt, map_one, Units.val_one]
    intro u
    rw [GlobalTheory.Ker.fmt, e, Matrix.map_one _ (map_zero _) (map_one _)]
    simp
  have hi : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D :=
    AddSubgroup.subset_closure ⟨1, fun v => one_mem _, 1, rfl⟩
  have hvac := GlobalTheory.T.weil_vacuum_finite_selfDualLattice_splitting D (Vc D i) (Wc D i) R.ψ R.θ p1.2.1 (D.sp.V_sig _) (D.sp.W_sig _) _ _ _ ho ⟨_, c1⟩ c4
    (fun _ => 1) (cart (R.MW i σ))
    (fun τ => ⟨Matrix.mul_one _, by simp, by
      have : gramAt D (Vc D i) τ = 1 := by
        rw [gramAt, p1.2.2.1]; exact Matrix.map_one _ (map_zero _) (map_one _)
      rw [this, Matrix.mul_one]; exact Matrix.PosDef.one⟩)
    (by rw [f9, ← p3]; exact hfr.2.2.2.1) _ _ f6 f7 _ hv 1 (one_mem _) k l1 hone l2 1 u
    ⟨map_one _, by simpa using hi, by simpa using hi⟩ u1 (by simp [IsDetRoot]) u2
  have hmu : ((((μ' * η'⁻¹) 1)⁻¹ * μ' u : Circle) : ℂ) = muS hV k := by
    rw [map_one, inv_one, one_mul, f11.2 k u u2]
  rw [hmu] at hvac
  obtain ⟨w, hw, hne⟩ := exists_real_ne_zero p1 Dc.idx hx p8
  obtain ⟨w', hw', z3, z4⟩ := z2 w hw
  have e1 := hcc h γ hγ n eT Dc.bas Dc.idx Dc.e p1 p2 p6 hx A₀ th p7 w hw
  have e2 := hcc (h * k) γ' hγ' n' eT' Dc'.bas Dc'.idx Dc'.e q1 q2 q6 hx' A' th' q7 w' hw'
  have e3 := z4 _ _ _ ho _ hv.2.theta
  have e4 : ((1, γ * h * k) : GA D (Vc D i) × GA D (Wc D i)) = (1, γ * h) * (1, k) := by rw [Prod.mk_mul_mk, one_mul]
  rw [ed, e4, map_mul, Module.End.mul_apply, hvac, map_smul, Pi.smul_apply, smul_eq_mul, e1, e2, z3] at e3
  have e5 : muS hV k * (cc (dictS hV h).1 * muS hV h) =
      cc (dictS hV (h * k)).1 * muS hV (h * k) * lam ^ (Vc D i).rank :=
    mul_right_cancel₀ hne (by linear_combination e3)
  have hm : muS hV (h * k) = muS hV h * muS hV k := GlobalTheory.GeoLevel.castDict_mu_mul hmuU.1 hV h k
  have h0 : muS hV (h * k) ≠ 0 := norm_ne_zero_iff.1 ((hmuU.2.1 _).trans_ne one_ne_zero)
  have e7 : cc (dictS hV h).1 = cc (dictS hV (h * k)).1 * lam ^ (Vc D i).rank :=
    mul_right_cancel₀ h0 (by rw [hm] at e5 ⊢; linear_combination e5)
  have e6 := z1 _ _ f hs
  rw [f4] at e6
  show cc (dictS hV h).1 * rdU _ _ (dictS hV h).1 (dictS hV h).2 =
    cc (dictS hV (h * k)).1 * rdU _ _ (dictS hV (h * k)).1 (dictS hV (h * k)).2
  rw [rdU_eq _ _ _ hx, rdU_eq _ _ _ hx', e6, e7, mul_assoc]
  exact congrArg _ (congrArg _ hev)

end GlobalTheory.GalOne.Equivar

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

open GlobalTheory.VecInv Formalism.IndefR.Lev

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F h i σ μ' η' ω f₀ f hc χ' hχ k hf hk`. Establish `hchi : ChiAt R i σ μ'` using `hc.2.1`. Establish `hη' : UnramEverywhere D η'` using `hc.2.2.1.2.1`. Establish `hW` using `hc.2.2.2.1`. Establish `hv` using `hc.2.2.2.2.1`.

Establish `hL` using `h.lev`. Establish `hch` using `chars_of_lift_ofFive D G Pl0 T0 A Ks R F h i`. Establish `hη` using `hch.1`. Establish `hxi` using `hch.2.1`. Establish `hQ : R.toLevCh.Q A.μ0 = ∅` using `hch.2.2.1`.

Establish `rW : (Wc D i).rank = D.R.r` using `D.sp.W_rank _ (Nat.le_add_left _ _) i.2`. Establish `hl : finE (Vc D i) k ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i) (flag1L (R.datVt i A.μ0))` using `hk`. Establish `hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i A.μ0) 1 k` using `⟨hf, hl.1, Subgroup.mem_bot.1 hl.2⟩`. Establish `hκ' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 1` using `⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact Formalism.L2.DIV.rTup_one⟩`. Establish `hmu : ∀ x, R.toLevCh.mu A.μ0 ((i : ℕ) + 1) x = R.mu0 ((i : ℕ) + 1) x` using `fun x => by show R.mu0 ((i : ℕ) + 1) x * R.xi A.μ0 x = _`.

Rewrite using `[hxi, MonoidHom.one_apply, mul_one]`. Use `(om_vec hW ⟨_, hη⟩ (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i)) (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)) (hL.βV i).choose_spec.1 (hL.βW i).choose_spec.1 hv).elim fun P h1 => h1.elim fun e h2 => h2.elim fun hee h3 …` and prove the remaining obligations. Establish `he` using `h3.2.1`. Establish `hP : ∀ PP, PP ∈ P ↔ PP ∈ R.toLevCh.Pg ∨ PP ∈ R.toLevCh.Q A.μ0` using `fun PP => by`. Rewrite using `[hQ]`.

Conclude with `h3.1 PP`. Establish `u1` using `(unrOff_mu hL A.μ0 i hP he).1`. Establish `v1 : UnrOff (e + cA D e) μ'` using `fun x a b c d => (hchi.2.2.2.1 x a).elim fun y hy => by`. Establish `e1 : D.what₂.embLL (algebraMap Ks D.what₂.LL y) = D.what₂.embLL 1`. Rewrite using `[← hy.1, ← hmu, u1 x a b c d, map_one, Circle.coe_one]`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `hy.2.trans ?_` and prove the remaining obligations. Rewrite using `[D.what₂.embLL.injective e1, map_one]`. Both sides reduce to the same expression. Establish `v2 : UnrOff (e + cA D e) η'` using `fun x a b c _ => hη' x a b c`.

Establish `sV : Stab (Vc D i) (R.βV i) k` using `⟨hf, parLev_St hκ.2.1⟩`. Establish `h4` using `h3.2.2 v1 (v1.mul v2.inv) _ (r_le_V i) (r_le_rank_Wc i) rW k 1 sV (Stab.one _ _) (fun PP hPP => blockTri_blkOf_le _ _ (parLev_g hκ.2.1 (hPP.resolve_right (Finset.notMem_empty _)))) (fun PP hPP => (congrFun hκ.2.2 ⟨PP, hPP⟩).trans (congrFun hκ'.2.2 ⟨PP, hPP⟩).symm)`. Establish `hinf : infPart D ((detAt e hee (Vc D i) k : (AE D)ˣ) : AE D) = 1`. Rewrite using `[Vac.detAt_val, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, GlobalTheory.PlaceVec.idemSum_infPart he, zero_mul, zero_add, sub_zero, RingHom.map_one]`. Establish `n1 : η' (detAt e hee (Vc D i) k) = 1` using `hη' _ hinf (Vac.finPart_detAt sV e hee) (by`.

Rewrite using `[← MonoidHom.map_inv]`. Conclude with `Vac.finPart_detAt sV.inv e hee)`. Establish `m0 : ((R.mu0 ((i : ℕ) + 1) (detAt e hee (Vc D i) k) : Circle) : ℂ) = (((levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ ⟨FWT.fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)` using `(congrArg (fun z : Circle => (z : ℂ)) (hmu _).symm).trans ((mu_detAt_eq_levChi hL i A.μ0 hQ hee hP he hκ).trans (congrArg Units.val (levFn_flag1 (V := Vc D i) (β := R.βV i) (L := R.datVt i A.μ0) (finE (Vc D i) k)).symm))`. Establish `m1 : ((μ' (detAt e hee (Vc D i) k) : Circle) : ℂ) = ((χ' ⟨FWT.fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)` using `(hchi.2.2.2.1 _ hinf).elim fun y hy => (hχ ⟨FWT.fin (Vc D i) k, hk⟩).elim fun y' hy' => hy.2.trans ((congrArg σ (D.what₂.embLL.injective (hy.1.symm.trans (m0.trans hy'.1.symm)))).trans hy'.2)`. Conclude with `smul_of_splitFac h4 (MonoidHom.map_one _) n1 m1`.
-/
theorem omega_level_conjVec_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), ∀ (μ' η' : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ), ConjW R i σ μ' η' ω f₀ f → ∀ χ' : levJ R i A.μ0 →* ℂˣ, (∀ k, ConjVal σ (((levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k : ℂˣ) : ℂ) ((χ' k : ℂˣ) : ℂ)) → ∀ k ∈ GfC (Vc D i), ∀ hk : FWT.fin (Vc D i) k ∈ levJ R i A.μ0, ω (k, 1) f = ((χ' ⟨FWT.fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • f := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i σ μ' η' ω f₀ f hc χ' hχ k hf hk
  have hchi : ChiAt R i σ μ' := hc.2.1
  have hη' : UnramEverywhere D η' := hc.2.2.1.2.1
  have hW := hc.2.2.2.1
  have hv := hc.2.2.2.2.1
  have hL := h.lev
  have hch := chars_of_lift_ofFive D G Pl0 T0 A Ks R F h i
  have hη := hch.1
  have hxi := hch.2.1
  have hQ : R.toLevCh.Q A.μ0 = ∅ := hch.2.2.1
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hl : finE (Vc D i) k ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i) (flag1L (R.datVt i A.μ0)) := hk
  have hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i A.μ0) 1 k := ⟨hf, hl.1, Subgroup.mem_bot.1 hl.2⟩
  have hκ' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 1 :=
    ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact Formalism.L2.DIV.rTup_one⟩
  have hmu : ∀ x, R.toLevCh.mu A.μ0 ((i : ℕ) + 1) x = R.mu0 ((i : ℕ) + 1) x := fun x => by
    show R.mu0 ((i : ℕ) + 1) x * R.xi A.μ0 x = _
    rw [hxi, MonoidHom.one_apply, mul_one]
  refine (om_vec hW ⟨_, hη⟩ (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i))
    (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)) (hL.βV i).choose_spec.1 (hL.βW i).choose_spec.1 hv).elim fun P h1 =>
      h1.elim fun e h2 => h2.elim fun hee h3 => ?_
  have he := h3.2.1
  have hP : ∀ PP, PP ∈ P ↔ PP ∈ R.toLevCh.Pg ∨ PP ∈ R.toLevCh.Q A.μ0 := fun PP => by
    rw [hQ]; exact h3.1 PP
  have u1 := (unrOff_mu hL A.μ0 i hP he).1
  have v1 : UnrOff (e + cA D e) μ' := fun x a b c d => (hchi.2.2.2.1 x a).elim fun y hy => by
    have e1 : D.what₂.embLL (algebraMap Ks D.what₂.LL y) = D.what₂.embLL 1 := by
      rw [← hy.1, ← hmu, u1 x a b c d, map_one, Circle.coe_one]
    apply Subtype.ext
    refine hy.2.trans ?_
    rw [D.what₂.embLL.injective e1, map_one]
    rfl
  have v2 : UnrOff (e + cA D e) η' := fun x a b c _ => hη' x a b c
  have sV : Stab (Vc D i) (R.βV i) k := ⟨hf, parLev_St hκ.2.1⟩
  have h4 := h3.2.2 v1 (v1.mul v2.inv) _ (r_le_V i) (r_le_rank_Wc i) rW k 1 sV (Stab.one _ _)
    (fun PP hPP => blockTri_blkOf_le _ _ (parLev_g hκ.2.1 (hPP.resolve_right (Finset.notMem_empty _))))
    (fun PP hPP => (congrFun hκ.2.2 ⟨PP, hPP⟩).trans (congrFun hκ'.2.2 ⟨PP, hPP⟩).symm)
  have hinf : infPart D ((detAt e hee (Vc D i) k : (AE D)ˣ) : AE D) = 1 := by
    rw [Vac.detAt_val, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, GlobalTheory.PlaceVec.idemSum_infPart he, zero_mul, zero_add,
      sub_zero, RingHom.map_one]
  have n1 : η' (detAt e hee (Vc D i) k) = 1 := hη' _ hinf (Vac.finPart_detAt sV e hee) (by
    rw [← MonoidHom.map_inv]
    exact Vac.finPart_detAt sV.inv e hee)
  have m0 : ((R.mu0 ((i : ℕ) + 1) (detAt e hee (Vc D i) k) : Circle) : ℂ) =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ ⟨FWT.fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ) :=
    (congrArg (fun z : Circle => (z : ℂ)) (hmu _).symm).trans
      ((mu_detAt_eq_levChi hL i A.μ0 hQ hee hP he hκ).trans (congrArg Units.val
        (levFn_flag1 (V := Vc D i) (β := R.βV i) (L := R.datVt i A.μ0) (finE (Vc D i) k)).symm))
  have m1 : ((μ' (detAt e hee (Vc D i) k) : Circle) : ℂ) = ((χ' ⟨FWT.fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ) :=
    (hchi.2.2.2.1 _ hinf).elim fun y hy => (hχ ⟨FWT.fin (Vc D i) k, hk⟩).elim fun y' hy' =>
      hy.2.trans ((congrArg σ (D.what₂.embLL.injective (hy.1.symm.trans (m0.trans hy'.1.symm)))).trans hy'.2)
  exact smul_of_splitFac h4 (MonoidHom.map_one _) n1 m1

end GlobalTheory.GalOne

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hR i σ μ' η' ω f₀ f hC c₀ c c₁ H j hF B io thP hL K' _ σ' Cl _ h bad J' Lh gam vol hrep y u g`. Use `hF.model.elim fun χ' hχ => ?_` and prove the remaining obligations. Establish `hχ1` using `hχ.1`. Establish `hHis` using `hχ.2`. Establish `hle` using `hrep.2.2.1`.

Establish `hN` using `hrep.2.2.2.1`. Establish `hvol` using `hrep.2.2.2.2.1`. Establish `hy` using `hrep.2.2.2.2.2.1`. Establish `hk` using `hrep.2.2.2.2.2.2`. Establish `hx : H.e y ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (levJ R i A.μ0) χ'` using `hHis.2.1.le (LinearMap.mem_range_self _ y)`.

Establish `hfin : ∀ k ∈ GfC (Vc D i), ∀ hk : fin (Vc D i) k ∈ levJ R i A.μ0, ∀ P, ω (k, 1) (ptAt R i σ B f P) = ((χ' ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • ptAt R i σ B f P` using `fun k hk hk' => GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ ω hR.models.inf hL.1 _ _ _ _ _ hL.2.1.theta k hk 1 (one_mem _) _ (GlobalTheory.GalOne.omega_level_conjVec_ofFive R F hR i σ μ' η' ω f₀ f hC χ' hχ1 k hk hk')`. Establish `key` using `integral_theta_chi hL.1 (D.sp.V_sig _) (hR.models.vpos i) c hF.coef (R.βV i) (R.datVt i A.μ0) (fun _ => Iff.rfl) χ' hx (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) B f ∘ₗ io u) (fun w => hL.2.1.theta _) (fun a ha w => hL.2.2.1.1 a ha _ w) (fun k …`. Establish `h2` using `hL.2.2.2.eq ((c.ext ∘ₗ H.e).rangeRestrict y) u g`. Use `h2.trans (Eq.trans ?_ (key.trans (Finset.sum_congr rfl fun k _ => ?_)))` and prove the remaining obligations. Both sides reduce to the same expression.

Establish `h3 : σ' (vol * ((gam k : K'))⁻¹) = ((J'.relIndex (levJ R i A.μ0) : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) J' (fin (Vc D i) (h k))) : ℕ) : ℂ)⁻¹`. Rewrite using `[map_mul σ', hvol, map_inv₀ σ', map_inv₀ σ', map_natCast σ', map_natCast σ', (hk k).2.2]`. Rewrite using `[h3]`. Both sides reduce to the same expression.
-/
theorem theta_eq_classSum_of_conjugate : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), ∀ (μ' η' : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ), ConjW R i σ μ' η' ω f₀ f → ∀ (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ c₀ c c₁ H j → ∀ (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))), LiftData R i σ μ' η' c H ω f₀ f B io thP → ∀ (K' : Type) [Field K'] (σ' : K' →+* ℂ) (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)) (bad : ℕ) (J' : Subgroup (Bridge.Gf (Vc D i))) (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K'), RepsR R i A.μ0 h bad J' Lh gam vol → ∀ (y : H.H) (u : LowT (R.MW i σ)) (g : GA D (Wc D i)), thP ((c.ext ∘ₗ H.e).rangeRestrict y) u g = ∑ k, σ' (vol * ((gam k : K'))⁻¹) * thetaKO ω (h k) g (ptAt R i σ B f (io u (H.e y (FWT.fin (Vc D i) (h k))))) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i σ μ' η' ω f₀ f hC c₀ c c₁ H j hF B io thP hL K' _ σ' Cl _ h bad J' Lh gam vol
    hrep y u g
  refine hF.model.elim fun χ' hχ => ?_
  have hχ1 := hχ.1
  have hHis := hχ.2
  have hle := hrep.2.2.1
  have hN := hrep.2.2.2.1
  have hvol := hrep.2.2.2.2.1
  have hy := hrep.2.2.2.2.2.1
  have hk := hrep.2.2.2.2.2.2
  have hx : H.e y ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (levJ R i A.μ0) χ' :=
    hHis.2.1.le (LinearMap.mem_range_self _ y)
  have hfin : ∀ k ∈ GfC (Vc D i), ∀ hk : fin (Vc D i) k ∈ levJ R i A.μ0, ∀ P, ω (k, 1) (ptAt R i σ B f P) =
      ((χ' ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • ptAt R i σ B f P := fun k hk hk' =>
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ ω hR.models.inf hL.1 _ _ _ _ _
      hL.2.1.theta k hk 1 (one_mem _) _ (GlobalTheory.GalOne.omega_level_conjVec_ofFive R F hR i σ μ' η' ω f₀ f hC χ' hχ1 k hk hk')
  have key := integral_theta_chi hL.1 (D.sp.V_sig _) (hR.models.vpos i) c hF.coef (R.βV i) (R.datVt i A.μ0)
    (fun _ => Iff.rfl) χ' hx
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) B f ∘ₗ io u)
    (fun w => hL.2.1.theta _) (fun a ha w => hL.2.2.1.1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _)
    (hR.models.νV i A.μ0) J' Cl h hle hN hy (fun k => (hk k).1.1) g
  have h2 := hL.2.2.2.eq ((c.ext ∘ₗ H.e).rangeRestrict y) u g
  refine h2.trans (Eq.trans ?_ (key.trans (Finset.sum_congr rfl fun k _ => ?_)))
  · rfl
  have h3 : σ' (vol * ((gam k : K'))⁻¹) = ((J'.relIndex (levJ R i A.μ0) : ℕ) : ℂ)⁻¹ *
      ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) J' (fin (Vc D i) (h k))) : ℕ) : ℂ)⁻¹ := by
    rw [map_mul σ', hvol, map_inv₀ σ', map_inv₀ σ', map_natCast σ', map_natCast σ', (hk k).2.2]
  rw [h3]
  rfl

end GlobalTheory.GalOne

end

section

noncomputable section

namespace GlobalTheory.AdTh.CoefExt

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

variable {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (φ : K →+* K')
  {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W]

variable {φ lam} {c₀ : VV K lam →ₛₗ[σ] W} {c' : VV K' lam →ₛₗ[σ'] W}

end GlobalTheory.AdTh.CoefExt

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ i Tp tup O hP`. Take `⟨gramR, c0R, c0L, hT, hc⟩` from `hP.lift.c0`. Establish `hσ` using `hP.lift.field`. Establish `hE : ∀ v, O.c0' (CoefExt.up O.jL (lamV D i) v) = c0L i v`. Introduce `v`.

Take `⟨w, hw, h⟩` from `hc v`. Rewrite using `[show CoefExt.up O.jL (lamV D i) v = w from Subtype.ext hw.symm]`. Conclude with `h`. Take `⟨h1, h2, h3⟩` from `hT.mapL i`. Use `⟨?_, ?_, CoefExt.span_top (W := (R.cV i).W) hE h3, fun m b hb => CoefExt.linearIndependent (W := (R.cV i).W) hE h2 b hb⟩` and prove the remaining obligations.

Establish `hn` using `GlobalTheory.StdFrame.neg_eq_false_of_vStd D i hP.lift.std`. Establish `hg : (D.sp.V ((i : ℕ) + 1)).gram = 1` using `hP.lift.std.1`. Set `v : VsV D i D.what₂.LL` to `⟨Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal D.what₂.LL _ (lamV D i τ), GlobalTheory.Proof.TensorMapDescent.ten_mem _ _ fun τ => Formalism.GradedWeylDivisibility.hwMem _ _ _ le_rfl _ (Formalism.L2.DIV.natW_antitone _)⟩`. Establish `hv : CoefExt.up O.jL (lamV D i) v = O.hw`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `hw` using `hP.io.1`. Unfold `hwOK at hw`. Use `Eq.trans ?_ hw.symm` and prove the remaining obligations. Use `show MvPolynomial.map O.jL (Formalism.L2.DIV.ten _) = _`. Rewrite using `[GlobalTheory.Proof.TensorMapDescent.map_ten]`.

Use `congr 1`. Use function extensionality and compare the values at `τ`. Conclude with `Formalism.L2.DIV.map_extremal _ _ _`. Establish `hG : (if D.sp.Vneg ((i : ℕ) + 1) then -(D.sp.V ((i : ℕ) + 1)).gram else (D.sp.V ((i : ℕ) + 1)).gram) = 1`. Rewrite using `[hn, hg]`.

Both sides reduce to the same expression. Establish `hi` using `inner_of_coefTie (hT.coefL i A.μ0) v v`. Rewrite `hi` using `[hG]`. Use `replace hi := hi.trans ((congrArg D.what₂.embLL (CoefExt.pairVr_extremal (labLL D) v rfl)).trans (map_one _))`. Rewrite using `[← hv, hE]`.

Establish `hi' : inner ℂ (c0L i v : (R.cV i).W) (c0L i v : (R.cV i).W) = 1` using `hi`. Rewrite `hi'` using `[inner_self_eq_norm_sq_to_K]`. Establish `h4 : ‖(c0L i v : (R.cV i).W)‖ ^ 2 = 1`. Establish `h5` using `congrArg norm hi'`. Simplify using `using h5`.

Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4`. Introduce `γ γE hγ v`. Establish `hu : IsUnit (γE.val).det` using `(Matrix.isUnit_iff_isUnit_det γE.val).1 γE.isUnit`. Establish `hγE : Matrix.nonsingInvUnit γE.val hu = γE` using `Units.ext rfl`. Establish `hemb : (fun τ => embF O.c' (tauE D τ)) = fun τ => O.jL.comp (labLL D τ)`.

Use function extensionality and compare the values at `fun τ => (embV_eq_embF O.c' O.jL hσ τ).symm`. Rewrite using `[rhoM, dif_pos hu, hγE, hemb]`. Conclude with `CoefExt.equivariant (W := (R.cV i).W) hE ((R.cV i).ρ γ) (Formalism.L2.DIV.rhoVr (labLL D) (lamV D i) γE) _ (CoefExt.up_rhoVr O.jL (lamV D i) (labLL D) γE) (h1 γ γE hγ) v`.
-/
theorem coefMap_norm_equivariant_basis_ofFive' : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ‖O.c0' O.hw‖ = 1 ∧ (∀ (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E), Bridge.IsRatMat (Vc D i) γ γE → ∀ v, O.c0' (rhoM O.c' (fun τ => embF O.c' (tauE D τ)) (lamV D i) (γE : Matrix _ _ D.host.E) v) = (R.cV i).ρ γ (O.c0' v)) ∧ Submodule.span ℂ (Set.range O.c0') = ⊤ ∧ ∀ (m : ℕ) (b : Fin m → VsV D i O.c'.F), LinearIndependent O.c'.F b → LinearIndependent ℂ (fun j => O.c0' (b j)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ i Tp tup O hP
  obtain ⟨gramR, c0R, c0L, hT, hc⟩ := hP.lift.c0
  have hσ := hP.lift.field
  have hE : ∀ v, O.c0' (CoefExt.up O.jL (lamV D i) v) = c0L i v := by
    intro v
    obtain ⟨w, hw, h⟩ := hc v
    rw [show CoefExt.up O.jL (lamV D i) v = w from Subtype.ext hw.symm]
    exact h
  obtain ⟨h1, h2, h3⟩ := hT.mapL i
  refine ⟨?_, ?_, CoefExt.span_top (W := (R.cV i).W) hE h3,
    fun m b hb => CoefExt.linearIndependent (W := (R.cV i).W) hE h2 b hb⟩
  · have hn := GlobalTheory.StdFrame.neg_eq_false_of_vStd D i hP.lift.std
    have hg : (D.sp.V ((i : ℕ) + 1)).gram = 1 := hP.lift.std.1
    let v : VsV D i D.what₂.LL := ⟨Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal D.what₂.LL _ (lamV D i τ),
      GlobalTheory.Proof.TensorMapDescent.ten_mem _ _ fun τ => Formalism.GradedWeylDivisibility.hwMem _ _ _ le_rfl _ (Formalism.L2.DIV.natW_antitone _)⟩
    have hv : CoefExt.up O.jL (lamV D i) v = O.hw := by
      apply Subtype.ext
      have hw := hP.io.1
      unfold hwOK at hw
      refine Eq.trans ?_ hw.symm
      show MvPolynomial.map O.jL (Formalism.L2.DIV.ten _) = _
      rw [GlobalTheory.Proof.TensorMapDescent.map_ten]
      congr 1
      funext τ
      exact Formalism.L2.DIV.map_extremal _ _ _
    have hG : (if D.sp.Vneg ((i : ℕ) + 1) then -(D.sp.V ((i : ℕ) + 1)).gram else (D.sp.V ((i : ℕ) + 1)).gram) = 1 := by
      rw [hn, hg]; rfl
    have hi := inner_of_coefTie (hT.coefL i A.μ0) v v
    rw [hG] at hi
    replace hi := hi.trans ((congrArg D.what₂.embLL (CoefExt.pairVr_extremal (labLL D) v rfl)).trans (map_one _))
    rw [← hv, hE]
    have hi' : inner ℂ (c0L i v : (R.cV i).W) (c0L i v : (R.cV i).W) = 1 := hi
    rw [inner_self_eq_norm_sq_to_K] at hi'
    have h4 : ‖(c0L i v : (R.cV i).W)‖ ^ 2 = 1 := by
      have h5 := congrArg norm hi'
      simpa using h5
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  · intro γ γE hγ v
    have hu : IsUnit (γE.val).det := (Matrix.isUnit_iff_isUnit_det γE.val).1 γE.isUnit
    have hγE : Matrix.nonsingInvUnit γE.val hu = γE := Units.ext rfl
    have hemb : (fun τ => embF O.c' (tauE D τ)) = fun τ => O.jL.comp (labLL D τ) :=
      funext fun τ => (embV_eq_embF O.c' O.jL hσ τ).symm
    rw [rhoM, dif_pos hu, hγE, hemb]
    exact CoefExt.equivariant (W := (R.cV i).W) hE ((R.cV i).ρ γ) (Formalism.L2.DIV.rhoVr (labLL D) (lamV D i) γE) _
      (CoefExt.up_rhoVr O.jL (lamV D i) (labLL D) γE) (h1 γ γE hγ) v

end GlobalTheory.AdTh

end

end

section

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DatumFourier

section Fourier

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.AdTh GlobalTheory.LevelPairing
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} (l : Geo.Tor.Level H)

end Fourier

section General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
  IsDedekindDomain NumberField Matrix GlobalTheory.LatVac GlobalTheory.AdelicLatMove GlobalTheory.PlaceVec
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

end General

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hI`. Take `⟨ε, hε⟩` from `hI`. Use `⟨ε, fun t l φ hφ hP e he => ?_⟩` and prove the remaining obligations. Take `⟨hvac, e₁, he₁, hθ⟩` from `hR.thP.vP i t`. Take `⟨e₂, he₂, hφ⟩` from `hφ`.

Take `rfl` from `idemSum_unique (Vc D i) he₁ he`. Take `rfl` from `idemSum_unique (Vc D i) he₂ he`. Establish `hβV` using `hR.lev.βV i`. Establish `hβW` using `hR.lev.βW i`. Establish `hS` using `GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβV`.

Establish `hT` using `GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβW`. Establish `hstd : R.ΛV i = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)`. Rewrite using `[GlobalTheory.PrincInLevel.eq_latC hβV, ← GlobalTheory.SplitReps.hLat_one, hV.2]`. Establish `hlat` using `mem_latRat_iff hV.1 hstd hβW`. Establish `hM : l.M ≠ 0` using `by have := l.three_le; omega`.

Establish `hM' : (l.M : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hM`. Establish `hsurj : ∀ M ∈ GlobalTheory.LatVac.latRat (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)), ∃ x : Fin (Vc D i).rank → Dw.La, M = Matrix.of fun a b => ι (x b) a`. Introduce `M hM`. Use `choose x hx using fun b => hι.2.ge ((hlat M).1 hM b)`. Conclude with `⟨x, Matrix.ext fun a b => (congrFun (hx b) a).symm⟩`.

Establish `hint : ∀ u ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True), IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u))` using `fun u hu => int_of_mem_latO (fun M hM => by`. Take `⟨x, rfl⟩` from `hsurj M hM`. Conclude with `(hφ x).1) hu`. Establish `: Finite (LevQ Dw l)` using `GlobalTheory.LevelPairing.finite_LevQ`. Use `Fintype.ofFinite (Fin (Vc D i).rank → LevQ Dw l)` as an intermediate fact.

Rewrite using `[finsum_eq_sum_of_fintype, Finset.smul_sum]`. Simplify using `only [smul_smul]`. Use `thetaAt_eq_sum _ _ hθ (fun q a b => ?_) fun w => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.LatVac.cA_cA, Matrix.of_apply, ← mul_assoc, GlobalTheory.PlaceVec.idemSum_mul_self he]`. Distinguish the cases in `hw : w ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True) ∧ IsHalf (cA D e) w`.

Use `swap`. Rewrite using `[halfInd, if_neg hw, zero_mul, if_neg]`. Introduce and unpack `⟨h1, h2⟩`. Establish `hN : ∀ PP ∈ R.Pg ∪ R.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal` using `fun PP hPP h => (hP PP (Finset.mem_union.1 hPP)).2 (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)`. Conclude with `hw ⟨mem_latO_of_int hS hT hβV.choose_spec.1 hβW.choose_spec.1 he (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot) (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) hN h1 h2, h1⟩`.

Establish `hw' : cA D e • w = w` using `Matrix.ext hw.2`. Take `⟨M, hM0, u, hu, hwM⟩` from `approx_mod (Nat.pos_of_ne_zero hM) hw.1`. Take `⟨x, rfl⟩` from `hsurj M hM0`. Establish `hfr : frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w = uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b)) + l.M • frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u)`. Rewrite using `[← hw', hwM, smul_add, GlobalTheory.PlaceVec.frMapAdj_add, frMapAdj_half, smul_comm]`.

Use `congr 1`. Conclude with `one_smul _ _`. Conclude with `(AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add _ _ (R.βV i) (R.βW i))).map_nsmul _ _`. Establish `hred : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) = redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b)))` using `fun PP hPP => by`. Rewrite using `[hfr]`.

Establish `: Ideal.span {(l.M : 𝓞 D.host.E)} ≤ l.Mb` using `l.prod ▸ Ideal.mul_le_left`. Conclude with `GlobalTheory.PlaceVec.redM_add_nsmul PP ((hP PP hPP).1 (this (Ideal.subset_span rfl))) (hφ x).1 (hint u hu)`. Rewrite using `[halfInd, if_pos hw, one_mul, if_pos ⟨hw.2, hw' ▸ hint w hw.1⟩, GlobalTheory.PlaceVec.omegaK_congr _ fun PP h => hred PP (Or.inl h), GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ fun PP h => hred PP (Or.inr h), ← (hφ x).2, RingHom.id_apply, ← inversion l φ x]`. Use `Finset.sum_congr rfl fun q _ => congrArg _ ?_` and prove the remaining obligations. Establish `hY : (Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E)) = Matrix.of fun a b => (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) * ι (cSep l • levRep (q b)) a` using `Matrix.ext fun a b => by simp only [Matrix.of_apply]; ring`.

Use `Eq.trans ?_ (char_eq (Y := Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E)) hvac.1 hS hT (GlobalTheory.PlaceVec.idemSum_infPart he) hw.2 hu hwM ((hlat _).2 fun b => ?_)).symm` and prove the remaining obligations. Rewrite using `[hY, hRat_std hV.1 _ _ _ (by rw [star_div₀, star_intCast, star_natCast]), ← Complex.exp_int_mul]`. Use `congr 1`. Establish `h1 : ∀ c : ℚ, ∀ z : D.host.E, Algebra.trace ℚ D.host.E (D.host.xi0 * ((c : D.host.E) * z)) = c * Algebra.trace ℚ D.host.E (D.host.xi0 * z)` using `fun c z => by`. Rewrite using `[mul_left_comm, ← Rat.smul_def, map_smul, smul_eq_mul]`.

Establish `h2 : ∀ y z, Dw.EF y z = -Dw.EF z y` using `fun y z => (LinearMap.IsAlt.neg Dw.alt z y).symm`. Establish `h3 : ((pairL (l` using `l) x (fun b => levRep (q b)) : ℤ) : ℚ) = -(((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 * ∑ b, (Wc D i).hT ((Wc D i).frame.equivFun.symm (ι (cSep l • levRep (q b)))) ((Wc D i).frame.equivFun.symm (ι (x b))))) := by`. Rewrite using `[pairL, Int.cast_sum, Finset.mul_sum, map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_congr rfl fun b _ => by rw [h2, Int.cast_neg, hε]`. Establish `h4` using `congrArg (fun z : ℚ => (z : ℂ)) h3`.

Rewrite using `[show (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) = ((((ε : ℤ) : ℚ) / (l.M : ℚ) : ℚ) : D.host.E) by push_cast; rfl, h1]`. Move the coercions through the operations in `at h4 ⊢`. Rewrite using `[h4]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `hι.2.le (LinearMap.mem_range_self ι ((ε : ℤ) • cSep l • levRep (q b)))`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `a`. Rewrite using `[map_zsmul, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, mul_div_cancel₀ _ hM', Pi.smul_apply, zsmul_eq_mul]`.
-/
theorem thetaVector_eq_sum_heisenberg_of_core_five' : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → R.vP i t = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (Matrix.of fun a b => e * incA D (((δ : ℤ) : D.host.E) * ι (cSep l₂ • levRep (q b)) a / (l₂.M : D.host.E))) (R.vacP i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hI
  obtain ⟨ε, hε⟩ := hI
  refine ⟨ε, fun t l φ hφ hP e he => ?_⟩
  obtain ⟨hvac, e₁, he₁, hθ⟩ := hR.thP.vP i t
  obtain ⟨e₂, he₂, hφ⟩ := hφ
  obtain rfl := idemSum_unique (Vc D i) he₁ he
  obtain rfl := idemSum_unique (Vc D i) he₂ he
  have hβV := hR.lev.βV i
  have hβW := hR.lev.βW i
  have hS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβV
  have hT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβW
  have hstd : R.ΛV i = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβV, ← GlobalTheory.SplitReps.hLat_one, hV.2]
  have hlat := mem_latRat_iff hV.1 hstd hβW
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hM' : (l.M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hsurj : ∀ M ∈ GlobalTheory.LatVac.latRat (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)), ∃ x : Fin (Vc D i).rank → Dw.La, M = Matrix.of fun a b => ι (x b) a := by
    intro M hM
    choose x hx using fun b => hι.2.ge ((hlat M).1 hM b)
    exact ⟨x, Matrix.ext fun a b => (congrFun (hx b) a).symm⟩
  have hint : ∀ u ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True),
      IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u)) := fun u hu =>
    int_of_mem_latO (fun M hM => by
      obtain ⟨x, rfl⟩ := hsurj M hM
      exact (hφ x).1) hu
  have : Finite (LevQ Dw l) := GlobalTheory.LevelPairing.finite_LevQ
  have := Fintype.ofFinite (Fin (Vc D i).rank → LevQ Dw l)
  rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
  simp only [smul_smul]
  refine thetaAt_eq_sum _ _ hθ (fun q a b => ?_) fun w => ?_
  · rw [GlobalTheory.LatVac.cA_cA, Matrix.of_apply, ← mul_assoc, GlobalTheory.PlaceVec.idemSum_mul_self he]
  by_cases hw : w ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True) ∧ IsHalf (cA D e) w
  swap
  · rw [halfInd, if_neg hw, zero_mul, if_neg]
    rintro ⟨h1, h2⟩
    have hN : ∀ PP ∈ R.Pg ∪ R.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP h =>
      (hP PP (Finset.mem_union.1 hPP)).2 (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
    exact hw ⟨mem_latO_of_int hS hT hβV.choose_spec.1 hβW.choose_spec.1 he (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) hN h1 h2, h1⟩
  have hw' : cA D e • w = w := Matrix.ext hw.2
  obtain ⟨M, hM0, u, hu, hwM⟩ := approx_mod (Nat.pos_of_ne_zero hM) hw.1
  obtain ⟨x, rfl⟩ := hsurj M hM0
  have hfr : frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w =
      uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b)) +
        l.M • frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u) := by
    rw [← hw', hwM, smul_add, GlobalTheory.PlaceVec.frMapAdj_add, frMapAdj_half, smul_comm]
    congr 1
    · exact one_smul _ _
    · exact (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add _ _ (R.βV i) (R.βW i))).map_nsmul _ _
  have hred : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) =
      redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b))) := fun PP hPP => by
    rw [hfr]
    have : Ideal.span {(l.M : 𝓞 D.host.E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact GlobalTheory.PlaceVec.redM_add_nsmul PP ((hP PP hPP).1 (this (Ideal.subset_span rfl))) (hφ x).1 (hint u hu)
  rw [halfInd, if_pos hw, one_mul, if_pos ⟨hw.2, hw' ▸ hint w hw.1⟩,
    GlobalTheory.PlaceVec.omegaK_congr _ fun PP h => hred PP (Or.inl h),
    GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ fun PP h => hred PP (Or.inr h), ← (hφ x).2, RingHom.id_apply, ← inversion l φ x]
  refine Finset.sum_congr rfl fun q _ => congrArg _ ?_
  have hY : (Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E)) =
      Matrix.of fun a b => (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) * ι (cSep l • levRep (q b)) a :=
    Matrix.ext fun a b => by simp only [Matrix.of_apply]; ring
  refine Eq.trans ?_ (char_eq (Y := Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E))
    hvac.1 hS hT (GlobalTheory.PlaceVec.idemSum_infPart he) hw.2 hu hwM ((hlat _).2 fun b => ?_)).symm
  · rw [hY, hRat_std hV.1 _ _ _ (by rw [star_div₀, star_intCast, star_natCast]), ← Complex.exp_int_mul]
    congr 1
    have h1 : ∀ c : ℚ, ∀ z : D.host.E, Algebra.trace ℚ D.host.E (D.host.xi0 * ((c : D.host.E) * z)) =
        c * Algebra.trace ℚ D.host.E (D.host.xi0 * z) := fun c z => by
      rw [mul_left_comm, ← Rat.smul_def, map_smul, smul_eq_mul]
    have h2 : ∀ y z, Dw.EF y z = -Dw.EF z y := fun y z => (LinearMap.IsAlt.neg Dw.alt z y).symm
    have h3 : ((pairL (l := l) x (fun b => levRep (q b)) : ℤ) : ℚ) = -(((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 *
        ∑ b, (Wc D i).hT ((Wc D i).frame.equivFun.symm (ι (cSep l • levRep (q b)))) ((Wc D i).frame.equivFun.symm (ι (x b))))) := by
      rw [pairL, Int.cast_sum, Finset.mul_sum, map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => by rw [h2, Int.cast_neg, hε]
    have h4 := congrArg (fun z : ℚ => (z : ℂ)) h3
    rw [show (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) = ((((ε : ℤ) : ℚ) / (l.M : ℚ) : ℚ) : D.host.E) by push_cast; rfl, h1]
    push_cast at h4 ⊢
    rw [h4]
    ring
  · have h1 := hι.2.le (LinearMap.mem_range_self ι ((ε : ℤ) • cSep l • levRep (q b)))
    convert h1 using 1
    funext a
    rw [map_zsmul, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, mul_div_cancel₀ _ hM', Pi.smul_apply, zsmul_eq_mul]

end GlobalTheory.DatumFourier

end

end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.RecPair

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F h i t hV`. Establish `hL` using `h.lev`. Establish `hW` using `h.thP.ωP i t`. Establish `hr : Odd D.R.r`. Use `D.R.m_add_three_le_k` as an intermediate fact.

Take `⟨a, ha⟩` from `D.R.k_even`. Take `⟨b, hb⟩` from `D.R.m_even`. Conclude with `⟨a + b - 1, by simp only [Ranks.r]; omega⟩`. Establish `rV : (Vc D i).rank = D.R.r + D.R.t` using `D.sp.V_rank _ (Nat.le_add_left _ _) i.2`. Establish `rW : (Wc D i).rank = D.R.r` using `D.sp.W_rank _ (Nat.le_add_left _ _) i.2`.

Establish `hev : Even (Vc D i).rank` using `rV ▸ hr.add_odd D.R.t_odd`. Establish `hη : GlobalTheory.WeilParts.IsEtaTilde D R.eta` using `GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hL.eta R.C.isEta _ _ _ hW.resS hW.resT (hev.add_odd (rW ▸ hr))`. Establish `lV` using `coe_eq_of_frame (hL.βV i)`. Establish `lW` using `coe_eq_of_frame (hL.βW i)`. Use `⟨⟨hW, h.models.inf, hV.1, hev, D.sp.V_sig _, D.sp.W_sig _, exp_mu hL i t, fun τ => ?_, fun v ε hv => ?_, ⟨_, hη⟩⟩, ?_, lV, lW, selfDual_of_coe lV, selfDual_of_coe lW, ?_⟩` and prove the remaining obligations.

Take `⟨a, ha⟩` from `exp_mu hL i t τ`. Take `⟨s, hs⟩` from `hr`. Use `⟨a - s - 1, ?_⟩` and prove the remaining obligations. Establish `h3` using `GlobalTheory.Mem.HeckeExp.hasInfExp_mul ha (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hη.2.2.2 τ))`. Establish `e : ((a - s - 1 : ℤ) : ℚ) + ((Wc D i).rank : ℚ) / 2 = (a : ℚ) + -(1 / 2)`.

Rewrite using `[rW, hs]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h3`.

Take `⟨-, e, ⟨⟨es, hes, -⟩, -⟩, -⟩` from `h.thP.vP i t`. Establish `key` using `fun P (hP : P.under (𝓞 D.host.F) = v) => (GlobalTheory.levCh_unramified_places D T0 R.toLevCh A.μ0 hL t).2.2.2 P fun PP hPP => by`. Rewrite using `[hP]`. Conclude with `under_ne (hes PP (Finset.mem_union.2 hPP)) hv`. Establish `u1` using `GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.mu0 i) v ε hv.1 fun P hP => (key P hP).2 i`.

Establish `u2` using `GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.xi t) v ε hv.1 fun P hP => (key P hP).1`. Establish `u3` using `GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ hL.eta v ε hv.1 fun P _ => R.C.isEta.unr P`. Establish `u4 : GlobalTheory.WeilParts.UnramAt ε (R.toLevCh.mu t ((i : ℕ) + 1))` using `fun x a b c => by show R.mu0 ((i : ℕ) + 1) x * R.xi t x = 1`. Rewrite using `[u1 x a b c, u2 x a b c, one_mul]`. Use `⟨u4, fun x a b c => ?_⟩` and prove the remaining obligations.

Use `show R.toLevCh.mu t ((i : ℕ) + 1) x * (R.eta x)⁻¹ = 1`. Rewrite using `[u4 x a b c, u3 x a b c, inv_one, one_mul]`. Rewrite using `[rV]`. Conclude with `(Nat.add_pos_left hr.pos _).ne'`. Rewrite using `[lV, ← GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, hV.2]`.

Both sides reduce to the same expression.
-/
theorem isPair_record_ofFive' : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (t : T0), VStd D i → IsPair R.ψ R.θ (Vc D i) (Wc D i) (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 (R.ωP i t) ∧ (Vc D i).rank ≠ 0 ∧ (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = L0c D (Vc D i) ∧ (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) = L0c D (Wc D i) ∧ IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank : Set (Fin (Vc D i).rank → D.host.E)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i t hV
  have hL := h.lev
  have hW := h.thP.ωP i t
  have hr : Odd D.R.r := by
    have := D.R.m_add_three_le_k
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hev : Even (Vc D i).rank := rV ▸ hr.add_odd D.R.t_odd
  have hη : GlobalTheory.WeilParts.IsEtaTilde D R.eta :=
    GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hL.eta R.C.isEta _ _ _ hW.resS hW.resT (hev.add_odd (rW ▸ hr))
  have lV := coe_eq_of_frame (hL.βV i)
  have lW := coe_eq_of_frame (hL.βW i)
  refine ⟨⟨hW, h.models.inf, hV.1, hev, D.sp.V_sig _, D.sp.W_sig _, exp_mu hL i t, fun τ => ?_, fun v ε hv => ?_, ⟨_, hη⟩⟩,
    ?_, lV, lW, selfDual_of_coe lV, selfDual_of_coe lW, ?_⟩
  · obtain ⟨a, ha⟩ := exp_mu hL i t τ
    obtain ⟨s, hs⟩ := hr
    refine ⟨a - s - 1, ?_⟩
    have h3 := GlobalTheory.Mem.HeckeExp.hasInfExp_mul ha (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hη.2.2.2 τ))
    have e : ((a - s - 1 : ℤ) : ℚ) + ((Wc D i).rank : ℚ) / 2 = (a : ℚ) + -(1 / 2) := by
      rw [rW, hs]; push_cast; ring
    rw [e]
    exact h3
  · obtain ⟨-, e, ⟨⟨es, hes, -⟩, -⟩, -⟩ := h.thP.vP i t
    have key := fun P (hP : P.under (𝓞 D.host.F) = v) =>
      (GlobalTheory.levCh_unramified_places D T0 R.toLevCh A.μ0 hL t).2.2.2 P fun PP hPP => by
        rw [hP]
        exact under_ne (hes PP (Finset.mem_union.2 hPP)) hv
    have u1 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.mu0 i) v ε hv.1 fun P hP => (key P hP).2 i
    have u2 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.xi t) v ε hv.1 fun P hP => (key P hP).1
    have u3 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ hL.eta v ε hv.1 fun P _ => R.C.isEta.unr P
    have u4 : GlobalTheory.WeilParts.UnramAt ε (R.toLevCh.mu t ((i : ℕ) + 1)) := fun x a b c => by
      show R.mu0 ((i : ℕ) + 1) x * R.xi t x = 1
      rw [u1 x a b c, u2 x a b c, one_mul]
    refine ⟨u4, fun x a b c => ?_⟩
    show R.toLevCh.mu t ((i : ℕ) + 1) x * (R.eta x)⁻¹ = 1
    rw [u4 x a b c, u3 x a b c, inv_one, one_mul]
  · rw [rV]
    exact (Nat.add_pos_left hr.pos _).ne'
  · rw [lV, ← GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, hV.2]
    rfl

end GlobalTheory.AdTh.RecPair

end

section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.AdTh.MovedDatum

variable {D : D7}

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hiso`. Take `⟨δ, hδ⟩` from `GlobalTheory.DatumFourier.thetaVector_eq_sum_heisenberg_of_core_five' D G Pl0 T0 A Ks R F hR i hV H Dw ι hι hiso`. Use `⟨δ, fun t l φ hφ hP bad N h k Λ mk hbad hh hΛ hT hL hmk Y γ u hY hu => ?_⟩` and prove the remaining obligations. Take `⟨e, he, -⟩` from `id hφ`. Take `⟨hp, -, a1, a2, a3, a4, a5⟩` from `GlobalTheory.AdTh.RecPair.isPair_record_ofFive' D G Pl0 T0 A Ks R F hR i t hV`.

Take `⟨hψ, hvac⟩` from `(hR.thP.vP i t).1`. Rewrite using `[hδ t l φ hφ hP e he, map_smul]`. Distinguish the cases in `hfin : Finite (Fin (Vc D i).rank → LevQ Dw l)`. Use `swap`. Use `haveI := not_finite_iff_infinite.1 hfin`.

Rewrite using `[Nat.card_eq_zero_of_infinite, Nat.cast_zero, _root_.inv_zero, zero_smul, zero_smul]`. Rewrite using `[map_finsum _ (Set.toFinite _)]`. Use `congr 1`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`.

Distinguish the cases in `hq : hatC l φ q = 0`. Rewrite using `[hq, zero_smul, zero_smul]`. Take `⟨c, hc, h1, h2⟩` from `step R.ψ hψ (Vc D i) (Wc D i) hp.std (rank_Wc i) (R.ΛV i) (R.ΛW i) a1 a2 a3 a4 a5 l ι hι δ _ e he (fun PP hPP => ⟨(hP PP (Finset.mem_union.1 hPP)).1, fun h2 => (hP PP (Finset.mem_union.1 hPP)).2 (by`. Take `⟨cQ, hcQ⟩` from `D.host.toHostRaw.two_dvd_QS`. Rewrite using `[hcQ, mul_assoc, mul_assoc, Nat.cast_mul, Nat.cast_ofNat]`.

Conclude with `Ideal.mul_mem_right _ _ h2)⟩)`. Use `bad N h k Λ mk (fun PP hPP => hbad PP (Finset.mem_union.1 hPP)) hh hΛ hT hL hmk Y hY q`. Use the proof step `(fun s hs => GlobalTheory.T.levelPoint_smul_integral_of_fourierCoeff_ne_zero D G Pl0 T0 A Ks R i H Dw ι t l φ hφ q hq s fun PP hPP => hs PP (Finset.mem_union.2 hPP))`. Use the proof step `(γ q) (u q) (hu q).1 (hu q).2`. Establish `h3 : heisO R.ψ (Vc D i) (Wc D i) (2 • actO (Vc D i) (Wc D i) h k c) (R.ωP i t (h, k) (R.vacP i)) = R.ωP i t (h, k) (R.vacP i)`.

Rewrite using `[← actO_two, ← hp.weil.om_heis h k _ _ hvac.theta, hvac.lat.1 c hc]`. Establish `h4` using `GlobalTheory.PlaceModel.heisL_heisL (Vc D i) (Wc D i) R.ψ _ _ (R.ωP i t (h, k) (R.vacP i)) |>.trans (congrArg (· • _) h2)`. Rewrite `h4` using `[one_smul, ← h1]`. Rewrite using `[hp.weil.om_heis h k _ _ hvac.theta]`. Use `congr 1`.

Use `Eq.trans ?_ h4` and prove the remaining obligations. Conclude with `congrArg _ h3.symm`.
-/
theorem moved_datum_ofFive' : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ (bad N : ℕ) (h : GA D (Vc D i)) (k : GA D (Wc D i)) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → SplitOffBad (Vc D i) bad h → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι k mk → ∀ (Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E) (γ : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (u : (Fin (Vc D i).rank → LevQ Dw l₂) → WO (Vc D i) (Wc D i)), IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) k)) mk N Y → (∀ q, colsR (rank_Wc i) (γ q) = (δ : ℤ) • Y q ∧ IsFinOf (Vc D i) (Wc D i) (γ q) (u q)) → R.ωP i t (h, k) (R.vP i t) = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (u q) (R.ωP i t (h, k) (R.vacP i)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hiso
  obtain ⟨δ, hδ⟩ := GlobalTheory.DatumFourier.thetaVector_eq_sum_heisenberg_of_core_five' D G Pl0 T0 A Ks R F hR i hV H Dw ι hι hiso
  refine ⟨δ, fun t l φ hφ hP bad N h k Λ mk hbad hh hΛ hT hL hmk Y γ u hY hu => ?_⟩
  obtain ⟨e, he, -⟩ := id hφ
  obtain ⟨hp, -, a1, a2, a3, a4, a5⟩ := GlobalTheory.AdTh.RecPair.isPair_record_ofFive' D G Pl0 T0 A Ks R F hR i t hV
  obtain ⟨hψ, hvac⟩ := (hR.thP.vP i t).1
  rw [hδ t l φ hφ hP e he, map_smul]
  by_cases hfin : Finite (Fin (Vc D i).rank → LevQ Dw l)
  swap
  · haveI := not_finite_iff_infinite.1 hfin
    rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero, _root_.inv_zero, zero_smul, zero_smul]
  rw [map_finsum _ (Set.toFinite _)]
  congr 1
  refine finsum_congr fun q => ?_
  rw [map_smul]
  by_cases hq : hatC l φ q = 0
  · rw [hq, zero_smul, zero_smul]
  obtain ⟨c, hc, h1, h2⟩ := step R.ψ hψ (Vc D i) (Wc D i) hp.std (rank_Wc i) (R.ΛV i) (R.ΛW i) a1 a2 a3 a4 a5 l ι hι δ
    _ e he (fun PP hPP => ⟨(hP PP (Finset.mem_union.1 hPP)).1, fun h2 => (hP PP (Finset.mem_union.1 hPP)).2 (by
      obtain ⟨cQ, hcQ⟩ := D.host.toHostRaw.two_dvd_QS
      rw [hcQ, mul_assoc, mul_assoc, Nat.cast_mul, Nat.cast_ofNat]; exact Ideal.mul_mem_right _ _ h2)⟩)
    bad N h k Λ mk (fun PP hPP => hbad PP (Finset.mem_union.1 hPP)) hh hΛ hT hL hmk Y hY q
    (fun s hs => GlobalTheory.T.levelPoint_smul_integral_of_fourierCoeff_ne_zero D G Pl0 T0 A Ks R i H Dw ι t l φ hφ q hq s fun PP hPP => hs PP (Finset.mem_union.2 hPP))
    (γ q) (u q) (hu q).1 (hu q).2
  have h3 : heisO R.ψ (Vc D i) (Wc D i) (2 • actO (Vc D i) (Wc D i) h k c) (R.ωP i t (h, k) (R.vacP i)) =
      R.ωP i t (h, k) (R.vacP i) := by
    rw [← actO_two, ← hp.weil.om_heis h k _ _ hvac.theta, hvac.lat.1 c hc]
  have h4 := GlobalTheory.PlaceModel.heisL_heisL (Vc D i) (Wc D i) R.ψ _ _ (R.ωP i t (h, k) (R.vacP i)) |>.trans
    (congrArg (· • _) h2)
  rw [one_smul, ← h1] at h4
  rw [hp.weil.om_heis h k _ _ hvac.theta]
  congr 1
  refine Eq.trans ?_ h4
  exact congrArg _ h3.symm

end GlobalTheory.AdTh.MovedDatum

end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.FinDatum

variable {D : D7}

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce and unpack `D G _ _ Pl0 T0 A T _ R F κ v₀ hR ⟨tie⟩ i`. Distinguish the cases in `hstd : VStd D i`. Use `swap`. Conclude with `⟨1, fun Tp tup O hP => absurd hP.lift.std hstd⟩`. Take `⟨hι, hiso⟩` from `lat_iotaW T tie.laws i`.

Take `⟨δ, hδ⟩` from `GlobalTheory.AdTh.MovedDatum.moved_datum_ofFive' D G Pl0 T0 A _ R F hR i hstd _ _ _ hι hiso`. Use `⟨-δ, fun Tp tup O hP t k => ?_⟩` and prove the remaining obligations. Establish `hw : ∀ q, inC O.c' (O.w t k q) = GlobalTheory.AdTh.hatC (O.dδ t).l₂ (fun x => inC O.c' (O.φ t x)) q` using `fun q => (congrArg (inC (O.dδ t).c₂) (hP.w t k q)).trans (GlobalTheory.AdTh.PairModel.hatC_phiHat (O.dδ t).c₂ _ q)`. Establish `hφ : PhiIs R i (RingHom.id ℂ) (tup t) (iotaW T i) (Mfr (O.dδ t).l₂ • ⊤) fun x => inC O.c' (O.φ t x)` using `(hP.tuple t).phi`. Take `⟨h1, h2, h3⟩` from `(hP.tuple t).half`.

Establish `hMb : (O.dδ t).l₂.Mb = T.Q.l.Mb * (O.dδ t).I` using `(hP.cov t).1.2.2.2.1`. Establish `hPg : ∀ PP ∈ R.Pg, (∏ PP ∈ R.Pg, PP.asIdeal) ≤ PP.asIdeal` using `fun PP h => Ideal.prod_le_inf.trans (Finset.inf_le h)`. Establish `hQ : ∀ PP ∈ R.Q (tup t), (∏ PP ∈ R.Q (tup t), PP.asIdeal) ≤ PP.asIdeal` using `fun PP h => Ideal.prod_le_inf.trans (Finset.inf_le h)`. Use `⟨fun q hq b s hs => ?_, fun N _ hN Y hY => ?_⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `GlobalTheory.HatInt.smul_eq_of_hatC_ne_zero D G Pl0 T0 A _ R i _ _ _ _ _ _ hφ q (by rw [← hw]; exact (map_ne_zero _).2 hq) s (fun PP h => h.elim (fun h => hPg PP h (Ideal.mul_le_left hs)) fun h => hQ PP h (Ideal.mul_le_right hs)) b`.

Conclude with `smul_eq_zero_of_smul_rep _ s z hz`. Establish `hl : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q (tup t) → (O.dδ t).l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal` using `fun PP h => ⟨by`. Rewrite using `[hMb]`. Conclude with `h.elim (fun h => Ideal.mul_le_left.trans (h1.le.trans (hPg PP h))) fun h => Ideal.mul_le_right.trans (h2 PP h), h3 PP h⟩`. Establish `hY'` using `isRoots_sign (-δ) hN hY`.

Establish `hL : GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) 1) = LinearMap.range (T.iota ((i : ℕ) + 1))`. Rewrite using `[← hι.2]`. Conclude with `latR_range _ _`. Rewrite `hY'` using `[← hL]`. Establish `h` using `hδ (tup t) (O.dδ t).l₂ _ hφ hl 0 (O.dδ t).l₂.M 1 1 ⟨Formalism.L2.Pj.stdLat D.host.E _⟩ (T.iota ((i : ℕ) + 1)) (fun PP _ => by simp) (splitOffBad_one _) ?_ ⟨1, Nat.coprime_one_left _, Submodule.smul_le_right, Submodule.smul_le_right⟩ ⟨(O.dδ t).l₂.odd, dvd_rfl, le_inf Submodule.smu …`.

Rewrite `h` using `[show ((1, 1) : GA D (Vc D i) × GA D (Wc D i)) = 1 from rfl, map_one, Module.End.one_apply, Module.End.one_apply]`. Simplify using `only [hw]`. Conclude with `h`. Introduce `v`. Rewrite using `[show FWT.fin (Vc D i) 1 = 1 from map_one _, hstd.2]`.

Use `⟨mem_std_star T.Q.H v, fun h => ?_⟩` and prove the remaining obligations. Establish `h'` using `mem_std_star T.Q.H _ h`. Simplify using `only [star_star] at h'`. Conclude with `h'`. Introduce `a _`.

Use `⟨0, zero_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, nsmul_zero, Units.val_one, Matrix.one_mulVec]`. Conclude with `sub_self _`. Introduce `q`. Use `⟨(isFinOf_finR _ _ _ _).1.trans ?_, (isFinOf_finR _ _ _ _).2⟩` and prove the remaining obligations.

Rewrite using `[smul_smul, Units.val_neg, mul_neg, ← Units.val_mul, Int.units_mul_self, Units.val_one, neg_smul, one_smul]`.
-/
theorem thetaVector_eq_sum_translates_of_core_five : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m), ∃ ε : ℤˣ, ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (t : Tp) (k : O.Cl' t), (∀ q, O.w t k q ≠ 0 → ∀ b, ∀ s ∈ (∏ PP ∈ R.Pg, PP.asIdeal) * ∏ PP ∈ R.Q (tup t), PP.asIdeal, s • q b = 0) ∧ ∀ N : ℕ, 0 < N → (O.dδ t).l₂.M ∣ N → ∀ Y : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ t).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E, IsRoots (O.dδ t).l₂ (LinearMap.range (T.iota ((i : ℕ) + 1))) ((ε : ℤ) • T.iota ((i : ℕ) + 1)) N Y → R.vP i (tup t) = ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ t).l₂) : ℕ) : ℂ)⁻¹ • ∑ᶠ q, inC O.c' (O.w t k q) • heisO R.ψ (Vc D i) (Wc D i) (finR (Vc D i) (rank_Wc i) (-(Y q))) (R.vacP i) := by
  rintro D G _ _ Pl0 T0 A T _ R F κ v₀ hR ⟨tie⟩ i
  by_cases hstd : VStd D i
  swap
  · exact ⟨1, fun Tp tup O hP => absurd hP.lift.std hstd⟩
  obtain ⟨hι, hiso⟩ := lat_iotaW T tie.laws i
  obtain ⟨δ, hδ⟩ := GlobalTheory.AdTh.MovedDatum.moved_datum_ofFive' D G Pl0 T0 A _ R F hR i hstd _ _ _ hι hiso
  refine ⟨-δ, fun Tp tup O hP t k => ?_⟩
  have hw : ∀ q, inC O.c' (O.w t k q) = GlobalTheory.AdTh.hatC (O.dδ t).l₂ (fun x => inC O.c' (O.φ t x)) q := fun q =>
    (congrArg (inC (O.dδ t).c₂) (hP.w t k q)).trans (GlobalTheory.AdTh.PairModel.hatC_phiHat (O.dδ t).c₂ _ q)
  have hφ : PhiIs R i (RingHom.id ℂ) (tup t) (iotaW T i) (Mfr (O.dδ t).l₂ • ⊤) fun x => inC O.c' (O.φ t x) :=
    (hP.tuple t).phi
  obtain ⟨h1, h2, h3⟩ := (hP.tuple t).half
  have hMb : (O.dδ t).l₂.Mb = T.Q.l.Mb * (O.dδ t).I := (hP.cov t).1.2.2.2.1
  have hPg : ∀ PP ∈ R.Pg, (∏ PP ∈ R.Pg, PP.asIdeal) ≤ PP.asIdeal := fun PP h =>
    Ideal.prod_le_inf.trans (Finset.inf_le h)
  have hQ : ∀ PP ∈ R.Q (tup t), (∏ PP ∈ R.Q (tup t), PP.asIdeal) ≤ PP.asIdeal := fun PP h =>
    Ideal.prod_le_inf.trans (Finset.inf_le h)
  refine ⟨fun q hq b s hs => ?_, fun N _ hN Y hY => ?_⟩
  · obtain ⟨z, hz⟩ := GlobalTheory.HatInt.smul_eq_of_hatC_ne_zero D G Pl0 T0 A _ R i _ _ _ _ _ _ hφ q
      (by rw [← hw]; exact (map_ne_zero _).2 hq) s
      (fun PP h => h.elim (fun h => hPg PP h (Ideal.mul_le_left hs)) fun h => hQ PP h (Ideal.mul_le_right hs)) b
    exact smul_eq_zero_of_smul_rep _ s z hz
  · have hl : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q (tup t) → (O.dδ t).l₂.Mb ≤ PP.asIdeal ∧
        ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP h =>
      ⟨by
        rw [hMb]
        exact h.elim (fun h => Ideal.mul_le_left.trans (h1.le.trans (hPg PP h))) fun h =>
          Ideal.mul_le_right.trans (h2 PP h), h3 PP h⟩
    have hY' := isRoots_sign (-δ) hN hY
    have hL : GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) 1) = LinearMap.range (T.iota ((i : ℕ) + 1)) := by
      rw [← hι.2]
      exact latR_range _ _
    rw [← hL] at hY'
    have h := hδ (tup t) (O.dδ t).l₂ _ hφ hl 0 (O.dδ t).l₂.M 1 1 ⟨Formalism.L2.Pj.stdLat D.host.E _⟩ (T.iota ((i : ℕ) + 1))
      (fun PP _ => by simp) (splitOffBad_one _) ?_ ⟨1, Nat.coprime_one_left _, Submodule.smul_le_right, Submodule.smul_le_right⟩
      ⟨(O.dδ t).l₂.odd, dvd_rfl, le_inf Submodule.smul_le_right Submodule.smul_le_right⟩ ?_ _
      (fun q => ((-(Y q)).submatrix id (Fin.cast (rank_Wc i)))ᵀ) (fun q => finR (Vc D i) (rank_Wc i) (-(Y q))) hY' ?_
    · rw [show ((1, 1) : GA D (Vc D i) × GA D (Wc D i)) = 1 from rfl, map_one, Module.End.one_apply,
        Module.End.one_apply] at h
      simp only [hw]
      exact h
    · intro v
      rw [show FWT.fin (Vc D i) 1 = 1 from map_one _, hstd.2]
      refine ⟨mem_std_star T.Q.H v, fun h => ?_⟩
      have h' := mem_std_star T.Q.H _ h
      simp only [star_star] at h'
      exact h'
    · intro a _
      refine ⟨0, zero_mem _, ?_⟩
      rw [map_one, nsmul_zero, Units.val_one, Matrix.one_mulVec]
      exact sub_self _
    · intro q
      refine ⟨(isFinOf_finR _ _ _ _).1.trans ?_, (isFinOf_finR _ _ _ _).2⟩
      rw [smul_smul, Units.val_neg, mul_neg, ← Units.val_mul, Int.units_mul_self, Units.val_one, neg_smul, one_smul]

end GlobalTheory.OneMapRef.FinDatum

end

section

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.DatumFourier

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hI`. Take `⟨ε, hε⟩` from `hI`. Use `⟨ε, fun t l φ hφ hP e he s f₀ f hf => ?_⟩` and prove the remaining obligations. Take `⟨hvac, e₁, he₁, hθ⟩` from `hf`. Take `⟨e₂, he₂, hφ⟩` from `hφ`.

Take `rfl` from `idemSum_unique (Vc D i) he₁ he`. Take `rfl` from `idemSum_unique (Vc D i) he₂ he`. Establish `hβV` using `hR.lev.βV i`. Establish `hβW` using `hR.lev.βW i`. Establish `hS` using `GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβV`.

Establish `hT` using `GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβW`. Establish `hstd : R.ΛV i = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)`. Rewrite using `[GlobalTheory.PrincInLevel.eq_latC hβV, ← GlobalTheory.SplitReps.hLat_one, hV.2]`. Establish `hlat` using `mem_latRat_iff hV.1 hstd hβW`. Establish `hM : l.M ≠ 0` using `by have := l.three_le; omega`.

Establish `hM' : (l.M : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hM`. Establish `hsurj : ∀ M ∈ GlobalTheory.LatVac.latRat (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)), ∃ x : Fin (Vc D i).rank → Dw.La, M = Matrix.of fun a b => ι (x b) a`. Introduce `M hM`. Use `choose x hx using fun b => hι.2.ge ((hlat M).1 hM b)`. Conclude with `⟨x, Matrix.ext fun a b => (congrFun (hx b) a).symm⟩`.

Establish `hint : ∀ u ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True), IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u))` using `fun u hu => int_of_mem_latO (fun M hM => by`. Take `⟨x, rfl⟩` from `hsurj M hM`. Conclude with `(hφ x).1) hu`. Establish `: Finite (LevQ Dw l)` using `GlobalTheory.LevelPairing.finite_LevQ`. Use `Fintype.ofFinite (Fin (Vc D i).rank → LevQ Dw l)` as an intermediate fact.

Rewrite using `[finsum_eq_sum_of_fintype, Finset.smul_sum]`. Simplify using `only [smul_smul]`. Use `thetaAt_eq_sum _ _ hθ (fun q a b => ?_) fun w => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.LatVac.cA_cA, Matrix.of_apply, ← mul_assoc, GlobalTheory.PlaceVec.idemSum_mul_self he]`. Distinguish the cases in `hw : w ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True) ∧ IsHalf (cA D e) w`.

Use `swap`. Rewrite using `[halfInd, if_neg hw, zero_mul, if_neg]`. Introduce and unpack `⟨h1, h2⟩`. Establish `hN : ∀ PP ∈ R.Pg ∪ R.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal` using `fun PP hPP h => (hP PP (Finset.mem_union.1 hPP)).2 (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)`. Conclude with `hw ⟨mem_latO_of_int hS hT hβV.choose_spec.1 hβW.choose_spec.1 he (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot) (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) hN h1 h2, h1⟩`.

Establish `hw' : cA D e • w = w` using `Matrix.ext hw.2`. Take `⟨M, hM0, u, hu, hwM⟩` from `approx_mod (Nat.pos_of_ne_zero hM) hw.1`. Take `⟨x, rfl⟩` from `hsurj M hM0`. Establish `hfr : frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w = uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b)) + l.M • frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u)`. Rewrite using `[← hw', hwM, smul_add, GlobalTheory.PlaceVec.frMapAdj_add, frMapAdj_half, smul_comm]`.

Use `congr 1`. Conclude with `one_smul _ _`. Conclude with `(AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add _ _ (R.βV i) (R.βW i))).map_nsmul _ _`. Establish `hred : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) = redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b)))` using `fun PP hPP => by`. Rewrite using `[hfr]`.

Establish `: Ideal.span {(l.M : 𝓞 D.host.E)} ≤ l.Mb` using `l.prod ▸ Ideal.mul_le_left`. Conclude with `GlobalTheory.PlaceVec.redM_add_nsmul PP ((hP PP hPP).1 (this (Ideal.subset_span rfl))) (hφ x).1 (hint u hu)`. Rewrite using `[halfInd, if_pos hw, one_mul, if_pos ⟨hw.2, hw' ▸ hint w hw.1⟩, GlobalTheory.PlaceVec.omegaK_congr _ fun PP h => hred PP (Or.inl h), GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ fun PP h => hred PP (Or.inr h), ← (hφ x).2, RingHom.id_apply, ← inversion l φ x]`. Use `Finset.sum_congr rfl fun q _ => congrArg _ ?_` and prove the remaining obligations. Establish `hY : (Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E)) = Matrix.of fun a b => (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) * ι (cSep l • levRep (q b)) a` using `Matrix.ext fun a b => by simp only [Matrix.of_apply]; ring`.

Use `Eq.trans ?_ (char_eq (Y := Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E)) hvac.1 hS hT (GlobalTheory.PlaceVec.idemSum_infPart he) hw.2 hu hwM ((hlat _).2 fun b => ?_)).symm` and prove the remaining obligations. Rewrite using `[hY, hRat_std hV.1 _ _ _ (by rw [star_div₀, star_intCast, star_natCast]), ← Complex.exp_int_mul]`. Use `congr 1`. Establish `h1 : ∀ c : ℚ, ∀ z : D.host.E, Algebra.trace ℚ D.host.E (D.host.xi0 * ((c : D.host.E) * z)) = c * Algebra.trace ℚ D.host.E (D.host.xi0 * z)` using `fun c z => by`. Rewrite using `[mul_left_comm, ← Rat.smul_def, map_smul, smul_eq_mul]`.

Establish `h2 : ∀ y z, Dw.EF y z = -Dw.EF z y` using `fun y z => (LinearMap.IsAlt.neg Dw.alt z y).symm`. Establish `h3 : ((pairL (l` using `l) x (fun b => levRep (q b)) : ℤ) : ℚ) = -(((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 * ∑ b, (Wc D i).hT ((Wc D i).frame.equivFun.symm (ι (cSep l • levRep (q b)))) ((Wc D i).frame.equivFun.symm (ι (x b))))) := by`. Rewrite using `[pairL, Int.cast_sum, Finset.mul_sum, map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_congr rfl fun b _ => by rw [h2, Int.cast_neg, hε]`. Establish `h4` using `congrArg (fun z : ℚ => (z : ℂ)) h3`.

Rewrite using `[show (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) = ((((ε : ℤ) : ℚ) / (l.M : ℚ) : ℚ) : D.host.E) by push_cast; rfl, h1]`. Move the coercions through the operations in `at h4 ⊢`. Rewrite using `[h4]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `hι.2.le (LinearMap.mem_range_self ι ((ε : ℤ) • cSep l • levRep (q b)))`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `a`. Rewrite using `[map_zsmul, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, mul_div_cancel₀ _ hM', Pi.smul_apply, zsmul_eq_mul]`.
-/
theorem vec_eq_sum_heis_ofFive : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ (s : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ), IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) s (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) R.Pg (R.Q t) (R.xiR t) f₀ f → f = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (Matrix.of fun a b => e * incA D (((δ : ℤ) : D.host.E) * ι (cSep l₂ • levRep (q b)) a / (l₂.M : D.host.E))) f₀ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hI
  obtain ⟨ε, hε⟩ := hI
  refine ⟨ε, fun t l φ hφ hP e he s f₀ f hf => ?_⟩
  obtain ⟨hvac, e₁, he₁, hθ⟩ := hf
  obtain ⟨e₂, he₂, hφ⟩ := hφ
  obtain rfl := idemSum_unique (Vc D i) he₁ he
  obtain rfl := idemSum_unique (Vc D i) he₂ he
  have hβV := hR.lev.βV i
  have hβW := hR.lev.βW i
  have hS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβV
  have hT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβW
  have hstd : R.ΛV i = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβV, ← GlobalTheory.SplitReps.hLat_one, hV.2]
  have hlat := mem_latRat_iff hV.1 hstd hβW
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hM' : (l.M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hsurj : ∀ M ∈ GlobalTheory.LatVac.latRat (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)), ∃ x : Fin (Vc D i).rank → Dw.La, M = Matrix.of fun a b => ι (x b) a := by
    intro M hM
    choose x hx using fun b => hι.2.ge ((hlat M).1 hM b)
    exact ⟨x, Matrix.ext fun a b => (congrFun (hx b) a).symm⟩
  have hint : ∀ u ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True),
      IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u)) := fun u hu =>
    int_of_mem_latO (fun M hM => by
      obtain ⟨x, rfl⟩ := hsurj M hM
      exact (hφ x).1) hu
  have : Finite (LevQ Dw l) := GlobalTheory.LevelPairing.finite_LevQ
  have := Fintype.ofFinite (Fin (Vc D i).rank → LevQ Dw l)
  rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
  simp only [smul_smul]
  refine thetaAt_eq_sum _ _ hθ (fun q a b => ?_) fun w => ?_
  · rw [GlobalTheory.LatVac.cA_cA, Matrix.of_apply, ← mul_assoc, GlobalTheory.PlaceVec.idemSum_mul_self he]
  by_cases hw : w ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True) ∧ IsHalf (cA D e) w
  swap
  · rw [halfInd, if_neg hw, zero_mul, if_neg]
    rintro ⟨h1, h2⟩
    have hN : ∀ PP ∈ R.Pg ∪ R.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP h =>
      (hP PP (Finset.mem_union.1 hPP)).2 (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
    exact hw ⟨mem_latO_of_int hS hT hβV.choose_spec.1 hβW.choose_spec.1 he (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) hN h1 h2, h1⟩
  have hw' : cA D e • w = w := Matrix.ext hw.2
  obtain ⟨M, hM0, u, hu, hwM⟩ := approx_mod (Nat.pos_of_ne_zero hM) hw.1
  obtain ⟨x, rfl⟩ := hsurj M hM0
  have hfr : frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w =
      uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b)) +
        l.M • frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u) := by
    rw [← hw', hwM, smul_add, GlobalTheory.PlaceVec.frMapAdj_add, frMapAdj_half, smul_comm]
    congr 1
    · exact one_smul _ _
    · exact (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add _ _ (R.βV i) (R.βW i))).map_nsmul _ _
  have hred : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) =
      redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b))) := fun PP hPP => by
    rw [hfr]
    have : Ideal.span {(l.M : 𝓞 D.host.E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact GlobalTheory.PlaceVec.redM_add_nsmul PP ((hP PP hPP).1 (this (Ideal.subset_span rfl))) (hφ x).1 (hint u hu)
  rw [halfInd, if_pos hw, one_mul, if_pos ⟨hw.2, hw' ▸ hint w hw.1⟩,
    GlobalTheory.PlaceVec.omegaK_congr _ fun PP h => hred PP (Or.inl h),
    GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ fun PP h => hred PP (Or.inr h), ← (hφ x).2, RingHom.id_apply, ← inversion l φ x]
  refine Finset.sum_congr rfl fun q _ => congrArg _ ?_
  have hY : (Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E)) =
      Matrix.of fun a b => (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) * ι (cSep l • levRep (q b)) a :=
    Matrix.ext fun a b => by simp only [Matrix.of_apply]; ring
  refine Eq.trans ?_ (char_eq (Y := Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E))
    hvac.1 hS hT (GlobalTheory.PlaceVec.idemSum_infPart he) hw.2 hu hwM ((hlat _).2 fun b => ?_)).symm
  · rw [hY, hRat_std hV.1 _ _ _ (by rw [star_div₀, star_intCast, star_natCast]), ← Complex.exp_int_mul]
    congr 1
    have h1 : ∀ c : ℚ, ∀ z : D.host.E, Algebra.trace ℚ D.host.E (D.host.xi0 * ((c : D.host.E) * z)) =
        c * Algebra.trace ℚ D.host.E (D.host.xi0 * z) := fun c z => by
      rw [mul_left_comm, ← Rat.smul_def, map_smul, smul_eq_mul]
    have h2 : ∀ y z, Dw.EF y z = -Dw.EF z y := fun y z => (LinearMap.IsAlt.neg Dw.alt z y).symm
    have h3 : ((pairL (l := l) x (fun b => levRep (q b)) : ℤ) : ℚ) = -(((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 *
        ∑ b, (Wc D i).hT ((Wc D i).frame.equivFun.symm (ι (cSep l • levRep (q b)))) ((Wc D i).frame.equivFun.symm (ι (x b))))) := by
      rw [pairL, Int.cast_sum, Finset.mul_sum, map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => by rw [h2, Int.cast_neg, hε]
    have h4 := congrArg (fun z : ℚ => (z : ℂ)) h3
    rw [show (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) = ((((ε : ℤ) : ℚ) / (l.M : ℚ) : ℚ) : D.host.E) by push_cast; rfl, h1]
    push_cast at h4 ⊢
    rw [h4]
    ring
  · have h1 := hι.2.le (LinearMap.mem_range_self ι ((ε : ℤ) • cSep l • levRep (q b)))
    convert h1 using 1
    funext a
    rw [map_zsmul, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, mul_div_cancel₀ _ hM', Pi.smul_apply, zsmul_eq_mul]

open GlobalTheory.AdTh.MovedDatum in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hiso`. Take `⟨δ, hδ⟩` from `vec_eq_sum_heis_ofFive D G Pl0 T0 A Ks R F hR i hV H Dw ι hι hiso`. Use `⟨δ, fun t l φ hφ hP bad N Λ mk hbad hh hΛ hT hL hmk Y γ u hY hu s f₀ f hf => ?_⟩` and prove the remaining obligations. Take `⟨e, he, -⟩` from `id hφ`. Take `⟨-, -, a1, a2, a3, a4, a5⟩` from `GlobalTheory.AdTh.RecPair.isPair_record_ofFive' D G Pl0 T0 A Ks R F hR i t hV`.

Take `⟨hψ, hvac⟩` from `hf.1`. Use `(hδ t l φ hφ hP e he s f₀ f hf).trans ?_` and prove the remaining obligations. Use `congr 1`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Distinguish the cases in `hq : hatC l φ q = 0`.

Rewrite using `[hq, zero_smul, zero_smul]`. Take `⟨c, hc, h1, h2⟩` from `step R.ψ hψ (Vc D i) (Wc D i) hV.1 (rank_Wc i) (R.ΛV i) (R.ΛW i) a1 a2 a3 a4 a5 l ι hι δ _ e he (fun PP hPP => ⟨(hP PP (Finset.mem_union.1 hPP)).1, fun h2 => (hP PP (Finset.mem_union.1 hPP)).2 (by`. Take `⟨cQ, hcQ⟩` from `D.host.toHostRaw.two_dvd_QS`. Rewrite using `[hcQ, mul_assoc, mul_assoc, Nat.cast_mul, Nat.cast_ofNat]`. Conclude with `Ideal.mul_mem_right _ _ h2)⟩)`.

Use `bad N 1 1 Λ mk (fun PP hPP => hbad PP (Finset.mem_union.1 hPP)) hh hΛ hT hL hmk Y hY q`. Use the proof step `(fun s hs => GlobalTheory.HatInt.smul_eq_of_hatC_ne_zero D G Pl0 T0 A Ks R i H Dw ι t l φ hφ q hq s fun PP hPP => hs PP (Finset.mem_union.2 hPP))`. Use the proof step `(γ q) (u q) (hu q).1 (hu q).2`. Establish `h0 : ∀ x : WO (Vc D i) (Wc D i), actO (Vc D i) (Wc D i) 1 1 x = x` using `fun x => by`. Rewrite using `[actO, inv_one, GlobalTheory.AdelicLatMove.mt_one, GlobalTheory.AdelicLatMove.mt_one, Matrix.mul_one, Matrix.one_mul]`.

Rewrite `h1`, `h2` using `[h0, h0]`. Establish `h3 : heisO R.ψ (Vc D i) (Wc D i) (2 • c) f₀ = f₀` using `hvac.lat.1 c hc`. Establish `h4` using `GlobalTheory.PlaceModel.heisL_heisL (Vc D i) (Wc D i) R.ψ _ _ f₀ |>.trans (congrArg (· • _) h2)`. Rewrite `h4` using `[one_smul, ← h1]`. Use `congr 1`.

Use `Eq.trans ?_ h4` and prove the remaining obligations. Conclude with `congrArg _ h3.symm`.
-/
theorem vec_eq_sum_roots_ofFive : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ (bad N : ℕ) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → SplitOffBad (Vc D i) bad 1 → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) 1)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι 1 mk → ∀ (Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E) (γ : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (u : (Fin (Vc D i).rank → LevQ Dw l₂) → WO (Vc D i) (Wc D i)), IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) 1)) mk N Y → (∀ q, colsR (rank_Wc i) (γ q) = (δ : ℤ) • Y q ∧ IsFinOf (Vc D i) (Wc D i) (γ q) (u q)) → ∀ (s : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ), IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) s (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) R.Pg (R.Q t) (R.xiR t) f₀ f → f = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (u q) f₀ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hiso
  obtain ⟨δ, hδ⟩ := vec_eq_sum_heis_ofFive D G Pl0 T0 A Ks R F hR i hV H Dw ι hι hiso
  refine ⟨δ, fun t l φ hφ hP bad N Λ mk hbad hh hΛ hT hL hmk Y γ u hY hu s f₀ f hf => ?_⟩
  obtain ⟨e, he, -⟩ := id hφ
  obtain ⟨-, -, a1, a2, a3, a4, a5⟩ := GlobalTheory.AdTh.RecPair.isPair_record_ofFive' D G Pl0 T0 A Ks R F hR i t hV
  obtain ⟨hψ, hvac⟩ := hf.1
  refine (hδ t l φ hφ hP e he s f₀ f hf).trans ?_
  congr 1
  refine finsum_congr fun q => ?_
  by_cases hq : hatC l φ q = 0
  · rw [hq, zero_smul, zero_smul]
  obtain ⟨c, hc, h1, h2⟩ := step R.ψ hψ (Vc D i) (Wc D i) hV.1 (rank_Wc i) (R.ΛV i) (R.ΛW i) a1 a2 a3 a4 a5 l ι hι δ
    _ e he (fun PP hPP => ⟨(hP PP (Finset.mem_union.1 hPP)).1, fun h2 => (hP PP (Finset.mem_union.1 hPP)).2 (by
      obtain ⟨cQ, hcQ⟩ := D.host.toHostRaw.two_dvd_QS
      rw [hcQ, mul_assoc, mul_assoc, Nat.cast_mul, Nat.cast_ofNat]; exact Ideal.mul_mem_right _ _ h2)⟩)
    bad N 1 1 Λ mk (fun PP hPP => hbad PP (Finset.mem_union.1 hPP)) hh hΛ hT hL hmk Y hY q
    (fun s hs => GlobalTheory.HatInt.smul_eq_of_hatC_ne_zero D G Pl0 T0 A Ks R i H Dw ι t l φ hφ q hq s
      fun PP hPP => hs PP (Finset.mem_union.2 hPP))
    (γ q) (u q) (hu q).1 (hu q).2
  have h0 : ∀ x : WO (Vc D i) (Wc D i), actO (Vc D i) (Wc D i) 1 1 x = x := fun x => by
    rw [actO, inv_one, GlobalTheory.AdelicLatMove.mt_one, GlobalTheory.AdelicLatMove.mt_one, Matrix.mul_one, Matrix.one_mul]
  rw [h0, h0] at h1 h2
  have h3 : heisO R.ψ (Vc D i) (Wc D i) (2 • c) f₀ = f₀ := hvac.lat.1 c hc
  have h4 := GlobalTheory.PlaceModel.heisL_heisL (Vc D i) (Wc D i) R.ψ _ _ f₀ |>.trans (congrArg (· • _) h2)
  rw [one_smul, ← h1] at h4
  congr 1
  refine Eq.trans ?_ h4
  exact congrArg _ h3.symm

end GlobalTheory.DatumFourier

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

open GlobalTheory.OneMapRef.FinDatum in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ hR tie i O hP`. Establish `hstd : VStd D i` using `hP.lift.std`. Take `⟨hι, hiso⟩` from `lat_iotaW T tie.laws i`. Take `⟨δ, hδ⟩` from `GlobalTheory.DatumFourier.vec_eq_sum_roots_ofFive D G Pl0 T0 A _ R F hR i hstd _ _ _ hι hiso`. Use `⟨-δ, fun s f₀ f hf k N _ hN Y hY => ?_⟩` and prove the remaining obligations.

Establish `hQ0 : R.Q A.μ0 = ∅` using `(chars_of_lift_ofFive D G Pl0 T0 A _ R F hR i).2.2.1`. Establish `hw : ∀ q, inC O.c' (O.w () k q) = GlobalTheory.AdTh.hatC (O.dδ ()).l₂ (fun x => inC O.c' (O.φ () x)) q` using `fun q => (congrArg (inC (O.dδ ()).c₂) (hP.w () k q)).trans (GlobalTheory.AdTh.PairModel.hatC_phiHat (O.dδ ()).c₂ _ q)`. Establish `hφ : PhiIs R i (RingHom.id ℂ) A.μ0 (iotaW T i) (Mfr (O.dδ ()).l₂ • ⊤) fun x => inC O.c' (O.φ () x)` using `(hP.tuple ()).phi`. Take `⟨h1, h2, h3⟩` from `(hP.tuple ()).half`. Establish `hMb : (O.dδ ()).l₂.Mb = T.Q.l.Mb * (O.dδ ()).I` using `(hP.cov ()).1.2.2.2.1`.

Establish `hPg : ∀ PP ∈ R.Pg, (∏ PP ∈ R.Pg, PP.asIdeal) ≤ PP.asIdeal` using `fun PP h => Ideal.prod_le_inf.trans (Finset.inf_le h)`. Establish `hl : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q A.μ0 → (O.dδ ()).l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal` using `fun PP h => ⟨by`. Rewrite using `[hMb]`. Conclude with `h.elim (fun h => Ideal.mul_le_left.trans (h1.le.trans (hPg PP h))) fun h => Ideal.mul_le_right.trans (h2 PP h), h3 PP h⟩`. Establish `hY'` using `isRoots_sign (-δ) hN hY`.

Establish `hL : GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) 1) = LinearMap.range (T.iota ((i : ℕ) + 1))`. Rewrite using `[← hι.2]`. Conclude with `latR_range _ _`. Rewrite `hY'` using `[← hL]`. Establish `h` using `hδ A.μ0 (O.dδ ()).l₂ _ hφ hl 0 (O.dδ ()).l₂.M ⟨Formalism.L2.Pj.stdLat D.host.E _⟩ (T.iota ((i : ℕ) + 1)) (fun PP _ => by simp) (splitOffBad_one _) ?_ ⟨1, Nat.coprime_one_left _, Submodule.smul_le_right, Submodule.smul_le_right⟩ ⟨(O.dδ ()).l₂.odd, dvd_rfl, le_inf Submodule.smul_le …`.

Simplify using `only [hw]`. Conclude with `h`. Introduce `v`. Rewrite using `[show FWT.fin (Vc D i) 1 = 1 from map_one _, hstd.2]`. Use `⟨mem_std_star T.Q.H v, fun h => ?_⟩` and prove the remaining obligations.

Establish `h'` using `mem_std_star T.Q.H _ h`. Simplify using `only [star_star] at h'`. Conclude with `h'`. Introduce `a _`. Use `⟨0, zero_mem _, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_one, nsmul_zero, Units.val_one, Matrix.one_mulVec]`. Conclude with `sub_self _`. Introduce `q`. Use `⟨(isFinOf_finR _ _ _ _).1.trans ?_, (isFinOf_finR _ _ _ _).2⟩` and prove the remaining obligations. Rewrite using `[smul_smul, Units.val_neg, mul_neg, ← Units.val_mul, Int.units_mul_self, Units.val_one, neg_smul, one_smul]`.
-/
theorem vec_eq_mean_translates_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → FWTie T R κ v₀ → ∀ (i : Fin D.R.m) (O : OM T R i), Pinned κ v₀ O → ∃ ε : ℤˣ, ∀ (s : Fam (Wc D i)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ), IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) s (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) R.Pg ∅ (fun _ => 1) f₀ f → ∀ (k : O.Cl' ()) (N : ℕ), 0 < N → (O.dδ ()).l₂.M ∣ N → ∀ Y : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E, IsRoots (O.dδ ()).l₂ (LinearMap.range (T.iota ((i : ℕ) + 1))) ((ε : ℤ) • T.iota ((i : ℕ) + 1)) N Y → f = ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) : ℕ) : ℂ)⁻¹ • ∑ᶠ q, inC O.c' (O.w () k q) • heisO R.ψ (Vc D i) (Wc D i) (finR (Vc D i) (rank_Wc i) (-(Y q))) f₀ := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR tie i O hP
  have hstd : VStd D i := hP.lift.std
  obtain ⟨hι, hiso⟩ := lat_iotaW T tie.laws i
  obtain ⟨δ, hδ⟩ := GlobalTheory.DatumFourier.vec_eq_sum_roots_ofFive D G Pl0 T0 A _ R F hR i hstd _ _ _ hι hiso
  refine ⟨-δ, fun s f₀ f hf k N _ hN Y hY => ?_⟩
  have hQ0 : R.Q A.μ0 = ∅ := (chars_of_lift_ofFive D G Pl0 T0 A _ R F hR i).2.2.1
  have hw : ∀ q, inC O.c' (O.w () k q) = GlobalTheory.AdTh.hatC (O.dδ ()).l₂ (fun x => inC O.c' (O.φ () x)) q := fun q =>
    (congrArg (inC (O.dδ ()).c₂) (hP.w () k q)).trans (GlobalTheory.AdTh.PairModel.hatC_phiHat (O.dδ ()).c₂ _ q)
  have hφ : PhiIs R i (RingHom.id ℂ) A.μ0 (iotaW T i) (Mfr (O.dδ ()).l₂ • ⊤) fun x => inC O.c' (O.φ () x) :=
    (hP.tuple ()).phi
  obtain ⟨h1, h2, h3⟩ := (hP.tuple ()).half
  have hMb : (O.dδ ()).l₂.Mb = T.Q.l.Mb * (O.dδ ()).I := (hP.cov ()).1.2.2.2.1
  have hPg : ∀ PP ∈ R.Pg, (∏ PP ∈ R.Pg, PP.asIdeal) ≤ PP.asIdeal := fun PP h =>
    Ideal.prod_le_inf.trans (Finset.inf_le h)
  have hl : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q A.μ0 → (O.dδ ()).l₂.Mb ≤ PP.asIdeal ∧
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP h =>
    ⟨by
      rw [hMb]
      exact h.elim (fun h => Ideal.mul_le_left.trans (h1.le.trans (hPg PP h))) fun h =>
        Ideal.mul_le_right.trans (h2 PP h), h3 PP h⟩
  have hY' := isRoots_sign (-δ) hN hY
  have hL : GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) 1) = LinearMap.range (T.iota ((i : ℕ) + 1)) := by
    rw [← hι.2]
    exact latR_range _ _
  rw [← hL] at hY'
  have h := hδ A.μ0 (O.dδ ()).l₂ _ hφ hl 0 (O.dδ ()).l₂.M ⟨Formalism.L2.Pj.stdLat D.host.E _⟩ (T.iota ((i : ℕ) + 1))
    (fun PP _ => by simp) (splitOffBad_one _) ?_ ⟨1, Nat.coprime_one_left _, Submodule.smul_le_right, Submodule.smul_le_right⟩
    ⟨(O.dδ ()).l₂.odd, dvd_rfl, le_inf Submodule.smul_le_right Submodule.smul_le_right⟩ ?_ _
    (fun q => ((-(Y q)).submatrix id (Fin.cast (rank_Wc i)))ᵀ) (fun q => finR (Vc D i) (rank_Wc i) (-(Y q))) hY' ?_
    s f₀ f (isThPVecOf_empty hQ0 hf)
  · simp only [hw]
    exact h
  · intro v
    rw [show FWT.fin (Vc D i) 1 = 1 from map_one _, hstd.2]
    refine ⟨mem_std_star T.Q.H v, fun h => ?_⟩
    have h' := mem_std_star T.Q.H _ h
    simp only [star_star] at h'
    exact h'
  · intro a _
    refine ⟨0, zero_mem _, ?_⟩
    rw [map_one, nsmul_zero, Units.val_one, Matrix.one_mulVec]
    exact sub_self _
  · intro q
    refine ⟨(isFinOf_finR _ _ _ _).1.trans ?_, (isFinOf_finR _ _ _ _).2⟩
    rw [smul_smul, Units.val_neg, mul_neg, ← Units.val_mul, Int.units_mul_self, Units.val_one, neg_smul, one_smul]

end GlobalTheory.GalOne

end

end

section

namespace GlobalTheory.ClassScalarValue

section Local

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR Formalism.IndefR.Links
  Formalism.L2.JoinChr Formalism.L2.Host Formalism.L2.Pj GlobalTheory.IdemSupport
open scoped TensorProduct Matrix nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

end Local

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT i Tp tup O hO t k h e P y he hP hs hy hLh hbad`. Establish `hL` using `hC.lev`. Take `⟨r1, r2, -, r4, -, r6⟩` from `(hO.reps t).1 k`. Establish `hcj` using `(GlobalTheory.ClassScalarCompare.latPin_iff_conjLat _ _).1 (hO.reps t).2 k`. Establish `g` using `GlobalTheory.ClassScalarCompare.guard_conjLat (H := T.Q.H) (L := (O.La t k).La) ⟨r1, r2, r6⟩`.

Rewrite `g` using `[hcj, GlobalTheory.ClassScalarCompare.conjLat_conjLat]`. Establish `hpq : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q` using `(hT.laws.unf _ ⟨Nat.le_add_left _ _, i.2⟩ _ T.toCore.good_σ₀).1`. Establish `hbar : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E)` using `RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)`. Take `⟨cc, c0, c1, c2, c3, c4⟩` from `exists_ideal (Vc D i) hO.lift.std.1 hO.lift.std.2 h e P y he hs hy (O.bad t) hP _ _ (chrEq_mul_inv (hL.mu0 i) (hL.xi (tup t)) hL.eta) (fun Q hQ x hx => by`. Establish `a1 : (R.C.mu0 i).UnrAt Q` using `(R.C.isMu0 i).unr Q fun j hj => hQ (by`.

Take `⟨u, hu⟩` from `(Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ j)).trans ((Fin.prod_univ_two D.host.g).symm ▸ (hO.bad t).2.2.2.2)`. Rewrite using `[hu, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hj)`. Establish `a2 : (R.xiH (tup t)).UnrAt Q`. Assume the negation of the conclusion as `hn`.

Break down `(hL.Q_ram (tup t) Q).1 hn with a | ⟨Q', a, a'⟩` into its components or cases. Conclude with `hQ (hbad Q (Or.inr a))`. Rewrite `hQ` using `[(GlobalTheory.IdemSupport.isConjPl_iff _ _).1 a', GlobalTheory.IdemSupport.mem_cP, map_natCast]`. Conclude with `hQ (hbad Q' (Or.inr a))`. Rewrite using `[Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, a1 x hx, a2 x hx, R.C.isEta.unr Q x hx, inv_one, one_mul, one_mul])`.

Use the proof step `(fun Q hQ x => by`. Rewrite using `[Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv, (R.C.isMu0 i).triv.1, (hL.xi_triv (tup t)).1, R.C.isEta.res.1, Formalism.L2.Host.etaFin, above_eq, Finset.card_pair hQ.symm, if_neg (by norm_num), inv_one, one_mul, one_mu …`. Rewrite `c1`, `c3` using `[← hbar]`. Rewrite `c3` using `[← hLh]`. Take `⟨q, q0, q1, q2⟩` from `(hO.ep t).2 (O.Lh t k) cc g.1 g.2.1 g.2.2 c1 c3`.

Establish `hB` using `(hO.tuple t).B cc c0 c2`. Establish `hi` using `GlobalTheory.ClassScalarCompare.stdIndex_conjLat (O.Lh t k)`. Rewrite `hi` using `[← hcj]`. Rewrite `q1` using `[← hpq, ← Nat.cast_pow]`. Use `value_calc (x := (((Lift.chrTh (R.toLevCh.mu (tup t)) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)) q0 (fun h0 => c0 (Ideal.absNorm_eq_zero_iff.1 h0)) (mIdx_ne_zero (O.La t k) D.R.r (fun h0 : O.Nc t k = 0 => by simpa [h0] using r4.1)) q1` as an intermediate fact.

Rewrite using `[(hO.ep t).1 k, q2, zCard_eq _ _ _ r4.2.2, map_mul, map_mul, map_mul, map_inv₀, map_inv₀, hB, ← c4, map_ratCast, map_natCast, map_natCast, ← Nat.cast_pow]`. Establish `hi' : ((O.La t k).Ln.toAddSubgroup.addSubgroupOf (O.La t k).La.toAddSubgroup).index = ((O.Lh t k ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf (O.Lh t k).toAddSubgroup).index` using `hi`. Rewrite `this` using `[← hi']`. Conclude with `this`.
-/
theorem class_scalar_value_ofFive' : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (t : Tp) (k : O.Cl' t) (h : GA D (Vc D i)) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), IsIdemSum e P → (∀ PP ∈ P, ((O.bad t : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h y → O.Lh t k = Bridge.hLat (Vc D i) (fin (Vc D i) h) → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q (tup t) → ((O.bad t : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → inC O.c' (O.ep t k * (((O.La t k).mIdx (O.Nc t k) D.R.r : O.c'.F))⁻¹ * ((O.La t k).zCard (O.Nc t k) D.R.r : O.c'.F)) = (((Lift.chrTh (R.toLevCh.mu (tup t)) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)⁻¹ * (Real.sqrt (((((O.La t k).La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf (O.La t k).La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT i Tp tup O hO t k h e P y he hP hs hy hLh hbad
  have hL := hC.lev
  obtain ⟨r1, r2, -, r4, -, r6⟩ := (hO.reps t).1 k
  have hcj := (GlobalTheory.ClassScalarCompare.latPin_iff_conjLat _ _).1 (hO.reps t).2 k
  have g := GlobalTheory.ClassScalarCompare.guard_conjLat (H := T.Q.H) (L := (O.La t k).La) ⟨r1, r2, r6⟩
  rw [hcj, GlobalTheory.ClassScalarCompare.conjLat_conjLat] at g
  have hpq : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q :=
    (hT.laws.unf _ ⟨Nat.le_add_left _ _, i.2⟩ _ T.toCore.good_σ₀).1
  have hbar : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
    RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := exists_ideal (Vc D i) hO.lift.std.1 hO.lift.std.2 h e P y he hs hy (O.bad t) hP _ _
    (chrEq_mul_inv (hL.mu0 i) (hL.xi (tup t)) hL.eta)
    (fun Q hQ x hx => by
      have a1 : (R.C.mu0 i).UnrAt Q := (R.C.isMu0 i).unr Q fun j hj => hQ (by
        obtain ⟨u, hu⟩ := (Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ j)).trans
          ((Fin.prod_univ_two D.host.g).symm ▸ (hO.bad t).2.2.2.2)
        rw [hu, Nat.cast_mul]
        exact Ideal.mul_mem_right _ _ hj)
      have a2 : (R.xiH (tup t)).UnrAt Q := by
        by_contra hn
        rcases (hL.Q_ram (tup t) Q).1 hn with a | ⟨Q', a, a'⟩
        · exact hQ (hbad Q (Or.inr a))
        · rw [(GlobalTheory.IdemSupport.isConjPl_iff _ _).1 a', GlobalTheory.IdemSupport.mem_cP, map_natCast] at hQ
          exact hQ (hbad Q' (Or.inr a))
      rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, a1 x hx, a2 x hx,
        R.C.isEta.unr Q x hx, inv_one, one_mul, one_mul])
    (fun Q hQ x => by
      rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv,
        (R.C.isMu0 i).triv.1, (hL.xi_triv (tup t)).1, R.C.isEta.res.1, Formalism.L2.Host.etaFin, above_eq,
        Finset.card_pair hQ.symm, if_neg (by norm_num), inv_one, one_mul, one_mul])
  rw [← hbar] at c1 c3
  rw [← hLh] at c3
  obtain ⟨q, q0, q1, q2⟩ := (hO.ep t).2 (O.Lh t k) cc g.1 g.2.1 g.2.2 c1 c3
  have hB := (hO.tuple t).B cc c0 c2
  have hi := GlobalTheory.ClassScalarCompare.stdIndex_conjLat (O.Lh t k)
  rw [← hcj] at hi
  rw [← hpq, ← Nat.cast_pow] at q1
  have := value_calc (x := (((Lift.chrTh (R.toLevCh.mu (tup t)) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)) q0
    (fun h0 => c0 (Ideal.absNorm_eq_zero_iff.1 h0))
    (mIdx_ne_zero (O.La t k) D.R.r (fun h0 : O.Nc t k = 0 => by simpa [h0] using r4.1)) q1
  rw [(hO.ep t).1 k, q2, zCard_eq _ _ _ r4.2.2, map_mul, map_mul, map_mul, map_inv₀, map_inv₀, hB, ← c4, map_ratCast,
    map_natCast, map_natCast, ← Nat.cast_pow]
  have hi' : ((O.La t k).Ln.toAddSubgroup.addSubgroupOf (O.La t k).La.toAddSubgroup).index =
      ((O.Lh t k ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf (O.Lh t k).toAddSubgroup).index := hi
  rw [← hi'] at this
  exact this

end GlobalTheory.ClassScalarValue

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.ClassScalar

open GlobalTheory.Ker

variable {D : D7}

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce and unpack `D G _ _ Pl0 T0 A T _ R F κ v₀ hC ⟨tie⟩ i Tp tup O hO t h J' hR k`. Take `⟨-, hbad, -, -, -, -, hk⟩` from `hR`. Take `⟨⟨-, e, P, he, hP, hs⟩, hLh, -⟩` from `hk k`. Take `⟨r1, -, -, r4, -, -⟩` from `(hO.reps t).1 k`. Take `⟨x, hx⟩` from `exists_isDetAt (GlobalTheory.PlaceDatum.idemSum_mul_self he) (Vc D i) (h k)`.

Use `⟨?_, ?_, e, P, x, he, hs, hx, ?_⟩` and prove the remaining obligations. Establish `hU` using `(GenLatCmp.unimod_iff (O.La t k).La).1 r1`. Establish `h4 : ∀ u ∈ stdL D.host.E (Vc D i).rank, (O.Nc t k : D.host.E) • u ∈ (O.La t k).La` using `fun u hu => ((GenLatCmp.span_smul_le _ _ _).1 r4.2.2 u (GenLatCmp.std_eq (E := D.host.E) ▸ hu)).1`. Establish `h5` using `GenLatCmp.smul_mem_std hU h4`. Conclude with `⟨GenLatCmp.fg_of_smul_le r4.1.pos h5, hU, _, r4.1.pos, Nat.coprime_one_right _, h5, h4⟩`.

Use `isMov_conj (isMov_hLat _ (hO.lift.std.2.trans GenLatCmp.std_eq) (h k)) fun v => ?_` and prove the remaining obligations. Rewrite using `[← hLh]`. Conclude with `(hO.reps t).2 k v`. Rewrite using `[GlobalTheory.ClassScalarValue.class_scalar_value_ofFive' D G Pl0 T0 A T R F κ v₀ hC ⟨tie.laws, tie.alg_eq, tie.kap, tie.hv₀, tie.chiR, tie.x0⟩ i Tp tup O hO t k (h k) e P x he hP hs hx hLh hbad, Circle.coe_inv, Nat.cast_pow, GenLatCmp.std_eq]`.
-/
theorem class_lattice_scalar_ofFive : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (t : Tp) (h : O.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), RepsR R i (tup t) h (O.bad t) J' (O.Lh t) (O.gam t) (O.vol t) → ∀ k, (O.La t k).La ∈ Vset D.host.E (Vc D i).rank 1 ∧ GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmtC (Vc D i) (h k)) (stdL D.host.E (Vc D i).rank) (O.La t k).La ∧ ∃ (e : AE D) (P : Finset (Pl D.host.E)) (x : (AE D)ˣ), IsIdemSum e P ∧ SuppAt e (Vc D i) (h k) ∧ IsDetAt e (Vc D i) (h k) x ∧ inC O.c' (O.ep t k * (((O.La t k).mIdx (O.Nc t k) D.R.r : O.c'.F))⁻¹ * ((O.La t k).zCard (O.Nc t k) D.R.r : O.c'.F)) = ((((Lift.chrTh (R.toLevCh.mu (tup t)) R.eta ((i : ℕ) + 1)).2 x)⁻¹ : Circle) : ℂ) * ((Real.sqrt ((((((O.La t k).La ⊓ stdL D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf (O.La t k).La.toAddSubgroup).index ^ D.R.r : ℕ) : ℝ)) : ℝ) : ℂ) := by
  rintro D G _ _ Pl0 T0 A T _ R F κ v₀ hC ⟨tie⟩ i Tp tup O hO t h J' hR k
  obtain ⟨-, hbad, -, -, -, -, hk⟩ := hR
  obtain ⟨⟨-, e, P, he, hP, hs⟩, hLh, -⟩ := hk k
  obtain ⟨r1, -, -, r4, -, -⟩ := (hO.reps t).1 k
  obtain ⟨x, hx⟩ := exists_isDetAt (GlobalTheory.PlaceDatum.idemSum_mul_self he) (Vc D i) (h k)
  refine ⟨?_, ?_, e, P, x, he, hs, hx, ?_⟩
  · have hU := (GenLatCmp.unimod_iff (O.La t k).La).1 r1
    have h4 : ∀ u ∈ stdL D.host.E (Vc D i).rank, (O.Nc t k : D.host.E) • u ∈ (O.La t k).La := fun u hu =>
      ((GenLatCmp.span_smul_le _ _ _).1 r4.2.2 u (GenLatCmp.std_eq (E := D.host.E) ▸ hu)).1
    have h5 := GenLatCmp.smul_mem_std hU h4
    exact ⟨GenLatCmp.fg_of_smul_le r4.1.pos h5, hU, _, r4.1.pos, Nat.coprime_one_right _, h5, h4⟩
  · refine isMov_conj (isMov_hLat _ (hO.lift.std.2.trans GenLatCmp.std_eq) (h k)) fun v => ?_
    rw [← hLh]
    exact (hO.reps t).2 k v
  · rw [GlobalTheory.ClassScalarValue.class_scalar_value_ofFive' D G Pl0 T0 A T R F κ v₀ hC ⟨tie.laws, tie.alg_eq, tie.kap, tie.hv₀, tie.chiR, tie.x0⟩ i Tp tup O hO
      t k (h k) e P x he hP hs hx hLh hbad, Circle.coe_inv, Nat.cast_pow, GenLatCmp.std_eq]

end GlobalTheory.OneMapRef.ClassScalar

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.ClassConj

section Local

open Formalism.L2.JoinChr Formalism.L2.Host

variable {D : D7}

end Local

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ hC tie i O hO σ σ' hσ μ' η' hμ hη h J' hR k`. Establish `hcl` using `GlobalTheory.OneMapRef.ClassScalar.class_lattice_scalar_ofFive D G Pl0 T0 A T R F κ v₀ hC ⟨tie⟩ i Unit (fun _ => A.μ0) O hO () h J' hR k`. Establish `hT : TieIn T R κ v₀` using `⟨tie.laws, tie.alg_eq, tie.kap, tie.hv₀, tie.chiR, tie.x0⟩`. Establish `hL` using `hC.lev`. Establish `hch` using `GlobalTheory.OneMapRef.chars_of_lift_ofFive D G Pl0 T0 A T.Q.c.F R F hC i`.

Take `⟨-, hbad, -, -, -, -, hk⟩` from `hR`. Take `⟨⟨-, e, P, he, hP, hs⟩, hLh, -⟩` from `hk k`. Take `⟨x, hx⟩` from `GlobalTheory.OneMapRef.ClassScalar.exists_isDetAt (GlobalTheory.PlaceDatum.idemSum_mul_self he) (Vc D i) (h k)`. Use `⟨hcl.1, hcl.2.1, e, P, x, he, hs, hx, ?_⟩` and prove the remaining obligations. Take `⟨r1, r2, -, r4, -, r6⟩` from `(hO.reps ()).1 k`.

Establish `hcj` using `(GlobalTheory.ClassScalarCompare.latPin_iff_conjLat _ _).1 (hO.reps ()).2 k`. Establish `g` using `GlobalTheory.ClassScalarCompare.guard_conjLat (H := T.Q.H) (L := (O.La () k).La) ⟨r1, r2, r6⟩`. Rewrite `g` using `[hcj, GlobalTheory.ClassScalarCompare.conjLat_conjLat]`. Establish `hpq : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q` using `(hT.laws.unf _ ⟨Nat.le_add_left _ _, i.2⟩ _ T.toCore.good_σ₀).1`. Establish `hbar : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E)` using `RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)`.

Take `⟨cc, c0, c1, c2, c3, c4, ⟨z, z1, z2⟩, x1⟩` from `exists_ideal_conj (Vc D i) hO.lift.std.1 hO.lift.std.2 (h k) e P x he hs hx (O.bad ()) hP _ _ (GlobalTheory.ClassScalarValue.chrEq_mul_inv (hL.mu0 i) (hL.xi A.μ0) hL.eta) (fun Q hQ x hx => by`. Establish `a1 : (R.C.mu0 i).UnrAt Q` using `(R.C.isMu0 i).unr Q fun j hj => hQ (by`. Take `⟨u, hu⟩` from `(Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ j)).trans ((Fin.prod_univ_two D.host.g).symm ▸ (hO.bad ()).2.2.2.2)`. Rewrite using `[hu, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hj)`.

Establish `a2 : (R.xiH A.μ0).UnrAt Q`. Assume the negation of the conclusion as `hn`. Break down `(hL.Q_ram A.μ0 Q).1 hn with a | ⟨Q', a, a'⟩` into its components or cases. Conclude with `hQ (hbad Q (Or.inr a))`. Rewrite `hQ` using `[(GlobalTheory.IdemSupport.isConjPl_iff _ _).1 a', GlobalTheory.IdemSupport.mem_cP, map_natCast]`.

Conclude with `hQ (hbad Q' (Or.inr a))`. Rewrite using `[Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, a1 x hx, a2 x hx, R.C.isEta.unr Q x hx, inv_one, one_mul, one_mul])`. Use the proof step `(fun Q hQ x => by`. Rewrite using `[Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv, (R.C.isMu0 i).triv.1, (hL.xi_triv A.μ0).1, R.C.isEta.res.1, Formalism.L2.Host.etaFin, GlobalTheory.ClassScalarValue.above_eq, Finset.card_pair hQ.symm, if_neg (by norm_num …`. Use `σ R.eta η' hch.1.2.1 hη`.

Rewrite `c1`, `c3` using `[← hbar]`. Rewrite `c3` using `[← hLh]`. Take `⟨q, q0, q1, q2⟩` from `(hO.ep ()).2 (O.Lh () k) cc g.1 g.2.1 g.2.2 c1 c3`. Establish `hB` using `(hO.tuple ()).B cc c0 c2`. Take `⟨w, w1, w2⟩` from `hμ.2.2.2.1 x x1`.

Establish `hjL : O.B () cc = O.jL (algebraMap T.Q.c.F D.what₂.LL w * z)`. Use `(inC O.c').injective ?_` and prove the remaining obligations. Establish `hf` using `RingHom.congr_fun hO.lift.field (algebraMap T.Q.c.F D.what₂.LL w * z)`. Use `hB.trans (Eq.trans ?_ hf.symm)` and prove the remaining obligations. Establish `hxi : R.xi A.μ0 x = 1` using `by rw [hch.2.1]; rfl`.

Rewrite using `[map_mul, ← w1, z1, ← c4]`. Use `show ((R.mu0 ((i : ℕ) + 1) x * R.xi A.μ0 x * (R.eta x)⁻¹ : Circle) : ℂ) * _ = _`. Rewrite using `[hxi, mul_one, Circle.coe_mul, Circle.coe_inv, mul_assoc]`. Establish `hσB : σ' (O.B () cc) = (((μ' * η'⁻¹) x : Circle) : ℂ) * ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ)`. Rewrite using `[hjL]`.

Use `(RingHom.congr_fun hσ (algebraMap T.Q.c.F D.what₂.LL w * z)).trans ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← w2, z2, MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv, mul_assoc]`. Establish `hi` using `GlobalTheory.ClassScalarCompare.stdIndex_conjLat (O.Lh () k)`. Rewrite `hi` using `[← hcj]`. Rewrite `q1` using `[← hpq, ← Nat.cast_pow]`.

Use `GlobalTheory.ClassScalarValue.value_calc (x := (((μ' * η'⁻¹) x : Circle) : ℂ)) q0 (fun h0 => c0 (Ideal.absNorm_eq_zero_iff.1 h0)) (GlobalTheory.ClassScalarValue.mIdx_ne_zero (O.La () k) D.R.r (fun h0 : O.Nc () k = 0 => by simpa [h0] using r4.1)) q1` as an intermediate fact. Rewrite using `[Circle.coe_inv, (hO.ep ()).1 k, q2, GlobalTheory.ClassScalarValue.zCard_eq _ _ _ r4.2.2, map_mul, map_mul, map_mul, map_inv₀, map_inv₀, hσB, map_ratCast, map_natCast, map_natCast]`. Establish `hi' : ((O.La () k).Ln.toAddSubgroup.addSubgroupOf (O.La () k).La.toAddSubgroup).index = ((O.Lh () k ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf (O.Lh () k).toAddSubgroup).index` using `hi`. Rewrite `this` using `[← hi']`. Rewrite using `[← GenLatCmp.std_eq]`.

Conclude with `this`.
-/
theorem class_scalar_conj_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → FWTie T R κ v₀ → ∀ (i : Fin D.R.m) (O : OM T R i), Pinned κ v₀ O → ∀ (σ : D.what₂.LL →+* ℂ) (σ' : O.c'.F →+* ℂ), σ'.comp O.jL = σ → ∀ μ' η' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → IsEtaConj σ R.eta η' → ∀ (h : O.Cl' () → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ()) → ∀ k, (O.La () k).La ∈ Vset D.host.E (Vc D i).rank 1 ∧ GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmtC (Vc D i) (h k)) (stdL D.host.E (Vc D i).rank) (O.La () k).La ∧ ∃ (e : AE D) (P : Finset (Pl D.host.E)) (x : (AE D)ˣ), IsIdemSum e P ∧ SuppAt e (Vc D i) (h k) ∧ IsDetAt e (Vc D i) (h k) x ∧ σ' (O.ep () k * (((O.La () k).mIdx (O.Nc () k) D.R.r : O.c'.F))⁻¹ * ((O.La () k).zCard (O.Nc () k) D.R.r : O.c'.F)) = ((((μ' * η'⁻¹) x)⁻¹ : Circle) : ℂ) * ((Real.sqrt ((((((O.La () k).La ⊓ stdL D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf (O.La () k).La.toAddSubgroup).index ^ D.R.r : ℕ) : ℝ)) : ℝ) : ℂ) := by
  classical
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC tie i O hO σ σ' hσ μ' η' hμ hη h J' hR k
  have hcl := GlobalTheory.OneMapRef.ClassScalar.class_lattice_scalar_ofFive D G Pl0 T0 A T R F κ v₀ hC ⟨tie⟩ i Unit (fun _ => A.μ0) O hO () h J' hR k
  have hT : TieIn T R κ v₀ := ⟨tie.laws, tie.alg_eq, tie.kap, tie.hv₀, tie.chiR, tie.x0⟩
  have hL := hC.lev
  have hch := GlobalTheory.OneMapRef.chars_of_lift_ofFive D G Pl0 T0 A T.Q.c.F R F hC i
  obtain ⟨-, hbad, -, -, -, -, hk⟩ := hR
  obtain ⟨⟨-, e, P, he, hP, hs⟩, hLh, -⟩ := hk k
  obtain ⟨x, hx⟩ := GlobalTheory.OneMapRef.ClassScalar.exists_isDetAt (GlobalTheory.PlaceDatum.idemSum_mul_self he) (Vc D i) (h k)
  refine ⟨hcl.1, hcl.2.1, e, P, x, he, hs, hx, ?_⟩
  obtain ⟨r1, r2, -, r4, -, r6⟩ := (hO.reps ()).1 k
  have hcj := (GlobalTheory.ClassScalarCompare.latPin_iff_conjLat _ _).1 (hO.reps ()).2 k
  have g := GlobalTheory.ClassScalarCompare.guard_conjLat (H := T.Q.H) (L := (O.La () k).La) ⟨r1, r2, r6⟩
  rw [hcj, GlobalTheory.ClassScalarCompare.conjLat_conjLat] at g
  have hpq : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q :=
    (hT.laws.unf _ ⟨Nat.le_add_left _ _, i.2⟩ _ T.toCore.good_σ₀).1
  have hbar : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
    RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)
  obtain ⟨cc, c0, c1, c2, c3, c4, ⟨z, z1, z2⟩, x1⟩ := exists_ideal_conj (Vc D i) hO.lift.std.1 hO.lift.std.2 (h k) e P x he hs hx
    (O.bad ()) hP _ _ (GlobalTheory.ClassScalarValue.chrEq_mul_inv (hL.mu0 i) (hL.xi A.μ0) hL.eta)
    (fun Q hQ x hx => by
      have a1 : (R.C.mu0 i).UnrAt Q := (R.C.isMu0 i).unr Q fun j hj => hQ (by
        obtain ⟨u, hu⟩ := (Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ j)).trans
          ((Fin.prod_univ_two D.host.g).symm ▸ (hO.bad ()).2.2.2.2)
        rw [hu, Nat.cast_mul]
        exact Ideal.mul_mem_right _ _ hj)
      have a2 : (R.xiH A.μ0).UnrAt Q := by
        by_contra hn
        rcases (hL.Q_ram A.μ0 Q).1 hn with a | ⟨Q', a, a'⟩
        · exact hQ (hbad Q (Or.inr a))
        · rw [(GlobalTheory.IdemSupport.isConjPl_iff _ _).1 a', GlobalTheory.IdemSupport.mem_cP, map_natCast] at hQ
          exact hQ (hbad Q' (Or.inr a))
      rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, a1 x hx, a2 x hx,
        R.C.isEta.unr Q x hx, inv_one, one_mul, one_mul])
    (fun Q hQ x => by
      rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv,
        (R.C.isMu0 i).triv.1, (hL.xi_triv A.μ0).1, R.C.isEta.res.1, Formalism.L2.Host.etaFin, GlobalTheory.ClassScalarValue.above_eq,
        Finset.card_pair hQ.symm, if_neg (by norm_num), inv_one, one_mul, one_mul])
    σ R.eta η' hch.1.2.1 hη
  rw [← hbar] at c1 c3
  rw [← hLh] at c3
  obtain ⟨q, q0, q1, q2⟩ := (hO.ep ()).2 (O.Lh () k) cc g.1 g.2.1 g.2.2 c1 c3
  have hB := (hO.tuple ()).B cc c0 c2
  obtain ⟨w, w1, w2⟩ := hμ.2.2.2.1 x x1
  have hjL : O.B () cc = O.jL (algebraMap T.Q.c.F D.what₂.LL w * z) := by
    refine (inC O.c').injective ?_
    have hf := RingHom.congr_fun hO.lift.field (algebraMap T.Q.c.F D.what₂.LL w * z)
    refine hB.trans (Eq.trans ?_ hf.symm)
    have hxi : R.xi A.μ0 x = 1 := by rw [hch.2.1]; rfl
    rw [map_mul, ← w1, z1, ← c4]
    show ((R.mu0 ((i : ℕ) + 1) x * R.xi A.μ0 x * (R.eta x)⁻¹ : Circle) : ℂ) * _ = _
    rw [hxi, mul_one, Circle.coe_mul, Circle.coe_inv, mul_assoc]
  have hσB : σ' (O.B () cc) = (((μ' * η'⁻¹) x : Circle) : ℂ) * ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ) := by
    rw [hjL]
    refine (RingHom.congr_fun hσ (algebraMap T.Q.c.F D.what₂.LL w * z)).trans ?_
    rw [map_mul, ← w2, z2, MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv, mul_assoc]
  have hi := GlobalTheory.ClassScalarCompare.stdIndex_conjLat (O.Lh () k)
  rw [← hcj] at hi
  rw [← hpq, ← Nat.cast_pow] at q1
  have := GlobalTheory.ClassScalarValue.value_calc (x := (((μ' * η'⁻¹) x : Circle) : ℂ)) q0
    (fun h0 => c0 (Ideal.absNorm_eq_zero_iff.1 h0))
    (GlobalTheory.ClassScalarValue.mIdx_ne_zero (O.La () k) D.R.r (fun h0 : O.Nc () k = 0 => by simpa [h0] using r4.1)) q1
  rw [Circle.coe_inv, (hO.ep ()).1 k, q2, GlobalTheory.ClassScalarValue.zCard_eq _ _ _ r4.2.2, map_mul, map_mul, map_mul, map_inv₀,
    map_inv₀, hσB, map_ratCast, map_natCast, map_natCast]
  have hi' : ((O.La () k).Ln.toAddSubgroup.addSubgroupOf (O.La () k).La.toAddSubgroup).index =
      ((O.Lh () k ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf (O.Lh () k).toAddSubgroup).index := hi
  rw [← hi'] at this
  rw [← GenLatCmp.std_eq]
  exact this

end GlobalTheory.GalOne.ClassConj

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.Term

open GlobalTheory.Ker GlobalTheory.TensLatMove GlobalTheory.OneMapRef.Term

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ hR tie i O hP σ σ' hσ μ' η' ω f₀ f hC`. Establish `hT : Nonempty (FWTie T R κ v₀)` using `⟨tie⟩`. Take `⟨hK, hμ, hη, hom, hvec, hθf⟩` from `hC`. Take `⟨ε₀, hε₀⟩` from `GlobalTheory.OneMapRef.FinDatum.thetaVector_eq_sum_translates_of_core_five D G Pl0 T0 A T R F κ v₀ hR hT i`. Take `⟨ε, hε⟩` from `GlobalTheory.GalOne.vec_eq_mean_translates_ofFive T R F κ v₀ hR tie i O hP`.

Use `⟨ε, fun h J' hrep k g' X eT g bas idx hS hp0 L hL hLG v hv a hz mk₂ hmk hm Y hY => ?_⟩` and prove the remaining obligations. Establish `hsupp` using `(hε₀ Unit (fun _ => A.μ0) O hP () k).1`. Establish `hsum` using `hε _ f₀ f hvec k`. Take `⟨hΛ, hmv, e, P, x, he, hs, hx, hval⟩` from `GlobalTheory.GalOne.ClassConj.class_scalar_conj_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ μ' η' hμ hη h J' hrep k`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hι, hLT⟩` from `FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hR hT i Unit (fun _ => A.μ0) O hP`.

Establish `hZ₀` using `(GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ hK).2.2.2.2.1`. Take `⟨LT, hLT1, hLT2, -⟩` from `hLT g'`. Rewrite `hZ₀` using `[← hp0]`. Establish `hZ` using `((oneg_frames D _ _ _ g _ _ _ X eT bas idx hS _ hZ₀).2.2.2.2 g').1`. Establish `hw : IsIntegral ℤ (T.Q.H.w0 : D.host.E)` using `T.Q.H.w0.isIntegral_coe`.

Establish `hw' : (T.Q.H.w0 : D.host.E) + cc (T.Q.H.w0 : D.host.E) = 1`. Rewrite using `[cc, ← T.Q.H.bar_eq]`. Conclude with `congrArg (fun t : 𝓞 D.host.E => (t : D.host.E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one T.Q.H)` after adjusting the coercions. Establish `hw2` using `AtRecord.isRelTraceOneIdempotentModTwo_hostElement T.Q.H`. Take `⟨hb0, hb, -, -, -, -, hrep⟩` from `hrep`.

Take `⟨⟨hfin, e', P', he', hP', hs'⟩, -⟩` from `hrep k`. Take `⟨-, -, ⟨c, hc, -, hc'⟩, ⟨-, hN, hN'⟩, -⟩` from `(hP.reps ()).1 k`. Use `replace hN' := hN'.trans inf_le_left`. Rewrite `hc'`, `hN'` using `[Formalism.L2.Pj.stdLat, FactsLat.pi_eq_stdL]`. Establish `hE` using `GlobalTheory.T.splitFinitePoint_moves_vacuum_to_projection D _ _ _ g _ _ _ X eT bas idx hS (D.sp.V_sig _) (D.sp.W_sig _) _ _ _ hom _ hw hw' hw2 _ hZ LT L hLT1 hL (hLG ▸ hLT2) e P he (h k) hfin hs x hx _ hΛ hmv v hv a _ hz`.

Use `⟨Const.isSB_gphi idx hS.2.2.2.2.2.2.2 hS.2.2.2.1 hw hw' hL hΛ hv.1 _ _, ?_⟩` and prove the remaining obligations. Take `⟨Y₀, hY₀⟩` from `DualMark.exists_roots (L := LinearMap.range (T.iota ((i : ℕ) + 1))) (O.dδ ()).l₂ ((ε : ℤ) • (T.iota ((i : ℕ) + 1)).rangeRestrict) (Vc D i).rank (O.dδ ()).l₂.M (Nat.pos_of_ne_zero (DualMark.level_ne _))`. Use `replace hY₀ : IsRoots (O.dδ ()).l₂ (LinearMap.range (T.iota ((i : ℕ) + 1))) ((ε : ℤ) • T.iota ((i : ℕ) + 1)) (O.dδ ()).l₂.M Y₀ := hY₀`. Establish `hmul (p p' : GA D (Vc D i) × GA D (Wc D i)) (u) : ω p (ω p' u) = ω (p * p') u` using `by rw [map_mul]; rfl`. Establish `hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) f₀`.

Use `hom.om_pres (1, g')⁻¹ _ hz.1` as an intermediate fact. Rewrite `this` using `[hmul, inv_mul_cancel, map_one]`. Then use the resulting hypothesis. Establish `hsp : ω (h k, g') f₀ = ω (h k, 1) (ω (1, g') f₀)`. Rewrite using `[hmul, Prod.mk_mul_mk, mul_one, one_mul]`. Establish `hBP : ((O.bad () ^ (R.Pg.card + (R.Q A.μ0).card) : ℕ) : 𝓞 D.host.E) ∈ (∏ PP ∈ R.Pg, PP.asIdeal) * ∏ PP ∈ R.Q A.μ0, PP.asIdeal`.

Rewrite using `[Nat.cast_pow, pow_add, ← Finset.prod_const, ← Finset.prod_const]`. Conclude with `Ideal.mul_mem_mul (Ideal.prod_mem_prod fun PP h => hb PP (Or.inl h)) (Ideal.prod_mem_prod fun PP h => hb PP (Or.inr h))`. Establish `hq` using `fun q (h0 : O.w () k q ≠ 0) => heis_root_zak (rank_Wc i) hS (isWeak_of_datum hom) hw hw' hw2 hZ hΛ hmv hL hLG hv hz hι hmk hm hN hN' hc hc' (pow_ne_zero (R.Pg.card + (R.Q A.μ0).card) hb0) he' (fun PP h h' => hP' PP h (PP.isPrime.mem_of_pow_mem _ (by rwa [Nat.cast_pow] at h'))) hs …`. Use `haveI : Finite (LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) := LevelPairing.finite_LevQ`. Use `haveI := Fintype.ofFinite (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂)`.

Establish `hsb : SW.IsSB (projA X bas (T.Q.H.w0 : D.host.E) (tens (O.La () k).La L) v)`. Take `⟨⟨v', hv'⟩, -, h, -⟩` from `TensVac.vacua _ _ X g bas idx _ hS.2.2.2.2.2.2.2 hS.2.2.2.1 _ hw hw' L hL 1 _ hΛ`. Rewrite using `[h v hv.1 v' hv']`. Conclude with `Const.isSB_smul_tf _ hv'.1`. Rewrite `hE` using `[mul_assoc a, ← hval]`.

Establish `key` using `zak_sum hS hZ (Const.isSB_smul_tf _ hsb) hE (fun q => inC O.c' (O.w () k q)) Y ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) : ℕ) : ℂ)⁻¹`. Rewrite using `[hsum _ (Nat.pos_of_ne_zero (DualMark.level_ne _)) dvd_rfl Y₀ hY₀, map_smul, gphi, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]`. Use `key using 1` and compare the differences between its conclusion and the goal. Establish `sw (s : ℂ) (c : _ → ℂ) (φ : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) → TF (Vc D i).rank g) : ∑ q, c q • s • φ q = s • ∑ q, c q • φ q`. Rewrite using `[Finset.smul_sum]`.

Conclude with `Finset.sum_congr rfl fun q _ => smul_comm _ _ _`. Simplify using `only [heisG_smul]`. Rewrite using `[sw, smul_smul]`. Use `congr 1`. Simplify using `only [map_mul, map_inv₀, map_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Use `congrArg _ (Finset.sum_congr rfl fun q _ => ?_)` and prove the remaining obligations. Distinguish the cases in `h0 : O.w () k q = 0`. Rewrite using `[h0, map_zero, zero_smul, zero_smul, map_zero]`. Rewrite using `[map_smul, hom.om_heis _ _ _ _ hth, hsp, hq q h0]`.
-/
theorem zak_class_term_conj_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → FWTie T R κ v₀ → ∀ (i : Fin D.R.m) (O : OM T R i), Pinned κ v₀ O → ∀ (σ : D.what₂.LL →+* ℂ) (σ' : O.c'.F →+* ℂ), σ'.comp O.jL = σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ), ConjW R i σ μ' η' ω f₀ f → ∃ ε : ℤˣ, TermAt O σ σ' ω f₀ f ε := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR tie i O hP σ σ' hσ μ' η' ω f₀ f hC
  have hT : Nonempty (FWTie T R κ v₀) := ⟨tie⟩
  obtain ⟨hK, hμ, hη, hom, hvec, hθf⟩ := hC
  obtain ⟨ε₀, hε₀⟩ := GlobalTheory.OneMapRef.FinDatum.thetaVector_eq_sum_translates_of_core_five D G Pl0 T0 A T R F κ v₀ hR hT i
  obtain ⟨ε, hε⟩ := GlobalTheory.GalOne.vec_eq_mean_translates_ofFive T R F κ v₀ hR tie i O hP
  refine ⟨ε, fun h J' hrep k g' X eT g bas idx hS hp0 L hL hLG v hv a hz mk₂ hmk hm Y hY => ?_⟩
  have hsupp := (hε₀ Unit (fun _ => A.μ0) O hP () k).1
  have hsum := hε _ f₀ f hvec k
  obtain ⟨hΛ, hmv, e, P, x, he, hs, hx, hval⟩ := GlobalTheory.GalOne.ClassConj.class_scalar_conj_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ μ' η' hμ hη h J' hrep k
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hι, hLT⟩ :=
    FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hR hT i Unit (fun _ => A.μ0) O hP
  have hZ₀ := (GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ hK).2.2.2.2.1
  obtain ⟨LT, hLT1, hLT2, -⟩ := hLT g'
  rw [← hp0] at hZ₀
  have hZ := ((oneg_frames D _ _ _ g _ _ _ X eT bas idx hS _ hZ₀).2.2.2.2 g').1
  have hw : IsIntegral ℤ (T.Q.H.w0 : D.host.E) := T.Q.H.w0.isIntegral_coe
  have hw' : (T.Q.H.w0 : D.host.E) + cc (T.Q.H.w0 : D.host.E) = 1 := by
    rw [cc, ← T.Q.H.bar_eq]
    exact_mod_cast congrArg (fun t : 𝓞 D.host.E => (t : D.host.E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one T.Q.H)
  have hw2 := AtRecord.isRelTraceOneIdempotentModTwo_hostElement T.Q.H
  obtain ⟨hb0, hb, -, -, -, -, hrep⟩ := hrep
  obtain ⟨⟨hfin, e', P', he', hP', hs'⟩, -⟩ := hrep k
  obtain ⟨-, -, ⟨c, hc, -, hc'⟩, ⟨-, hN, hN'⟩, -⟩ := (hP.reps ()).1 k
  replace hN' := hN'.trans inf_le_left
  rw [Formalism.L2.Pj.stdLat, FactsLat.pi_eq_stdL] at hc' hN'
  have hE := GlobalTheory.T.splitFinitePoint_moves_vacuum_to_projection D _ _ _ g _ _ _ X eT bas idx hS (D.sp.V_sig _) (D.sp.W_sig _) _ _ _ hom _ hw hw' hw2 _ hZ LT L
    hLT1 hL (hLG ▸ hLT2) e P he (h k) hfin hs x hx _ hΛ hmv v hv a _ hz
  refine ⟨Const.isSB_gphi idx hS.2.2.2.2.2.2.2 hS.2.2.2.1 hw hw' hL hΛ hv.1 _ _, ?_⟩
  obtain ⟨Y₀, hY₀⟩ := DualMark.exists_roots (L := LinearMap.range (T.iota ((i : ℕ) + 1))) (O.dδ ()).l₂
    ((ε : ℤ) • (T.iota ((i : ℕ) + 1)).rangeRestrict) (Vc D i).rank (O.dδ ()).l₂.M
    (Nat.pos_of_ne_zero (DualMark.level_ne _))
  replace hY₀ : IsRoots (O.dδ ()).l₂ (LinearMap.range (T.iota ((i : ℕ) + 1))) ((ε : ℤ) • T.iota ((i : ℕ) + 1))
    (O.dδ ()).l₂.M Y₀ := hY₀
  have hmul (p p' : GA D (Vc D i) × GA D (Wc D i)) (u) : ω p (ω p' u) = ω (p * p') u := by rw [map_mul]; rfl
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) f₀ := by
    have := hom.om_pres (1, g')⁻¹ _ hz.1
    rwa [hmul, inv_mul_cancel, map_one] at this
  have hsp : ω (h k, g') f₀ = ω (h k, 1) (ω (1, g') f₀) := by
    rw [hmul, Prod.mk_mul_mk, mul_one, one_mul]
  have hBP : ((O.bad () ^ (R.Pg.card + (R.Q A.μ0).card) : ℕ) : 𝓞 D.host.E) ∈
      (∏ PP ∈ R.Pg, PP.asIdeal) * ∏ PP ∈ R.Q A.μ0, PP.asIdeal := by
    rw [Nat.cast_pow, pow_add, ← Finset.prod_const, ← Finset.prod_const]
    exact Ideal.mul_mem_mul (Ideal.prod_mem_prod fun PP h => hb PP (Or.inl h))
      (Ideal.prod_mem_prod fun PP h => hb PP (Or.inr h))
  have hq := fun q (h0 : O.w () k q ≠ 0) => heis_root_zak (rank_Wc i) hS (isWeak_of_datum hom) hw hw' hw2 hZ hΛ hmv hL hLG
    hv hz hι hmk hm hN hN' hc hc' (pow_ne_zero (R.Pg.card + (R.Q A.μ0).card) hb0) he'
    (fun PP h h' => hP' PP h (PP.isPrime.mem_of_pow_mem _ (by rwa [Nat.cast_pow] at h'))) hs' hY₀ hY
    (fun b => hsupp q h0 b _ hBP)
  haveI : Finite (LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) := LevelPairing.finite_LevQ
  haveI := Fintype.ofFinite (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂)
  have hsb : SW.IsSB (projA X bas (T.Q.H.w0 : D.host.E) (tens (O.La () k).La L) v) := by
    obtain ⟨⟨v', hv'⟩, -, h, -⟩ :=
      TensVac.vacua _ _ X g bas idx _ hS.2.2.2.2.2.2.2 hS.2.2.2.1 _ hw hw' L hL 1 _ hΛ
    rw [h v hv.1 v' hv']
    exact Const.isSB_smul_tf _ hv'.1
  rw [mul_assoc a, ← hval] at hE
  have key := zak_sum hS hZ (Const.isSB_smul_tf _ hsb) hE (fun q => inC O.c' (O.w () k q)) Y
    ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) : ℕ) : ℂ)⁻¹
  rw [hsum _ (Nat.pos_of_ne_zero (DualMark.level_ne _)) dvd_rfl Y₀ hY₀, map_smul, gphi, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, map_sum]
  convert key using 1
  · have sw (s : ℂ) (c : _ → ℂ)
        (φ : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) → TF (Vc D i).rank g) :
        ∑ q, c q • s • φ q = s • ∑ q, c q • φ q := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun q _ => smul_comm _ _ _
    simp only [heisG_smul]
    rw [sw, smul_smul]
    congr 1
    simp only [map_mul, map_inv₀, map_natCast]
    ring
  · refine congrArg _ (Finset.sum_congr rfl fun q _ => ?_)
    by_cases h0 : O.w () k q = 0
    · rw [h0, map_zero, zero_smul, zero_smul, map_zero]
    · rw [map_smul, hom.om_heis _ _ _ _ hth, hsp, hq q h0]

end GlobalTheory.GalOne.Term

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT i O hO σ σ' _`. Use `(GlobalTheory.OneMapRefCompare.cover_const O (κ i) _ hT.laws hR.lev hO).elim fun u hu => ?_` and prove the remaining obligations. Use `⟨σ' u, ?_, fun _ => ?_⟩` and prove the remaining obligations. Conclude with `hu.1.elim fun m hm => Complex.norm_eq_one_of_pow_eq_one ((map_pow σ' u m).symm.trans ((congrArg σ' hm.2).trans (map_one σ'))) hm.1.ne'`. Set `_ : Algebra (O.dδ ()).c₂.F ℂ` to `(σ'.comp ((O.dδ ()).eF.symm : (O.dδ ()).c₂.F →+* O.c'.F)).toAlgebra`.

Introduce `y₂`. Use `(congrArg (fun f => evR (O.dδ ()).Xo₂ (O.dδ ()).c₂ f y₂) hu.2).trans ?_` and prove the remaining obligations. Use `(GlobalTheory.OneMapRefCompare.evR_smul _ _ y₂).trans ?_` and prove the remaining obligations. Use `(congrArg (_ * ·) (GlobalTheory.OneMapRefCompare.evR_one y₂)).trans ((_root_.mul_one _).trans ?_)` and prove the remaining obligations. Conclude with `congrArg σ' ((O.dδ ()).eF.symm_apply_apply u)`.
-/
theorem cover_const_at_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → FWTie T R κ v₀ → ∀ (i : Fin D.R.m) (O : OM T R i), Pinned κ v₀ O → ∀ (σ : D.what₂.LL →+* ℂ) (σ' : O.c'.F →+* ℂ), σ'.comp O.jL = σ → ∃ c0 : ℂ, ‖c0‖ = 1 ∧ (OverK σ → CovAt O σ' c0) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT i O hO σ σ' _
  refine (GlobalTheory.OneMapRefCompare.cover_const O (κ i) _ hT.laws hR.lev hO).elim fun u hu => ?_
  refine ⟨σ' u, ?_, fun _ => ?_⟩
  · exact hu.1.elim fun m hm => Complex.norm_eq_one_of_pow_eq_one
      ((map_pow σ' u m).symm.trans ((congrArg σ' hm.2).trans (map_one σ'))) hm.1.ne'
  · let _ : Algebra (O.dδ ()).c₂.F ℂ := (σ'.comp ((O.dδ ()).eF.symm : (O.dδ ()).c₂.F →+* O.c'.F)).toAlgebra
    intro y₂
    refine (congrArg (fun f => evR (O.dδ ()).Xo₂ (O.dδ ()).c₂ f y₂) hu.2).trans ?_
    refine (GlobalTheory.OneMapRefCompare.evR_smul _ _ y₂).trans ?_
    refine (congrArg (_ * ·) (GlobalTheory.OneMapRefCompare.evR_one y₂)).trans ((_root_.mul_one _).trans ?_)
    exact congrArg σ' ((O.dδ ()).eF.symm_apply_apply u)

end GlobalTheory.GalOne

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

end Gen

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ hR _ i O hP σ'`. Establish `hQ : R.Q A.μ0 = ∅` using `(chars_of_lift_ofFive D G Pl0 T0 A _ R F hR i).2.2.1`. Establish `hq : ∀ {a b : ℕ} (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) r ξ k y, Q = ∅ → omegaQ (D` using `D) (a := a) (b := b) Q r ξ k y = 1 := by`. Introduce and unpack `a b _ r ξ k y rfl`. Rewrite using `[omegaQ, dif_pos (fun _ h => absurd h (Finset.notMem_empty _))]`.

Simplify using the standard rewrite rules. Establish `hk : ∀ {a b : ℕ} (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) y, omegaK (D` using `D) (a := a) (b := b) Q y = 0 ∨ omegaK (D := D) (a := a) (b := b) Q y = 1 := by`. Introduce `a b Q y`. Unfold `omegaK`. Use `split_ifs`.

Use `exacts [Or.inr rfl, Or.inl rfl]`. Establish `hφ : ∀ x, O.φ () x = 0 ∨ O.φ () x = 1` using `fun x => (hP.tuple ()).phi.elim fun e he => by`. Establish `hx : x = fun b => Submodule.Quotient.mk (qRep (x b))`. Use function extensionality and compare the values at `fun b => (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (x b))).symm`. Establish `h` using `((congrArg (fun y => inC O.c' (O.φ () y)) hx).trans (he.2 _).2).trans ((congrArg (HMul.hMul _) (hq _ _ _ _ _ hQ)).trans (mul_one _))`.

Conclude with `(hk _ _).imp (fun h' => (map_eq_zero_iff _ (inC O.c').injective).1 (h.trans h')) fun h' => (map_eq_one_iff _ (inC O.c').injective).1 (h.trans h')`. Use `(map_phiHat (Dw := T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).c₂ (σ'.comp ((O.dδ ()).eF.symm : (O.dδ ()).c₂.F →+* O.c'.F))).imp fun m hm => ⟨hm.1, fun k q => ?_⟩` and prove the remaining obligations. Establish `h` using `hm.2 _ (fun x => (O.dδ ()).eF (O.φ () x)) (fun x => (hφ x).imp (fun h => by rw [h, map_zero]) fun h => by rw [h, map_one]) q`. Establish `h1` using `congrArg (σ'.comp ((O.dδ ()).eF.symm : (O.dδ ()).c₂.F →+* O.c'.F)) (hP.w () k q)`. Establish `h2` using `congrArg (inC (O.dδ ()).c₂) (hP.w () k (m • q))`.

Conclude with `((congrArg σ' ((O.dδ ()).eF.symm_apply_apply _).symm).trans h1).trans (h.trans h2.symm)`.
-/
theorem conj_coeff_eq_dilate_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → FWTie T R κ v₀ → ∀ (i : Fin D.R.m) (O : OM T R i), Pinned κ v₀ O → ∀ σ' : O.c'.F →+* ℂ, ∃ m : ℤ, IsCoprime m ((O.dδ ()).l₂.M : ℤ) ∧ ∀ k q, σ' (O.w () k q) = inC O.c' (O.w () k (m • q)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR _ i O hP σ'
  have hQ : R.Q A.μ0 = ∅ := (chars_of_lift_ofFive D G Pl0 T0 A _ R F hR i).2.2.1
  have hq : ∀ {a b : ℕ} (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) r ξ k y, Q = ∅ → omegaQ (D := D) (a := a) (b := b) Q r ξ k y = 1 := by
    rintro a b _ r ξ k y rfl
    rw [omegaQ, dif_pos (fun _ h => absurd h (Finset.notMem_empty _))]
    simp
  have hk : ∀ {a b : ℕ} (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) y,
      omegaK (D := D) (a := a) (b := b) Q y = 0 ∨ omegaK (D := D) (a := a) (b := b) Q y = 1 := by
    intro a b Q y
    unfold omegaK
    split_ifs
    exacts [Or.inr rfl, Or.inl rfl]
  have hφ : ∀ x, O.φ () x = 0 ∨ O.φ () x = 1 := fun x => (hP.tuple ()).phi.elim fun e he => by
    have hx : x = fun b => Submodule.Quotient.mk (qRep (x b)) :=
      funext fun b => (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (x b))).symm
    have h := ((congrArg (fun y => inC O.c' (O.φ () y)) hx).trans (he.2 _).2).trans
      ((congrArg (HMul.hMul _) (hq _ _ _ _ _ hQ)).trans (mul_one _))
    exact (hk _ _).imp (fun h' => (map_eq_zero_iff _ (inC O.c').injective).1 (h.trans h'))
      fun h' => (map_eq_one_iff _ (inC O.c').injective).1 (h.trans h')
  refine (map_phiHat (Dw := T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).c₂
    (σ'.comp ((O.dδ ()).eF.symm : (O.dδ ()).c₂.F →+* O.c'.F))).imp fun m hm => ⟨hm.1, fun k q => ?_⟩
  have h := hm.2 _ (fun x => (O.dδ ()).eF (O.φ () x))
    (fun x => (hφ x).imp (fun h => by rw [h, map_zero]) fun h => by rw [h, map_one]) q
  have h1 := congrArg (σ'.comp ((O.dδ ()).eF.symm : (O.dδ ()).c₂.F →+* O.c'.F)) (hP.w () k q)
  have h2 := congrArg (inC (O.dδ ()).c₂) (hP.w () k (m • q))
  exact ((congrArg σ' ((O.dδ ()).eF.symm_apply_apply _).symm).trans h1).trans (h.trans h2.symm)

end GlobalTheory.GalOne

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalCentral

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

end Res

variable {D : D7}

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ hR tie i O hO m hm`. Establish `hT` using `tie.laws`. Establish `hL` using `hR.lev`. Establish `hβ` using `hL.βW i`. Establish `hι` using `GlobalTheory.LevelAction.latEmb_iotaW T hT i`.

Establish `hMb : T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal` using `(hO.tuple ()).half.1`. Establish `hp : T.Q.l.Mb * Mfr T.Q.l = Ideal.span {((T.Q.l.M : ℕ) : 𝓞 D.host.E)}` using `T.Q.l.prod`. Establish `hp' : (∏ PP ∈ R.Pg, PP.asIdeal) * Mfr T.Q.l = Ideal.span {((T.Q.l.M : ℕ) : 𝓞 D.host.E)}` using `by rw [← hMb]; exact hp`. Establish `hM0 : 0 < T.Q.l.M` using `lt_of_lt_of_le (by norm_num) T.Q.l.three_le`. Establish `hu : ∀ P : R.Pg, IsUnit ((m : ℤ) : kP P.1)` using `fun P => isUnit_of_coprime hm (cast_res R.Pg hp' P.2)`.

Take `⟨z, hz⟩` from `R.eG.surjective fun P => scalGL D.R.r (hu P)`. Use `⟨z, Subgroup.mem_center_iff.2 fun g => R.eG.injective ?_, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[R.eG.map_mul, R.eG.map_mul, hz]`. Use function extensionality and compare the values at `P`. Conclude with `scalGL_comm (hu P) (R.eG g P)`.

Take `⟨k, hk, hf⟩` from `hO.lift.lev z`. Establish `hr` using `redFn_int (L := R.datWp i R.triv) (rank_Wc i) hk m (fun P => (congrArg Units.val (congrFun hz P)).trans (scalGL_val _ (hu P)))`. Take `⟨w₃, hw₃, e₃⟩` from `GlobalTheory.OneMapRef.Lift.cong_on_half hι (fun b hb => exists_cong_int (b := b) hβ R.Pg hp' (parLev_St hk.2.1) m hr hb) a ha`. Take `⟨w₂, hw₂, e₂⟩` from `hf a ha`. Conclude with `GlobalTheory.OneMapRef.Lift.sign_div hι hM0 (add_mem hw₂ hw₃) (int_calc e₂ e₃)`.
-/
theorem central_lev_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → FWTie T R κ v₀ → ∀ (i : Fin D.R.m) (O : OM T R i), Pinned κ v₀ O → ∀ m : ℤ, IsCoprime m (T.Q.l.M : ℤ) → ∃ z ∈ Subgroup.center G, ∀ a ∈ Mfr T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La), ∃ b : (T.Q.Dw ((i : ℕ) + 1)).La, O.lev z a = m • a + T.Q.l.M • b := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR tie i O hO m hm
  have hT := tie.laws
  have hL := hR.lev
  have hβ := hL.βW i
  have hι := GlobalTheory.LevelAction.latEmb_iotaW T hT i
  have hMb : T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal := (hO.tuple ()).half.1
  have hp : T.Q.l.Mb * Mfr T.Q.l = Ideal.span {((T.Q.l.M : ℕ) : 𝓞 D.host.E)} := T.Q.l.prod
  have hp' : (∏ PP ∈ R.Pg, PP.asIdeal) * Mfr T.Q.l = Ideal.span {((T.Q.l.M : ℕ) : 𝓞 D.host.E)} := by rw [← hMb]; exact hp
  have hM0 : 0 < T.Q.l.M := lt_of_lt_of_le (by norm_num) T.Q.l.three_le
  have hu : ∀ P : R.Pg, IsUnit ((m : ℤ) : kP P.1) := fun P => isUnit_of_coprime hm (cast_res R.Pg hp' P.2)
  obtain ⟨z, hz⟩ := R.eG.surjective fun P => scalGL D.R.r (hu P)
  refine ⟨z, Subgroup.mem_center_iff.2 fun g => R.eG.injective ?_, fun a ha => ?_⟩
  · rw [R.eG.map_mul, R.eG.map_mul, hz]
    funext P
    exact scalGL_comm (hu P) (R.eG g P)
  · obtain ⟨k, hk, hf⟩ := hO.lift.lev z
    have hr := redFn_int (L := R.datWp i R.triv) (rank_Wc i) hk m
      (fun P => (congrArg Units.val (congrFun hz P)).trans (scalGL_val _ (hu P)))
    obtain ⟨w₃, hw₃, e₃⟩ := GlobalTheory.OneMapRef.Lift.cong_on_half hι (fun b hb => exists_cong_int (b := b) hβ R.Pg hp'
      (parLev_St hk.2.1) m hr hb) a ha
    obtain ⟨w₂, hw₂, e₂⟩ := hf a ha
    exact GlobalTheory.OneMapRef.Lift.sign_div hι hM0 (add_mem hw₂ hw₃) (int_calc e₂ e₃)

end GlobalTheory.GalCentral

end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m}

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Substitute `hk` using the available equality. Establish `hn` using `(FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hR ⟨tie⟩ i _ _ O hP).2.2.1`. Establish `hZ` using `hF.2.2.2.2.1`. Establish `hH` using `fun k => io_mem O hP (x k)`. Use `(Finset.mul_sum _ _ _).trans ((Finset.sum_congr rfl fun j _ => ?_).trans (Finset.mul_sum _ _ _).symm)` and prove the remaining obligations.

Use `(hioc (x₁ j) (x j) (hx j)).elim fun Q hQQ => ?_` and prove the remaining obligations. Establish `hQ` using `hQQ.1`. Establish `hQ'` using `hQQ.2`. Establish `hT` using `hterm h J' hreps j (γ * k₀) X eT g Dc.bas Dc.idx hS hp0 _ hsd hlat v hv _ hzak mk₂ hmk₂ hma₂ (Y j) (hY j)`. Establish `hsb` using `hT.1`.

Establish `hzk` using `hT.2`. Establish `h5` using `kernel_value hS hC.2.2.2.1 hp0 hZ (hreps.2.2.2.2.2.2 j).1.1 hγ k₀ hC.2.2.2.2.2 Q ((isSB_algebra_haar_linear ℚ _ _ _ _ hsb hsb).2.1 _) hzk Dc.hr`. Establish `h6 : ∀ φ : TF (Vc D i).rank g, ∀ x', ph * thP X Dc.hr Dc.bas Dc.idx φ (toP (Vc D i) (rank_Wc i) eT Dc.hr Q) x' = (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * thP X Dc.hr Dc.bas Dc.idx φ (MvPolynomial.rename Dc.eL (MvPolynomial.map σ' (O.io (x j)))) x'` using `fun φ x' => by`. Rewrite using `[thP, thP, ← I2.polyDeriv_smul, ← I2.polyDeriv_smul, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, hQ' _ eT g Dc hS.2.2.2.2.2.2.1]`. Establish `h7` using `(congrArg (ph * ·) h5).trans (h6 _ _)`.

Rewrite `h7` using `[ShortRead.theta_smul₂ Dc.hr Dc.idx Dc.sympl hn hsb (Dc.mem _ (hH j)) hdom]`. Establish `h9 : gphi X Dc.bas (T.Q.H.w0 : D.host.E) (O.La () j).La X.Λ v (fun q => σ' (O.w () j q)) (fun q => Y j (m • q)) = gphi X Dc.bas (T.Q.H.w0 : D.host.E) (O.La () j).La X.Λ v (fun q => inC O.c' (O.w () j q)) (Y j)`. Rewrite using `[funext (hw j)]`. Conclude with `((GlobalTheory.T.marking_roots_dilation_coprime_level _ _ _ (O.dδ ()).l₂ _ _ X.Λ mk₂ m hm).2 0 (Y j)).2 g X Dc.bas _ _ v fun q => inC O.c' (O.w () j q)`. Rewrite using `[hQ, h9]`.

Simplify using `only [map_mul] at h7 ⊢`. Take the linear combination `(σ' (O.vol ()) * σ' ((O.gam () j : O.c'.F))⁻¹) * h7`.
-/
theorem adelic_value_ofFive (hR : GlobalTheory.Core5 R F) (tie : FWTie T R κ v₀) (O : OM T R i) (hP : Pinned κ v₀ O)
    {σ : D.what₂.LL →+* ℂ} {σ' : O.c'.F →+* ℂ} (hF : FactsAt O σ σ') {μ' η' : (AE D)ˣ →* Circle}
    {ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)} {f₀ f : WO (Vc D i) (Wc D i) → ℂ}
    (hC : ConjW R i σ μ' η' ω f₀ f)
    {X : Data D.host.E D.R.r} {eT : D.what₂.Tau ≃ X.Ψ} {g : ℕ}
    (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' σ' X g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i)))
    (hS : IsSet R.ψ R.θ (Vc D i) (Wc D i) (rank_Wc i) X eT Dc.bas) (hp0 : X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q) (hsd : SelfD X X.Λ)
    {k : GA D (Wc D i)} (hlat : latW (rank_Wc i) X.Λ = latG (Wc D i) k)
    {v : TF (Vc D i).rank g} (hv : IsVac X Dc.bas (T.Q.H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) X.Λ) v)
    {mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)} (hmk₂ : ∀ b, mk₂ b ∈ X.Λ)
    (hma₂ : MarkAd (rank_Wc i) (O.dδ ()).l₂ (iotaW T i) k mk₂) {ε : ℤˣ}
    {Y : O.Cl' () → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E}
    (hY : ∀ j, IsRoots (O.dδ ()).l₂ X.Λ ((ε : ℤ) • mk₂) (O.Nc () j) (Y j))
    (hdom : frOf (rank_Wc i) eT (mvZ R.θ k (zAt R i σ)) ∈ X.dom) (x : O.Cl' () → VsV D i O.c'.F)
    (hterm : TermAt O σ σ' ω f₀ f ε) {m : ℤ} (hm : IsCoprime m ((O.dδ ()).l₂.M : ℤ))
    (hw : ∀ j q, σ' (O.w () j q) = inC O.c' (O.w () j (m • q)))
    {c : CoefA (Vc D i)} {c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W} {Λ : c.W → WO (Vc D i) (Wc D i) → ℂ} {ph : ℂ}
    (hioc : IoAt κ O σ σ' c₁ f Λ ph) {x₁ : O.Cl' () → VsV D i D.what₂.LL} (hx : ∀ j, IsUp O (x₁ j) (x j))
    {h : O.Cl' () → GA D (Vc D i)} {J' : Subgroup (Bridge.Gf (Vc D i))}
    (hreps : RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ()))
    {γ k₀ : GA D (Wc D i)} (hγ : γ ∈ GQ (Wc D i)) (hk : k = γ * k₀) {a : ℂ}
    (hzak : Zak R.ψ R.θ (rank_Wc i) eT Dc.bas Dc.idx (frOf (rank_Wc i) eT (mvZ R.θ k (zAt R i σ))) (a • v) (ω (1, k) f₀)) :
    ph * ∑ j, σ' (O.vol () * ((O.gam () j : O.c'.F))⁻¹) * thetaKO ω (h j) k₀ (Λ (c₁ (x₁ j))) =
      a * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
      clsSum σ' X Dc.hr Dc.bas Dc.idx Dc.eL (O.w ()) (O.La ()) (O.Nc ()) (O.gam ()) (O.vol ()) (O.ep ())
        (fun j => O.io (x j)) X.Λ v (fun j q => Y j (m • q)) (frOf (rank_Wc i) eT (mvZ R.θ k (zAt R i σ))) := by
  subst hk
  have hn := (FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hR ⟨tie⟩ i _ _ O hP).2.2.1
  have hZ := hF.2.2.2.2.1
  have hH := fun k => io_mem O hP (x k)
  refine (Finset.mul_sum _ _ _).trans ((Finset.sum_congr rfl fun j _ => ?_).trans (Finset.mul_sum _ _ _).symm)
  refine (hioc (x₁ j) (x j) (hx j)).elim fun Q hQQ => ?_
  have hQ := hQQ.1
  have hQ' := hQQ.2
  have hT := hterm h J' hreps j (γ * k₀) X eT g Dc.bas Dc.idx hS hp0 _ hsd hlat v hv _ hzak mk₂ hmk₂
    hma₂ (Y j) (hY j)
  have hsb := hT.1
  have hzk := hT.2
  have h5 := kernel_value hS hC.2.2.2.1 hp0 hZ (hreps.2.2.2.2.2.2 j).1.1 hγ k₀ hC.2.2.2.2.2 Q
    ((isSB_algebra_haar_linear ℚ _ _ _ _ hsb hsb).2.1 _) hzk Dc.hr
  have h6 : ∀ φ : TF (Vc D i).rank g, ∀ x', ph * thP X Dc.hr Dc.bas Dc.idx φ (toP (Vc D i) (rank_Wc i) eT Dc.hr Q) x' =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * thP X Dc.hr Dc.bas Dc.idx φ
        (MvPolynomial.rename Dc.eL (MvPolynomial.map σ' (O.io (x j)))) x' := fun φ x' => by
    rw [thP, thP, ← I2.polyDeriv_smul, ← I2.polyDeriv_smul, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul,
      hQ' _ eT g Dc hS.2.2.2.2.2.2.1]
  have h7 := (congrArg (ph * ·) h5).trans (h6 _ _)
  rw [ShortRead.theta_smul₂ Dc.hr Dc.idx Dc.sympl hn hsb (Dc.mem _ (hH j)) hdom] at h7
  have h9 : gphi X Dc.bas (T.Q.H.w0 : D.host.E) (O.La () j).La X.Λ v (fun q => σ' (O.w () j q)) (fun q => Y j (m • q)) =
      gphi X Dc.bas (T.Q.H.w0 : D.host.E) (O.La () j).La X.Λ v (fun q => inC O.c' (O.w () j q)) (Y j) := by
    rw [funext (hw j)]
    exact ((GlobalTheory.T.marking_roots_dilation_coprime_level _ _ _ (O.dδ ()).l₂ _ _ X.Λ mk₂ m hm).2 0 (Y j)).2 g X Dc.bas _ _ v
      fun q => inC O.c' (O.w () j q)
  rw [hQ, h9]
  simp only [map_mul] at h7 ⊢
  linear_combination (σ' (O.vol ()) * σ' ((O.gam () j : O.c'.F))⁻¹) * h7

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Set `_ : Algebra O.c'.F ℂ` to `σ'.toAlgebra`. Set `_ : Algebra (O.dδ ()).c₂.F ℂ` to `(σ'.comp ((O.dδ ()).eF.symm : (O.dδ ()).c₂.F →+* O.c'.F)).toAlgebra`. Introduce `y B hB hrd`. Establish `hn` using `(FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hR ⟨tie⟩ i _ _ O hP).2.2.1`. Establish `hpq` using `(FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hR ⟨tie⟩ i _ _ O hP).2.2.2.2.2.2.2.2.2.2.2.1`.

Establish `hemb` using `(FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hR ⟨tie⟩ i _ _ O hP).2.2.2.2.2.2.2.2.2.2.2.2.2.1`. Establish `hj : InR D ((i : ℕ) + 1)` using `⟨Nat.le_add_left _ _, i.2⟩`. Take `⟨hlev, hA₂, hnab⟩` from `hP.cov ()`. Take `⟨him, -, hov, -⟩` from `(markAd_laws D _ _ _ _ (rank_Wc i) _ hemb _ _ hlat T.Q.l).2 mk hmk hma`. Establish `him₂` using `(GlobalTheory.T.marking_roots_dilation_coprime_level _ _ _ _ _ 0 _ _ n hn₂).1 ((markAd_laws D _ _ _ _ (rank_Wc i) _ hemb _ _ hlat (O.dδ ()).l₂).2 mk₂ hmk₂ hma₂).1`.

Establish `him₁` using `(GlobalTheory.T.marking_roots_dilation_coprime_level _ _ _ _ _ 0 _ _ n hn₁).1 him`. Establish `hov'` using `markOver_zsmul (hov _ hlev.1.1 (Ideal.map_mono hlev.1.2.1) mk₂ hmk₂ hma₂) n`. Take `⟨y', hy', hev⟩ : ∃ y' : FrPt (T.Q.Xo ((i : ℕ) + 1)) O.c' ℂ, levR (O.lev z, LinearMap.id) y y' ∧ evR _ O.c' (actLev O.c' O.lev2 z f) y = evR _ O.c' f y'` from `⟨_, mvPt_spec hP.act.2.total z _, evalAt_actL hP.act.2 (GlobalTheory.TransferCompare.evalWD_framed _ _) frMap_trans_id z hf.1 _⟩`. Take `⟨A', hrd', hmk''⟩` from `GlobalTheory.T.analyticFibre_description_levelMove_marking_comp _ _ _ _ _ O.c' _ _ _ Dc.bas Dc.idx Dc.e _ _ Dc.sympl hdom hsd (O.lev z) _ y' hy' B`. Establish `hA' : A'.Marked (n • mk)` using `marked_of_congr A' (hmk'' mk hB) fun a ha => by`.

Take `⟨b, hb⟩` from `hzl a ha`. Conclude with `⟨mk b, hmk b, by rw [LinearMap.comp_apply, hb, map_add, map_zsmul, map_nsmul]; rfl⟩`. Establish `halg : ∀ s : O.c'.F, algebraMap (O.dδ ()).c₂.F ℂ ((O.dδ ()).eF s) = algebraMap O.c'.F ℂ s` using `fun s => rfl`. Take `⟨y₂, A₂, hov₂, hA₂', hrd₂⟩` from `MarkLift.exists_lift_marked _ _ _ _ _ O.c' _ (O.dδ ()) halg hlev tie.laws.pins.2.1.2 hA₂ (fun h => absurd h hpq) _ g _ Dc.bas Dc.idx Dc.e _ _ y' A' Dc.sympl hdom hsd _ _ him₁ hA' him₂ hov'`. Establish `hrk : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q` using `(tie.laws.unf _ hj _ T.good_σ₀).1`.

Establish `h1` using `evR_eq_clsSum GlobalTheory.ChartFree.chartIndep _ _ _ _ _ O.c' _ (O.dδ ()) halg hnab _ g _ Dc.bas Dc.idx Dc.e _ _ y' y₂ A₂ hov₂ Dc.sympl hdom hsd _ Dc.hr Dc.eL hrk hn Dc.dir_eq th v κ' (hrd₂ th (hrd' th hrd)) hv hκ _ him₂ hA₂' (O.Cl' ()) (O.w ()) (O.La ()) (O.Nc ()) (O.gam ()) (O …`. Establish `h2` using `hcv y₂`. Rewrite using `[hev, h1, h2]`. Both sides reduce to the same expression.
-/
theorem geometric_value_ofFive (hR : GlobalTheory.Core5 R F) (tie : FWTie T R κ v₀) (O : OM T R i) (hP : Pinned κ v₀ O)
    {σ' : O.c'.F →+* ℂ} {X : Data D.host.E D.R.r} {g : ℕ}
    (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' σ' X g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i))) (hsd : SelfD X X.Λ)
    {k : GA D (Wc D i)} (hlat : latW (rank_Wc i) X.Λ = latG (Wc D i) k)
    {v : TF (Vc D i).rank g} (hv : IsVac X Dc.bas (T.Q.H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) X.Λ) v)
    {mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)} (hmk₂ : ∀ b, mk₂ b ∈ X.Λ)
    (hma₂ : MarkAd (rank_Wc i) (O.dδ ()).l₂ (iotaW T i) k mk₂) {n : ℤ} (hn₂ : IsCoprime n ((O.dδ ()).l₂.M : ℤ))
    (hn₁ : IsCoprime n (T.Q.l.M : ℤ))
    {Y : O.Cl' () → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E}
    (hY : ∀ j, IsRoots (O.dδ ()).l₂ X.Λ (n • mk₂) (O.Nc () j) (Y j)) {fr : Frame X.Ψ D.R.r}
    (hdom : fr ∈ X.dom) (x : O.Cl' () → VsV D i O.c'.F) {c0 : ℂ} (hcv : CovAt O σ' c0) {z : G}
    (hzl : ∀ a ∈ Mfr T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La), ∃ b, O.lev z a = n • a + T.Q.l.M • b)
    {mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)} (hmk : ∀ b, mk b ∈ X.Λ)
    (hma : MarkAd (rank_Wc i) T.Q.l (iotaW T i) k mk) {th : (Fin g → ℂ) → ℂ} {κ' : ℂ}
    (hκ : ∀ z : Fin (Vc D i).rank → Fin g → ℂ, ∏ b, th (z b) = κ' * thA X Dc.bas Dc.idx v fr z)
    {f : Rul (T.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA (κ i)) (Vc D i).rank)
    (hcls : IsThClsD (T.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ ()) (O.w ()) (O.La ()) (O.Nc ()) (O.gam ()) (O.vol ()) (O.ep ())
      O.io x f) :
    letI : Algebra O.c'.F ℂ := σ'.toAlgebra
    ∀ (y : FrPt (T.Q.Xo ((i : ℕ) + 1)) O.c' ℂ) (B : AnFib X Dc.bas Dc.idx Dc.e fr X.Λ y), B.Marked mk → B.Reads 1 y.s th →
      evR (T.Q.Xo ((i : ℕ) + 1)) O.c' (actLev O.c' O.lev2 z f) y = c0 * κ' *
      clsSum σ' X Dc.hr Dc.bas Dc.idx Dc.eL (O.w ()) (O.La ()) (O.Nc ()) (O.gam ()) (O.vol ()) (O.ep ())
        (fun j => O.io (x j)) X.Λ v Y fr := by
  let _ : Algebra O.c'.F ℂ := σ'.toAlgebra
  let _ : Algebra (O.dδ ()).c₂.F ℂ := (σ'.comp ((O.dδ ()).eF.symm : (O.dδ ()).c₂.F →+* O.c'.F)).toAlgebra
  intro y B hB hrd
  have hn := (FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hR ⟨tie⟩ i _ _ O hP).2.2.1
  have hpq := (FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hR ⟨tie⟩ i _ _ O hP).2.2.2.2.2.2.2.2.2.2.2.1
  have hemb := (FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hR ⟨tie⟩ i _ _ O hP).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨hlev, hA₂, hnab⟩ := hP.cov ()
  obtain ⟨him, -, hov, -⟩ := (markAd_laws D _ _ _ _ (rank_Wc i) _ hemb _ _ hlat T.Q.l).2 mk hmk hma
  have him₂ := (GlobalTheory.T.marking_roots_dilation_coprime_level _ _ _ _ _ 0 _ _ n hn₂).1
    ((markAd_laws D _ _ _ _ (rank_Wc i) _ hemb _ _ hlat (O.dδ ()).l₂).2 mk₂ hmk₂ hma₂).1
  have him₁ := (GlobalTheory.T.marking_roots_dilation_coprime_level _ _ _ _ _ 0 _ _ n hn₁).1 him
  have hov' := markOver_zsmul (hov _ hlev.1.1 (Ideal.map_mono hlev.1.2.1) mk₂ hmk₂ hma₂) n
  obtain ⟨y', hy', hev⟩ : ∃ y' : FrPt (T.Q.Xo ((i : ℕ) + 1)) O.c' ℂ, levR (O.lev z, LinearMap.id) y y' ∧
      evR _ O.c' (actLev O.c' O.lev2 z f) y = evR _ O.c' f y' :=
    ⟨_, mvPt_spec hP.act.2.total z _,
      evalAt_actL hP.act.2 (GlobalTheory.TransferCompare.evalWD_framed _ _) frMap_trans_id z hf.1 _⟩
  obtain ⟨A', hrd', hmk''⟩ := GlobalTheory.T.analyticFibre_description_levelMove_marking_comp _ _ _ _ _ O.c' _ _ _ Dc.bas Dc.idx Dc.e _ _ Dc.sympl hdom hsd (O.lev z) _ y' hy' B
  have hA' : A'.Marked (n • mk) :=
    marked_of_congr A' (hmk'' mk hB) fun a ha => by
      obtain ⟨b, hb⟩ := hzl a ha
      exact ⟨mk b, hmk b, by rw [LinearMap.comp_apply, hb, map_add, map_zsmul, map_nsmul]; rfl⟩
  have halg : ∀ s : O.c'.F, algebraMap (O.dδ ()).c₂.F ℂ ((O.dδ ()).eF s) = algebraMap O.c'.F ℂ s := fun s => rfl
  obtain ⟨y₂, A₂, hov₂, hA₂', hrd₂⟩ := MarkLift.exists_lift_marked _ _ _ _ _ O.c' _ (O.dδ ()) halg hlev tie.laws.pins.2.1.2 hA₂
    (fun h => absurd h hpq) _ g _ Dc.bas Dc.idx Dc.e _ _ y' A' Dc.sympl hdom hsd _ _ him₁ hA' him₂ hov'
  have hrk : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := (tie.laws.unf _ hj _ T.good_σ₀).1
  have h1 := evR_eq_clsSum GlobalTheory.ChartFree.chartIndep _ _ _ _ _ O.c' _ (O.dδ ()) halg hnab _ g _ Dc.bas Dc.idx Dc.e _ _ y' y₂ A₂
    hov₂ Dc.sympl hdom hsd _ Dc.hr Dc.eL hrk hn Dc.dir_eq th v κ' (hrd₂ th (hrd' th hrd)) hv hκ _ him₂ hA₂' (O.Cl' ()) (O.w ())
    (O.La ()) (O.Nc ()) (O.gam ()) (O.vol ()) (O.ep ()) _ O.io x (wtA (κ i))
    (fun j => ⟨((hP.reps ()).1 j).1, ((hP.reps ()).1 j).2.2.1, ((hP.reps ()).1 j).2.2.2.1⟩)
    (fun k => io_mem O hP (x k)) Y hY f hcls
  have h2 := hcv y₂
  rw [hev, h1, h2]
  rfl

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Establish `hF` using `GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ hC.1`. Use `(GlobalTheory.GalOne.Term.zak_class_term_conj_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ μ' η' ω f₀ f hC).elim fun ε hterm => ?_` and prove the remaining obligations. Use `(GlobalTheory.GalOne.cover_const_at_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ).elim fun c0 h4 => ?_` and prove the remaining obligations. Establish `hcv` using `h4.2 hC.1`. Use `(GlobalTheory.GalOne.conj_coeff_eq_dilate_ofFive T R F κ v₀ hR tie i O hP σ').elim fun m hm => ?_` and prove the remaining obligations.

Establish `hε : ∀ b : ℤ, IsCoprime (ε : ℤ) b` using `fun b => ⟨ε, 0, by simp [← Units.val_mul]⟩`. Establish `hn₂ : IsCoprime (m * (ε : ℤ)) ((O.dδ ()).l₂.M : ℤ)` using `hm.1.mul_left (hε _)`. Establish `hn₁ : IsCoprime (m * (ε : ℤ)) (T.Q.l.M : ℤ)` using `hn₂.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 (hP.cov ()).1.1.1)`. Use `(GlobalTheory.GalCentral.central_lev_ofFive T R F κ v₀ hR tie i O hP _ hn₁).elim fun z hz => ?_` and prove the remaining obligations. Establish `hn` using `(FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hR ⟨tie⟩ i _ _ O hP).2.2.1`.

Establish `hemb` using `(FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hR ⟨tie⟩ i _ _ O hP).2.2.2.2.2.2.2.2.2.2.2.2.2.1`. Use `⟨c0, h4.1, z, hz.1, fun {c c₁ Λ ph} hioc {h J'} hreps x₁ x hx f' hf hcls n as fs hbc q => ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.GalOne.framed_point_at_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ hC.1 hV q).elim fun γ k1 => k1.2.elim fun g k2 => k2.elim fun eT k3 => k3.elim fun Dc k4 => k4.elim fun hdom k5 => k5.2.2.2.2.2.2.1.elim fun A₀ k6 => k6.elim fun th k7 => ?_` and prove the remaining obligations. Establish `hS` using `k5.1`. Establish `hM` using `k5.2.1`.

Establish `hp0` using `k5.2.2.1`. Establish `hsd` using `k5.2.2.2.1`. Establish `hlat` using `k5.2.2.2.2.1`. Establish `hfr` using `k5.2.2.2.2.2.1`. Establish `hFr` using `hcc q γ k1.1 g eT Dc.bas Dc.idx Dc.e hS hM hfr hdom A₀ th k7.1`.

Set `_ : Algebra T.Q.c.F ℂ` to `(sOf O σ').toAlgebra`. Set `_ : Algebra O.c'.F ℂ` to `σ'.toAlgebra`. Establish `hw : IsIntegral ℤ (T.Q.H.w0 : D.host.E)` using `T.Q.H.w0.isIntegral_coe`. Establish `hw' : (T.Q.H.w0 : D.host.E) + cc (T.Q.H.w0 : D.host.E) = 1`. Rewrite using `[cc, ← T.Q.H.bar_eq]`.

Conclude with `congrArg (fun t : 𝓞 D.host.E => (t : D.host.E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one T.Q.H)` after adjusting the coercions. Use `(TensVac.vacua _ _ _ _ Dc.bas Dc.idx (Vc D i).rank Dc.sympl hn _ hw hw' _ hsd 1 _ (Base.stdL_mem_Vset (Vc D i).rank 1)).1.elim fun v hv => ?_` and prove the remaining obligations. Establish `hT` using `isTheta1_of_reads_generator _ _ _ _ _ T.Q.c _ _ _ Dc.bas Dc.idx Dc.e _ _ _ A₀ Dc.sympl hdom hsd th k7.1`. Use `(VacProd.prod_eq_mul_thA _ _ _ _ Dc.bas Dc.idx (Vc D i).rank Dc.sympl hn _ hw hw' _ hsd v hv _ hdom th hT).elim fun κ' hκ => ?_` and prove the remaining obligations. Establish `hzak : Zak R.ψ R.θ (rank_Wc i) eT Dc.bas Dc.idx (frOf (rank_Wc i) eT (mvZ R.θ (γ * q) (zAt R i σ))) ((cst (dictS hV q).1 * muS hV q * κ') • v) (ω (1, γ * q) f₀)` using `⟨hC.2.2.2.1.om_pres _ _ (isThetaFunO_of_isVacO hC.2.2.2.2.1.1), fun w hw0 => (hFr w hw0).trans (hfr ▸ thR_smul_of_prod hκ _ _)⟩`.

Use `(markAd_laws D _ _ _ _ (rank_Wc i) _ hemb _ _ hlat T.Q.l).1.elim fun mk hmk => ?_` and prove the remaining obligations. Establish `h7` using `markAd_laws D _ _ _ _ (rank_Wc i) _ hemb _ _ hlat (O.dδ ()).l₂`. Use `h7.1.elim fun mk₂ hmk₂ => ?_` and prove the remaining obligations. Establish `hM₂ : 0 < (O.dδ ()).l₂.M` using `lt_of_lt_of_le (by norm_num) (O.dδ ()).l₂.three_le`. Establish `h8` using `fun k => (DualMark.dual_marking _ _ _ (O.dδ ()).l₂ _ _ _ _ _ hsd (isMark_sign (h7.2 mk₂ hmk₂.1 hmk₂.2).1 ε) (Complex.isPrimitiveRoot_exp _ hM₂.ne')).2.2.2.2 (Vc D i).rank (O.Nc () k) ((hP.reps ()).1 k).2.2.2.1.1.pos`.

Establish `hY` using `fun k => (h8 k).choose_spec`. Establish `hY'` using `fun k => ((GlobalTheory.T.marking_roots_dilation_coprime_level _ _ _ (O.dδ ()).l₂ _ _ _ ((ε : ℤ) • mk₂) m hm.1).2 _ _).1 (fun a => zsmul_mem (hmk₂.1 a) _) (hY k)`. Simplify using `only [smul_smul] at hY'`. Establish `hAo : AlgOver T.Q.c O.c' O.hle ℂ` using `fun _ => rfl`. Establish `ha` using `adelic_value_ofFive hR tie O hP hF hC Dc hS hp0 hsd hlat hv hmk₂.1 hmk₂.2 hY (hfr ▸ hdom) x hterm hm.1 hm.2 hioc hx hreps k1.1 rfl hzak`.

Establish `hg` using `geometric_value_ofFive hR tie O hP Dc hsd hlat hv hmk₂.1 hmk₂.2 hn₂ hn₁ hY' hdom x hcv hz.2 hmk.1 hmk.2 hκ hf hcls _ (fibExt hAo A₀) (k5.2.2.2.2.2.2.2 g Dc.bas Dc.idx Dc.e Dc.sympl hM A₀ mk hmk.1 hmk.2) k7.1`. Establish `hb` using `hbc ℂ hAo ((ptC (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV q).1 ⟨(dictS hV q).2, hdom⟩).ext O.hle hAo)`. Establish `e1 : ∑ k, σ' (as k) * rdU (T.U ((i : ℕ) + 1) (sOf O σ')) (fs k) (dictS hV q).1 (dictS hV q).2 = _` using `(Finset.sum_congr rfl fun k _ => congrArg (σ' (as k) * ·) (dif_pos hdom)).trans (hb.symm.trans hg)`. Rewrite `ha` using `[← hfr]`. Establish `alg : ∀ {n : ℕ} (a r : Fin n → ℂ) (ph c0 S l c u k C : ℂ), ph * S = c * u * k * l * C → ∑ j, a j * r j = c0 * k * C → ph * c0 * S = ∑ j, a j * (l * (c * u * r j))` using `fun a r ph c0 S l c u k C h1 h2 => by`.

Establish `h3 : ∑ j, a j * (l * (c * u * r j)) = l * c * u * ∑ j, a j * r j`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Rewrite using `[h3, h2]`. Take the linear combination `c0 * h1`.

Conclude with `alg _ _ _ _ _ _ _ _ _ _ ha e1`.
-/
theorem identity_of_frConst_ofFive (hR : GlobalTheory.Core5 R F) (tie : FWTie T R κ v₀) (O : OM T R i) (hP : Pinned κ v₀ O)
    {σ : D.what₂.LL →+* ℂ} {σ' : O.c'.F →+* ℂ} (hσ : σ'.comp O.jL = σ) {μ' η' : (AE D)ˣ →* Circle}
    {ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)} {f₀ f : WO (Vc D i) (Wc D i) → ℂ}
    (hC : ConjW R i σ μ' η' ω f₀ f) (hV : T.V ((i : ℕ) + 1) (sOf O σ') = Wc D i)
    {cst : (T.U ((i : ℕ) + 1) (sOf O σ')).Comp → ℂ} (hcc : FrAtEmb O σ σ' hV ω f₀ cst) :
    ∃ c0 : ℂ, ‖c0‖ = 1 ∧ ∃ z ∈ Subgroup.center G, ∀ {c : CoefA (Vc D i)} {c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W}
      {Λ : c.W → WO (Vc D i) (Wc D i) → ℂ} {ph : ℂ}, IoAt κ O σ σ' c₁ f Λ ph →
      ∀ {h : O.Cl' () → GA D (Vc D i)} {J' : Subgroup (Bridge.Gf (Vc D i))},
      RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ()) →
      ∀ (x₁ : O.Cl' () → VsV D i D.what₂.LL) (x : O.Cl' () → VsV D i O.c'.F), (∀ j, IsUp O (x₁ j) (x j)) →
      ∀ f' ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA (κ i)) (Vc D i).rank,
      IsThClsD (T.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ ()) (O.w ()) (O.La ()) (O.Nc ()) (O.gam ()) (O.vol ()) (O.ep ()) O.io x f' →
      ∀ (n : ℕ) (as : Fin n → O.c'.F) (fs : Fin n → T.R ((i : ℕ) + 1)),
      IsBC O.hle (actLev O.c' O.lev2 z f') as fs → ∀ k₀ : GA D (Wc D i),
        ph * c0 * ∑ j, σ' (O.vol () * ((O.gam () j : O.c'.F))⁻¹) * thetaKO ω (h j) k₀ (Λ (c₁ (x₁ j))) =
          ∑ k, σ' (as k) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
            (cst (dictS hV k₀).1 * muS hV k₀ * rdU (T.U ((i : ℕ) + 1) (sOf O σ')) (fs k) (dictS hV k₀).1 (dictS hV k₀).2)) := by
  have hF := GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ hC.1
  refine (GlobalTheory.GalOne.Term.zak_class_term_conj_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ μ' η' ω f₀ f hC).elim fun ε hterm => ?_
  refine (GlobalTheory.GalOne.cover_const_at_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ).elim fun c0 h4 => ?_
  have hcv := h4.2 hC.1
  refine (GlobalTheory.GalOne.conj_coeff_eq_dilate_ofFive T R F κ v₀ hR tie i O hP σ').elim fun m hm => ?_
  have hε : ∀ b : ℤ, IsCoprime (ε : ℤ) b := fun b => ⟨ε, 0, by simp [← Units.val_mul]⟩
  have hn₂ : IsCoprime (m * (ε : ℤ)) ((O.dδ ()).l₂.M : ℤ) := hm.1.mul_left (hε _)
  have hn₁ : IsCoprime (m * (ε : ℤ)) (T.Q.l.M : ℤ) :=
    hn₂.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 (hP.cov ()).1.1.1)
  refine (GlobalTheory.GalCentral.central_lev_ofFive T R F κ v₀ hR tie i O hP _ hn₁).elim fun z hz => ?_
  have hn := (FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hR ⟨tie⟩ i _ _ O hP).2.2.1
  have hemb := (FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hR ⟨tie⟩ i _ _ O hP).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨c0, h4.1, z, hz.1, fun {c c₁ Λ ph} hioc {h J'} hreps x₁ x hx f' hf hcls n as fs hbc q => ?_⟩
  refine (GlobalTheory.GalOne.framed_point_at_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ hC.1 hV q).elim fun γ k1 => k1.2.elim fun g k2 =>
    k2.elim fun eT k3 => k3.elim fun Dc k4 => k4.elim fun hdom k5 => k5.2.2.2.2.2.2.1.elim fun A₀ k6 => k6.elim fun th k7 => ?_
  have hS := k5.1
  have hM := k5.2.1
  have hp0 := k5.2.2.1
  have hsd := k5.2.2.2.1
  have hlat := k5.2.2.2.2.1
  have hfr := k5.2.2.2.2.2.1
  have hFr := hcc q γ k1.1 g eT Dc.bas Dc.idx Dc.e hS hM hfr hdom A₀ th k7.1
  let _ : Algebra T.Q.c.F ℂ := (sOf O σ').toAlgebra
  let _ : Algebra O.c'.F ℂ := σ'.toAlgebra
  have hw : IsIntegral ℤ (T.Q.H.w0 : D.host.E) := T.Q.H.w0.isIntegral_coe
  have hw' : (T.Q.H.w0 : D.host.E) + cc (T.Q.H.w0 : D.host.E) = 1 := by
    rw [cc, ← T.Q.H.bar_eq]
    exact_mod_cast congrArg (fun t : 𝓞 D.host.E => (t : D.host.E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one T.Q.H)
  refine (TensVac.vacua _ _ _ _ Dc.bas Dc.idx (Vc D i).rank Dc.sympl hn _ hw hw' _ hsd 1 _
    (Base.stdL_mem_Vset (Vc D i).rank 1)).1.elim fun v hv => ?_
  have hT := isTheta1_of_reads_generator _ _ _ _ _ T.Q.c _ _ _ Dc.bas Dc.idx Dc.e _ _ _ A₀ Dc.sympl hdom hsd th k7.1
  refine (VacProd.prod_eq_mul_thA _ _ _ _ Dc.bas Dc.idx (Vc D i).rank Dc.sympl hn _ hw hw' _ hsd v hv _ hdom th hT).elim
    fun κ' hκ => ?_
  have hzak : Zak R.ψ R.θ (rank_Wc i) eT Dc.bas Dc.idx (frOf (rank_Wc i) eT (mvZ R.θ (γ * q) (zAt R i σ)))
      ((cst (dictS hV q).1 * muS hV q * κ') • v) (ω (1, γ * q) f₀) :=
    ⟨hC.2.2.2.1.om_pres _ _ (isThetaFunO_of_isVacO hC.2.2.2.2.1.1), fun w hw0 =>
      (hFr w hw0).trans (hfr ▸ thR_smul_of_prod hκ _ _)⟩
  refine (markAd_laws D _ _ _ _ (rank_Wc i) _ hemb _ _ hlat T.Q.l).1.elim fun mk hmk => ?_
  have h7 := markAd_laws D _ _ _ _ (rank_Wc i) _ hemb _ _ hlat (O.dδ ()).l₂
  refine h7.1.elim fun mk₂ hmk₂ => ?_
  have hM₂ : 0 < (O.dδ ()).l₂.M := lt_of_lt_of_le (by norm_num) (O.dδ ()).l₂.three_le
  have h8 := fun k => (DualMark.dual_marking _ _ _ (O.dδ ()).l₂ _ _ _ _ _ hsd (isMark_sign (h7.2 mk₂ hmk₂.1 hmk₂.2).1 ε)
    (Complex.isPrimitiveRoot_exp _ hM₂.ne')).2.2.2.2 (Vc D i).rank (O.Nc () k) ((hP.reps ()).1 k).2.2.2.1.1.pos
  have hY := fun k => (h8 k).choose_spec
  have hY' := fun k => ((GlobalTheory.T.marking_roots_dilation_coprime_level _ _ _ (O.dδ ()).l₂ _ _ _ ((ε : ℤ) • mk₂) m hm.1).2 _ _).1
    (fun a => zsmul_mem (hmk₂.1 a) _) (hY k)
  simp only [smul_smul] at hY'
  have hAo : AlgOver T.Q.c O.c' O.hle ℂ := fun _ => rfl
  have ha := adelic_value_ofFive hR tie O hP hF hC Dc hS hp0 hsd hlat hv hmk₂.1 hmk₂.2 hY (hfr ▸ hdom) x hterm hm.1 hm.2 hioc hx hreps
    k1.1 rfl hzak
  have hg := geometric_value_ofFive hR tie O hP Dc hsd hlat hv hmk₂.1 hmk₂.2 hn₂ hn₁ hY' hdom x hcv hz.2 hmk.1 hmk.2 hκ hf hcls
    _ (fibExt hAo A₀) (k5.2.2.2.2.2.2.2 g Dc.bas Dc.idx Dc.e Dc.sympl hM A₀ mk hmk.1 hmk.2) k7.1
  have hb := hbc ℂ hAo ((ptC (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV q).1 ⟨(dictS hV q).2, hdom⟩).ext O.hle hAo)
  have e1 : ∑ k, σ' (as k) * rdU (T.U ((i : ℕ) + 1) (sOf O σ')) (fs k) (dictS hV q).1 (dictS hV q).2 = _ :=
    (Finset.sum_congr rfl fun k _ => congrArg (σ' (as k) * ·) (dif_pos hdom)).trans (hb.symm.trans hg)
  rw [← hfr] at ha
  have alg : ∀ {n : ℕ} (a r : Fin n → ℂ) (ph c0 S l c u k C : ℂ), ph * S = c * u * k * l * C → ∑ j, a j * r j = c0 * k * C →
      ph * c0 * S = ∑ j, a j * (l * (c * u * r j)) := fun a r ph c0 S l c u k C h1 h2 => by
    have h3 : ∑ j, a j * (l * (c * u * r j)) = l * c * u * ∑ j, a j * r j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h3, h2]
    linear_combination c0 * h1
  exact alg _ _ _ _ _ _ _ _ _ _ ha e1

/- English proof (translation)
Substitute `hs` using the available equality. Establish `ht : TieIn T R κ v₀` using `⟨tie.laws, tie.alg_eq, tie.kap, tie.hv₀, tie.chiR, tie.x0⟩`. Take `⟨w, hw⟩` from `(GlobalTheory.HolDict.holShape_of_good D G Pl0 T0 A T R κ v₀ ht i σ hg).2.2`. Take `⟨th, -, h1, h2, ⟨x0, -, h3⟩, -⟩` from `(GlobalTheory.HolDict.goodDict_core D G Pl0 T0 A T R κ v₀ hR.lev hR.models ht hpb i σ hg hV w hw).unif`. Use `⟨fun h => hu _, fun γ hγ h => ?_, fun g hg h => ?_, fun k hk h => ?_⟩` and prove the remaining obligations.

Conclude with `(h1 γ hγ h).elim fun _ e => congrArg (fun y => u y.1) e.2`. Conclude with `(h3 h g hg).elim fun _ e => congrArg (fun y => u y.1) e.2`. Conclude with `(h2 k hk h).elim fun _ e => congrArg (fun y => u y.1) e.2`.
-/
theorem comp_inv_ofFive (hR : GlobalTheory.Core5 R F) (tie : FWTie T R κ v₀) (hpb : T.pb = R.C.P.pb) {σ : D.what₂.LL →+* ℂ}
    {s : T.Q.c.F →+* ℂ} (hs : res T σ = s) (hg : GoodEmb T.Q.c s) (hV : T.V ((i : ℕ) + 1) s = Wc D i)
    (u : (T.U ((i : ℕ) + 1) s).Comp → ℂ) (hu : ∀ k, ‖u k‖ = 1) : PhaseFun R i fun h => u (dictS hV h).1 := by
  subst hs
  have ht : TieIn T R κ v₀ := ⟨tie.laws, tie.alg_eq, tie.kap, tie.hv₀, tie.chiR, tie.x0⟩
  obtain ⟨w, hw⟩ := (GlobalTheory.HolDict.holShape_of_good D G Pl0 T0 A T R κ v₀ ht i σ hg).2.2
  obtain ⟨th, -, h1, h2, ⟨x0, -, h3⟩, -⟩ :=
    (GlobalTheory.HolDict.goodDict_core D G Pl0 T0 A T R κ v₀ hR.lev hR.models ht hpb i σ hg hV w hw).unif
  refine ⟨fun h => hu _, fun γ hγ h => ?_, fun g hg h => ?_, fun k hk h => ?_⟩
  · exact (h1 γ hγ h).elim fun _ e => congrArg (fun y => u y.1) e.2
  · exact (h3 h g hg).elim fun _ e => congrArg (fun y => u y.1) e.2
  · exact (h2 k hk h).elim fun _ e => congrArg (fun y => u y.1) e.2

/- English proof (translation)
Establish `ht : TieIn T R κ v₀` using `⟨tie.laws, tie.alg_eq, tie.kap, tie.hv₀, tie.chiR, tie.x0⟩`. Establish `h4` using `(GlobalTheory.AdTh.coefMap_norm_equivariant_basis_ofFive' D G Pl0 T0 A T R F κ v₀ hR ht i _ _ O hP).2.2.2`. Use `(hj.base x₀ y).elim fun v hv => (hc v).elim fun v' hv' => ⟨v, ?_, hv.2⟩` and prove the remaining obligations. Establish `h1 : O.c0' x = O.c0' v'` using `hx.symm.trans (hv.1.trans hv'.2.symm)`. Conclude with `(congrArg Subtype.val (inj_of_indep _ h4 h1)).trans hv'.1`.
-/
theorem exists_values_ofFive (hR : GlobalTheory.Core5 R F) (tie : FWTie T R κ v₀) (O : OM T R i) (hP : Pinned κ v₀ O) {σ : D.what₂.LL →+* ℂ}
    {c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W} (hc : CoefficientBaseChange R i O.jL (inC O.c') c₀ O.c0')
    {c : CoefA (Vc D i)} {c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W} {H : HMod (Bridge.Gf (Vc D i) → c.W)}
    {j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H} (hj : IsConjForms R i σ c₀ c c₁ H j) (x₀ : A.fam.amb.FL i A.μ0)
    (y : Bridge.Gf (Vc D i)) (x : VsV D i O.c'.F) (hx : (R.HV i A.μ0).e (jVx R i A.μ0 x₀) y = O.c0' x) :
    ∃ x₁, IsUp O x₁ x ∧ H.e (j x₀) y = c₁ x₁ := by
  have ht : TieIn T R κ v₀ := ⟨tie.laws, tie.alg_eq, tie.kap, tie.hv₀, tie.chiR, tie.x0⟩
  have h4 := (GlobalTheory.AdTh.coefMap_norm_equivariant_basis_ofFive' D G Pl0 T0 A T R F κ v₀ hR ht i _ _ O hP).2.2.2
  refine (hj.base x₀ y).elim fun v hv => (hc v).elim fun v' hv' => ⟨v, ?_, hv.2⟩
  have h1 : O.c0' x = O.c0' v' := hx.symm.trans (hv.1.trans hv'.2.symm)
  exact (congrArg Subtype.val (inj_of_indep _ h4 h1)).trans hv'.1

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Substitute `hs` using the available equality. Establish `hF` using `GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ hC.1`. Establish `hpb` using `GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R tie.laws.toLawsM hR.lev (hP.tuple ()).half`. Establish `hcE` using `tie.laws.cUnit _ (inR i) _ hF.2.1`. Establish `hκn` using `(FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hR ⟨tie⟩ i _ _ O hP).2.2.2.1`.

Use `(GlobalTheory.GalOne.FrameConst.exists_frAtEmb_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ μ' η' ω f₀ f hC hV).elim fun cst hcc => ?_` and prove the remaining obligations. Use `(identity_of_frConst_ofFive hR tie O hP hσ hC hV hcc.2).elim fun c0 h1 => h1.2.elim fun z h2 => ?_` and prove the remaining obligations. Establish `hext` using `(tie.hv₀ i σ).1`. Set `v₁ : ∀ ρ, lowT (R.MW i σ) ρ` to `fun ρ => ⟨v₀ i σ ρ, (hext ρ).2.1⟩`. Use `(GlobalTheory.GalOne.IoCmp.ioAt_of_conj_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ μ' η' ω f₀ f hC c c₁ ⟨hj.coef, hj.act, hj.indep, hj.span, hj.pair⟩ B hL.2.1.onb io hL.2.2.1 v₁ rfl).elim fun ph h3 => ?_` and prove the remaining obligations.

Use `⟨fun g => cst (dictS hV g).1 / T.cE _ _ (dictS hV g).1, z, ph * c0, comp_inv_ofFive hR tie hpb hF.1 hF.2.1 hV (fun k => cst k / T.cE _ _ k) (fun k => by rw [norm_div, hcc.1, hcE, div_one]), h2.1, by rw [norm_mul, h3.1, h1.1, _root_.one_mul], fun g k hk φ y => ?_, fun x₀ n a fs hc …` and prove the remaining obligations. Use `(GlobalTheory.GalOne.Equivar.eqAt_of_frAtEmb_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ μ' η' ω f₀ f hC hV cst hcc.2 g k hk φ φ.2).2.elim fun b hb => ?_` and prove the remaining obligations. Establish `e1 : (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) = algebraMap T.Q.c.F D.what₂.LL b` using `D.what₂.embLL.injective ((hR.grp.chiW i g).trans hb.1.symm)`. Establish `e2 : σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) = sOf O σ' b` using `(congrArg σ e1).trans (RingHom.congr_fun hF.1 b)`. Use `(div_mul_phiC hV hcE cst _ _ y).trans (Eq.trans ?_ (congrArg₂ (· * ·) e2 (div_mul_phiC hV hcE cst _ _ (y * k))).symm)` and prove the remaining obligations.

Establish `e3 : ∀ φ y, phiAt T i (sOf O σ') hV cst φ y = cst (dictS hV y).1 * muS hV y * rdU (T.U ((i : ℕ) + 1) (sOf O σ')) φ (dictS hV y).1 (dictS hV y).2` using `fun _ _ => rfl`. Establish `e4` using `((e3 _ _).symm.trans (hb.2 y)).trans (congrArg (sOf O σ' b * ·) (e3 _ _))`. Conclude with `(congrArg (_ * ·) e4).trans (mul_left_comm _ _ _)`. Establish `hvv : v = v₁` using `funext fun ρ => Subtype.ext (congrFun hv ρ)`. Use `(congrArg (fun w => ph * c0 * thP ((c.ext ∘ₗ H.e).rangeRestrict (j x₀)) (PiTensorProduct.tprod ℂ w) g) hvv).trans ?_` and prove the remaining obligations.

Use `hcs.elim fun x h4 => h4.elim fun f' h5 => ?_` and prove the remaining obligations. Establish `h6` using `fun k => exists_values_ofFive hR tie O hP hc hj x₀ _ (x k) (h5.1 k)`. Establish `hbc` using `(GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hP.act.1).2 (wtA (κ i)) (Vc D i).rank z n _ _ f' h5.2.1 (fun k => hκn ▸ ((mem_cusp _ _ _ _ _ _).1 (fs k).2).1) h5.2.2.2`. Establish `h7` using `h2.2 h3.2 hreps (fun k => (h6 k).choose) x (fun k => (h6 k).choose_spec.1) f' h5.2.1 h5.2.2.1 n _ _ hbc g`. Establish `h8` using `GlobalTheory.GalOne.theta_eq_classSum_of_conjugate R F hR i σ μ' η' ω f₀ f hC c₀ c c₁ H j hj B io thP hL _ σ' _ h _ J' _ _ _ hreps (j x₀) (PiTensorProduct.tprod ℂ v₁) g`.

Use `(congrArg (ph * c0 * ·) (h8.trans (Finset.sum_congr rfl fun k _ => ?_))).trans (h7.trans (Finset.sum_congr rfl fun k _ => ?_))` and prove the remaining obligations. Conclude with `congrArg (fun w => _ * thetaKO ω (h k) g (ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v₁) w))) (h6 k).choose_spec.2`. Conclude with `congrArg₂ (· * ·) (RingHom.congr_fun hσ (a k)) (div_mul_phiC hV hcE cst _ _ g).symm`.
-/
theorem oneMap_of_ext_ofFive (hR : GlobalTheory.Core5 R F) (tie : FWTie T R κ v₀) (O : OM T R i) (hP : Pinned κ v₀ O)
    {h : O.Cl' () → GA D (Vc D i)} {J' : Subgroup (Bridge.Gf (Vc D i))}
    (hreps : RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ()))
    {c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W} (hc : CoefficientBaseChange R i O.jL (inC O.c') c₀ O.c0')
    {σ : D.what₂.LL →+* ℂ} {σ' : O.c'.F →+* ℂ} (hσ : σ'.comp O.jL = σ) {s : T.Q.c.F →+* ℂ} (hs : s = sOf O σ')
    (hV : T.V ((i : ℕ) + 1) s = Wc D i) {μ' η' : (AE D)ˣ →* Circle}
    {c : CoefA (Vc D i)} {c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W} {H : HMod (Bridge.Gf (Vc D i) → c.W)}
    {j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H} (hj : IsConjForms R i σ c₀ c c₁ H j)
    {ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)} {f₀ f : WO (Vc D i) (Wc D i) → ℂ}
    (hC : ConjW R i σ μ' η' ω f₀ f) {B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ}
    {io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank}
    {thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))}
    (hL : LiftData R i σ μ' η' c H ω f₀ f B io thP) :
    ∃ (u : GA D (Wc D i) → ℂ) (z : G) (ka : ℂ), PhaseFun R i u ∧ z ∈ Subgroup.center G ∧ ‖ka‖ = 1 ∧
      (∀ g k, IsLiftW R i g k → ∀ (f : Cu T κ i) (h : GA D (Wc D i)),
        u h * phiC T hV (wtA (κ i)) (actG O g (f : T.R ((i : ℕ) + 1))) h =
          σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) *
            (u (h * k) * phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) (h * k))) ∧
      ∀ x₀ (n : ℕ) (a : Fin n → D.what₂.LL) (fs : Fin n → Cu T κ i), IsClassSum O κ h x₀ a fs →
        ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (fun ρ => (v ρ : (R.MW i σ).sm ρ)) = v₀ i σ → ∀ g,
          ka * thP ((c.ext ∘ₗ H.e).rangeRestrict (j x₀)) (PiTensorProduct.tprod ℂ v) g =
            ∑ k, σ (a k) * (u g * phiC T hV (wtA (κ i)) (actG O z (fs k : T.R ((i : ℕ) + 1))) g) := by
  subst hs
  have hF := GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ hC.1
  have hpb := GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R tie.laws.toLawsM hR.lev (hP.tuple ()).half
  have hcE := tie.laws.cUnit _ (inR i) _ hF.2.1
  have hκn := (FactsLat.facts_lat_ofFive D G Pl0 T0 A T R F κ v₀ hR ⟨tie⟩ i _ _ O hP).2.2.2.1
  refine (GlobalTheory.GalOne.FrameConst.exists_frAtEmb_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ μ' η' ω f₀ f hC hV).elim fun cst hcc => ?_
  refine (identity_of_frConst_ofFive hR tie O hP hσ hC hV hcc.2).elim fun c0 h1 => h1.2.elim fun z h2 => ?_
  have hext := (tie.hv₀ i σ).1
  let v₁ : ∀ ρ, lowT (R.MW i σ) ρ := fun ρ => ⟨v₀ i σ ρ, (hext ρ).2.1⟩
  refine (GlobalTheory.GalOne.IoCmp.ioAt_of_conj_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ μ' η' ω f₀ f hC c c₁ ⟨hj.coef, hj.act, hj.indep, hj.span, hj.pair⟩
    B hL.2.1.onb io hL.2.2.1 v₁ rfl).elim fun ph h3 => ?_
  refine ⟨fun g => cst (dictS hV g).1 / T.cE _ _ (dictS hV g).1, z, ph * c0,
    comp_inv_ofFive hR tie hpb hF.1 hF.2.1 hV (fun k => cst k / T.cE _ _ k) (fun k => by rw [norm_div, hcc.1, hcE, div_one]),
    h2.1, by rw [norm_mul, h3.1, h1.1, _root_.one_mul], fun g k hk φ y => ?_, fun x₀ n a fs hcs v hv g => ?_⟩
  · refine (GlobalTheory.GalOne.Equivar.eqAt_of_frAtEmb_ofFive T R F κ v₀ hR tie i O hP σ σ' hσ μ' η' ω f₀ f hC hV cst hcc.2 g k hk φ φ.2).2.elim fun b hb => ?_
    have e1 : (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) = algebraMap T.Q.c.F D.what₂.LL b :=
      D.what₂.embLL.injective ((hR.grp.chiW i g).trans hb.1.symm)
    have e2 : σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) = sOf O σ' b :=
      (congrArg σ e1).trans (RingHom.congr_fun hF.1 b)
    refine (div_mul_phiC hV hcE cst _ _ y).trans (Eq.trans ?_
      (congrArg₂ (· * ·) e2 (div_mul_phiC hV hcE cst _ _ (y * k))).symm)
    have e3 : ∀ φ y, phiAt T i (sOf O σ') hV cst φ y = cst (dictS hV y).1 * muS hV y *
        rdU (T.U ((i : ℕ) + 1) (sOf O σ')) φ (dictS hV y).1 (dictS hV y).2 := fun _ _ => rfl
    have e4 := ((e3 _ _).symm.trans (hb.2 y)).trans (congrArg (sOf O σ' b * ·) (e3 _ _))
    exact (congrArg (_ * ·) e4).trans (mul_left_comm _ _ _)
  · have hvv : v = v₁ := funext fun ρ => Subtype.ext (congrFun hv ρ)
    refine (congrArg (fun w => ph * c0 * thP ((c.ext ∘ₗ H.e).rangeRestrict (j x₀)) (PiTensorProduct.tprod ℂ w) g) hvv).trans ?_
    refine hcs.elim fun x h4 => h4.elim fun f' h5 => ?_
    have h6 := fun k => exists_values_ofFive hR tie O hP hc hj x₀ _ (x k) (h5.1 k)
    have hbc := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hP.act.1).2 (wtA (κ i)) (Vc D i).rank z n _ _ f' h5.2.1
      (fun k => hκn ▸ ((mem_cusp _ _ _ _ _ _).1 (fs k).2).1) h5.2.2.2
    have h7 := h2.2 h3.2 hreps (fun k => (h6 k).choose) x (fun k => (h6 k).choose_spec.1) f' h5.2.1 h5.2.2.1 n _ _ hbc g
    have h8 := GlobalTheory.GalOne.theta_eq_classSum_of_conjugate R F hR i σ μ' η' ω f₀ f hC c₀ c c₁ H j hj B io thP hL _ σ' _ h _ J' _ _ _ hreps (j x₀)
      (PiTensorProduct.tprod ℂ v₁) g
    refine (congrArg (ph * c0 * ·) (h8.trans (Finset.sum_congr rfl fun k _ => ?_))).trans
      (h7.trans (Finset.sum_congr rfl fun k _ => ?_))
    · exact congrArg (fun w => _ * thetaKO ω (h k) g (ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v₁) w))) (h6 k).choose_spec.2
    · exact congrArg₂ (· * ·) (RingHom.congr_fun hσ (a k)) (div_mul_phiC hV hcE cst _ _ g).symm

end GlobalTheory.GalOne

end

end
