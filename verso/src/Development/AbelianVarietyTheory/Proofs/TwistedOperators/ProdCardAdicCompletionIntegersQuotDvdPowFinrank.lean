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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ _ s k hk`. Use `set I : Ideal (𝓞 F) := Ideal.span {(k : 𝓞 F)} with hIdef`. Establish `hI : I ≠ 0`. Rewrite using `[hIdef, Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hk.ne'` after adjusting the coercions.

Establish `hmap : ∀ v : HeightOneSpectrum (𝓞 F), I.map (algebraMap (𝓞 F) (v.adicCompletionIntegers F)) = Ideal.span {(k : v.adicCompletionIntegers F)}`. Introduce `v`. Rewrite using `[hIdef, Ideal.map_span, Set.image_singleton, map_natCast]`. Take `⟨hfin, hprod⟩` from `GlobalTheory.LocalDifferentProduct.finprod_card_quot_map hI`. Simplify using `only [hmap] at hfin hprod`.

Establish `hnorm : Ideal.absNorm I = k ^ Module.finrank ℚ F`. Rewrite using `[hIdef, Ideal.absNorm_span_singleton]`. Establish `e : (k : 𝓞 F) = algebraMap ℤ (𝓞 F) (k : ℤ)` using `by simp`. Rewrite using `[e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Int.natAbs_pow]`. Simplify using the standard rewrite rules.

Rewrite using `[← hnorm, ← hprod, finprod_eq_prod_of_mulSupport_subset (s := s ∪ hfin.toFinset) _ (by intro x hx; simp [hx])]`. Conclude with `Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_left`.
-/
theorem prod_card_quot_natCast_dvd_pow_finrank : ∀ (F : Type) [Field F] [NumberField F] (s : Finset (HeightOneSpectrum (𝓞 F))) (k : ℕ), 0 < k → ∏ v ∈ s, Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {(k : v.adicCompletionIntegers F)}) ∣ k ^ Module.finrank ℚ F := by
  intro F _ _ s k hk
  classical
  set I : Ideal (𝓞 F) := Ideal.span {(k : 𝓞 F)} with hIdef
  have hI : I ≠ 0 := by
    rw [hIdef, Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hk.ne'
  have hmap : ∀ v : HeightOneSpectrum (𝓞 F),
      I.map (algebraMap (𝓞 F) (v.adicCompletionIntegers F)) =
        Ideal.span {(k : v.adicCompletionIntegers F)} := by
    intro v
    rw [hIdef, Ideal.map_span, Set.image_singleton, map_natCast]
  obtain ⟨hfin, hprod⟩ := GlobalTheory.LocalDifferentProduct.finprod_card_quot_map hI
  simp only [hmap] at hfin hprod
  have hnorm : Ideal.absNorm I = k ^ Module.finrank ℚ F := by
    rw [hIdef, Ideal.absNorm_span_singleton]
    have e : (k : 𝓞 F) = algebraMap ℤ (𝓞 F) (k : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Int.natAbs_pow]
    simp
  rw [← hnorm, ← hprod, finprod_eq_prod_of_mulSupport_subset (s := s ∪ hfin.toFinset) _
    (by intro x hx; simp [hx])]
  exact Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_left

end GlobalTheory
