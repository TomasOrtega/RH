import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.BaseChangeMinimal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsBaseChangeRelabel
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)

noncomputable section

universe u u' v w

namespace BaseChange

variable {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F'] {K : Type*} [Fintype K]
  {ι : K → Type*} [∀ k, Fintype (ι k)]

/- English proof (translation)
Use `hV.1.1` as an intermediate fact. Establish `hc` using `BaseChangeMin.comap_of_mem_minimalPrimes_map V W hW`. Establish `hVo : NumbersDVR.IsMultiProjPrime V` using `(Objects.isMultiProjPrime_iff V).mpr hV.1`. Establish `hJ : NumbersDVR.IsMultiHomogIdeal (V.map (MvPolynomial.map (algebraMap F F')))` using `FieldNumbers.isMultiHomogIdeal_map hVo.multiHomog`. Establish `hWo : NumbersDVR.IsMultiProjPrime W`.

Use `⟨hW.1.1, FieldNumbers.PFContracted.isMultiHomogIdeal_of_mem_minimalPrimes hJ hW, ?_⟩` and prove the remaining obligations. Introduce `k`. Take `⟨i, hi⟩` from `hVo.relevant k`. Use `⟨i, fun hX => hi ?_⟩` and prove the remaining obligations. Rewrite using `[← hc, Ideal.mem_comap, MvPolynomial.map_X]`.

Conclude with `hX`. Use `⟨(Objects.isMultiProjPrime_iff W).mp hWo, ?_⟩` and prove the remaining obligations. Rewrite using `[BaseChangeMin.ringKrullDim_of_mem_minimalPrimes_map V W hW]`. Conclude with `hV.2`.
-/
theorem isProjVarF_of_mem_minimalPrimes {V : Ideal (MRingOver F ι)} {n : ℕ} (hV : IsProjVarF V n)
    {W : Ideal (MRingOver F' ι)}
    (hW : W ∈ (V.map (MvPolynomial.map (algebraMap F F'))).minimalPrimes) : IsProjVarF W n := by
  classical
  have := hV.1.1
  have hc := BaseChangeMin.comap_of_mem_minimalPrimes_map V W hW
  have hVo : NumbersDVR.IsMultiProjPrime V := (Objects.isMultiProjPrime_iff V).mpr hV.1
  have hJ : NumbersDVR.IsMultiHomogIdeal (V.map (MvPolynomial.map (algebraMap F F'))) :=
    FieldNumbers.isMultiHomogIdeal_map hVo.multiHomog
  have hWo : NumbersDVR.IsMultiProjPrime W := by
    refine ⟨hW.1.1, FieldNumbers.PFContracted.isMultiHomogIdeal_of_mem_minimalPrimes hJ hW, ?_⟩
    intro k
    obtain ⟨i, hi⟩ := hVo.relevant k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hc, Ideal.mem_comap, MvPolynomial.map_X]
    exact hX
  refine ⟨(Objects.isMultiProjPrime_iff W).mp hWo, ?_⟩
  rw [BaseChangeMin.ringKrullDim_of_mem_minimalPrimes_map V W hW]
  exact hV.2

end BaseChange

open BaseChange

/- English proof (translation)
Introduce `I I' hI hI' V n L hV`. Establish `hEU` using `ExistsUnique.of_found hN hUq hBase F ι`. Establish `hEU'` using `ExistsUnique.of_found hN' hUq' hBase' F' ι`. Use `hV.1.1` as an intermediate fact. Use `set J := V.map (MvPolynomial.map (algebraMap F F')) with hJdef`.

Establish `hmin : ∀ W ∈ J.minimalPrimes, IsProjVarF W n` using `fun W hW => isProjVarF_of_mem_minimalPrimes hV hW`. Establish `hVo : NumbersDVR.IsMultiProjPrime V` using `(Objects.isMultiProjPrime_iff V).mpr hV.1`. Establish `hJ : NumbersDVR.IsMultiHomogIdeal J` using `FieldNumbers.isMultiHomogIdeal_map hVo.multiHomog`. Establish `hdim : ringKrullDim (MRingOver F' ι ⧸ J) < ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)`. Use `lt_of_le_of_lt (BaseChangeMin.ringKrullDim_quotient_le_of_minimalPrimes _ (N := ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) fun Z hZ => (hmin Z hZ).2.le) ?_` and prove the remaining obligations.

Conclude with `(show n + Fintype.card K < n + 1 + Fintype.card K by omega)` after adjusting the coercions. Rewrite using `[Numbers.agree_of_existsUnique hN hEU I hI V n L hV, ← (hBC.1 F F' K ι V).2 n L, hAs F' K ι n J hJ hdim L]`. Unfold `NumbersDVR.cycEval`. Rewrite using `[finsum_mem_def]`. Use `finsum_congr fun W => ?_` and prove the remaining obligations.

Unfold `idealCycle`. Distinguish the cases in `hW : W ∈ J.minimalPrimes`. Establish `: W.IsPrime` using `hW.1.1`. Establish `hWv` using `hmin W hW`. Rewrite using `[dif_pos ⟨hW, (Objects.isMultiProjPrime_iff W).mpr hWv.1 |>.relevant⟩, Set.indicator_of_mem hW, Numbers.agree_of_existsUnique hN' hEU' I' hI' W n L hWv]`.

Simplify using `only [ReciprocityTheory.ChartRestriction.G.Geo.multAt, dif_pos this]`. Both sides reduce to the same expression. Rewrite using `[dif_neg (fun h => hW h.1), Set.indicator_of_notMem hW]`. Simplify using the standard rewrite rules.
-/
theorem BaseChange.of_found (hN : IntNumIsFieldIntersection.Statement.{u})
    (hUq : FieldNumbers.IntNumUnique.Statement.{u}) (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hN' : IntNumIsFieldIntersection.Statement.{u'})
    (hUq' : FieldNumbers.IntNumUnique.Statement.{u'})
    (hBase' : FieldNumbers.IntNumBase.Statement.{u'})
    (hBC : FieldNumbers.IntNumBaseChange.Statement.{u, u'}) (hAs : IntNumAssoc.Statement.{u'})
    (F : Type u) (F' : Type u') [Field F] [Field F'] [Algebra F F'] {K : Type} [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] : ReciprocityTheory.ChartRestriction.G.AI.I1.BaseChangeStatement F F' ι := by
  classical
  intro I I' hI hI' V n L hV
  have hEU := ExistsUnique.of_found hN hUq hBase F ι
  have hEU' := ExistsUnique.of_found hN' hUq' hBase' F' ι
  have := hV.1.1
  set J := V.map (MvPolynomial.map (algebraMap F F')) with hJdef
  have hmin : ∀ W ∈ J.minimalPrimes, IsProjVarF W n :=
    fun W hW => isProjVarF_of_mem_minimalPrimes hV hW
  have hVo : NumbersDVR.IsMultiProjPrime V := (Objects.isMultiProjPrime_iff V).mpr hV.1
  have hJ : NumbersDVR.IsMultiHomogIdeal J := FieldNumbers.isMultiHomogIdeal_map hVo.multiHomog
  have hdim : ringKrullDim (MRingOver F' ι ⧸ J) < ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    refine lt_of_le_of_lt (BaseChangeMin.ringKrullDim_quotient_le_of_minimalPrimes _
      (N := ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) fun Z hZ => (hmin Z hZ).2.le) ?_
    exact_mod_cast (show n + Fintype.card K < n + 1 + Fintype.card K by omega)
  rw [Numbers.agree_of_existsUnique hN hEU I hI V n L hV, ← (hBC.1 F F' K ι V).2 n L,
    hAs F' K ι n J hJ hdim L]
  unfold NumbersDVR.cycEval
  rw [finsum_mem_def]
  refine finsum_congr fun W => ?_
  unfold idealCycle
  by_cases hW : W ∈ J.minimalPrimes
  · have : W.IsPrime := hW.1.1
    have hWv := hmin W hW
    rw [dif_pos ⟨hW, (Objects.isMultiProjPrime_iff W).mpr hWv.1 |>.relevant⟩,
      Set.indicator_of_mem hW, Numbers.agree_of_existsUnique hN' hEU' I' hI' W n L hWv]
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.multAt, dif_pos this]
    rfl
  · rw [dif_neg (fun h => hW h.1), Set.indicator_of_notMem hW]
    simp

/- English proof (translation)
The claim follows from `BaseChange.of_found IntNumIsFieldIntersection.full FieldNumbers.IntNumUnique.full FieldNumbers.IntNumBase.full IntNumIsFieldIntersection.full FieldNumbers.IntNumUnique.full FieldNumbers.IntNumBase.full FieldNumbers.IntNumBaseChange.full IntNumAssoc.full F F' ι`.
-/
theorem BaseChange.full (F : Type u) (F' : Type u') [Field F] [Field F'] [Algebra F F'] {K : Type}
    [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] : ReciprocityTheory.ChartRestriction.G.AI.I1.BaseChangeStatement F F' ι :=
  BaseChange.of_found IntNumIsFieldIntersection.full FieldNumbers.IntNumUnique.full
    FieldNumbers.IntNumBase.full IntNumIsFieldIntersection.full FieldNumbers.IntNumUnique.full
    FieldNumbers.IntNumBase.full FieldNumbers.IntNumBaseChange.full IntNumAssoc.full F F' ι

end

end GroundTheory.Heights₂.Heights.Targets
