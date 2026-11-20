import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDLocalization
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatNormalFibres
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibresRegularPolynomial
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StJacobianPrimeDerivations
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDerivationAdicCompletion
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAdicCompletionRegular
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDerivationCotangentIndependent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularQuotientIndependent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

/- English proof (translation)
Introduce `k _ n M hM P _`. Set `B` to `MvPolynomial (Fin n) k`. Set `Bh` to `AdicCompletion M B`. Set `L` to `Localization.AtPrime P`. Take `⟨h, f, D, s, hfp, hs, hsp, hdet⟩` from `hJ k n (P.comap (algebraMap B Bh)) (Ideal.comap_isPrime _ _)`.

Use `choose D' hD' using fun j => hE B M (D j)`. Establish `: IsRegularLocalRing Bh` using `hC B inferInstance M inferInstance`. Establish `: IsRegularLocalRing L` using `GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.localization_atPrime P`. Establish `hdet' : (Matrix.of fun i j => D' j (algebraMap B Bh (f i))).det ∉ P`. Establish `hm : (Matrix.of fun i j => D' j (algebraMap B Bh (f i))) = (algebraMap B Bh).mapMatrix (Matrix.of fun i j => D j (f i))`.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply]`. Conclude with `hD' j (f i)`. Rewrite using `[hm, ← RingHom.map_det]`. Conclude with `hdet`.

Establish `hmem : ∀ i, algebraMap Bh L (algebraMap B Bh (f i)) ∈ maximalIdeal L` using `fun i => (IsLocalization.AtPrime.to_map_mem_maximal_iff L P _).mpr (hfp i)`. Establish `hreg` using `hQ L h _ hmem (hI Bh P h D' (fun i => algebraMap B Bh (f i)) hfp hdet')`. Establish `heq : Ideal.span (Set.range fun i => algebraMap Bh L (algebraMap B Bh (f i))) = Ideal.map (algebraMap Bh L) (Ideal.map (algebraMap B Bh) (P.comap (algebraMap B Bh)))`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (hfp i))`. Rewrite using `[Ideal.map_map, Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Establish `hu : IsUnit (algebraMap Bh L (algebraMap B Bh s))` using `(IsLocalization.AtPrime.isUnit_to_map_iff L P _).mpr hs`.

Establish `hsx` using `Ideal.mem_map_of_mem ((algebraMap Bh L).comp (algebraMap B Bh)) (hsp x hx)`. Rewrite `hsx` using `[Ideal.map_span, ← Set.range_comp, map_mul]`. Conclude with `(Ideal.unit_mul_mem_iff_mem _ hu).mp hsx`. Conclude with `IsRegularLocalRing.of_ringEquiv (Ideal.quotEquivOfEq heq)`.
-/
theorem FormalFibresRegularPolynomial.proof (hJ : JacobianPrimeDerivations.Statement)
    (hE : DerivationAdicCompletion.Statement) (hC : AdicCompletionRegular.Statement)
    (hI : DerivationCotangentIndependent.Statement) (hQ : RegularQuotientIndependent.Statement) :
    FormalFibresRegularPolynomial.Statement := by
  intro k _ n M hM P _
  let B := MvPolynomial (Fin n) k
  let Bh := AdicCompletion M B
  let L := Localization.AtPrime P
  obtain ⟨h, f, D, s, hfp, hs, hsp, hdet⟩ := hJ k n (P.comap (algebraMap B Bh)) (Ideal.comap_isPrime _ _)
  choose D' hD' using fun j => hE B M (D j)
  have : IsRegularLocalRing Bh := hC B inferInstance M inferInstance
  have : IsRegularLocalRing L := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.localization_atPrime P
  have hdet' : (Matrix.of fun i j => D' j (algebraMap B Bh (f i))).det ∉ P := by
    have hm : (Matrix.of fun i j => D' j (algebraMap B Bh (f i))) =
        (algebraMap B Bh).mapMatrix (Matrix.of fun i j => D j (f i)) := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
      exact hD' j (f i)
    rw [hm, ← RingHom.map_det]
    exact hdet
  have hmem : ∀ i, algebraMap Bh L (algebraMap B Bh (f i)) ∈ maximalIdeal L := fun i =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L P _).mpr (hfp i)
  have hreg := hQ L h _ hmem (hI Bh P h D' (fun i => algebraMap B Bh (f i)) hfp hdet')
  have heq : Ideal.span (Set.range fun i => algebraMap Bh L (algebraMap B Bh (f i))) =
      Ideal.map (algebraMap Bh L) (Ideal.map (algebraMap B Bh) (P.comap (algebraMap B Bh))) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (hfp i))
    · rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro x hx
      have hu : IsUnit (algebraMap Bh L (algebraMap B Bh s)) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff L P _).mpr hs
      have hsx := Ideal.mem_map_of_mem ((algebraMap Bh L).comp (algebraMap B Bh)) (hsp x hx)
      rw [Ideal.map_span, ← Set.range_comp, map_mul] at hsx
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hsx
  exact IsRegularLocalRing.of_ringEquiv (Ideal.quotEquivOfEq heq)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
