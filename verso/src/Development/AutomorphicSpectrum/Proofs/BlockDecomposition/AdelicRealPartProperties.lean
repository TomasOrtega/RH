import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmR
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta

namespace GlobalTheory.CompanionTheory.CenTheta

/- English proof (translation)
Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `v a b`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [finAt, Ad3.dg2, Ad3.R.lc] <;> rfl`. Introduce `g h`.

Unfold `GL2Classical.realPart`. Rewrite using `[map_mul, Prod.fst_mul, map_mul]`. Introduce `a b`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [GL2Classical.realPart, Ad3.dg2, RationalIdeles.realPart] <;> rfl`.

Introduce `z`. Establish `h` using `((Units.val (z : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ)).2.2).and ((Units.val (z⁻¹ : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ)).2.2)`. Use `⟨(Filter.eventually_cofinite.mp h).toFinset, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite `hv` using `[Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not]`. Conclude with `⟨(mem_valuationInteger_iff v _).mpr hv.1, (mem_valuationInteger_iff v _).mpr hv.2⟩`.
-/
theorem realPart_multiplicative_and_diagonal :
    (∀ (v : Pl) (a b : Jd), finAt v (dg2 a b : G2) = dg2 (Ad3.R.lc v a) (Ad3.R.lc v b)) ∧
    (∀ g h : G2, GL2Classical.realPart (g * h) = GL2Classical.realPart g * GL2Classical.realPart h) ∧
    (∀ a b : Jd, GL2Classical.realPart (dg2 a b : G2) =
      dg2 (RationalIdeles.realPart a) (RationalIdeles.realPart b)) ∧
    (∀ z : Jd, ∃ S : Finset Pl, ∀ v ∉ S, Ad3.R.lc v z ∈ unQ v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v a b
    ext i j
    fin_cases i <;> fin_cases j <;> simp [finAt, Ad3.dg2, Ad3.R.lc] <;> rfl
  · intro g h
    unfold GL2Classical.realPart
    rw [map_mul, Prod.fst_mul, map_mul]
  · intro a b
    ext i j
    fin_cases i <;> fin_cases j <;> simp [GL2Classical.realPart, Ad3.dg2, RationalIdeles.realPart] <;> rfl
  · intro z
    have h := ((Units.val (z : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ)).2.2).and
      ((Units.val (z⁻¹ : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ)).2.2)
    refine ⟨(Filter.eventually_cofinite.mp h).toFinset, fun v hv => ?_⟩
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv
    exact ⟨(mem_valuationInteger_iff v _).mpr hv.1, (mem_valuationInteger_iff v _).mpr hv.2⟩

end GlobalTheory.CompanionTheory.CenTheta
