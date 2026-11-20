import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

/- English proof (translation)
Introduce `K _ _ σ x q m hq hqm h`. Take `⟨hx0, n, h1, h2⟩` from `h`. Establish `hx : x ≠ 0` using `fun h0 => hx0 (by rw [h0, map_zero])`. Establish `hinj : Function.Injective σ.toIntAlgHom` using `σ.injective`. Establish `i1 : (q : K) ^ n * x ∈ integralClosure ℤ K`.

Rewrite using `[mem_integralClosure_iff, ← isIntegral_algHom_iff σ.toIntAlgHom hinj]`. Simplify using `using h1`. Establish `i2 : (q : K) ^ n * x⁻¹ ∈ integralClosure ℤ K`. Rewrite using `[mem_integralClosure_iff, ← isIntegral_algHom_iff σ.toIntAlgHom hinj]`. Simplify using `using h2`.

Use `set a : 𝓞 K := ⟨_, i1⟩ with ha_def`. Use `set b : 𝓞 K := ⟨_, i2⟩ with hb_def`. Establish `ha : algebraMap (𝓞 K) K a = (q : K) ^ n * x` using `rfl`. Establish `hb : algebraMap (𝓞 K) K b = (q : K) ^ n * x⁻¹` using `rfl`. Take `⟨d, rfl⟩` from `hqm`.

Use `GlobalTheory.Square.AwayClosure.of_integral (k := n) (l := n) (a := a * (d : 𝓞 K) ^ n) (b := b * (d : 𝓞 K) ^ n) hx ?_ ?_` and prove the remaining obligations. Rewrite using `[RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_natCast, ha]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_natCast, hb]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.Square.isAwayUnit_of_unitOff_embedding : ∀ {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (x : K) (q m : ℕ), 0 < q → q ∣ m →
    GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff q (σ x) → GlobalTheory.Square.IsAwayUnit m x := by
  intro K _ _ σ x q m hq hqm h
  obtain ⟨hx0, n, h1, h2⟩ := h
  have hx : x ≠ 0 := fun h0 => hx0 (by rw [h0, map_zero])
  have hinj : Function.Injective σ.toIntAlgHom := σ.injective
  have i1 : (q : K) ^ n * x ∈ integralClosure ℤ K := by
    rw [mem_integralClosure_iff, ← isIntegral_algHom_iff σ.toIntAlgHom hinj]
    simpa using h1
  have i2 : (q : K) ^ n * x⁻¹ ∈ integralClosure ℤ K := by
    rw [mem_integralClosure_iff, ← isIntegral_algHom_iff σ.toIntAlgHom hinj]
    simpa using h2
  set a : 𝓞 K := ⟨_, i1⟩ with ha_def
  set b : 𝓞 K := ⟨_, i2⟩ with hb_def
  have ha : algebraMap (𝓞 K) K a = (q : K) ^ n * x := rfl
  have hb : algebraMap (𝓞 K) K b = (q : K) ^ n * x⁻¹ := rfl
  obtain ⟨d, rfl⟩ := hqm
  refine GlobalTheory.Square.AwayClosure.of_integral (k := n) (l := n) (a := a * (d : 𝓞 K) ^ n)
    (b := b * (d : 𝓞 K) ^ n) hx ?_ ?_
  · rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_natCast, ha]
    push_cast
    ring
  · rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_natCast, hb]
    push_cast
    ring
