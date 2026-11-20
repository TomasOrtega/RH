import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightLocalNormalIndex
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalQuotCard
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalQuotCentred
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartResidue
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

/- English proof (translation)
Introduce `L _ _ O hft hfr m _`. Use `set A := Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors`. Use `set C := integralClosure A L`. Establish `: Algebra.FiniteType ℤ O` using `hft`. Establish `: CharZero O` using `⟨fun a b h ↦ by`.

Use `congrArg (fun t : O ↦ (t : L)) h` as an intermediate fact. Simplify using `using this⟩`. Establish `hfin : Module.Finite O (integralClosure O L)` using `Model.finite_integralClosure_fractionRing_of_charZero O L`. Take `⟨d, hd, hdI⟩` from `FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors O) (Module.Finite.iff_fg.mp hfin : (Subalgebra.toSubmodule (integralClosure O L)).FG)`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`.

Establish `hdL : algebraMap O L d ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd`. Establish `hdC : ∀ x ∈ C, algebraMap O L d * x ∈ A`. Introduce `x hx`. Take `⟨⟨s, hs⟩, hsx⟩` from `IsIntegral.exists_multiple_integral_of_isLocalization (R := O) (M := m.primeCompl) (Rₘ := A) x hx`. Take `⟨o, ho⟩` from `hdI _ hsx`.

Establish `hs0 : algebraMap O L s ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (m.primeCompl_le_nonZeroDivisors hs)`. Simplify using `only [Submonoid.smul_def, Algebra.smul_def] at ho`. Use `⟨o, s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[ho]`. Clear the denominators using the available nonvanishing facts.

Establish `hAC : A.toSubring ≤ C.toSubring` using `fun x hx ↦ (isIntegral_algebraMap : IsIntegral A (algebraMap A L ⟨x, hx⟩))`. Use `set f := algebraMap O L d`. Establish `hinj : Function.Injective (AddMonoidHom.mulLeft f)` using `mul_right_injective₀ hdL`. Establish `h1 : A.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ C.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f)` using `AddSubgroup.map_mono hAC`. Establish `h2 : C.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ A.toSubring.toAddSubgroup`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hdC y hy`. Establish `e1` using `AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2`. Rewrite `e1` using `[AddSubgroup.relIndex_map_map_of_injective _ _ hinj]`. Establish `hcard : (A.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f)).relIndex A.toSubring.toAddSubgroup ≠ 0`.

Set `e : Localization.AtPrime m ≃ₐ[O] A` to `IsLocalization.algEquiv m.primeCompl _ _`. Establish `hq1 : Nat.card (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) d}) = Nat.card (A.toSubring ⧸ Ideal.span {(algebraMap O A d : A.toSubring)})`. Use `Nat.card_congr (Ideal.quotientEquiv _ _ e.toRingEquiv ?_).toEquiv` and prove the remaining obligations. Rewrite using `[Ideal.map_span, Set.image_singleton]`. Use `congr 2`.

Conclude with `(e.commutes d).symm`. Establish `hfL : ((algebraMap O A d : A.toSubring) : L) = f` using `rfl`. Establish `hcq` using `card_quot_span_eq_relIndex A.toSubring (algebraMap O A d : A.toSubring)`. Rewrite `hcq` using `[hfL]`. Establish `key : Nat.card (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) d}) ≠ 0`.

Rewrite using `[LocalQuotCard.proof L O hft hfr m d hd0]`. Use `pow_ne_zero _ ?_` and prove the remaining obligations. Establish `hq : Algebra.FiniteType ℤ (O ⧸ m)` using `@Algebra.FiniteType.of_surjective ℤ O (O ⧸ m) _ _ _ _ _ hft (Ideal.Quotient.mkₐ ℤ m) (Ideal.Quotient.mkₐ_surjective ℤ m)`. Set `_ : Field (O ⧸ m)` to `Ideal.Quotient.field m`. Apply the tactic sequence `obtain ⟨hp, hc⟩ := @natCard_eq_pow_length_of_finiteType (O ⧸ m) _ (by convert hq <;> rfl) (ringChar (O ⧸ m)) (ringChar.charP _)`.

Rewrite using `[hc]`. Conclude with `pow_ne_zero _ hp.ne_zero`. Rewrite using `[← hcq]`. Conclude with `fun h ↦ key (hq1.trans h)`. Rewrite `hcard` using `[← e1]`.

Conclude with `left_ne_zero_of_mul hcard`.
-/
theorem LocalNormalIndex.proof : LocalNormalIndex.Statement := by
  intro L _ _ O hft hfr m _
  set A := Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors
  set C := integralClosure A L
  have : Algebra.FiniteType ℤ O := hft
  have : CharZero O := ⟨fun a b h ↦ by
    have := congrArg (fun t : O ↦ (t : L)) h
    simpa using this⟩

  have hfin : Module.Finite O (integralClosure O L) :=
    Model.finite_integralClosure_fractionRing_of_charZero O L
  obtain ⟨d, hd, hdI⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors O)
    (Module.Finite.iff_fg.mp hfin : (Subalgebra.toSubmodule (integralClosure O L)).FG)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdL : algebraMap O L d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd

  have hdC : ∀ x ∈ C, algebraMap O L d * x ∈ A := by
    intro x hx
    obtain ⟨⟨s, hs⟩, hsx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (R := O) (M := m.primeCompl) (Rₘ := A) x hx
    obtain ⟨o, ho⟩ := hdI _ hsx
    have hs0 : algebraMap O L s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (m.primeCompl_le_nonZeroDivisors hs)
    simp only [Submonoid.smul_def, Algebra.smul_def] at ho
    refine ⟨o, s, hs, ?_⟩
    rw [ho]
    field_simp

  have hAC : A.toSubring ≤ C.toSubring := fun x hx ↦
    (isIntegral_algebraMap : IsIntegral A (algebraMap A L ⟨x, hx⟩))
  set f := algebraMap O L d
  have hinj : Function.Injective (AddMonoidHom.mulLeft f) := mul_right_injective₀ hdL
  have h1 : A.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤
      C.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f) := AddSubgroup.map_mono hAC
  have h2 : C.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ A.toSubring.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact hdC y hy
  have e1 := AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hinj] at e1
  have hcard : (A.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f)).relIndex
      A.toSubring.toAddSubgroup ≠ 0 := by
    let e : Localization.AtPrime m ≃ₐ[O] A := IsLocalization.algEquiv m.primeCompl _ _
    have hq1 : Nat.card (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) d}) =
        Nat.card (A.toSubring ⧸ Ideal.span {(algebraMap O A d : A.toSubring)}) := by
      refine Nat.card_congr (Ideal.quotientEquiv _ _ e.toRingEquiv ?_).toEquiv
      rw [Ideal.map_span, Set.image_singleton]
      congr 2
      exact (e.commutes d).symm
    have hfL : ((algebraMap O A d : A.toSubring) : L) = f := rfl
    have hcq := card_quot_span_eq_relIndex A.toSubring (algebraMap O A d : A.toSubring)
    rw [hfL] at hcq
    have key : Nat.card (Localization.AtPrime m ⧸
        Ideal.span {algebraMap O (Localization.AtPrime m) d}) ≠ 0 := by
      rw [LocalQuotCard.proof L O hft hfr m d hd0]
      refine pow_ne_zero _ ?_
      have hq : Algebra.FiniteType ℤ (O ⧸ m) :=
        @Algebra.FiniteType.of_surjective ℤ O (O ⧸ m) _ _ _ _ _ hft (Ideal.Quotient.mkₐ ℤ m)
          (Ideal.Quotient.mkₐ_surjective ℤ m)
      let _ : Field (O ⧸ m) := Ideal.Quotient.field m
      obtain ⟨hp, hc⟩ :=
        @natCard_eq_pow_length_of_finiteType (O ⧸ m) _
          (by convert hq <;> rfl) (ringChar (O ⧸ m)) (ringChar.charP _)
      rw [hc]
      exact pow_ne_zero _ hp.ne_zero
    rw [← hcq]
    exact fun h ↦ key (hq1.trans h)
  rw [← e1] at hcard
  exact left_ne_zero_of_mul hcard

end GroundTheory.Heights₂.Heights
