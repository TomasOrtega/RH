import Mathlib

namespace GlobalTheory

open IsLocalRing

open IsLocalRing in

/- English proof (translation)
Use `haveI : Algebra.IsIntegral K Ω := inferInstance`. Use `letI : TopologicalSpace (integralClosure V Ω) := ⊥`. Use `haveI : DiscreteTopology (integralClosure V Ω) := ⟨rfl⟩`. Use `haveI : ContinuousSMul (Ω ≃ₐ[K] Ω) (integralClosure V Ω) := by`. Rewrite using `[continuousSMul_iff_stabilizer_isOpen]`.

Introduce `x`. Use `stabilizer_isOpen_of_isIntegral (K := K) (L := Ω) (x : Ω) using 2` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Simplify using `[MulAction.mem_stabilizer_iff, Subtype.ext_iff]`. Use `haveI : Algebra.IsInvariant V (integralClosure V Ω) (Ω ≃ₐ[K] Ω) := by`.

Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Establish `hmem : (x : Ω) ∈ IntermediateField.fixedField (⊤ : Subgroup (Ω ≃ₐ[K] Ω))`. Introduce and unpack `⟨g, -⟩`. Conclude with `congrArg Subtype.val (hx g)`. Rewrite `hmem` using `[InfiniteGalois.fixedField_bot, IntermediateField.mem_bot]`.

Take `⟨k, hk⟩` from `hmem`. Establish `hx2 : IsIntegral V (x : Ω)` using `x.2`. Rewrite `hx2` using `[← hk]`. Establish `hint : IsIntegral V k` using `(isIntegral_algHom_iff (IsScalarTower.toAlgHom V K Ω) (algebraMap K Ω).injective).mp hx2`. Take `⟨v, hv⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint`.

Use `⟨v, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `[IsScalarTower.algebraMap_apply V K Ω, hv, hk]`. Use `haveI : (maximalIdeal (integralClosure V Ω)).LiesOver (maximalIdeal V) := by`. Use `⟨(IsLocalRing.eq_maximalIdeal ?_).symm⟩` and prove the remaining obligations. Conclude with `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _`.

Use `letI : Fintype (V ⧸ maximalIdeal V) := @Fintype.ofFinite _ hfin`. Use `letI : Field (V ⧸ maximalIdeal V) := Ideal.Quotient.field _`. Use `letI : Field (integralClosure V Ω ⧸ maximalIdeal (integralClosure V Ω)) := Ideal.Quotient.field _`. Use `haveI : Algebra.IsIntegral (V ⧸ maximalIdeal V) (integralClosure V Ω ⧸ maximalIdeal (integralClosure V Ω)) := inferInstance`. Use `haveI : Algebra.IsAlgebraic (V ⧸ maximalIdeal V) (integralClosure V Ω ⧸ maximalIdeal (integralClosure V Ω)) := Algebra.IsIntegral.isAlgebraic`.

Take `⟨g, hg⟩` from `Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Ω ≃ₐ[K] Ω) (maximalIdeal V) (maximalIdeal (integralClosure V Ω)) (FiniteField.frobeniusAlgEquivOfAlgebraic (V ⧸ maximalIdeal V) _)`. Use `⟨g.1, fun x => ⟨g.1 • x, rfl, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq]`. Establish `h` using `congrArg (fun e => e (Ideal.Quotient.mk (maximalIdeal (integralClosure V Ω)) x)) hg`. Simplify using `only [Ideal.Quotient.stabilizerHom_apply, FiniteField.frobeniusAlgEquivOfAlgebraic_apply] at h`.

Rewrite `h` using `[Fintype.card_eq_nat_card]`. Rewrite using `[map_pow]`. Conclude with `h`.
-/
theorem _root_.GlobalTheory.exists_arithFrobenius_absGalois (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (hfin : Finite (IsLocalRing.ResidueField V)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω] [IsLocalRing (integralClosure V Ω)] : ∃ φ : Ω ≃ₐ[K] Ω, ∀ x : integralClosure V Ω, ∃ y : integralClosure V Ω, (y : Ω) = φ x ∧ y - x ^ Nat.card (IsLocalRing.ResidueField V) ∈ IsLocalRing.maximalIdeal (integralClosure V Ω) := by
  classical
  haveI : Algebra.IsIntegral K Ω := inferInstance
  letI : TopologicalSpace (integralClosure V Ω) := ⊥
  haveI : DiscreteTopology (integralClosure V Ω) := ⟨rfl⟩
  haveI : ContinuousSMul (Ω ≃ₐ[K] Ω) (integralClosure V Ω) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    convert stabilizer_isOpen_of_isIntegral (K := K) (L := Ω) (x : Ω) using 2
    ext g
    simp [MulAction.mem_stabilizer_iff, Subtype.ext_iff]
  haveI : Algebra.IsInvariant V (integralClosure V Ω) (Ω ≃ₐ[K] Ω) := by
    refine ⟨fun x hx => ?_⟩
    have hmem : (x : Ω) ∈ IntermediateField.fixedField (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) := by
      rintro ⟨g, -⟩
      exact congrArg Subtype.val (hx g)
    rw [InfiniteGalois.fixedField_bot, IntermediateField.mem_bot] at hmem
    obtain ⟨k, hk⟩ := hmem
    have hx2 : IsIntegral V (x : Ω) := x.2
    rw [← hk] at hx2
    have hint : IsIntegral V k :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom V K Ω) (algebraMap K Ω).injective).mp hx2
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    refine ⟨v, Subtype.ext ?_⟩
    simp [IsScalarTower.algebraMap_apply V K Ω, hv, hk]
  haveI : (maximalIdeal (integralClosure V Ω)).LiesOver (maximalIdeal V) := by
    refine ⟨(IsLocalRing.eq_maximalIdeal ?_).symm⟩
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
  letI : Fintype (V ⧸ maximalIdeal V) := @Fintype.ofFinite _ hfin
  letI : Field (V ⧸ maximalIdeal V) := Ideal.Quotient.field _
  letI : Field (integralClosure V Ω ⧸ maximalIdeal (integralClosure V Ω)) :=
    Ideal.Quotient.field _
  haveI : Algebra.IsIntegral (V ⧸ maximalIdeal V)
      (integralClosure V Ω ⧸ maximalIdeal (integralClosure V Ω)) := inferInstance
  haveI : Algebra.IsAlgebraic (V ⧸ maximalIdeal V)
      (integralClosure V Ω ⧸ maximalIdeal (integralClosure V Ω)) := Algebra.IsIntegral.isAlgebraic
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Ω ≃ₐ[K] Ω)
    (maximalIdeal V) (maximalIdeal (integralClosure V Ω))
    (FiniteField.frobeniusAlgEquivOfAlgebraic (V ⧸ maximalIdeal V) _)
  refine ⟨g.1, fun x => ⟨g.1 • x, rfl, ?_⟩⟩
  rw [← Ideal.Quotient.eq]
  have h := congrArg (fun e => e (Ideal.Quotient.mk (maximalIdeal (integralClosure V Ω)) x)) hg
  simp only [Ideal.Quotient.stabilizerHom_apply, FiniteField.frobeniusAlgEquivOfAlgebraic_apply] at h
  rw [Fintype.card_eq_nat_card] at h
  rw [map_pow]
  exact h

end GlobalTheory
