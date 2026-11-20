import Mathlib

namespace GlobalTheory.CardinalPower

open IntermediateField

/- English proof (translation)
Set `M : IntermediateField K L` to `adjoin K (X : Set L)`. Use `haveI : FiniteDimensional K M := finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)`. Use `haveI : Finite M := Module.finite_of_finite K`. Use `haveI : Normal K M := inferInstance`. Take `⟨n, hn⟩` from `(FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K M).2 (σ.restrictNormal M)`.

Use `⟨n.1, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hxM : x ∈ M` using `subset_adjoin K _ hx`. Establish `h1` using `AlgEquiv.restrictNormal_commutes σ M ⟨x, hxM⟩`. Rewrite `h1` using `[← hn]`. Simplify using `only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate] at h1`.

Simplify using `using h1.symm`.
-/
theorem exists_pow_card_eq {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (σ : Gal(L/K)) (X : Finset L) :
    ∃ i : ℕ, ∀ x ∈ X, (σ : L → L) x = x ^ Fintype.card K ^ i := by
  classical
  let M : IntermediateField K L := adjoin K (X : Set L)
  haveI : FiniteDimensional K M :=
    finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  haveI : Finite M := Module.finite_of_finite K
  haveI : Normal K M := inferInstance
  obtain ⟨n, hn⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K M).2 (σ.restrictNormal M)
  refine ⟨n.1, fun x hx => ?_⟩
  have hxM : x ∈ M := subset_adjoin K _ hx
  have h1 := AlgEquiv.restrictNormal_commutes σ M ⟨x, hxM⟩
  rw [← hn] at h1
  simp only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate] at h1
  simpa using h1.symm

/- English proof (translation)
Introduce `σ X` and use `exists_pow_card_eq σ X`.
-/
theorem target : ∀ {K L : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : Field L]
    [inst_3 : Algebra K L] [Algebra.IsAlgebraic K L] (σ : Gal(L/K)) (X : Finset L),
    ∃ (i : ℕ), ∀ x ∈ X, (σ : L → L) x = x ^ Fintype.card K ^ i :=
  fun σ X => exists_pow_card_eq σ X

end GlobalTheory.CardinalPower
