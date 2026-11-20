import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent

namespace GlobalTheory.CompanionTheory.Kaehler

/- English proof (translation)
Use `letI : Algebra (MvPolynomial I K) L := (MvPolynomial.aeval u).toRingHom.toAlgebra`. Establish `hmap : ∀ q : MvPolynomial I K, algebraMap (MvPolynomial I K) L q = MvPolynomial.aeval u q` using `fun _ => rfl`. Establish `: IsScalarTower K (MvPolynomial I K) L` using `IsScalarTower.of_algebraMap_eq fun x => by rw [hmap, AlgHom.commutes]`. Establish `: FaithfulSMul (MvPolynomial I K) L` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hu`. Establish `: IsFractionRing (MvPolynomial I K) L` using `IsFractionRing.of_field (MvPolynomial I K) L fun z => by`.

Establish `hz : z ∈ IntermediateField.adjoin K (Set.range u)` using `by rw [hadj]; trivial`. Take `⟨r, s, h⟩` from `(IntermediateField.mem_adjoin_range_iff K u z).1 hz`. Conclude with `⟨r, s, h⟩`. Use `Algebra.FormallyEtale.of_isLocalization (Rₘ := L) (nonZeroDivisors (MvPolynomial I K))` as an intermediate fact. Establish `hbc` using `KaehlerDifferential.isBaseChange_of_formallyEtale K (MvPolynomial I K) L`.

Rewrite using `[Module.finrank_eq_card_basis (hbc.basis (KaehlerDifferential.mvPolynomialBasis K I))]`.
-/
theorem finrank_kaehlerDifferential_of_adjoin_eq_top (K L : Type) [Field K] [Field L] [Algebra K L]
    (I : Type) [Fintype I] (u : I → L) (hu : AlgebraicIndependent K u)
    (hadj : IntermediateField.adjoin K (Set.range u) = ⊤) :
    Module.finrank L (KaehlerDifferential K L) = Fintype.card I := by
  classical
  letI : Algebra (MvPolynomial I K) L := (MvPolynomial.aeval u).toRingHom.toAlgebra
  have hmap : ∀ q : MvPolynomial I K, algebraMap (MvPolynomial I K) L q = MvPolynomial.aeval u q :=
    fun _ => rfl
  have : IsScalarTower K (MvPolynomial I K) L :=
    IsScalarTower.of_algebraMap_eq fun x => by rw [hmap, AlgHom.commutes]
  have : FaithfulSMul (MvPolynomial I K) L := (faithfulSMul_iff_algebraMap_injective _ _).2 hu
  have : IsFractionRing (MvPolynomial I K) L := IsFractionRing.of_field (MvPolynomial I K) L fun z => by
    have hz : z ∈ IntermediateField.adjoin K (Set.range u) := by rw [hadj]; trivial
    obtain ⟨r, s, h⟩ := (IntermediateField.mem_adjoin_range_iff K u z).1 hz
    exact ⟨r, s, h⟩
  have := Algebra.FormallyEtale.of_isLocalization (Rₘ := L) (nonZeroDivisors (MvPolynomial I K))
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale K (MvPolynomial I K) L
  rw [Module.finrank_eq_card_basis (hbc.basis (KaehlerDifferential.mvPolynomialBasis K I))]

end GlobalTheory.CompanionTheory.Kaehler
