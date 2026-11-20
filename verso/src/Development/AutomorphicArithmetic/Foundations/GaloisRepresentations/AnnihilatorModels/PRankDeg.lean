import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `hSF A S _ _ _ _ _ d hd`. Use function extensionality and compare the values at `p`. Use `letI : Algebra A (AlgebraicClosure p.asIdeal.ResidueField) := ((algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp (algebraMap A p.asIdeal.ResidueField)).toAlgebra`. Set `q : PrimeSpectrum (AlgebraicClosure p.asIdeal.ResidueField)` to `⟨⊥, Ideal.isPrime_bot⟩`. Establish `hq : PrimeSpectrum.comap (algebraMap A (AlgebraicClosure p.asIdeal.ResidueField)) q = p`.

Use extensionality with `x`. Express the relevant statement in the definitionally equal form `algebraMap A (AlgebraicClosure p.asIdeal.ResidueField) x ∈ (⊥ : Ideal _) ↔ x ∈ p.asIdeal`. Rewrite using `[Ideal.mem_bot]`. Express the relevant statement in the definitionally equal form `algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField) (algebraMap A p.asIdeal.ResidueField x) = 0 ↔ x ∈ p.asIdeal`. Rewrite using `[map_eq_zero_iff _ (algebraMap p.asIdeal.ResidueField _).injective, Ideal.algebraMap_residueField_eq_zero]`.

Rewrite using `[← hq, ← Module.rankAtStalk_baseChange q, Module.rankAtStalk_eq_finrank_of_free]`. Take `⟨hfin, hsp⟩` from `hSF A S (AlgebraicClosure p.asIdeal.ResidueField) inferInstance`. Use `haveI := Fintype.ofFinite (S →ₐ[A] AlgebraicClosure p.asIdeal.ResidueField)`. Establish `e` using `AlgEquiv.ofBijective (splitMap fun z => z) hsp`. Establish `h1` using `e.toLinearEquiv.finrank_eq`.

Rewrite `h1` using `[Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, hd (AlgebraicClosure p.asIdeal.ResidueField)]`. Simplify using `[h1]`.
-/
theorem UpperTheory.Gal.crystallineComparison.rankDeg_of :
    SplitsField → RankOfDeg := by
  intro hSF A S _ _ _ _ _ d hd
  funext p
  letI : Algebra A (AlgebraicClosure p.asIdeal.ResidueField) :=
    ((algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
      (algebraMap A p.asIdeal.ResidueField)).toAlgebra
  let q : PrimeSpectrum (AlgebraicClosure p.asIdeal.ResidueField) := ⟨⊥, Ideal.isPrime_bot⟩
  have hq : PrimeSpectrum.comap (algebraMap A (AlgebraicClosure p.asIdeal.ResidueField)) q = p := by
    ext x
    change algebraMap A (AlgebraicClosure p.asIdeal.ResidueField) x ∈ (⊥ : Ideal _) ↔ x ∈ p.asIdeal
    rw [Ideal.mem_bot]
    change algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)
      (algebraMap A p.asIdeal.ResidueField x) = 0 ↔ x ∈ p.asIdeal
    rw [map_eq_zero_iff _ (algebraMap p.asIdeal.ResidueField _).injective,
      Ideal.algebraMap_residueField_eq_zero]
  rw [← hq, ← Module.rankAtStalk_baseChange q, Module.rankAtStalk_eq_finrank_of_free]
  obtain ⟨hfin, hsp⟩ := hSF A S (AlgebraicClosure p.asIdeal.ResidueField) inferInstance
  haveI := Fintype.ofFinite (S →ₐ[A] AlgebraicClosure p.asIdeal.ResidueField)
  have e := AlgEquiv.ofBijective (splitMap fun z => z) hsp
  have h1 := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card,
    hd (AlgebraicClosure p.asIdeal.ResidueField)] at h1
  simp [h1]
