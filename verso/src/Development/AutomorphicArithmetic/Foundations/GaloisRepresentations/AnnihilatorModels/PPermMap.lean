import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `I I' P _ _ f g h`. Establish `hc : ∀ p : P, Fintype.card {i // f i = p} = Fintype.card {j // g j = p}`. Introduce `p`. Establish `hp` using `congrArg (Multiset.count p) h`. Simplify using `only [Multiset.count_map] at hp`.

Rewrite using `[Fintype.card_subtype, Fintype.card_subtype]`. Simplify `hp` using `[Finset.card_def, Finset.filter_val, eq_comm]`. Set `e : ∀ p, {i // f i = p} ≃ {j // g j = p}` to `fun p => Fintype.equivOfCardEq (hc p)`. Use `⟨(Equiv.sigmaFiberEquiv f).symm.trans ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv g)), ?_⟩` and prove the remaining obligations. Introduce `i`.

Use `show f i = g ((e (f i)) ⟨i, rfl⟩).1`. Conclude with `((e (f i)) ⟨i, rfl⟩).2.symm`.
-/
theorem UpperTheory.Gal.crystallineComparison.permMap_of :
    PermOfMap := by
  classical
  intro I I' P _ _ f g h
  have hc : ∀ p : P, Fintype.card {i // f i = p} = Fintype.card {j // g j = p} := by
    intro p
    have hp := congrArg (Multiset.count p) h
    simp only [Multiset.count_map] at hp
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card_def, Finset.filter_val, eq_comm] using hp
  let e : ∀ p, {i // f i = p} ≃ {j // g j = p} := fun p => Fintype.equivOfCardEq (hc p)
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv g)), ?_⟩
  intro i
  show f i = g ((e (f i)) ⟨i, rfl⟩).1
  exact ((e (f i)) ⟨i, rfl⟩).2.symm
