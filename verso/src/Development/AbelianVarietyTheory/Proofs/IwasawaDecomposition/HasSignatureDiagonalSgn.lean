import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. By extensionality, compare the relevant components.

Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem hasSignature_diagonal_sgn (N : ℕ) (neg : Fin N → Bool) :
    Formalism.UG.HasSignature (Matrix.diagonal fun i : Fin N => (Examples₂.sgn (neg i) : ℂ))
      (Finset.univ.filter fun i => neg i = false).card
      (Finset.univ.filter fun i => neg i = true).card := by
  classical
  let e1 : {i // neg i = false} ≃ Fin (Finset.univ.filter fun i => neg i = false).card :=
    Fintype.equivFinOfCardEq (Fintype.card_subtype _)
  let e2 : {i // ¬ neg i = false} ≃ Fin (Finset.univ.filter fun i => neg i = true).card :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype]; simp)
  let f : Fin (Finset.univ.filter fun i => neg i = false).card ⊕
      Fin (Finset.univ.filter fun i => neg i = true).card ≃ Fin N :=
    (Equiv.sumCongr e1.symm e2.symm).trans (Equiv.sumCompl fun i => neg i = false)
  have h1 : ∀ i, neg (f (Sum.inl i)) = false := fun i => (e1.symm i).2
  have h2 : ∀ i, neg (f (Sum.inr i)) = true := fun i => by
    have h : ¬ neg (f (Sum.inr i)) = false := (e2.symm i).2
    simpa using h
  refine ⟨f.symm, 1, ?_⟩
  simp only [Units.val_one, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, h1, h2, Examples₂.sgn]
  split_ifs <;> simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Express the relevant assertion in an equivalent form by its definition. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem stdSpace_sigOK_count (E : Type) [Field E] [NumberField E] [StarRing E]
    (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ) (neg : Fin N → Bool) :
    (Formalism.BasicNotions.Examples₂.stdSpace hstar N neg (Finset.univ.filter fun i => neg i = false).card
      (Finset.univ.filter fun i => neg i = true).card).SigOK := by
  intro τ
  have hg : (Formalism.BasicNotions.Examples₂.stdSpace hstar N neg (Finset.univ.filter fun i => neg i = false).card
      (Finset.univ.filter fun i => neg i = true).card).gram.map τ =
      Matrix.diagonal fun i : Fin N => (Examples₂.sgn (neg i) : ℂ) := by
    ext i j
    rw [Matrix.map_apply]
    refine (congrArg τ (Examples₂.stdSpace_gram_apply hstar N neg _ _ i j)).trans ?_
    change τ (if i = j then (Examples₂.sgn (neg i) : E) else 0) =
      if i = j then (Examples₂.sgn (neg i) : ℂ) else 0
    by_cases h : i = j <;> simp [h, Examples₂.map_sgn]
  rw [hg]
  exact hasSignature_diagonal_sgn N neg

end GlobalTheory
