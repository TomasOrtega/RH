import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LSatLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem lsat_spec_colAddGen {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n) (c : R) :
    (aeval (fun o : Option (Fin r × Fin n) => Option.elim o (C c) X)).comp (colAddGen R l j) =
      colAdd R l j c := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, colAddGen, colAdd, aeval_X]
  split_ifs <;> simp

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem lsat_spec_rename {R : Type*} [CommRing R] {r n : ℕ} (c : R) :
    (aeval (fun o : Option (Fin r × Fin n) => Option.elim o (C c) X)).comp
      (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [rename_X]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem lsat_eval_colAddGen {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n)
    (x : Option (Fin r × Fin n) → R) :
    (aeval x).comp (colAddGen R l j) = (aeval (x ∘ some)).comp (colAdd R l j (x none)) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, colAddGen, colAdd, aeval_X]
  split_ifs <;> simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem dualWeylModuleMemIff : DualWeylPoint := by
  intro R _ _ _ r n ν f
  rw [lsat_mem_dualWeyl]
  refine and_congr_right fun _ => forall₂_congr fun l j => imp_congr_right fun _ => ?_
  constructor
  · intro h c
    let ψ : Option (Fin r × Fin n) → MvPolynomial (Fin r × Fin n) R :=
      fun o => Option.elim o (C c) X
    have h1 : aeval ψ (colAddGen R l j f) = aeval ψ (rename some f) := by rw [h]
    have e1 : aeval ψ (colAddGen R l j f) = colAdd R l j c f := by
      rw [← AlgHom.comp_apply, lsat_spec_colAddGen]
    have e2 : aeval ψ (rename some f) = f := by
      rw [← AlgHom.comp_apply, lsat_spec_rename, AlgHom.id_apply]
    rw [← e1, h1, e2]
  · intro h
    apply MvPolynomial.funext
    intro x
    have e := congrArg (fun φ => φ f) (lsat_eval_colAddGen (R := R) l j x)
    simp only [AlgHom.comp_apply, h] at e
    change aeval x (colAddGen R l j f) = aeval x (rename some f)
    rw [e, aeval_rename]

end Formalism.GradedWeylDivisibility
