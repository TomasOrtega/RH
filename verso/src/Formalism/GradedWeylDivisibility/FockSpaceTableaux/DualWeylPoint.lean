import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LSatLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply, colAddGen, colAdd, aeval_X]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem lsat_spec_colAddGen {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n) (c : R) :
    (aeval (fun o : Option (Fin r × Fin n) => Option.elim o (C c) X)).comp (colAddGen R l j) =
      colAdd R l j c := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, colAddGen, colAdd, aeval_X]
  split_ifs <;> simp

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `[rename_X]`.
-/
theorem lsat_spec_rename {R : Type*} [CommRing R] {r n : ℕ} (c : R) :
    (aeval (fun o : Option (Fin r × Fin n) => Option.elim o (C c) X)).comp
      (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [rename_X]

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply, colAddGen, colAdd, aeval_X]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem lsat_eval_colAddGen {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n)
    (x : Option (Fin r × Fin n) → R) :
    (aeval x).comp (colAddGen R l j) = (aeval (x ∘ some)).comp (colAdd R l j (x none)) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, colAddGen, colAdd, aeval_X]
  split_ifs <;> simp

/- English proof (translation)
Introduce `R _ _ _ r n ν f`. Rewrite using `[lsat_mem_dualWeyl]`. Use `and_congr_right fun _ => forall₂_congr fun l j => imp_congr_right fun _ => ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `h c`.

Set `ψ : Option (Fin r × Fin n) → MvPolynomial (Fin r × Fin n) R` to `fun o => Option.elim o (C c) X`. Establish `h1 : aeval ψ (colAddGen R l j f) = aeval ψ (rename some f)` using `by rw [h]`. Establish `e1 : aeval ψ (colAddGen R l j f) = colAdd R l j c f`. Rewrite using `[← AlgHom.comp_apply, lsat_spec_colAddGen]`. Establish `e2 : aeval ψ (rename some f) = f`.

Rewrite using `[← AlgHom.comp_apply, lsat_spec_rename, AlgHom.id_apply]`. Rewrite using `[← e1, h1, e2]`. Introduce `h`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`.

Establish `e` using `congrArg (fun φ => φ f) (lsat_eval_colAddGen (R := R) l j x)`. Simplify using `only [AlgHom.comp_apply, h] at e`. Express the relevant statement in the definitionally equal form `aeval x (colAddGen R l j f) = aeval x (rename some f)`. Rewrite using `[e, aeval_rename]`.
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
