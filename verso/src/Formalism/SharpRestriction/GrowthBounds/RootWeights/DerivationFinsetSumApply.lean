import Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantIsotypicOrthogonal

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]`.
-/
theorem derivation_finset_sum_apply {σ α : Type} (s : Finset α)
    (D : α → Derivation K (MvPolynomial σ K) (MvPolynomial σ K)) (F : MvPolynomial σ K) :
    (∑ l ∈ s, D l) F = ∑ l ∈ s, D l F := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

open Classical in

def glDerivation (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι) (a b : Fin n) :
    Derivation K (MvPolynomial (ι × Fin n) K) (MvPolynomial (ι × Fin n) K) :=
  ∑ l : ι, if l ∈ S then
      (if LL.vec l then (X (l, a) : MvPolynomial (ι × Fin n) K) • pderiv (l, b)
       else -((X (l, b) : MvPolynomial (ι × Fin n) K) • pderiv (l, a)))
    else 0

/- English proof (translation)
Unfold `glAct glDerivation`. Rewrite using `[LinearMap.sum_apply, derivation_finset_sum_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem gl_action_eq_derivation (LL : Letters ι) (S : Set ι) (a b : Fin n) (F : MvPolynomial (ι × Fin n) K) :
    glAct K LL S a b F = glDerivation K LL S a b F := by
  unfold glAct glDerivation
  rw [LinearMap.sum_apply, derivation_finset_sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

open Classical in
/- English proof (translation)
Unfold `glDerivation`. Rewrite using `[derivation_finset_sum_apply, Finset.sum_eq_single l]`. Apply the tactic sequence `split_ifs <;> simp_all [pderiv_X, Pi.single_apply]`. Apply the tactic sequence `intro l' _ hl' split_ifs <;> simp [pderiv_X, Pi.single_apply, Ne.symm hl']`. Simplify using the standard rewrite rules.
-/
theorem gl_derivation_variable (LL : Letters ι) (S : Set ι) (a b : Fin n) (l : ι) (c : Fin n) :
    glDerivation K LL S a b (X (l, c)) =
      if l ∈ S then (if LL.vec l then (if c = b then X (l, a) else 0) else (if c = a then -X (l, b) else 0))
      else 0 := by
  unfold glDerivation
  rw [derivation_finset_sum_apply, Finset.sum_eq_single l]
  · split_ifs <;> simp_all [pderiv_X, Pi.single_apply]
  · intro l' _ hl'
    split_ifs <;> simp [pderiv_X, Pi.single_apply, Ne.symm hl']
  · simp

/- English proof (translation)
Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce and unpack `⟨l, e⟩`. Rewrite using `[Derivation.commutator_apply]`. Distinguish the cases in `hl : l ∈ S`. Distinguish the cases in `hv : LL.vec l = true`.

Simplify using `only [gl_derivation_variable, hl, hv, if_true, apply_ite (glDerivation K LL S a b), apply_ite (glDerivation K LL S c d), map_zero, Derivation.coe_sub, Pi.sub_apply]`. Apply the tactic sequence `by_cases h1 : b = c <;> by_cases h2 : d = a <;> by_cases h3 : e = d <;> by_cases h4 : e = b <;> subst_vars <;> simp_all [gl_derivation_variable] <;> grind`. Simplify using `only [gl_derivation_variable, hl, hv, if_true, apply_ite (glDerivation K LL S a b), apply_ite (glDerivation K LL S c d), map_zero, map_neg, Derivation.coe_sub, Pi.sub_apply]`. Apply the tactic sequence `by_cases h1 : b = c <;> by_cases h2 : d = a <;> by_cases h3 : e = c <;> by_cases h4 : e = a <;> subst_vars <;> simp_all [gl_derivation_variable]`. Apply the tactic sequence `by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [gl_derivation_variable, hl, h1, h2]`.
-/
theorem gl_derivation_lie_bracket (LL : Letters ι) (S : Set ι) (a b c d : Fin n) :
    ⁅glDerivation K LL S a b, glDerivation K LL S c d⁆ =
      (if b = c then glDerivation K LL S a d else 0) - (if d = a then glDerivation K LL S c b else 0) := by
  classical
  apply MvPolynomial.derivation_ext
  rintro ⟨l, e⟩
  rw [Derivation.commutator_apply]
  by_cases hl : l ∈ S
  · by_cases hv : LL.vec l = true
    · simp only [gl_derivation_variable, hl, hv, if_true, apply_ite (glDerivation K LL S a b), apply_ite (glDerivation K LL S c d),
        map_zero, Derivation.coe_sub, Pi.sub_apply]
      by_cases h1 : b = c <;> by_cases h2 : d = a <;> by_cases h3 : e = d <;> by_cases h4 : e = b <;>
        subst_vars <;> simp_all [gl_derivation_variable] <;> grind
    · simp only [gl_derivation_variable, hl, hv, if_true, apply_ite (glDerivation K LL S a b), apply_ite (glDerivation K LL S c d),
        map_zero, map_neg, Derivation.coe_sub, Pi.sub_apply]
      by_cases h1 : b = c <;> by_cases h2 : d = a <;> by_cases h3 : e = c <;> by_cases h4 : e = a <;>
        subst_vars <;> simp_all [gl_derivation_variable]
  · by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [gl_derivation_variable, hl, h1, h2]

end Formalism.MainNotions.G.GLWeightTheory
