import Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantIsotypicOrthogonal

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_weightSpace_iff_diagonal_rep (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
theorem gl_commutation_apply {E : GLOps n K V} (hE : IsGLRep E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) + (if b = c then E a d x else 0) - (if d = a then E c b x else 0) := by
  have h := LinearMap.congr_fun (hE.1 a b c d) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have e1 : (if b = c then E a d else 0) x = (if b = c then E a d x else 0) := by split_ifs <;> rfl
  have e2 : (if d = a then E c b else 0) x = (if d = a then E c b x else 0) := by split_ifs <;> rfl
  rw [e1, e2] at h
  rw [add_sub_assoc, ← h]
  abel

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations.

Apply the first step, then apply the next step to every resulting obligation.
-/
theorem gl_rep_weight_shift {E : GLOps n K V} (hE : IsGLRep E) {mu : Fin n → ℤ} {x : V}
    (hx : x ∈ weightSp E mu) (a b : Fin n) : E a b x ∈ weightSp E (mu + rootW a b) := by
  rw [mem_weightSpace_iff_diagonal_rep] at hx ⊢
  intro c
  rw [gl_commutation_apply hE c c a b x, hx c, map_smul]
  simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  push_cast
  split_ifs <;> subst_vars <;> first | module | (exfalso; simp_all; done)

end Formalism.MainNotions.G.GLWeightTheory
