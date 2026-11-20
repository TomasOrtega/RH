import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def coordV (c : Fin n) : (Fin n → M) →ₗ[ℂ] M := LinearMap.proj c

def tensV (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun c => (E a b).comp (coordV c) + if c = a then coordV b else 0

def tensVd (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun c => (E a b).comp (coordV c) - if c = b then coordV a else 0

def eeV (E : Fin n → Fin n → Module.End ℂ M) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun s => ∑ r, (E r s).comp (coordV r)

def eeVd (E : Fin n → Fin n → Module.End ℂ M) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun r => -∑ s, (E r s).comp (coordV s)

def diagOp (A : Module.End ℂ M) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun c => A.comp (coordV c)

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem tensV_coord (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + if c = a then f b else 0 := by
  simp only [tensV, coordV, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  split_ifs <;> simp [LinearMap.proj_apply]

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem tensVd_coord (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - if c = b then f a else 0 := by
  simp only [tensVd, coordV, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  split_ifs <;> simp [LinearMap.proj_apply]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem eeV_coord (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (s : Fin n) :
    eeV E f s = ∑ r, E r s (f r) := by
  simp [eeV, coordV, LinearMap.pi_apply, LinearMap.sum_apply]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem eeVd_coord (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (r : Fin n) :
    eeVd E f r = -∑ s, E r s (f s) := by
  simp [eeVd, coordV, LinearMap.pi_apply, LinearMap.sum_apply]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem diagOp_coord (A : Module.End ℂ M) (f : Fin n → M) (c : Fin n) :
    diagOp (n := n) A f c = A (f c) := by
  simp [diagOp, coordV]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem isGlRep_apply_swap {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (a b c d : Fin n) (v : M) :
    E a b (E c d v) = E c d (E a b v) + ((if b = c then E a d v else 0) - (if d = a then E c b v else 0)) := by
  have h := LinearMap.congr_fun (hE a b c d) v
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, sub_eq_iff_eq_add'] at h
  rw [h]; congr 1
  split_ifs <;> simp

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem ite_end_coord (p : Prop) [Decidable p] (A : Module.End ℂ (Fin n → M)) (f : Fin n → M) (x : Fin n) :
    (if p then A else 0) f x = if p then A f x else 0 := by
  split_ifs <;> rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem tensV_isGlRep {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) : IsGlRep (tensV E) := by
  intro a b c d
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [LinearMap.sub_apply, Pi.sub_apply, Module.End.mul_apply, tensV_coord, map_add,
    isGlRep_apply_swap hE a b c d, ite_end_coord]
  split_ifs <;> subst_vars <;>
    simp only [map_zero, add_zero, sub_zero, zero_sub, sub_self] <;> abel

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem tensVd_isGlRep {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) : IsGlRep (tensVd E) := by
  intro a b c d
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [LinearMap.sub_apply, Pi.sub_apply, Module.End.mul_apply, tensVd_coord, map_sub,
    isGlRep_apply_swap hE a b c d, ite_end_coord]
  split_ifs <;> subst_vars <;>
    simp only [map_zero, add_zero, sub_zero, zero_sub, sub_self] <;> first | (exfalso; simp_all; done) | abel

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.
-/
theorem casimir_tensV {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) :
    casimir (tensV E) = diagOp (casimir E) + (n : ℂ) • 1 + (2 : ℂ) • eeV E := by
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [casimir, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply,
    Module.End.mul_apply, Pi.add_apply, Pi.smul_apply, diagOp_coord, eeV_coord, tensV_coord, map_add,
    Module.End.one_apply]
  simp only [apply_ite (E _ _), map_zero, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have key : ∀ g : Fin n → Fin n → M, (∑ i, ∑ j, if x = i then g i j else 0) = ∑ j, g x j := by
    intro g
    rw [Finset.sum_eq_single x (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
    simp
  rw [key (fun i j => E j i (f j) + f i)]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.cast_smul_eq_nsmul, two_smul]
  abel

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.
-/
theorem casimir_tensVd {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) :
    casimir (tensVd E) = diagOp (casimir E) + (n : ℂ) • 1 + (2 : ℂ) • eeVd E := by
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [casimir, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply,
    Module.End.mul_apply, Pi.add_apply, Pi.smul_apply, diagOp_coord, eeVd_coord, tensVd_coord, map_sub,
    Module.End.one_apply]
  simp only [apply_ite (E _ _), map_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have key : ∀ g : Fin n → Fin n → M, (∑ i, ∑ j, if x = i then g i j else 0) = ∑ j, g x j := by
    intro g
    rw [Finset.sum_eq_single x (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
    simp
  rw [key (fun i j => E i j (f j))]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul, two_smul]
  abel

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Simplify using the standard rewrite rules.
-/
theorem eeV_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (a b : Fin n) :
    tensV E a b * eeV E = eeV E * tensV E a b := by
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [Module.End.mul_apply, tensV_coord, eeV_coord, map_sum, map_add, isGlRep_apply_swap hE a b]
  simp only [apply_ite (E _ _), map_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : x = a
  · subst h; simp only [if_true]; abel
  · simp only [h, if_false, Finset.sum_const_zero, sub_zero, add_zero]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Establish an intermediate fact. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.
-/
theorem eeVd_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (a b : Fin n) :
    tensVd E a b * eeVd E = eeVd E * tensVd E a b := by
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [Module.End.mul_apply, tensVd_coord, eeVd_coord, map_sum, map_neg, map_sub, isGlRep_apply_swap hE a b]
  simp only [apply_ite (E _ _), map_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : x = b
  · subst h; simp only [if_true]; abel
  · have h' : ¬ b = x := fun e => h e.symm
    simp only [h, h', if_false, Finset.sum_const_zero, sub_zero, zero_sub]
    abel

end ReciprocityTheory.ChartRestriction.DS
