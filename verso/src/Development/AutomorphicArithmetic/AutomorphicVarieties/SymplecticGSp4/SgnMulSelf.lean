import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem wt_add' (i k j : Fin 4) : wt i j = wt i k + wt k j := by
  simp only [wt, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem wt_self' (i : Fin 4) : wt i i = 0 := by
  simp [wt]

variable {R : Type} [CommRing R]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
private theorem wv_add' (t : Rˣ × Rˣ) (a b : ℤ × ℤ) : wv t (a + b) = wv t a * wv t b := by
  simp only [wv, Prod.fst_add, Prod.snd_add, zpow_add]
  rw [mul_mul_mul_comm]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem wv_zero' (t : Rˣ × Rˣ) : wv t 0 = 1 := by simp [wv]

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem adj_mul' (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn] <;> ring

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem adj_adj' (X : M4 R) : adj (adj X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
private theorem adj_smul' (a : R) (X : M4 R) : adj (a • X) = a • adj X := by
  ext i j
  simp only [adj_apply, Matrix.smul_apply, smul_eq_mul]
  rw [mul_smul_comm]

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem adj_one' : adj (1 : M4 R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Matrix.one_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem tconj_apply' (t : Rˣ × Rˣ) (X : M4 R) (i j : Fin 4) : tconj t X i j = (wv t (wt i j) : R) * X i j := rfl

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem tconj_unit' (t : Rˣ × Rˣ) : ∃ u : (M4 R)ˣ, ∀ X, tconj t X = u * X * (u⁻¹ : (M4 R)ˣ) := by
  let d : Fin 4 → Rˣ := fun i => wv t (lamW i, muW i)
  have key : ∀ i j, wv t (wt i j) = d i * (d j)⁻¹ := by
    intro i j
    rw [eq_mul_inv_iff_mul_eq, ← wv_add']
    congr 1
    simp [wt]
  let u : (M4 R)ˣ := ⟨Matrix.diagonal fun i => (d i : R), Matrix.diagonal fun i => ((d i)⁻¹ : Rˣ),
    by simp [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one], by simp [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]⟩
  refine ⟨u, fun X => ?_⟩
  ext i j
  simp only [u, Units.inv_mk, tconj_apply', key, Units.val_mul, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

end UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.V.GradeZeroInterpolatingElement.grp :
    ∀ (R : Type) [CommRing R], (∀ X Y : M4 R, adj (X * Y) = adj Y * adj X) ∧ (∀ X : M4 R, adj (adj X) = X) ∧ (∀ X Y : M4 R, adj (X + Y) = adj X + adj Y) ∧ (∀ (a : R) (X : M4 R), adj (a • X) = a • adj X) ∧ adj (1 : M4 R) = 1 ∧ (∀ (R' : Type) [CommRing R'] (f : R →+* R') (X : M4 R), adj (X.map f) = (adj X).map f) ∧ (∀ (ν : R) (g g' : M4 R), IsGSp ν g → g * g' = 1 → adj g = ν • g') ∧ (∀ (ν ν' : R) (g g' : M4 R), IsGSp ν g → IsGSp ν' g' → IsGSp (ν * ν') (g * g')) ∧ (∀ (t : Rˣ × Rˣ) (X Y : M4 R), tconj t (X * Y) = tconj t X * tconj t Y) ∧ (∀ t : Rˣ × Rˣ, tconj t (1 : M4 R) = 1) ∧ (∀ (t : Rˣ × Rˣ) (X : M4 R), adj (tconj t X) = tconj t (adj X)) ∧ (∀ (t : Rˣ × Rˣ) (X : M4 R), (tconj t X).trace = X.trace) ∧ (∀ t : Rˣ × Rˣ, ∃ u : (M4 R)ˣ, ∀ X, tconj t X = u * X * (u⁻¹ : (M4 R)ˣ)) := by
  intro R _
  refine ⟨adj_mul', adj_adj', ?_, adj_smul', adj_one', ?_, ?_, ?_, ?_, ?_, ?_, ?_, tconj_unit'⟩
  · intro X Y
    ext i j
    simp [adj_apply]
  · intro R' _ f X
    ext i j
    simp [adj_apply, Matrix.map_apply]
  · intro ν g g' hg h
    have hg' : adj g * g = ν • 1 := hg
    calc adj g = adj g * (g * g') := by rw [h, mul_one]
      _ = adj g * g * g' := (mul_assoc _ _ _).symm
      _ = ν • g' := by rw [hg', smul_mul_assoc, one_mul]
  · intro ν ν' g g' hg hg'
    have h1 : adj g * g = ν • 1 := hg
    have h2 : adj g' * g' = ν' • 1 := hg'
    show adj (g * g') * (g * g') = (ν * ν') • 1
    rw [adj_mul', mul_assoc, ← mul_assoc (adj g), h1, smul_mul_assoc, one_mul, mul_smul_comm, h2,
      smul_smul]
  · intro t X Y
    ext i j
    simp only [tconj_apply', Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [wt_add' i k j, wv_add', Units.val_mul]
    ring
  · intro t
    ext i j
    rw [tconj_apply', Matrix.one_apply]
    split_ifs with h
    · subst h
      simp [wt_self', wv_zero']
    · simp
  · intro t X
    ext i j
    simp only [adj_apply, tconj_apply']
    rw [wt_rev, mul_smul_comm]
  · intro t X
    simp [Matrix.trace, tconj_apply', wt_self', wv_zero']
