import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private def UpperTheory.V.Ws.P1.formJ (R : Type) [CommRing R] : M4 R :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.Ws.P1.formJ, Matrix.mul_apply, Fin.sum_univ_four]`.
-/
private theorem UpperTheory.V.Ws.P1.formJ_sq (R : Type) [CommRing R] :
    UpperTheory.V.Ws.P1.formJ R * UpperTheory.V.Ws.P1.formJ R = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.Ws.P1.formJ, Matrix.mul_apply, Fin.sum_univ_four]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[UpperTheory.V.Ws.P1.formJ, Matrix.mul_apply, Fin.sum_univ_four, UpperTheory.V.GradeZeroInterpolatingElement.adj, UpperTheory.V.GradeZeroInterpolatingElement.sgn, Fin.rev]`.
-/
private theorem UpperTheory.V.Ws.P1.formJ_adj (R : Type) [CommRing R] (g : M4 R) :
    g.transpose * UpperTheory.V.Ws.P1.formJ R = UpperTheory.V.Ws.P1.formJ R * UpperTheory.V.GradeZeroInterpolatingElement.adj g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperTheory.V.Ws.P1.formJ, Matrix.mul_apply, Fin.sum_univ_four, UpperTheory.V.GradeZeroInterpolatingElement.adj, UpperTheory.V.GradeZeroInterpolatingElement.sgn, Fin.rev]

/- English proof (translation)
Introduce `R _`. Use `⟨⟨UpperTheory.V.Ws.P1.formJ R, -UpperTheory.V.Ws.P1.formJ R, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_neg, UpperTheory.V.Ws.P1.formJ_sq, neg_neg]`. Rewrite using `[neg_mul, UpperTheory.V.Ws.P1.formJ_sq, neg_neg]`. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.Ws.P1.formJ]`.

Introduce `ν g hg`. Establish `h : UpperTheory.V.GradeZeroInterpolatingElement.adj g * g = ν • 1` using `hg`. Simplify using `only [Units.val_mk]`. Rewrite using `[UpperTheory.V.Ws.P1.formJ_adj, mul_assoc, h, Matrix.mul_smul, Matrix.mul_one]`.
-/
theorem UpperTheory.V.Ws.P1.gspForm :
    ∀ (R : Type) [CommRing R], ∃ J : (M4 R)ˣ, (J : M4 R).transpose = -J ∧ ∀ (ν : R) (g : M4 R), IsGSp ν g → g.transpose * (J : M4 R) * g = ν • (J : M4 R) := by
  intro R _
  refine ⟨⟨UpperTheory.V.Ws.P1.formJ R, -UpperTheory.V.Ws.P1.formJ R, ?_, ?_⟩, ?_, ?_⟩
  · rw [mul_neg, UpperTheory.V.Ws.P1.formJ_sq, neg_neg]
  · rw [neg_mul, UpperTheory.V.Ws.P1.formJ_sq, neg_neg]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.Ws.P1.formJ]
  · intro ν g hg
    have h : UpperTheory.V.GradeZeroInterpolatingElement.adj g * g = ν • 1 := hg
    simp only [Units.val_mk]
    rw [UpperTheory.V.Ws.P1.formJ_adj, mul_assoc, h, Matrix.mul_smul, Matrix.mul_one]
