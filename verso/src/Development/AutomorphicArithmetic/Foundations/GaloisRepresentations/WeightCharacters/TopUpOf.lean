import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqRepTopVecOfUnitriangular

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

/- English proof (translation)
Introduce `a κ b hb`. Establish `hbt : (b : Matrix (Fin a) (Fin a) ℂ).BlockTriangular id` using `fun i j h => hb i j h`. Establish `hdiag : ∀ i, (b : Matrix (Fin a) (Fin a) ℂ) i i ≠ 0`. Establish `hdet : (b : Matrix (Fin a) (Fin a) ℂ).det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero`. Rewrite `hdet` using `[Matrix.det_of_upperTriangular hbt]`.

Conclude with `fun i => (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ i)`. Set `t : Fin a → ℂˣ` to `fun i => Units.mk0 _ (hdiag i)`. Use `set D := diagGL ℂ a t with hD`. Use `set u := D⁻¹ * b with hu`. Establish `hbu : b = D * u` using `by rw [hu, mul_inv_cancel_left]`.

Establish `hDinv : ((D⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) = Matrix.diagonal fun i => (((t i)⁻¹ : ℂˣ) : ℂ)` using `rfl`. Establish `hucoe : (u : Matrix (Fin a) (Fin a) ℂ) = Matrix.diagonal (fun i => (((t i)⁻¹ : ℂˣ) : ℂ)) * (b : Matrix (Fin a) (Fin a) ℂ)`. Rewrite using `[hu, Units.val_mul, hDinv]`. Establish `hut : (u : Matrix (Fin a) (Fin a) ℂ).BlockTriangular id`. Rewrite using `[hucoe]`.

Conclude with `(Matrix.blockTriangular_diagonal _).mul hbt`. Establish `hu1 : ∀ i, (u : Matrix (Fin a) (Fin a) ℂ) i i = 1`. Introduce `i`. Rewrite using `[hucoe, Matrix.diagonal_mul]`. Simplify using `[t, hdiag i]`.

Establish `hfix : (sqRep ℂ a κ u) (top κ) = top κ`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `(factSqHighestWeight ℂ a κ).2 u hut hu1`. Establish `hscal : (sqRep ℂ a κ D) (top κ) = chi κ b • top κ`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `h` using `(factSqHighestWeight ℂ a κ).1 t`. Establish `hc : (((∏ i, t i ^ κ.w i : ℂˣ)) : ℂ) = chi κ b`. Rewrite using `[Units.coe_prod]`. Simplify using `only [Units.val_zpow_eq_zpow_val, chi, t, Units.val_mk0]`. Rewrite `h` using `[hc]`.

Conclude with `h`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hbu, map_mul, Module.End.mul_apply]`. Use `_ = chi κ b • top κ := by rw [hfix, hscal]`.
-/
theorem UpperTheory.Gal.Wt.topUp_of :
    UpperTheory.Gal.Wt.TopUp := by
  intro a κ b hb
  have hbt : (b : Matrix (Fin a) (Fin a) ℂ).BlockTriangular id := fun i j h => hb i j h
  have hdiag : ∀ i, (b : Matrix (Fin a) (Fin a) ℂ) i i ≠ 0 := by
    have hdet : (b : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
    rw [Matrix.det_of_upperTriangular hbt] at hdet
    exact fun i => (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ i)
  let t : Fin a → ℂˣ := fun i => Units.mk0 _ (hdiag i)
  set D := diagGL ℂ a t with hD
  set u := D⁻¹ * b with hu
  have hbu : b = D * u := by rw [hu, mul_inv_cancel_left]
  have hDinv : ((D⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) =
      Matrix.diagonal fun i => (((t i)⁻¹ : ℂˣ) : ℂ) := rfl
  have hucoe : (u : Matrix (Fin a) (Fin a) ℂ) =
      Matrix.diagonal (fun i => (((t i)⁻¹ : ℂˣ) : ℂ)) * (b : Matrix (Fin a) (Fin a) ℂ) := by
    rw [hu, Units.val_mul, hDinv]
  have hut : (u : Matrix (Fin a) (Fin a) ℂ).BlockTriangular id := by
    rw [hucoe]
    exact (Matrix.blockTriangular_diagonal _).mul hbt
  have hu1 : ∀ i, (u : Matrix (Fin a) (Fin a) ℂ) i i = 1 := by
    intro i
    rw [hucoe, Matrix.diagonal_mul]
    simp [t, hdiag i]
  have hfix : (sqRep ℂ a κ u) (top κ) = top κ := by
    apply Subtype.ext
    exact (factSqHighestWeight ℂ a κ).2 u hut hu1
  have hscal : (sqRep ℂ a κ D) (top κ) = chi κ b • top κ := by
    apply Subtype.ext
    have h := (factSqHighestWeight ℂ a κ).1 t
    have hc : (((∏ i, t i ^ κ.w i : ℂˣ)) : ℂ) = chi κ b := by
      rw [Units.coe_prod]
      simp only [Units.val_zpow_eq_zpow_val, chi, t, Units.val_mk0]
    rw [hc] at h
    exact h
  calc (sqRep ℂ a κ b) (top κ) = (sqRep ℂ a κ D) ((sqRep ℂ a κ u) (top κ)) := by
        rw [hbu, map_mul, Module.End.mul_apply]
    _ = chi κ b • top κ := by rw [hfix, hscal]
