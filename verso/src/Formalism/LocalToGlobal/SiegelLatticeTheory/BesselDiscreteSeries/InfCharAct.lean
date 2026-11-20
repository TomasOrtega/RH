import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfCharData

noncomputable section

open Matrix

namespace Formalism.MainNotions.BesselDiscreteSeries

open ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Establish `key : φ = (MonoidAlgebra.lift ℂ A (FreeMonoid X) (FreeMonoid.lift fun x => φ (FreeAlgebra.ι ℂ x))).comp (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R` using `ℂ) (X := X)).toAlgHom := by`. Apply `FreeAlgebra.hom_ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Simplify using `[FreeAlgebra.equivMonoidAlgebraFreeMonoid]`. Use `(DFunLike.congr_fun key p).trans ?_` and prove the remaining obligations.

Simplify using `only [AlgHom.comp_apply, MonoidAlgebra.lift_apply, FreeMonoid.lift_apply]`. Both sides reduce to the same expression.
-/
theorem freeAlg_hom_eq_sum {X A : Type} [Ring A] [Algebra ℂ A] (φ : FreeAlgebra ℂ X →ₐ[ℂ] A)
    (p : FreeAlgebra ℂ X) :
    φ p = Finsupp.sum (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).coeff
      (fun w c => c • (w.toList.map fun x => φ (FreeAlgebra.ι ℂ x)).prod) := by
  have key : φ = (MonoidAlgebra.lift ℂ A (FreeMonoid X) (FreeMonoid.lift fun x => φ (FreeAlgebra.ι ℂ x))).comp
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := X)).toAlgHom := by
    apply FreeAlgebra.hom_ext
    funext x
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  refine (DFunLike.congr_fun key p).trans ?_
  simp only [AlgHom.comp_apply, MonoidAlgebra.lift_apply, FreeMonoid.lift_apply]
  rfl

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Simplify using `only [Formalism.L2.SG.LitS.thetaJ, S7.cpart1, sub_eq_add_neg]`. Both sides reduce to the same expression.
-/
theorem thetaJ_cpart1 (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    (1 / 2 : ℂ) • (Y + Formalism.L2.SG.LitS.thetaJ ε Y) = S7.cpart1 ε Y := by
  simp only [Formalism.L2.SG.LitS.thetaJ, S7.cpart1, sub_eq_add_neg]
  rfl

/- English proof (translation)
Simplify using `only [Formalism.L2.SG.LitS.thetaJ, S7.cpart2, sub_neg_eq_add]`. Both sides reduce to the same expression.
-/
theorem thetaJ_cpart2 (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    (1 / (2 * Complex.I)) • (Y - Formalism.L2.SG.LitS.thetaJ ε Y) = S7.cpart2 ε Y := by
  simp only [Formalism.L2.SG.LitS.thetaJ, S7.cpart2, sub_neg_eq_add]
  rfl

/- English proof (translation)
Unfold `Formalism.L2.SG.LitS.dsigC`. Rewrite using `[thetaJ_cpart1, thetaJ_cpart2]`. Both sides reduce to the same expression.
-/
theorem dsigC_eq (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (Y : Matrix (Fin n) (Fin n) ℂ) (v : H) :
    Formalism.L2.SG.LitS.dsigC ε σ Y v = dS σ (S7.cpart1 ε Y) v + Complex.I • dS σ (S7.cpart2 ε Y) v := by
  unfold Formalism.L2.SG.LitS.dsigC
  rw [thetaJ_cpart1, thetaJ_cpart2]
  rfl

variable {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons p w ih`. Rewrite using `[List.map_cons, List.map_cons, List.prod_cons, Module.End.mul_apply, smE_apply hσ]`. Use `show Formalism.L2.SG.LitS.dsigC ε σ (Formalism.L2.SG.LitS.unitM p) (Formalism.L2.SG.LitS.dsigCW ε σ (w.map Formalism.L2.SG.LitS.unitM) x) = _`.

Rewrite using `[ih, dsigC_eq]`. Both sides reduce to the same expression.
-/
theorem dsigCW_word (hσ : IsURepOn (UJset ε) σ) (w : List (Fin n × Fin n)) (x : smD ε σ) :
    Formalism.L2.SG.LitS.dsigCW ε σ (w.map Formalism.L2.SG.LitS.unitM) x =
      (((w.map fun p => smE ε σ p.1 p.2).prod x : smD ε σ) : H) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, Module.End.mul_apply, smE_apply hσ]
    show Formalism.L2.SG.LitS.dsigC ε σ (Formalism.L2.SG.LitS.unitM p)
      (Formalism.L2.SG.LitS.dsigCW ε σ (w.map Formalism.L2.SG.LitS.unitM) x) = _
    rw [ih, dsigC_eq]
    rfl

def smAlg (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ (smD ε σ) :=
  FreeAlgebra.lift ℂ fun p => smE ε σ p.1 p.2

/- English proof (translation)
Rewrite using `[freeAlg_hom_eq_sum (smAlg ε σ) p]`. Simplify using `only [Formalism.L2.SG.LitS.actU, Finsupp.sum, dsigCW_word hσ, smAlg, FreeAlgebra.lift_ι_apply]`. Rewrite using `[LinearMap.sum_apply, Submodule.coe_sum]`. Use `Finset.sum_congr rfl (fun w _ => ?_)` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, Submodule.coe_smul]`.
-/
theorem actU_eq (hσ : IsURepOn (UJset ε) σ) (p : FreeAlgebra ℂ (Fin n × Fin n)) (x : smD ε σ) :
    Formalism.L2.SG.LitS.actU ε σ p x = ((smAlg ε σ p x : smD ε σ) : H) := by
  rw [freeAlg_hom_eq_sum (smAlg ε σ) p]
  simp only [Formalism.L2.SG.LitS.actU, Finsupp.sum, dsigCW_word hσ, smAlg, FreeAlgebra.lift_ι_apply]
  rw [LinearMap.sum_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [LinearMap.smul_apply, Submodule.coe_smul]

/- English proof (translation)
Use `(actU_eq hσ _ ⟨v, hv⟩).trans ?_` and prove the remaining obligations. Simplify using `only [smAlg, ReciprocityTheory.ChartRestriction.DS.ICD.qdet_map, Formalism.L2.SG.LitS.Egl, FreeAlgebra.lift_ι_apply]`.
-/
theorem actU_qdet (hσ : IsURepOn (UJset ε) σ) (u : ℂ) (v : H) (hv : v ∈ smD ε σ) :
    Formalism.L2.SG.LitS.actU ε σ (Formalism.REAL.qdet (Formalism.L2.SG.LitS.Egl n) u) v =
      ((Formalism.REAL.qdet (smE ε σ) u ⟨v, hv⟩ : smD ε σ) : H) := by
  refine (actU_eq hσ _ ⟨v, hv⟩).trans ?_
  simp only [smAlg, ReciprocityTheory.ChartRestriction.DS.ICD.qdet_map, Formalism.L2.SG.LitS.Egl, FreeAlgebra.lift_ι_apply]

/- English proof (translation)
Conclude with `(ReciprocityTheory.ChartRestriction.DS.mem_smD_iff ε σ v).mpr hv`.
-/
theorem mem_smD_of_smoothVecs {v : H} (hv : v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ) :
    v ∈ smD ε σ := by
  exact (ReciprocityTheory.ChartRestriction.DS.mem_smD_iff ε σ v).mpr hv

end Formalism.MainNotions.BesselDiscreteSeries
