import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes

noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.DIV

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem chainOpM_smul {Rg : Type} [CommSemiring Rg] {ι : ℕ → Type} [∀ j, Fintype (ι j)]
    {M : ℕ → Type} [∀ j, AddCommMonoid (M j)] [∀ j, Module Rg (M j)]
    (w : ∀ j, ι j → Rg) (Km : ∀ j, ι j → ι (j + 1) → (M j →ₗ[Rg] M (j + 1))) (m : ℕ) (c : Rg) (f : ι 0 → M 0) :
    Formalism.ThetaLiftIndependence.chainOpM w Km m (c • f) = c • Formalism.ThetaLiftIndependence.chainOpM w Km m f := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show Formalism.ThetaLiftIndependence.kerOpM (w m) (Km m) (Formalism.ThetaLiftIndependence.chainOpM w Km m (c • f)) =
      c • Formalism.ThetaLiftIndependence.kerOpM (w m) (Km m) (Formalism.ThetaLiftIndependence.chainOpM w Km m f)
    rw [ih]
    funext j
    simp only [Formalism.ThetaLiftIndependence.kerOpM, Pi.smul_apply, map_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem col_smul {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc)
    (c : ℂ) (f : C.cls 0 → C.Y 0 → ℂ) : C.col (c • f) = c • C.col f := chainOpM_smul C.wt C.Kmap R.m c f

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem ptilCol_smul {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} (P : PeriodMap R C)
    (c : ℂ) (f : C.cls 0 → C.Y 0 → ℂ) (F : P.Mt) : P.PtilCol (c • f) F = c * P.PtilCol f F := by
  show P.Ptil (C.col (c • f)) F = c * P.Ptil (C.col f) F
  rw [col_smul]
  simp only [Formalism.BasicNotions.PeriodMap.Ptil, map_smul, LinearMap.smul_apply, smul_eq_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem perColSmul (D : D7) : WeightDegreeSizes.PerColSmul D := by
  intro u μ c φ F
  by_cases h : μ = D.what₂.mu0
  · subst h
    rw [D.perCol_base_eq_PtilCol, D.perCol_base_eq_PtilCol, map_smul]
    exact ptilCol_smul _ c _ _
  · rw [D.perCol_tie u μ h, D.perCol_tie u μ h, map_smul]
    have : (((c • D.eMu u φ : (D.mem u).A.Mram)) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) =
        c • ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) := rfl
    rw [this, map_smul]
    exact ptilCol_smul _ c _ _

end Formalism.MainNotions.DIV

end
