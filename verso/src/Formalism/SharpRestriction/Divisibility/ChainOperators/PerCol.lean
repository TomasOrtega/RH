import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes

noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.DIV

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => rfl`. Consider the case `succ m ih => show Formalism.ThetaLiftIndependence.kerOpM (w m) (Km m) (Formalism.ThetaLiftIndependence.chainOpM w Km m (c • f)) = c • Formalism.ThetaLiftIndependence.kerOpM (w m) (Km m) (Formalism.ThetaLiftIndependence.chainOpM w Km m f)`. Rewrite using `[ih]`. Use function extensionality and compare the values at `j`.

Simplify using `only [Formalism.ThetaLiftIndependence.kerOpM, Pi.smul_apply, map_smul, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm]`.
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
The claim follows from `chainOpM_smul C.wt C.Kmap R.m c f`.
-/
theorem col_smul {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc)
    (c : ℂ) (f : C.cls 0 → C.Y 0 → ℂ) : C.col (c • f) = c • C.col f := chainOpM_smul C.wt C.Kmap R.m c f

/- English proof (translation)
Use `show P.Ptil (C.col (c • f)) F = c * P.Ptil (C.col f) F`. Rewrite using `[col_smul]`. Simplify using `only [Formalism.BasicNotions.PeriodMap.Ptil, map_smul, LinearMap.smul_apply, smul_eq_mul]`.
-/
theorem ptilCol_smul {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} (P : PeriodMap R C)
    (c : ℂ) (f : C.cls 0 → C.Y 0 → ℂ) (F : P.Mt) : P.PtilCol (c • f) F = c * P.PtilCol f F := by
  show P.Ptil (C.col (c • f)) F = c * P.Ptil (C.col f) F
  rw [col_smul]
  simp only [Formalism.BasicNotions.PeriodMap.Ptil, map_smul, LinearMap.smul_apply, smul_eq_mul]

/- English proof (translation)
Introduce `u μ c φ F`. Distinguish the cases in `h : μ = D.what₂.mu0`. Substitute `h` using the available equality. Rewrite using `[D.perCol_base_eq_PtilCol, D.perCol_base_eq_PtilCol, map_smul]`. Conclude with `ptilCol_smul _ c _ _`.

Rewrite using `[D.perCol_tie u μ h, D.perCol_tie u μ h, map_smul]`. Establish `: (((c • D.eMu u φ : (D.mem u).A.Mram)) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) = c • ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)` using `rfl`. Rewrite using `[this, map_smul]`. Conclude with `ptilCol_smul _ c _ _`.
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
