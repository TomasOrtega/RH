import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ExpOfDeriv
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo
open scoped TensorProduct

/- English proof (translation)
Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Treat this case separately.

Treat this case separately. Treat this case separately.
-/
private theorem span_val {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a d : ℕ} (P : Sm E a → Prop)
    (x y : GA E a) (c : ℂ) (h : ∀ φ, P φ → φ.1 x = c * φ.1 y) (m : Sm E a ⊗[ℂ] (Fin d → ℂ))
    (hm : m ∈ Submodule.span ℂ {z : Sm E a ⊗[ℂ] (Fin d → ℂ) | ∃ φ v, P φ ∧ z = φ ⊗ₜ[ℂ] v}) : ev m x = c • ev m y := by
  induction hm using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨φ, v, hφ, rfl⟩ := hz
    rw [ev_tmul, ev_tmul, h φ hφ, mul_smul]
  | zero => simp
  | add z w _ _ hz hw => simp only [map_add, Pi.add_apply, hz, hw, smul_add]
  | smul s z _ hz => simp only [map_smul, Pi.smul_apply, hz, smul_comm s c]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.V.Lit.Geo.centreVal :
    CentreVal := by
  intro E _ _ _ a U Ξ r hr q α hα X γ t g
  refine span_val (IsLevelFn U Ξ) _ _ _ (fun φ hφ => ?_) _ (hα.3 X)
  rw [mul_assoc, hφ.1, aInv E a φ _ (hφ.2.2 r hr), neg_mul]
