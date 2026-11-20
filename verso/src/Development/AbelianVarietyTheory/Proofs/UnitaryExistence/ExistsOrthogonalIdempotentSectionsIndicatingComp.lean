import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOrthogonalIdempotentSectionsPeriodSpacesStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedUniformisationComponentsPeriodSpacesBijectStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory.CompRead

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_idempotents_rdU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), 1 ≤ r → GoodEmb c σ → IsUnf U → FnAlgClosed Xo c → ∃ χ : U.Comp → Rul Xo c, (∀ k, χ k ∈ sec Xo c 0 0) ∧ (∀ k, χ k * χ k = χ k) ∧ (∀ k k', k ≠ k' → χ k * χ k' = 0) ∧ ∑ k, χ k = 1 ∧ ∀ k k' x, x ∈ (U.X k').dom → (k' = k → rdU U (χ k) k' x = 1) ∧ (k' ≠ k → rdU U (χ k) k' x = 0) := by
  intro E _ _ _ H Dw l Xo c σ r U hr hσ hU hF
  obtain ⟨g, e, F, ik, φ, hφ, hP⟩ := hU.2.2.2.2.2
  have hb : Function.Bijective ik := by
    refine GlobalTheory.T.framedUniformisation_components_periodSpaces_bijective E H Dw l Xo c σ r U hr hσ hU g e F ik φ hφ (fun k x => ?_)
    obtain ⟨Pm, h1, h2, h3, h4, -⟩ := hP k x
    exact ⟨Pm, h1, h2, h3, h4⟩
  obtain ⟨χ, h0, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_orthogonal_idempotentSections_periodSpaces E H Dw l Xo c σ g _ F hF
  refine ⟨fun k => χ (ik k), fun k => h0 _, fun k => h1 _, fun k k' h => h2 _ _ (fun h' => h (hb.1 h')), ?_, ?_⟩
  · rw [← h3]
    exact hb.sum_comp χ
  · intro k k' x hx
    obtain ⟨Pm, -, hp, hu, -⟩ := hP k' ⟨x, hx⟩
    have hv := h4 (U.un k' ⟨x, hx⟩) (ik k) (ik k') Pm hp hu
    have hr : rdU U (χ (ik k)) k' x = toC (evR Xo c (χ (ik k)) (U.un k' ⟨x, hx⟩)) := dif_pos hx
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hr, hv, if_pos (congrArg ik h)]
    · rw [hr, hv, if_neg (fun h' => h (hb.1 h'))]

end GlobalTheory.CompRead
