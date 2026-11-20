import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOrthogonalIdempotentSectionsPeriodSpacesStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedUniformisationComponentsPeriodSpacesBijectStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory.CompRead

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ r U hr hσ hU hF`. Take `⟨g, e, F, ik, φ, hφ, hP⟩` from `hU.2.2.2.2.2`. Establish `hb : Function.Bijective ik`. Use `GlobalTheory.T.framedUniformisation_components_periodSpaces_bijective E H Dw l Xo c σ r U hr hσ hU g e F ik φ hφ (fun k x => ?_)` and prove the remaining obligations. Take `⟨Pm, h1, h2, h3, h4, -⟩` from `hP k x`.

Conclude with `⟨Pm, h1, h2, h3, h4⟩`. Take `⟨χ, h0, h1, h2, h3, h4⟩` from `GlobalTheory.T.exists_orthogonal_idempotentSections_periodSpaces E H Dw l Xo c σ g _ F hF`. Use `⟨fun k => χ (ik k), fun k => h0 _, fun k => h1 _, fun k k' h => h2 _ _ (fun h' => h (hb.1 h')), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← h3]`. Conclude with `hb.sum_comp χ`.

Introduce `k k' x hx`. Take `⟨Pm, -, hp, hu, -⟩` from `hP k' ⟨x, hx⟩`. Establish `hv` using `h4 (U.un k' ⟨x, hx⟩) (ik k) (ik k') Pm hp hu`. Establish `hr : rdU U (χ (ik k)) k' x = toC (evR Xo c (χ (ik k)) (U.un k' ⟨x, hx⟩))` using `dif_pos hx`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations.

Rewrite using `[hr, hv, if_pos (congrArg ik h)]`. Rewrite using `[hr, hv, if_neg (fun h' => h (hb.1 h'))]`.
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
