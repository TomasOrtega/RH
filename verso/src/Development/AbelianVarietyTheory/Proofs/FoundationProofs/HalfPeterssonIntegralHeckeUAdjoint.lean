import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionHeckeUEqSumSlashStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonDoubleCosetAdjointStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrablePeterssonIntegrandModerateGrowthStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthQExpansionOfCoeffPolynomialGrowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthAlgebraSlashStableStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeULeftRepresentativesLevelChangeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsRightGamma0CosetDecompositionHeckeUStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuousStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

/- English proof (translation)
Introduce `k L N l ε ρ h a hk hL hNL hl hlL hlN hW hh ha`. Establish `hN : 0 < N` using `Nat.pos_of_dvd_of_pos hNL hL`. Establish `hcop : l.Coprime N` using `(Nat.Prime.coprime_iff_not_dvd hl).2 hlN`. Establish `hpos : 0 < l` using `hl.pos`. Take `⟨-, hUa⟩` from `GlobalTheory.T.qExpansion_heckeU_eq_sum_slash k l a hk hpos ha.1`.

Establish `hcontH : Continuous (qs h)` using `(GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hh.1.1).2`. Establish `hcontA : Continuous (qs a)` using `(GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha.1).2`. Establish `hModA : Mod (qs a)` using `GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth a ha.1`. Establish `hdet : ∀ j : Fin l, (repU l j).det = l`. Introduce `j`.

Simplify using `[repU, Matrix.det_fin_two]`. Establish `hint : ∀ i : Fin l, Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * slz k (repU l i) (qs a) τ * (τ.im : ℂ) ^ k))`. Introduce `i`. Establish `hd : 0 < (repU l i).det` using `by rw [hdet]; exact_mod_cast hpos`. Conclude with `GlobalTheory.T.integrable_petersson_integrand_moderateGrowth k L L N ε h ρ _ hk hL hNL hW hh (((GlobalTheory.T.slashIntMatrixPosDet_properties k (qs a) hk).2.2.2.1 _ hd hcontA).aestronglyMeasurable) ((GlobalTheory.T.hasModerateGrowth_algebra_slash_stable).2.2 (qs a) k _ hd (by si …`.

Establish `key` using `GlobalTheory.T.petersson_doubleCoset_adjoint k L N l ε ρ (DU L l) (Fin l) (Fin l) (repU l) (fun j => (repL L l (some j)).adjugate) (qs h) (qs a) hk hN hNL hpos hcop hW (by`. Introduce `δ hδ`. Take `⟨h1, h2, -⟩` from `hδ`. Conclude with `⟨h1, (Int.natCast_dvd_natCast.2 hNL).trans h2⟩)`. Use the proof step `((GlobalTheory.T.heckeU_leftRepresentatives_level_change L l hl).1 hlL) (GlobalTheory.T.isRightGamma0CosetDecomposition_heckeU L l hL hl hlL) hh.1.2 ha.2 hcontH hcontA hint`.

Establish `e1 : qs (Uo l a) = hsum k (ch ε) (repU l) (qs a)`. Use function extensionality and compare the values at `τ`. Rewrite using `[hUa τ]`. Simplify using `[hsum, repU, ch]`. Establish `e2 : (fun τ => ∑ j : Fin l, slz k (repL L l (some j)) (qs h) τ) = (fun τ => ∑ j, ch ε⁻¹ ((fun j => (repL L l (some j)).adjugate) j 0 0) * slz k ((fun j => (repL L l (some j)).adjugate) j).adjugate (qs h) τ)`.

Use function extensionality and compare the values at `τ`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Simplify using `[repL, ch, Matrix.adjugate_fin_two_of]`. Rewrite using `[e1, e2]`. Conclude with `key`.
-/
theorem adjoint_U : ∀ (k L N l : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → l.Prime → l ∣ L → ¬ l ∣ N → Wt L ρ → CF k L (ch ε) h → MF k L (ch ε) a → pet k ρ (qs h) (qs (Uo l a)) = pet k ρ (fun τ => ∑ j : Fin l, slz k (repL L l (some j)) (qs h) τ) (qs a) := by
  intro k L N l ε ρ h a hk hL hNL hl hlL hlN hW hh ha
  have hN : 0 < N := Nat.pos_of_dvd_of_pos hNL hL
  have hcop : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hl).2 hlN
  have hpos : 0 < l := hl.pos
  obtain ⟨-, hUa⟩ := GlobalTheory.T.qExpansion_heckeU_eq_sum_slash k l a hk hpos ha.1
  have hcontH : Continuous (qs h) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hh.1.1).2
  have hcontA : Continuous (qs a) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha.1).2
  have hModA : Mod (qs a) := GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth a ha.1
  have hdet : ∀ j : Fin l, (repU l j).det = l := by
    intro j; simp [repU, Matrix.det_fin_two]
  have hint : ∀ i : Fin l, Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * slz k (repU l i) (qs a) τ * (τ.im : ℂ) ^ k)) := by
    intro i
    have hd : 0 < (repU l i).det := by rw [hdet]; exact_mod_cast hpos
    exact GlobalTheory.T.integrable_petersson_integrand_moderateGrowth k L L N ε h ρ _ hk hL hNL hW hh
      (((GlobalTheory.T.slashIntMatrixPosDet_properties k (qs a) hk).2.2.2.1 _ hd hcontA).aestronglyMeasurable)
      ((GlobalTheory.T.hasModerateGrowth_algebra_slash_stable).2.2 (qs a) k _ hd (by simp [repU]) hModA)
  have key := GlobalTheory.T.petersson_doubleCoset_adjoint k L N l ε ρ (DU L l) (Fin l) (Fin l) (repU l)
    (fun j => (repL L l (some j)).adjugate) (qs h) (qs a) hk hN hNL hpos hcop hW
    (by
      intro δ hδ
      obtain ⟨h1, h2, -⟩ := hδ
      exact ⟨h1, (Int.natCast_dvd_natCast.2 hNL).trans h2⟩)
    ((GlobalTheory.T.heckeU_leftRepresentatives_level_change L l hl).1 hlL) (GlobalTheory.T.isRightGamma0CosetDecomposition_heckeU L l hL hl hlL) hh.1.2 ha.2 hcontH hcontA hint
  have e1 : qs (Uo l a) = hsum k (ch ε) (repU l) (qs a) := by
    funext τ
    rw [hUa τ]
    simp [hsum, repU, ch]
  have e2 : (fun τ => ∑ j : Fin l, slz k (repL L l (some j)) (qs h) τ) =
      (fun τ => ∑ j, ch ε⁻¹ ((fun j => (repL L l (some j)).adjugate) j 0 0) *
        slz k ((fun j => (repL L l (some j)).adjugate) j).adjugate (qs h) τ) := by
    funext τ
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [repL, ch, Matrix.adjugate_fin_two_of]
  rw [e1, e2]
  exact key

end GlobalTheory
