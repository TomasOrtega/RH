import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFormCongrOfEventuallyEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelActionPreservesFlatForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSymplecticTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapRigidity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricTranslationPullbackFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCoordsSymplecticPullbackForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcCompHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteQuotientOfIsLatLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPeriodMapSimplyConnectedStatement
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

namespace GlobalTheory

open GlobalTheory.TorsionForm in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isDatum_twistFactor : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (g : ℕ) (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M M' : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ) (h : Pt E g → ℝ), IsDatum B τ M' j h → IsLat M → M ≤ M' → ∀ χ : AddChar (M' ⧸ M.submoduleOf M') ℂ, IsDatum B τ M' (twistFactor M M' χ j) h := by
  intro E _ _ g B τ M M' j h hD hM hle χ
  obtain ⟨hP, hM', ⟨hd, hc⟩, hs, hpos, hinv⟩ := hD
  haveI : Finite (↥M' ⧸ M.submoduleOf M') := finite_quotient_of_isLat_le M M' hM hM' hle
  have hnorm : ∀ q, ‖χ q‖ = 1 := by
    intro q
    have hfin : IsOfFinAddOrder q := isOfFinAddOrder_of_finite q
    have hn : 0 < addOrderOf q := hfin.addOrderOf_pos
    have hpow : χ q ^ addOrderOf q = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, addOrderOf_nsmul_eq_zero, AddChar.map_zero_eq_one]
    have : ‖χ q‖ ^ addOrderOf q = 1 := by rw [← norm_pow, hpow, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  have hval : ∀ l (hl : l ∈ M') (P : Pt E g),
      twistFactor M M' χ j l P = χ (Submodule.Quotient.mk ⟨l, hl⟩) * j l P := by
    intro l hl P; unfold twistFactor; rw [dif_pos hl]
  refine ⟨hP, hM', ⟨fun l hl => ⟨?_, ?_⟩, ?_⟩, hs, hpos, ?_⟩
  · have : twistFactor M M' χ j l = fun P => χ (Submodule.Quotient.mk ⟨l, hl⟩) * j l P :=
      funext (hval l hl)
    rw [this]; exact (hd l hl).1.const_mul _
  · intro P hP'
    rw [hval l hl]
    refine mul_ne_zero ?_ ((hd l hl).2 P hP')
    intro h0; have := hnorm (Submodule.Quotient.mk ⟨l, hl⟩); rw [h0, norm_zero] at this
    exact zero_ne_one this
  · intro l hl l' hl' P hP'
    rw [hval _ (M'.add_mem hl hl'), hval l hl, hval l' hl', hc l hl l' hl' P hP']
    have : (Submodule.Quotient.mk ⟨l + l', M'.add_mem hl hl'⟩ : ↥M' ⧸ M.submoduleOf M') =
        Submodule.Quotient.mk ⟨l, hl⟩ + Submodule.Quotient.mk ⟨l', hl'⟩ := by
      rw [← Submodule.Quotient.mk_add]; rfl
    rw [this, AddChar.map_add_eq_mul]; ring
  · intro l hl P hP'
    rw [hval l hl, norm_mul, hnorm, one_mul]
    exact hinv l hl P hP'

end GlobalTheory
