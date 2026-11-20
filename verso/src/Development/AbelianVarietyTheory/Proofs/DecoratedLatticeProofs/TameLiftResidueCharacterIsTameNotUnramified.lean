import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.TameLiftChar

open ValuativeRel

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem val_le_iff (x y : Fv D.host.F v) :
    valuation (Fv D.host.F v) x ≤ valuation (Fv D.host.F v) y ↔ Valued.v x ≤ Valued.v y := by
  haveI : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [← Valuation.Compatible.vle_iff_le (v := valuation (Fv D.host.F v)),
    Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))))]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem val_lt_one_iff (x : Fv D.host.F v) :
    valuation (Fv D.host.F v) x < 1 ↔ Valued.v x < 1 := by
  have h := val_le_iff (D := D) (v := v) 1 x
  rw [map_one, map_one] at h
  rw [← not_le, ← not_le, h]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem val_eq_one_iff (x : Fv D.host.F v) :
    valuation (Fv D.host.F v) x = 1 ↔ Valued.v x = 1 := by
  have h1 := val_le_iff (D := D) (v := v) 1 x
  have h2 := val_le_iff (D := D) (v := v) x 1
  rw [map_one, map_one] at h1 h2
  rw [le_antisymm_iff, le_antisymm_iff, h1, h2]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem rdQ_one (φ : SplitProj D v) : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (1 : D.host.E) = 1 := by
  show φ (1 ⊗ₜ 1) = 1
  rw [← Algebra.TensorProduct.one_def, map_one]

def rdQHom (φ : SplitProj D v) : D.host.E →+* Fv D.host.F v :=
  φ.toRingHom.comp (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] _).toRingHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rdQHom_apply (φ : SplitProj D v) (x : D.host.E) : rdQHom φ x = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ x := rfl

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem val_rdQ_le_one (φ : SplitProj D v) (x : 𝓞 D.host.E) : Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E)) ≤ 1 := by
  let w : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ)) := Valued.v
  have hx : IsIntegral ℤ (x : D.host.E) := x.2
  obtain ⟨p, hm, hp⟩ := hx
  have hO : IsIntegral w.integer (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E)) := by
    refine ⟨p.map (Int.castRingHom w.integer), hm.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← rdQHom_apply]
    have : (algebraMap w.integer (Fv D.host.F v)).comp (Int.castRingHom _) =
        (rdQHom φ).comp (algebraMap ℤ D.host.E) := RingHom.ext_int _ _
    rw [this, ← Polynomial.hom_eval₂, hp, map_zero]
  exact (Valuation.integer.integers w).mem_of_integral hO

end GlobalTheory.TameLiftChar

open GlobalTheory.TameLiftChar in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem GlobalTheory.tameLift_isTame_not_isUnram : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E) (ξ : (kP PP)ˣ →* ℂˣ), IsProjAt φ PP → ξ ≠ 1 → ∀ ξl : (Fv D.host.F v)ˣ →* ℂˣ, LiftsChar φ PP ξl ξ → GlobalTheory.SplitWeil.IsTame ξl ∧ ¬ GlobalTheory.SplitWeil.IsUnram ξl := by
  intro D v φ PP ξ hP hξ ξl hl
  refine ⟨?_, ?_⟩
  · intro x hx
    have hr : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (x : Fv D.host.F v) ((1 : (kP PP)ˣ) : kP PP) := by
      refine ⟨1, by simp, ?_⟩
      simpa [rdQ_one] using (val_lt_one_iff _).1 hx
    rw [hl x 1 hr, map_one]
  · intro hun
    obtain ⟨k, hk⟩ : ∃ k, ξ k ≠ 1 := by
      by_contra h; push_neg at h; exact hξ (MonoidHom.ext h)
    obtain ⟨x0, hx0⟩ := Ideal.Quotient.mk_surjective (k : kP PP)
    have hnot : x0 ∉ PP.asIdeal := by
      intro hm
      have : ((k : kP PP)) = 0 := by rw [← hx0]; exact Ideal.Quotient.eq_zero_iff_mem.2 hm
      exact k.ne_zero this
    have hle := val_rdQ_le_one φ x0
    have hge : ¬ Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E)) < 1 := fun h => hnot ((hP x0).2 h)
    have h1 : Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E)) = 1 := le_antisymm hle (not_lt.1 hge)
    have hne : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h1; exact zero_ne_one h1
    let u : (Fv D.host.F v)ˣ := Units.mk0 _ hne
    have hr : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (u : Fv D.host.F v) (k : kP PP) := ⟨x0, hx0, by simp [u]⟩
    exact hk ((hl u k hr).symm.trans (hun u ((val_eq_one_iff _).2 h1)))
