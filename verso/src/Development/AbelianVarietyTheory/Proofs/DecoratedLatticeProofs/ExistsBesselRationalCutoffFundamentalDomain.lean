import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoExt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Fold

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem exists_cutoff_srat : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (Fs : Set X.B.I.GA), IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ β : X.B.I.GA → ENNReal, Measurable β ∧ (∀ x, ∑' σ : Srat X u, β ((σ : X.B.I.GA) * x) = 1) ∧ ∀ F : X.B.I.GA → ENNReal, Measurable F → (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) → ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ∫⁻ x, β x * F x ∂(X.B.I.muA X.B.μf) := by
  intro D X u Fs hFs
  have hR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  haveI : BorelSpace X.B.I.GA := hR.2.2.2.1
  haveI : SecondCountableTopology X.B.I.GA := hR.2.1
  haveI : DiscreteTopology (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) := hR.2.2.2.2
  haveI : DiscreteTopology (Srat X u) := Formalism.L2.SG.Pf.srat_discrete X u
  haveI : Countable (Srat X u) := Formalism.L2.SG.Pf.countable_of_discrete _
  obtain ⟨_, hleft, _⟩ := Formalism.L2.SG.EvalTOntoExt.instances X
  obtain ⟨F', hF'm, h1, h2⟩ := Formalism.L2.SG.Pf.exists_strictFund (Srat X u)
  have hF' := Formalism.L2.SG.Pf.isFund_of_strict (Srat X u) hF'm h1 h2 (X.B.I.muA X.B.μf)
  refine ⟨F'.indicator 1, measurable_one.indicator hF'm, ?_, ?_⟩
  · intro x
    obtain ⟨s, hs, hsx⟩ := h1 x
    rw [tsum_eq_single (⟨s, hs⟩ : Srat X u)]
    · simp [Set.indicator_of_mem hsx]
    · intro t ht
      have hne : ((t : X.B.I.GA) * x) ∉ F' := by
        intro htx
        apply ht
        have := h2 _ hsx ((t : X.B.I.GA) * s⁻¹) ((Srat X u).mul_mem t.2 ((Srat X u).inv_mem hs))
          (by simpa [mul_assoc] using htx)
        exact Subtype.ext (by simpa [mul_inv_eq_one] using this)
      simp [Set.indicator_of_notMem hne]
  · intro F hFm hFinv
    rw [hFs.setLIntegral_eq hF' F (fun g x => by simpa [Subgroup.smul_def, smul_eq_mul] using hFinv g g.2 x)]
    rw [← lintegral_indicator hF'm]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ F' <;> simp [Set.indicator, hx]

end GlobalTheory.Core.Mi.Fold
