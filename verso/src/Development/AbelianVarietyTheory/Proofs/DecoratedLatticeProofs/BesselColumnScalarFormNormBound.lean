import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierCoefficientBessel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.ColBound

/- English proof (translation)
Introduce `D X h u ψ A B hK T`. Establish `hca` using `(GlobalTheory.Core.Mi.PhCol.ph_colForm D X h u ψ A B hK T).1`. Take `⟨K, hKc, hKg⟩` from `B.cpt`. Establish `hb : ∀ ξ, ∃ c : ℝ, 0 ≤ c ∧ ∀ a, ‖B.colForm T.1 ξ a‖ ≤ c`. Introduce `ξ`.

Take `⟨c, hc⟩` from `hKc.exists_bound_of_continuousOn ((hca ξ).2.continuousOn)`. Use `⟨max c 0, le_max_right _ _, fun a => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, hγK⟩` from `hKg a`. Rewrite using `[← (hca ξ).1 γ hγ a]`. Conclude with `(hc _ hγK).trans (le_max_left _ _)`.

Set `b` to `Module.finBasis ℂ (X.Vpi u)`. Use `choose c hc0 hc using fun i => hb (b i)`. Set `L : ∀ i, X.Vpi u →L[ℂ] ℂ` to `fun i => LinearMap.toContinuousLinearMap (b.coord i)`. Use `⟨∑ i, ‖L i‖ * c i, fun ξ a => ?_⟩` and prove the remaining obligations. Establish `hlin : B.colForm T.1 ξ a = ∑ i, L i ξ * B.colForm T.1 (b i) a`.

Establish `hξ : ξ = ∑ i, b.repr ξ i • b i` using `(b.sum_repr ξ).symm`. Establish `e1 : B.colForm T.1 ξ a = (T.1 ξ) (B.toH a)` using `rfl`. Rewrite using `[e1]`. Use `conv_lhs => rw [hξ]`. Rewrite using `[map_sum, Finset.sum_apply]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Pi.smul_apply, smul_eq_mul]`. Both sides reduce to the same expression. Rewrite using `[hlin, Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem colForm_bound : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK), ∃ C : ℝ, ∀ (ξ : X.Vpi u) (a : GA D A), ‖B.colForm T.1 ξ a‖ ≤ C * ‖ξ‖ := by
  intro D X h u ψ A B hK T
  have hca := (GlobalTheory.Core.Mi.PhCol.ph_colForm D X h u ψ A B hK T).1
  obtain ⟨K, hKc, hKg⟩ := B.cpt
  have hb : ∀ ξ, ∃ c : ℝ, 0 ≤ c ∧ ∀ a, ‖B.colForm T.1 ξ a‖ ≤ c := by
    intro ξ
    obtain ⟨c, hc⟩ := hKc.exists_bound_of_continuousOn ((hca ξ).2.continuousOn)
    refine ⟨max c 0, le_max_right _ _, fun a => ?_⟩
    obtain ⟨γ, hγ, hγK⟩ := hKg a
    rw [← (hca ξ).1 γ hγ a]
    exact (hc _ hγK).trans (le_max_left _ _)
  let b := Module.finBasis ℂ (X.Vpi u)
  choose c hc0 hc using fun i => hb (b i)
  let L : ∀ i, X.Vpi u →L[ℂ] ℂ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  refine ⟨∑ i, ‖L i‖ * c i, fun ξ a => ?_⟩
  have hlin : B.colForm T.1 ξ a = ∑ i, L i ξ * B.colForm T.1 (b i) a := by
    have hξ : ξ = ∑ i, b.repr ξ i • b i := (b.sum_repr ξ).symm
    have e1 : B.colForm T.1 ξ a = (T.1 ξ) (B.toH a) := rfl
    rw [e1]
    conv_lhs => rw [hξ]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [hlin, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  calc ‖L i ξ‖ * ‖B.colForm T.1 (b i) a‖ ≤ (‖L i‖ * ‖ξ‖) * c i :=
        mul_le_mul ((L i).le_opNorm ξ) (hc i a) (norm_nonneg _) (by positivity)
    _ = ‖L i‖ * c i * ‖ξ‖ := by ring

end GlobalTheory.Core.Mi.ColBound

end
