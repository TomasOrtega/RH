import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameIdempotentCutMatrixMemStabiliserReductionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingIdempotentPatchInFrameStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLIffIsUnitDetAtPrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseEqOfSameIdempotentPrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemAtConjOfOtherPrimeOverSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.SplitOffRed

/- English proof (translation)
Take `⟨a, h1, h2⟩` from `GlobalTheory.FunObj.Comparison₂.exists_resS_eq PP' s`. Rewrite using `[h1, GlobalTheory.FunObj.Comparison₂.mk_eq_zero_iff]`. Rewrite `h2` using `[GlobalTheory.FunObj.Comparison₂.cptO_apply PP' s]`. Express the relevant statement in the definitionally equal form `Valued.v (GlobalTheory.StdFrames.cpt PP' (s : Formalism.IndefR.Datum.EAf D) - _) < 1 at h2`. Rewrite `h2` using `[h, zero_sub, Valuation.map_neg]`.

Conclude with `h2`.
-/
theorem resS_eq_zero_of_cpt {D : D7} (PP' : Formalism.L2.DIV.Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h : GlobalTheory.StdFrames.cpt PP' (s : Formalism.IndefR.Datum.EAf D) = 0) : Formalism.L2.DIV.resS D.host.F PP' s = 0 := by
  obtain ⟨a, h1, h2⟩ := GlobalTheory.FunObj.Comparison₂.exists_resS_eq PP' s
  rw [h1, GlobalTheory.FunObj.Comparison₂.mk_eq_zero_iff]
  rw [GlobalTheory.FunObj.Comparison₂.cptO_apply PP' s] at h2
  change Valued.v (GlobalTheory.StdFrames.cpt PP' (s : Formalism.IndefR.Datum.EAf D) - _) < 1 at h2
  rw [h, zero_sub, Valuation.map_neg] at h2
  exact h2

/- English proof (translation)
Introduce `D k _ _ _ _ q PP hq V β κ hS hst PP' hne`. Establish `hPP' : PP' ≠ PP` using `fun h => hne (h ▸ rfl)`. Establish `hcP : GlobalTheory.IdemSupport.cP PP' ≠ PP` using `fun h => hne (by rw [← h, GlobalTheory.IdemSupport.under_cP])`. Establish `h1 : q.e * q.e = q.e` using `q.split.1`. Establish `hc1 : cA D q.e * cA D q.e = cA D q.e` using `by rw [← map_mul, h1]`.

Establish `hi1 : toEAf D q.e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `(GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP hq).1`. Establish `hi2 : toEAf D (cA D q.e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hc1]))`. Establish `hint : toEAf D (q.e + cA D q.e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E`. Rewrite using `[RingHom.map_add]`. Conclude with `add_mem hi1 hi2`.

Establish `hc0 : GlobalTheory.StdFrames.cpt PP' (toEAf D (q.e + cA D q.e)) = 0`. Rewrite using `[RingHom.map_add, RingHom.map_add, (GlobalTheory.StdFrames.cpt_of_isIdemAt hq).2 PP' hPP', zero_add, GlobalTheory.StdFrames.toEAf_cA]`. Conclude with `GlobalTheory.StdFrames.cpt_sg_eq_zero ((GlobalTheory.StdFrames.cpt_of_isIdemAt hq).2 _ hcP)`. Establish `hres : Formalism.L2.DIV.resS D.host.F PP' ⟨toEAf D (q.e + cA D q.e), hint⟩ = 0` using `resS_eq_zero_of_cpt PP' _ hc0`. Establish `hval : (Lev.finE V κ).val = (Formalism.L2.Theta.mt V κ).map (toEAf D)` using `rfl`.

Use `GlobalTheory.LevSplit.redFn_eq_one β PP' (Lev.finE V κ) hst ⟨toEAf D (q.e + cA D q.e), hint⟩ hres ?_` and prove the remaining obligations. Use extensionality with `i j`. Use `congrArg (toEAf D) (hS i j)` as an intermediate fact. Rewrite `this` using `[RingHom.map_mul, Matrix.sub_apply, RingHom.map_sub]`. Use `show toEAf D (q.e + cA D q.e) * ((Lev.finE V κ).val - 1) i j = ((Lev.finE V κ).val - 1) i j`.

Rewrite using `[Matrix.sub_apply, hval, Matrix.map_apply]`. Establish `e1 : (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j = toEAf D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)`. Apply the tactic sequence `rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp`. Rewrite using `[e1]`. Conclude with `this`.
-/
theorem redFn_eq_one_off : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E}, Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (κ : GA D V), Formalism.L2.Theta.SuppAt q.e V κ → Lev.finE V κ ∈ Formalism.L2.DIV.St β → ∀ PP' : Formalism.L2.DIV.Pl D.host.E, PP'.under (𝓞 D.host.F) ≠ PP.under (𝓞 D.host.F) → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1 := by
  intro D k _ _ _ _ q PP hq V β κ hS hst PP' hne
  have hPP' : PP' ≠ PP := fun h => hne (h ▸ rfl)
  have hcP : GlobalTheory.IdemSupport.cP PP' ≠ PP := fun h => hne (by rw [← h, GlobalTheory.IdemSupport.under_cP])
  have h1 : q.e * q.e = q.e := q.split.1
  have hc1 : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, h1]
  have hi1 : toEAf D q.e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP hq).1
  have hi2 : toEAf D (cA D q.e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hc1]))
  have hint : toEAf D (q.e + cA D q.e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [RingHom.map_add]; exact add_mem hi1 hi2
  have hc0 : GlobalTheory.StdFrames.cpt PP' (toEAf D (q.e + cA D q.e)) = 0 := by
    rw [RingHom.map_add, RingHom.map_add, (GlobalTheory.StdFrames.cpt_of_isIdemAt hq).2 PP' hPP', zero_add,
      GlobalTheory.StdFrames.toEAf_cA]
    exact GlobalTheory.StdFrames.cpt_sg_eq_zero ((GlobalTheory.StdFrames.cpt_of_isIdemAt hq).2 _ hcP)
  have hres : Formalism.L2.DIV.resS D.host.F PP' ⟨toEAf D (q.e + cA D q.e), hint⟩ = 0 :=
    resS_eq_zero_of_cpt PP' _ hc0
  have hval : (Lev.finE V κ).val = (Formalism.L2.Theta.mt V κ).map (toEAf D) := rfl
  refine GlobalTheory.LevSplit.redFn_eq_one β PP' (Lev.finE V κ) hst ⟨toEAf D (q.e + cA D q.e), hint⟩ hres ?_
  ext i j
  have := congrArg (toEAf D) (hS i j)
  rw [RingHom.map_mul, Matrix.sub_apply, RingHom.map_sub] at this
  show toEAf D (q.e + cA D q.e) * ((Lev.finE V κ).val - 1) i j = ((Lev.finE V κ).val - 1) i j
  rw [Matrix.sub_apply, hval, Matrix.map_apply]
  have e1 : (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j = toEAf D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  rw [e1]
  exact this

end GlobalTheory.SplitOffRed

end
