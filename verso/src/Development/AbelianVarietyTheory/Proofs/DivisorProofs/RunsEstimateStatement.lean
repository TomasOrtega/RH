import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterRunWithLawsAndPinsAtSpecialPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupLevelStructureActionFixedRunsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRowsStatement
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

set_option autoImplicit false

namespace GlobalTheory.BigOn.RunsExist

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

/- English proof (translation)
Establish `hL : Links2 p` using `GlobalTheory.T.second_link_of_weight_rows D L hT Gi Gl Kc Y cX ex Csz p hR hM.1`. Establish `hC : CoreTies L ex.errX p.T (R2 p)` using `hM.2.1`. Take `⟨r₁, l₁, c₁, d₁, x₁, p₁⟩` from `GlobalTheory.T.exists_parameterRun_with_laws_and_pins_at_special_prime D L hT Gi Gl Kc Y cX ex Csz p hL hC D.host.pde (Or.inl rfl)`. Take `⟨r₂, l₂, c₂, d₂, x₂, p₂⟩` from `GlobalTheory.T.exists_parameterRun_with_laws_and_pins_at_special_prime D L hT Gi Gl Kc Y cX ex Csz p hL hC D.host.pde' (Or.inr rfl)`. Establish `hcore : GlobalTheory.Hk3.Core (R2 p) (F2 p)` using `⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩`.

Take `⟨ℓ, hℓ⟩` from `GlobalTheory.T.finiteGroup_levelStructure_action_fixedRuns D _ _ _ _ p.T (R2 p) (F2 p) p.κ p.v₀ (fw2 p) (om2 p) hcore hL.2.2.2.2.2.2.1 p.rhoGeo (fun i => (hR.oneMap i).1) hC.level`. Set `r : TwoRuns p.T p.P.Gp` to `⟨r₁, r₂, ℓ⟩`. Establish `hown : OwnPin r` using `ownPin_of d₁ d₂`. Establish `hused : ∀ v, (r.used v = r₂ ∧ ownAt D v = D.host.pde') ∨ (r.used v = r₁ ∧ ownAt D v = D.host.pde)`. Introduce `v`.

Distinguish the cases in `h : Formalism.EigenvalueLevelCeiling.plc v = D.host.pde`. Conclude with `Or.inl ⟨if_pos h, if_pos h⟩`. Conclude with `Or.inr ⟨if_neg h, if_neg h⟩`. Establish `hlaws : ∀ v, LawsFull (r.used v).full`. Introduce `v`.

Apply the tactic sequence `rcases hused v with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]`. Use `exacts [l₂, l₁]`. Use `⟨r, ⟨hlaws, ?_, ?_, ?_, ?_, ?_, hC.level⟩, hown⟩` and prove the remaining obligations. Introduce `v`. Apply the tactic sequence `rcases hused v with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]`.

Use `exacts [c₂, c₁]`. Introduce `v`. Apply the tactic sequence `rcases hused v with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]`. Use `exacts [x₂, x₁]`. Introduce `v hv i`.

Apply the tactic sequence `rcases hused v with ⟨h, ho⟩ | ⟨h, ho⟩ <;> rw [h]`. Use `exacts [p₂ v hv ho i, p₁ v hv ho i]`. Introduce `v i`. Conclude with `(hℓ (r.used v) (hlaws v) i).1`. Introduce `v i`.

Conclude with `(hℓ (r.used v) (hlaws v) i).2`.
-/
theorem exists_runs_at (p : PtAt ex Csz) (hR : p.Rows) (hM : More p) :
    ∃ r : TwoRuns p.T p.P.Gp, RunsOk (fw2 p) r ∧ OwnPin r := by
  have hL : Links2 p := GlobalTheory.T.second_link_of_weight_rows D L hT Gi Gl Kc Y cX ex Csz p hR hM.1
  have hC : CoreTies L ex.errX p.T (R2 p) := hM.2.1
  obtain ⟨r₁, l₁, c₁, d₁, x₁, p₁⟩ :=
    GlobalTheory.T.exists_parameterRun_with_laws_and_pins_at_special_prime D L hT Gi Gl Kc Y cX ex Csz p hL hC D.host.pde (Or.inl rfl)
  obtain ⟨r₂, l₂, c₂, d₂, x₂, p₂⟩ :=
    GlobalTheory.T.exists_parameterRun_with_laws_and_pins_at_special_prime D L hT Gi Gl Kc Y cX ex Csz p hL hC D.host.pde' (Or.inr rfl)
  have hcore : GlobalTheory.Hk3.Core (R2 p) (F2 p) :=
    ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.finiteGroup_levelStructure_action_fixedRuns D _ _ _ _ p.T (R2 p) (F2 p) p.κ p.v₀ (fw2 p) (om2 p) hcore hL.2.2.2.2.2.2.1
    p.rhoGeo (fun i => (hR.oneMap i).1) hC.level
  let r : TwoRuns p.T p.P.Gp := ⟨r₁, r₂, ℓ⟩
  have hown : OwnPin r := ownPin_of d₁ d₂
  have hused : ∀ v, (r.used v = r₂ ∧ ownAt D v = D.host.pde') ∨ (r.used v = r₁ ∧ ownAt D v = D.host.pde) := by
    intro v
    by_cases h : Formalism.EigenvalueLevelCeiling.plc v = D.host.pde
    · exact Or.inl ⟨if_pos h, if_pos h⟩
    · exact Or.inr ⟨if_neg h, if_neg h⟩
  have hlaws : ∀ v, LawsFull (r.used v).full := by
    intro v
    rcases hused v with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    exacts [l₂, l₁]
  refine ⟨r, ⟨hlaws, ?_, ?_, ?_, ?_, ?_, hC.level⟩, hown⟩
  · intro v
    rcases hused v with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    exacts [c₂, c₁]
  · intro v
    rcases hused v with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    exacts [x₂, x₁]
  · intro v hv i
    rcases hused v with ⟨h, ho⟩ | ⟨h, ho⟩ <;> rw [h]
    exacts [p₂ v hv ho i, p₁ v hv ho i]
  · intro v i
    exact (hℓ (r.used v) (hlaws v) i).1
  · intro v i
    exact (hℓ (r.used v) (hlaws v) i).2

end GlobalTheory.BigOn.RunsExist

/- English proof (translation)
Use `⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩` and prove the remaining obligations. Conclude with `⟨0, fun x hx _ i p hR hM => GlobalTheory.BigOn.RunsExist.exists_runs_at p hR hM⟩`.
-/
theorem GlobalTheory.BigOn.runsSt : RunsSt := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  exact ⟨0, fun x hx _ i p hR hM => GlobalTheory.BigOn.RunsExist.exists_runs_at p hR hM⟩
