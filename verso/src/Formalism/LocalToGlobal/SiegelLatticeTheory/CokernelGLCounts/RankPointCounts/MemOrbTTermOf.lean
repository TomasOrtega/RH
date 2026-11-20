import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RepAtTup

noncomputable section

namespace Formalism.L2.SG.Pf.FibPart

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Part

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def clsSet (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (u' : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (Z : PairVal.MatR D) : Set (Set (LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))) :=
  {O | ∃ F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z,
    O = {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z ∧ CntLocal.NilradicalFlagMoved F0 Λ F' F''}}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cntE_eq (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : PairVal.MatR D) :
    CntLocal.cntE (CntLocal.Tn u') F0 Λ Z = (clsSet F0 u' Λ Z).encard := rfl

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem pd_of_ez {Λ : Submodule (𝓞 D.host.E) (VS D).V} {Z : PairVal.MatR D}
    {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    (h : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z) : PD D Λ (lf D F0) u' F' :=
  ⟨h.1.1, h.1.2.1, h.2.2.2.1⟩

def termOf (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (h : PD D Λ (lf D F0) u' F') : TermDef.Term D u u' F0 what₂ :=
  ⟨Λ, hΛ, TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') ⟨F', h⟩⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem n0rel_refl (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) :
    CntLocal.NilradicalFlagMoved F0 Λ F' F' :=
  ⟨1, ⟨TermDef.one_mem_NLam Λ (lf D F0), fun _ => rfl, rfl⟩, fun _ => rfl, rfl⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dcrel_of_n0rel {Λ : Submodule (𝓞 D.host.E) (VS D).V} {F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    (hl₁ : IsLift Λ F₁) (hl₂ : IsLift Λ F₂) (h : CntLocal.NilradicalFlagMoved F0 Λ F₁ F₂) : DCRel Λ (lf D F0) F₁ F₂ := by
  obtain ⟨n, hn, he, hz⟩ := h
  refine ⟨n, hn.1, 1, TermDef.one_mem_NLam Λ F₁, fun a => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [Formalism.L2.SG.Pf.frame_last_td, Formalism.L2.SG.Pf.frame_last_td]
      exact hz.symm
    · rw [Formalism.L2.SG.Pf.frame_castSucc_td, Formalism.L2.SG.Pf.frame_castSucc_td]
      exact (he i).symm
  · rw [hl₂.2, hl₁.2]
    exact hz.symm

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Substitute using the available equality. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem orbT_disj {Z : PairVal.MatR D} {γ₁ γ₂ : TermDef.Term D u u' F0 what₂} (hl : γ₁.lam = γ₂.lam)
    {O : Set (LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))}
    (h₁ : O ∈ PairVal.orbT D u u' F0 what₂ γ₁ Z) (h₂ : O ∈ PairVal.orbT D u u' F0 what₂ γ₂ Z) : γ₁ = γ₂ := by
  obtain ⟨Λ₁, m₁, c₁⟩ := γ₁
  obtain ⟨Λ₂, m₂, c₂⟩ := γ₂
  simp only at hl
  subst hl
  obtain ⟨F₁, hF₁, ⟨p₁, hc₁⟩, rfl⟩ := h₁
  obtain ⟨F₂, hF₂, ⟨p₂, hc₂⟩, hO⟩ := h₂
  have hmem := (Set.ext_iff.1 hO F₁).1 ⟨hF₁, n0rel_refl Λ₁ F₁⟩
  have hdc := dcrel_of_n0rel hF₂.1.1 hF₁.1.1 hmem.2
  have e : TermDef.mk Λ₁ (lf D F0) (PD D Λ₁ (lf D F0) u') ⟨F₂, p₂⟩ =
      TermDef.mk Λ₁ (lf D F0) (PD D Λ₁ (lf D F0) u') ⟨F₁, p₁⟩ := Quot.sound hdc
  have hcc : c₁ = c₂ := hc₁.symm.trans (e.symm.trans hc₂)
  subst hcc
  rfl

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem mem_orbT_termOf (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) {Z : PairVal.MatR D}
    {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    (hF : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z) :
    {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z ∧ CntLocal.NilradicalFlagMoved F0 Λ F' F''} ∈
      PairVal.orbT D u u' F0 what₂ (termOf Λ hΛ F' (pd_of_ez hF)) Z :=
  ⟨F', hF, ⟨pd_of_ez hF, rfl⟩, rfl⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem repIn_termOf (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) {Z : PairVal.MatR D}
    {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    (hF : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z) :
    RepIn u u' F0 what₂ (termOf Λ hΛ F' (pd_of_ez hF)) Z :=
  ⟨F', hF, ⟨pd_of_ez hF, rfl⟩⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem eligAt_termOf (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) {Z : PairVal.MatR D}
    {w : Point D.host.E (D.R.rS + 1)} (hZ : AtMat w Z) {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    (hF : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z) :
    EligAt (termOf Λ hΛ F' (pd_of_ez hF)) w := by
  refine ⟨⟨⟨F', ⟨pd_of_ez hF, rfl⟩, hF.2.2.1⟩, ?_⟩, ⟨F', ⟨pd_of_ez hF, rfl⟩, hF.1.2.2, ?_⟩⟩
  · show TermDef.Gt Λ (lf D F0) (PD D Λ (lf D F0) u') (TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') ⟨F', _⟩) ≠ 0
    rw [TermDef.Gt_mk (Formalism.L2.SG.Pf.g_value_function _ _ _)]
    exact hF.1.2.2
  · obtain ⟨L, U, hL, hU, he⟩ := hZ
    refine ⟨L, U, hL, hU, ?_⟩
    rw [← he]
    congr 1
    exact hF.2.2.2.2

end Part

end Formalism.L2.SG.Pf.FibPart
