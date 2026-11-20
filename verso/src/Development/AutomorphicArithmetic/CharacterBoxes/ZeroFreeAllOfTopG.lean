import Development.AutomorphicArithmetic.CharacterBoxes.Supply
import Development.AutomorphicArithmetic.CharacterBoxes.DivinNOfHypV
import Development.AutomorphicArithmetic.PrimitiveCosets.LevelGmLeOnFamilyScales
import Development.AutomorphicArithmetic.PrimitiveCosets.Imports

noncomputable section

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX

def TopG : Prop :=
  ∀ (la : ℝ) (G : FReq), 1 < la → HostExW la G.req →
    (∀ {eps : ℝ} (Fm : FamP eps), G.cls la Fm → HypV Fm.toFamCore) → FamilyClassConnected (G.cls la)

/- English proof (translation)
Assemble the required witnesses or components as `⟨Fm.x1 + 1, fun x hx i => (h.2 x (by linarith) i).2⟩`.
-/
theorem hypV_of_cls (ψ : PChar) (la : ℝ) {eps : ℝ} (Fm : FamP eps) (h : (GChi ψ).cls la Fm) : HypV Fm.toFamCore :=
  ⟨Fm.x1 + 1, fun x hx i => (h.2 x (by linarith) i).2⟩

/- English proof (translation)
Use `⟨4, Fm.x1 + 1, fun x hx i => ?_⟩` and prove the remaining obligations. Establish `h1` using `(h.2 x (by linarith) i).1`. Rewrite `h1` using `[Fm.L_x x i (by linarith), Fm.L_eps x i]`. Conclude with `h1`.
-/
theorem eFamC_of_cls (ψ : PChar) (la : ℝ) {eps : ℝ} (Fm : FamP eps) (h : (GChi ψ).cls la Fm) :
    EFamC (Level.cyc ψ) Fm.toFamCore := by
  refine ⟨4, Fm.x1 + 1, fun x hx i => ?_⟩
  have h1 := (h.2 x (by linarith) i).1
  rw [Fm.L_x x i (by linarith), Fm.L_eps x i] at h1
  exact h1

/- English proof (translation)
Establish `key : ZeroFreeOn fun _ => True` using `zeroFreeOn_of_tiedWin_cyc (Fam := FamP) (core := fun Fm => Fm.toFamCore) (Tied := fun Fm => ChainTied Fm) hla (fun ψ _ => UpperTheory.Comparison₂.level_gm_le_on_family_scales _) (fun ψ _ => UpperTheory.Comparison₂.formB _) fun ψ _ => by`. Take `⟨eD, eL, ε₁, h1, h2⟩` from `h la (GChi ψ) hla (hS ψ) (hypV_of_cls ψ la)`. Use `⟨eD, eL, ε₁, h1, fun eps a b => ?_⟩` and prove the remaining obligations. Take `⟨Fm, c, d⟩` from `h2 eps a b`. Conclude with `⟨Fm, eFamC_of_cls ψ la Fm c, c.1, d⟩`.

Conclude with `key`.
-/
theorem zeroFreeAll_of_topG {la : ℝ} (hla : 1 < la) (h : TopG) (hS : ∀ ψ : PChar, HostExW la (GChi ψ).req) : ZeroFreeAll := by
  have key : ZeroFreeOn fun _ => True :=
    zeroFreeOn_of_tiedWin_cyc (Fam := FamP) (core := fun Fm => Fm.toFamCore) (Tied := fun Fm => ChainTied Fm) hla
      (fun ψ _ => UpperTheory.Comparison₂.level_gm_le_on_family_scales _) (fun ψ _ => UpperTheory.Comparison₂.formB _) fun ψ _ => by
        obtain ⟨eD, eL, ε₁, h1, h2⟩ := h la (GChi ψ) hla (hS ψ) (hypV_of_cls ψ la)
        refine ⟨eD, eL, ε₁, h1, fun eps a b => ?_⟩
        obtain ⟨Fm, c, d⟩ := h2 eps a b
        exact ⟨Fm, eFamC_of_cls ψ la Fm c, c.1, d⟩
  exact key

end UpperTheory.Top

end
