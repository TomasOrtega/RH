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

/- English proof (authored)
Take the eventual threshold x₁ + 1. At each x beyond this threshold and each index i, membership in the character family gives the two conditions defining GChi at the corresponding host. Its second condition is the VVle bound required by HypV.
-/
theorem hypV_of_cls (ψ : PChar) (la : ℝ) {eps : ℝ} (Fm : FamP eps) (h : (GChi ψ).cls la Fm) : HypV Fm.toFamCore :=
  ⟨Fm.x1 + 1, fun x hx i => (h.2 x (by linarith) i).2⟩

/- English proof (authored)
Use the constant 4 and the eventual threshold x₁ + 1. The first condition in GChi gives EAtH at the chosen host. Its scale coordinates are x and ε, by the two scale identities for the family. Substituting these coordinates gives the asserted eventual condition.
-/
theorem eFamC_of_cls (ψ : PChar) (la : ℝ) {eps : ℝ} (Fm : FamP eps) (h : (GChi ψ).cls la Fm) :
    EFamC (Level.cyc ψ) Fm.toFamCore := by
  refine ⟨4, Fm.x1 + 1, fun x hx i => ?_⟩
  have h1 := (h.2 x (by linarith) i).1
  rw [Fm.L_x x i (by linarith), Fm.L_eps x i] at h1
  exact h1

/- English proof (authored)
Use the cyclic tied-window nonvanishing theorem with families FamP and the tie relation ChainTied. Its comparison hypotheses are the level bound on family scales and the form-B theorem. For each ψ, feed TopG the host-existence input for GChi ψ and the HypV bound that follows from membership in that class. This gives the exponents, a positive ε cutoff, and the required families. Each family supplies EFamC by eFamC_of_cls, its windows directly from class membership, and the tie data from connectedness. The resulting nonvanishing theorem applies to every primitive character.
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
