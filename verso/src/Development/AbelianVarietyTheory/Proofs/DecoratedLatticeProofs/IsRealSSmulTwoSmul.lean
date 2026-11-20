import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing

noncomputable section

open MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.Scale

variable {D : D7}

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w₀ : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w₀ (c • f) = c • heisO ψ S T w₀ f := by
  funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem comb_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : WO S T →₀ ℂ) (c : ℂ) (f : WO S T → ℂ) :
    comb ψ S T a (c • f) = c • comb ψ S T a f := by
  simp only [comb, heisO_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_comm]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem biComb_smul (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (a : WO A S →₀ ℂ) (a' : WO S A' →₀ ℂ) (c : ℂ)
    (C : WO A S → WO S A' → ℂ) : biComb ψ A S A' a a' (c • C) = c • biComb ψ A S A' a a' C := by
  funext u v
  simp only [biComb]
  have h1 : (fun u' => comb ψ S A' a' ((c • C) u') v) = c • fun u' => comb ψ S A' a' (C u') v := by
    funext u'
    show comb ψ S A' a' (c • C u') v = c * comb ψ S A' a' (C u') v
    rw [comb_smul]; rfl
  rw [h1, comb_smul]; rfl

/- English proof (translation)
Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem isThetaFunO_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) where
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    exact ⟨U, hUo, fun u hu hi => by rw [heisO_smul, hU u hu hi]⟩
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := contDiff_const.mul (hf.smooth k L hL hfin w)

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem isLatVac_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {Λ : AddSubgroup (WO S T)} {f : WO S T → ℂ}
    (hf : IsLatVac (heisO ψ S T) Λ f) : IsLatVac (heisO ψ S T) Λ (c • f) :=
  ⟨fun u hu => by rw [heisO_smul, hf.1 u hu], fun e' he u hu hh => by rw [heisO_smul, hf.2 e' he u hu hh]⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isBiVac_smul {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {LA : Set (Fin A.rank → D.host.E)}
    {LS : Set (Fin S.rank → D.host.E)} {LA' : Set (Fin A'.rank → D.host.E)} (c : ℂ) {C : WO A S → WO S A' → ℂ}
    (h : IsBiVac ψ A S A' LA LS LA' C) : IsBiVac ψ A S A' LA LS LA' (c • C) where
  cont := continuous_const.mul h.cont
  left v := by
    have e : (fun u => (c • C) u v) = c • fun u => C u v := rfl
    rw [e]; exact ⟨isThetaFunO_smul c (h.left v).1, isLatVac_smul c (h.left v).2⟩
  right u := by
    have e : (c • C) u = c • C u := rfl
    rw [e]; exact ⟨isThetaFunO_smul c (h.right u).1, isLatVac_smul c (h.right u).2⟩

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem isBiSmooth_smul {A S A' : HSp D} (c : ℂ) {C : WO A S → WO S A' → ℂ} (h : IsBiSmooth C) :
    IsBiSmooth (c • C) :=
  fun n L L' hL hL' h0 h0' u v => by
    show ContDiff ℝ _ fun t => c * C (u + L t) (v + L' t)
    exact ContDiff.mul contDiff_const (h n L L' hL hL' h0 h0' u v)

end GlobalTheory.SeeSaw.Scale

end
