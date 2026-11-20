import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlaceAlt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepOff

/- English proof (translation)
Establish `h0 : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (offP v w) Ψ`. Establish `h1` using `(GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) (offP v w) (fun p => ¬ offP v w p) (fun p hp hn => hn hp)).2.2.2.2 (v.N j) (v.N (j + 1)) Ψ (hv.sd j (by omega)) (hv.sd (j + 1) hj)`. Establish `h2 : (fun p => offP v w p ∨ ¬ offP v w p) = fun _ : Pl D => True`. Use function extensionality and compare the values at `p`. Conclude with `propext ⟨fun _ => trivial, fun _ => em _⟩`.

Rewrite `h1` using `[h2]`. Conclude with `(h1.1 hΨ).1`. Establish `hQ` using `((GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) (· ∈ w.Q) (offP v w) (fun p hp hn => hn.2 hp)).2.1 (w.eQ j) (hf.atQ j).1).2 _ _ _ h0`. Conclude with `((GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) (· ∈ v.gP) (offP v w) (fun p hp hn => hn.1 hp)).2.1 (v.eG j) (hv.atG j).1).2 _ _ _ hQ`.
-/
theorem vac_off {D : D7} {c : Comm D} {v : VCom c} {t : Tup c} {w : VTup t} (hc : c.Is) (hv : v.Is) (hf : VForm v w)
    (j : ℕ) (hj : j + 1 < D.R.m) (Ψ : WO (c.V j) (c.V (j + 1)) → ℂ)
    (hΨ : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ) :
    Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (offP v w) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ)) := by
  have h0 : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (offP v w) Ψ := by
    have h1 := (GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) (offP v w) (fun p => ¬ offP v w p)
      (fun p hp hn => hn hp)).2.2.2.2 (v.N j) (v.N (j + 1)) Ψ (hv.sd j (by omega)) (hv.sd (j + 1) hj)
    have h2 : (fun p => offP v w p ∨ ¬ offP v w p) = fun _ : Pl D => True := by
      funext p; exact propext ⟨fun _ => trivial, fun _ => em _⟩
    rw [h2] at h1
    exact (h1.1 hΨ).1
  have hQ := ((GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) (· ∈ w.Q) (offP v w)
    (fun p hp hn => hn.2 hp)).2.1 (w.eQ j) (hf.atQ j).1).2 _ _ _ h0
  exact ((GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) (· ∈ v.gP) (offP v w)
    (fun p hp hn => hn.1 hp)).2.1 (v.eG j) (hv.atG j).1).2 _ _ _ hQ

/- English proof (translation)
Introduce `D c v t w hc hv ht hf _ hoff _ _ _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ _ G x a _ f _ κ hκ q₁ q₂`. Establish `k₁` using `vac_off hc hv hf j (by omega) Ψ₁ h₁`. Establish `k₂` using `vac_off hc hv hf (j + 1) (by omega) Ψ₂ h₂`. Take `⟨e₁, e₂⟩` from `(hoff j σ h _ _ k₁ k₂).1 κ hκ`. Establish `a₁ : ∀ g, t.om j (g, q₁ * κ) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) = t.om j (g, q₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁))`.

Introduce `g`. Establish `: ((g, q₁ * κ) : GA D (c.V j) × GA D (c.V (j + 1))) = (g, q₁) * (1, κ)` using `by simp`. Rewrite using `[this, map_mul, Module.End.mul_apply, e₁]`. Establish `a₂ : t.om (j + 1) (q₁ * κ, q₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) = t.om (j + 1) (q₁, q₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂))`. Establish `: ((q₁ * κ, q₂) : GA D (c.V (j + 1)) × GA D (c.V (j + 1 + 1))) = (q₁, q₂) * (κ, 1)` using `by simp`.

Rewrite using `[this, map_mul, Module.End.mul_apply, e₂]`. Rewrite `a₁` using `[← (ht.sBF j (σ + 1) h).1]`. Rewrite `a₂` using `[← (ht.sFB j σ h).1]`. Unfold `integ Chain.hand`. Use `Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations.

Use `erw [a₁ g, a₂]`.
-/
theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ κ, InK (c.V (j + 1)) (v.N (j + 1)) (offP v w) κ → ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f (q₁ * κ) q₂ = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hf _ hoff _ _ _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ _ G x a _ f _ κ hκ q₁ q₂
  have k₁ := vac_off hc hv hf j (by omega) Ψ₁ h₁
  have k₂ := vac_off hc hv hf (j + 1) (by omega) Ψ₂ h₂
  obtain ⟨e₁, e₂⟩ := (hoff j σ h _ _ k₁ k₂).1 κ hκ
  have a₁ : ∀ g, t.om j (g, q₁ * κ) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) =
      t.om j (g, q₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) := by
    intro g
    have : ((g, q₁ * κ) : GA D (c.V j) × GA D (c.V (j + 1))) = (g, q₁) * (1, κ) := by simp
    rw [this, map_mul, Module.End.mul_apply, e₁]
  have a₂ : t.om (j + 1) (q₁ * κ, q₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) =
      t.om (j + 1) (q₁, q₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) := by
    have : ((q₁ * κ, q₂) : GA D (c.V (j + 1)) × GA D (c.V (j + 1 + 1))) = (q₁, q₂) * (κ, 1) := by simp
    rw [this, map_mul, Module.End.mul_apply, e₂]
  rw [← (ht.sBF j (σ + 1) h).1] at a₁
  rw [← (ht.sFB j σ h).1] at a₂
  unfold integ Chain.hand
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  erw [a₁ g, a₂]

end GlobalTheory.DStepOff
