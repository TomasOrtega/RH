import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColComb

variable {D : D7}

/- English proof (translation)
Unfold `comb`. Rewrite using `[Finset.sum_apply]`. Both sides reduce to the same expression.
-/
theorem comb_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) (w : WO S T) :
    comb ψ S T c f w = ∑ u ∈ c.support, c u * (ψ (symplOH S T w u) * f (w + u)) := by
  unfold comb
  rw [Finset.sum_apply]
  rfl

/- English proof (translation)
Simplify using `only [comb_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem comb_comm (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c₁ : WO A S →₀ ℂ) (c₂ : WO S A' →₀ ℂ)
    (G : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    comb ψ S A' c₂ (fun v' => comb ψ A S c₁ (fun u' => G u' v') u) v =
      comb ψ A S c₁ (fun u' => comb ψ S A' c₂ (G u') v) u := by
  simp only [comb_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Use function extensionality and compare the values at `u v`. Use `show comb ψ A S c₁ (fun u' => comb ψ S A' c₂ (fun v' => comb ψ A S c₁' (fun u'' => comb ψ S A' c₂' (F u'') v') u') v) u = comb ψ A S c₁'' (fun u' => comb ψ S A' c₂'' (F u') v) u`. Rewrite using `[h₁]`. Use `congr 1`. Use function extensionality and compare the values at `u'`.

Rewrite using `[comb_comm]`. Simplify using `only [h₂]`.
-/
theorem biComb_biComb (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c₁ c₁' c₁'' : WO A S →₀ ℂ) (c₂ c₂' c₂'' : WO S A' →₀ ℂ)
    (h₁ : ∀ f, comb ψ A S c₁'' f = comb ψ A S c₁ (comb ψ A S c₁' f))
    (h₂ : ∀ f, comb ψ S A' c₂'' f = comb ψ S A' c₂ (comb ψ S A' c₂' f)) (F : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' c₁ c₂ (biComb ψ A S A' c₁' c₂' F) = biComb ψ A S A' c₁'' c₂'' F := by
  funext u v
  show comb ψ A S c₁ (fun u' => comb ψ S A' c₂ (fun v' => comb ψ A S c₁' (fun u'' => comb ψ S A' c₂' (F u'') v') u') v) u =
    comb ψ A S c₁'' (fun u' => comb ψ S A' c₂'' (F u') v) u
  rw [h₁]
  congr 1
  funext u'
  rw [comb_comm]
  simp only [h₂]

end GlobalTheory.ColComb

open GlobalTheory.ColComb in
/- English proof (translation)
Use `⟨0, fun _ _ _ => ⟨0, ?_⟩⟩` and prove the remaining obligations. Introduce `D _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ ch _ _`. Use `beta_reduce`. Introduce `c c' c'' hc C u`. Unfold `evT`.

Use `congr 1`. Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `hk' : 2 * k + 1 < D.R.m`. Use `Finset.mem_range.mp hk` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Simplify using `only [combC]`. Rewrite using `[biComb_biComb (h₁ := hc (2 * k) (by omega)) (h₂ := hc (2 * k + 1) hk')]`.
-/
theorem GlobalTheory.ColComb.main : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (c : Combs ch.G) (c' c'' : ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), (∀ j, j < D.R.m → ∀ f, comb ch.W.ψ _ _ (c'' j) f = comb ch.W.ψ _ _ (c.1 j) (comb ch.W.ψ _ _ (c' j) f)) → ∀ (C : BiFam ch.G) (u : ColPt ch.G), evT (combC ch.W c (combC ch.W (c', 0) C)) 1 u 0 = evT (combC ch.W (c'', 0) C) 1 u 0 := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ ch _ _
  beta_reduce
  intro c c' c'' hc C u
  unfold evT
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' : 2 * k + 1 < D.R.m := by
    have := Finset.mem_range.mp hk
    omega
  simp only [combC]
  rw [biComb_biComb (h₁ := hc (2 * k) (by omega)) (h₂ := hc (2 * k + 1) hk')]

end
