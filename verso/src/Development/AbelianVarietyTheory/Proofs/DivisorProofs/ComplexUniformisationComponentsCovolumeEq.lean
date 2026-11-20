import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLevelGroupDataSameCovolumeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportSelfDualDataOneHermitianSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqSelfDualLatticesSameHermitianSpaceStatement

open NumberField

namespace GlobalTheory.EqCovol

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ r U hσ hU hG hp hq k k'`. Take `⟨Y, hΨ, hp0, -, -, -, hL, hS, hc⟩` from `GlobalTheory.T.exists_fullLevelGroup_data_same_covolume E H Dw l Xo c σ r U hσ hU hG hp hq k`. Take `⟨Y', hΨ', hp0', -, -, -, hL', hS', hc'⟩` from `GlobalTheory.T.exists_fullLevelGroup_data_same_covolume E H Dw l Xo c σ r U hσ hU hG hp hq k'`. Take `⟨hr, hk, -⟩` from `hU`. Establish `hY : ∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0` using `fun τ => hΨ ▸ (hk k).2 τ`.

Establish `hY' : ∀ τ : E →+* ℂ, τ ∈ Y'.Ψ ↔ τ (H.rt : E) = H.rt0` using `fun τ => hΨ' ▸ (hk k').2 τ`. Establish `eΨ : Y'.Ψ = Y.Ψ` using `Finset.ext fun τ => (hY' τ).trans (hY τ).symm`. Establish `ep : Y'.p0 = Y.p0` using `by rw [hp0, hp0', (hk k).1, (hk k').1]`. Establish `h1 : 1 ≤ Y.p0` using `by rw [hp0, (hk k).1]; exact hq`. Establish `h2 : Y.p0 < r` using `by rw [hp0, (hk k).1, hr]; omega`.

Take `⟨Z, hZΨ, hZG, hZξ, hZp, hZL, hZS, hZc⟩` from `GlobalTheory.T.exists_transport_selfDual_data_one_hermitianSpace E H l r Y Y' hY eΨ ep h1 h2 hL' hS hS'`. Rewrite using `[hc, hc', ← hZc]`. Conclude with `GlobalTheory.T.covolume_eq_selfDual_lattices_same_hermitian_space E H l r Y Z hG hY hZΨ hZG hZξ hZp h1 h2 hL hZL hS hZS`.
-/
theorem covol_eq_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k k' : U.Comp, GlobalTheory.TrueCx.covol (U.X k) = GlobalTheory.TrueCx.covol (U.X k') := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hG hp hq k k'
  obtain ⟨Y, hΨ, hp0, -, -, -, hL, hS, hc⟩ := GlobalTheory.T.exists_fullLevelGroup_data_same_covolume E H Dw l Xo c σ r U hσ hU hG hp hq k
  obtain ⟨Y', hΨ', hp0', -, -, -, hL', hS', hc'⟩ := GlobalTheory.T.exists_fullLevelGroup_data_same_covolume E H Dw l Xo c σ r U hσ hU hG hp hq k'
  obtain ⟨hr, hk, -⟩ := hU
  have hY : ∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => hΨ ▸ (hk k).2 τ
  have hY' : ∀ τ : E →+* ℂ, τ ∈ Y'.Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => hΨ' ▸ (hk k').2 τ
  have eΨ : Y'.Ψ = Y.Ψ := Finset.ext fun τ => (hY' τ).trans (hY τ).symm
  have ep : Y'.p0 = Y.p0 := by rw [hp0, hp0', (hk k).1, (hk k').1]
  have h1 : 1 ≤ Y.p0 := by rw [hp0, (hk k).1]; exact hq
  have h2 : Y.p0 < r := by rw [hp0, (hk k).1, hr]; omega
  obtain ⟨Z, hZΨ, hZG, hZξ, hZp, hZL, hZS, hZc⟩ := GlobalTheory.T.exists_transport_selfDual_data_one_hermitianSpace E H l r Y Y' hY eΨ ep h1 h2 hL' hS hS'
  rw [hc, hc', ← hZc]
  exact GlobalTheory.T.covolume_eq_selfDual_lattices_same_hermitian_space E H l r Y Z hG hY hZΨ hZG hZξ hZp h1 h2 hL hZL hS hZS

end GlobalTheory.EqCovol
