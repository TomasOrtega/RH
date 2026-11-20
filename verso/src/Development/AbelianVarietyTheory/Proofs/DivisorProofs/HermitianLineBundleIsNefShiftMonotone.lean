import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.NefShift

/- English proof (translation)
Introduce `_ k _ X _ p D hX M t t' htt h`. Use `⟨fun σ => ?_, h.vertical, ?_⟩` and prove the remaining obligations. Use `(h.semiPos σ).addFn_const (2 * (t' - t))` as an intermediate fact. Establish `e : (((M.shift (fun _ => t) fun _ => rfl).φ σ).addFn fun _ => 2 * (t' - t)) = (M.shift (fun _ => t') fun _ => rfl).φ σ`. Simplify using `only [HermLB.shift, Weight.addFn]`.

Use `congr 1`. Use function extensionality and compare the values at `a b`. Expand and normalize the polynomial expressions, which then agree. Conclude with `e ▸ this`. Introduce `Z i _ _ _ hc hd`.

Take `⟨r, hr, h0⟩` from `h.horizontal Z i hc hd`. Use `⟨r, hr, ?_⟩` and prove the remaining obligations. Establish `e₁` using `HtSelfInter.curveDeg_shift hX M t i hc hd (r := r) hr`. Establish `e₂` using `HtSelfInter.curveDeg_shift hX M t' i hc hd (r := r) hr`. Rewrite using `[e₂]`.

Rewrite `h0` using `[e₁]`. Use polynomial arithmetic with `[(Nat.cast_nonneg _ : (0:ℝ) ≤ Nat.card (X.residueField (i (genericPoint Z)) →+* ℂ))]`.
-/
theorem isNef_shift_mono : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (t t' : ℝ), t ≤ t' →
    (M.shift (fun _ => t) fun _ => rfl).IsNef D → (M.shift (fun _ => t') fun _ => rfl).IsNef D := by
  intro _ k _ X _ p D hX M t t' htt h
  refine ⟨fun σ => ?_, h.vertical, ?_⟩
  · have := (h.semiPos σ).addFn_const (2 * (t' - t))
    have e : (((M.shift (fun _ => t) fun _ => rfl).φ σ).addFn fun _ => 2 * (t' - t)) =
        (M.shift (fun _ => t') fun _ => rfl).φ σ := by
      simp only [HermLB.shift, Weight.addFn]
      congr 1
      funext a b
      ring
    exact e ▸ this
  · intro Z i _ _ _ hc hd
    obtain ⟨r, hr, h0⟩ := h.horizontal Z i hc hd
    refine ⟨r, hr, ?_⟩
    have e₁ := HtSelfInter.curveDeg_shift hX M t i hc hd (r := r) hr
    have e₂ := HtSelfInter.curveDeg_shift hX M t' i hc hd (r := r) hr
    rw [e₂]
    rw [e₁] at h0
    nlinarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ Nat.card (X.residueField (i (genericPoint Z)) →+* ℂ))]

end GlobalTheory.NefShift
