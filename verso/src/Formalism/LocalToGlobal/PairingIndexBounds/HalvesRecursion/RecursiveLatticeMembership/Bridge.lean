import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.Statement

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Rec

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Mv Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem HfS_apply (D : D7) (T : Tor D) (N N' : ℕ) (z w : VC D N N') : HfS D T N N' z w = Hf D T z w := rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem al_pm (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') : al D T x = 1 ∨ al D T x = -1 := by
  unfold al
  rcases Int.even_or_odd (round (Real.sqrt D.host.d / 2 * (Hf D T x x).re)) with h | h
  · left; exact h.neg_one_zpow
  · right; exact h.neg_one_zpow

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem exp_int_sign (b : ℤ) :
    Complex.exp (-((Real.pi : ℂ) * Complex.I * (b : ℂ))) = Complex.exp ((Real.pi : ℂ) * Complex.I * (b : ℂ)) := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  exact ⟨-b, by push_cast; ring⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem local_global_comparison_holds : Bridge := by
  intro D T N N'
  refine ⟨fun x y => ?_, fun x G => rfl, fun La₁ La₂ G => ?_, fun La' G hG => ?_, fun La' hI => ?_⟩
  · show Hf D T y x = starRingEnd ℂ (Hf D T x y)
    exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_herm T x y
  · funext z
    simp only [Iop, inter, relIdx, AddSubgroup.relIndex]
    rfl
  · intro x hx z
    exact hG.2 x hx z
  · refine ⟨fun x _ => al_pm D T x, fun x hx y hy => ?_⟩
    have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.semiChar_of_HfInt T hI x hx y hy
    rw [h]
    obtain ⟨a, b, -, hab⟩ := hI x hx y hy
    have him : (Hf D T x y).im = b := by rw [hab]; simp
    simp only [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.cf, altE, HfS_apply, him]
    have e := exp_int_sign b
    push_cast at e ⊢
    rw [e]

end Formalism.L2.PairingIndexBounds.Rec
