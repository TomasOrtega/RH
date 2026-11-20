import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainFractionalIdealRelations
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.AdaptFBIdeals

variable {D : D7}

/- English proof (translation)
Establish `h1 : (d.pX ⬝ d.jX) i i = 1` using `by rw [d.pX_jX]; exact Matrix.one_apply_eq i`. Rewrite `h1` using `[Matrix.mul_apply]`. Establish `h2 : a = ∑ k, d.pX i k * colMul d.jX i a k`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2]`.

Conclude with `Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.latV_supp h k)`.
-/
theorem supp_of_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (v : Pl D) (i : Fin ρ) (a : AE D)
    (h : colMul d.jX i a ∈ latV S L (· = v)) : a ∈ idAt D (· = v) := by
  have h1 : (d.pX ⬝ d.jX) i i = 1 := by rw [d.pX_jX]; exact Matrix.one_apply_eq i
  rw [Matrix.mul_apply] at h1
  have h2 : a = ∑ k, d.pX i k * colMul d.jX i a k := by
    calc a = a * ∑ k, d.pX i k * d.jX k i := by rw [h1, mul_one]
      _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; simp only [colMul]; ring
  rw [h2]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.latV_supp h k)

/- English proof (translation)
Proceed by induction on `h using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, -, hα, x, -, rfl⟩` from `hy`. Conclude with `GlobalTheory.FinPl.LatMem.tmul_mem_idAt hα _`. Consider the case `zero => exact zero_mem _`.

Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `neg x _ hx => exact neg_mem hx`.
-/
theorem idV_supp (𝔞 : FI D) (v : Pl D) {a : AE D} (h : a ∈ idV 𝔞 v) : a ∈ idAt D (· = v) := by
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, -, hα, x, -, rfl⟩ := hy
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hα _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

/- English proof (translation)
Establish `hc : ∀ {n : ℕ} (x : Mx D S.rank n) (i : Fin n), colMul x i 0 = 0` using `fun x i => by`. Use function extensionality and compare the values at `k`. Simplify using `[colMul]`. Rewrite using `[hL]`. Simplify using `only [Matrix.mulVec_mulVec, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.zero_mulVec, Matrix.one_mulVec, Pi.zero_apply, hc, zero_mem, implies_true, true_and]`.
-/
theorem j_zero_mul_mem_lattice_iff {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (M : Lat S₀) (v : Pl D) (hL : MonoAt d L M v)
    (w : Fin S₀.rank → AE D) : d.j0 *ᵥ w ∈ latV S L (· = v) ↔ w ∈ latV S₀ M (· = v) := by
  have hc : ∀ {n : ℕ} (x : Mx D S.rank n) (i : Fin n), colMul x i 0 = 0 := fun x i => by
    funext k; simp [colMul]
  rw [hL]
  simp only [Matrix.mulVec_mulVec, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.zero_mulVec, Matrix.one_mulVec, Pi.zero_apply, hc,
    zero_mem, implies_true, true_and]

end GlobalTheory.SeeSaw.AdaptFBIdeals

namespace GlobalTheory.SeeSaw

end GlobalTheory.SeeSaw
