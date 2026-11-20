import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DwCons

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobGL.Chart

def cmL (n : ℕ) : (Idx n → ℝ) →L[ℝ] Mat n :=
  ∑ p, (ContinuousLinearMap.proj p : (Idx n → ℝ) →L[ℝ] ℝ).smulRight (bs p)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem cmL_apply {n : ℕ} (t : Idx n → ℝ) : cmL n t = cm t := by
  simp [cmL, cm]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem cm_single {n : ℕ} (p : Idx n) : cmL n (Pi.single p 1) = bs p := by
  rw [cmL_apply]
  simp [cm, Pi.single_apply, ite_smul]

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hasFDerivAt_chart {n : ℕ} (t : Idx n → ℝ) :
    HasFDerivAt (fun t : Idx n → ℝ => (1 : Mat n) + cm t) (cmL n) t := by
  have h : (fun t : Idx n → ℝ => (1 : Mat n) + cm t) = fun t => 1 + cmL n t := by
    funext s; rw [cmL_apply]
  rw [h]
  exact (cmL n).hasFDerivAt.const_add 1

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem contDiff_chart {n : ℕ} : ContDiff ℝ ∞ (fun t : Idx n → ℝ => (1 : Mat n) + cm t) := by
  have h : (fun t : Idx n → ℝ => (1 : Mat n) + cm t) = fun t => 1 + cmL n t := by
    funext s; rw [cmL_apply]
  rw [h]
  exact contDiff_const.add (cmL n).contDiff

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem isOpen_GLs' {n : ℕ} : IsOpen (GLs n) := by
  have : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne_fun this continuous_const

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem contDiffOn_fderiv_const {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (v : E) : ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g v) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply contDiffOn_const

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem contDiffOn_Dw {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V)
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (L : List (Idx n)) : ContDiffOn ℝ ∞ (Dw L f) (GLs n) := by
  induction L with
  | nil => exact hf
  | cons p L ih =>
    rw [Dw_cons]
    exact contDiffOn_fderiv_const isOpen_GLs' ih (bs p)

/- English proof (translation)
Proceed by induction. Treat this case separately. Both sides reduce to the same expression. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem pd_chart {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V)
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (L : List (Idx n)) :
    ∀ t : Idx n → ℝ, 1 + cm t ∈ GLs n →
      pd L (fun t : Idx n → ℝ => f (1 + cm t)) t = Dw L f (1 + cm t) := by
  induction L with
  | nil => intro t _; rfl
  | cons p L ih =>
    intro t ht
    have hopen : IsOpen {s : Idx n → ℝ | (1 : Mat n) + cm s ∈ GLs n} :=
      isOpen_GLs'.preimage contDiff_chart.continuous
    have hev : pd L (fun t : Idx n → ℝ => f (1 + cm t)) =ᶠ[nhds t]
        fun s => Dw L f (1 + cm s) :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds ht) (fun s hs => ih s hs)
    have hD : DifferentiableAt ℝ (Dw L f) (1 + cm t) :=
      ((contDiffOn_Dw f hf L).contDiffAt (isOpen_GLs'.mem_nhds ht)).differentiableAt (by simp)
    have hc : HasFDerivAt (fun s : Idx n → ℝ => Dw L f (1 + cm s))
        ((fderiv ℝ (Dw L f) (1 + cm t)).comp (cmL n)) t :=
      hD.hasFDerivAt.comp t (hasFDerivAt_chart t)
    rw [pd_cons, Dw_cons]
    show fderiv ℝ (pd L fun t : Idx n → ℝ => f (1 + cm t)) t (Pi.single p 1) = _
    rw [hev.fderiv_eq, hc.fderiv]
    simp [cm_single]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem chart_main : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
    ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ (fun t : Idx n → ℝ => f (1 + cm t)) {t | 1 + cm t ∈ GLs n} ∧
      ∀ (L : List (Idx n)) (t : Idx n → ℝ), 1 + cm t ∈ GLs n →
        pd L (fun t : Idx n → ℝ => f (1 + cm t)) t = Dw L f (1 + cm t) := by
  intro n V _ _ f hf
  refine ⟨?_, fun L t ht => pd_chart f hf L t ht⟩
  exact hf.comp contDiff_chart.contDiffOn (fun t ht => ht)

end GlobalTheory.CompanionTheory.SobGL.Chart
