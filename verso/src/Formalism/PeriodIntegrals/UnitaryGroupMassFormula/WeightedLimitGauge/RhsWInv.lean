import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsHaar

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

def orbV (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (x : Mt k r) : Fin (2 * r + k + 1) → ℂ := Matrix.of x *ᵥ z'

def rmulM (b : Mat k r) (x : Mt k r) : Mt k r := fun i j => (Matrix.of x * b) i j

def DescUniq : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (μW' : Measure (Mt k r)), IsHaarOn (UWset k r z') μW' →
    μW' Set.univ ≠ ⊤ → ∀ ν₁ ν₂ : Measure (Mt k r), SigmaFinite ν₁ → SigmaFinite ν₂ →
    ν₁ {x | Matrix.of x ∉ UWb k r} = 0 → ν₂ {x | Matrix.of x ∉ UWb k r} = 0 →
    (∀ b ∈ UWset k r z', ν₁.map (rmulM b) = ν₁) → (∀ b ∈ UWset k r z', ν₂.map (rmulM b) = ν₂) →
    ν₁.map (orbV k r z') = ν₂.map (orbV k r z') → ν₁ = ν₂

def RInvNu : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∀ b ∈ UWset k r z',
      (nuR k r z z' μW μW' μsec).map (rmulM b) = nuR k r z z' μW μW' μsec

def OrbInv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∀ s ∈ UWb k r, ∀ F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞, Measurable F →
      rhsW k r z z' μW μW' μsec (fun x => F (s *ᵥ orbV k r z' x)) =
        rhsW k r z z' μW μW' μsec (fun x => F (orbV k r z' x))

/- English proof (translation)
Unfold `orbV`. Conclude with `Continuous.matrix_mulVec (continuous_id' (X := Mt k r)) continuous_const`.
-/
theorem orbV_cont (z' : Fin (2 * r + k + 1) → ℂ) : Continuous (orbV k r z') := by
  unfold orbV
  exact Continuous.matrix_mulVec (continuous_id' (X := Mt k r)) continuous_const

/- English proof (translation)
Unfold `rmulM`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Conclude with `(Continuous.matrix_mul (continuous_id' (X := Mt k r)) continuous_const).matrix_elem i j`.
-/
theorem rmulM_cont (b : Mat k r) : Continuous (rmulM b : Mt k r → Mt k r) := by
  unfold rmulM
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (Continuous.matrix_mul (continuous_id' (X := Mt k r)) continuous_const).matrix_elem i j

def lmulE (s : Mat k r) (hs : IsUnit s.det) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM s
  invFun := lmulM s⁻¹
  left_inv x := Matrix.nonsing_inv_mul_cancel_left (A := s) (Matrix.of x) hs
  right_inv x := Matrix.mul_nonsing_inv_cancel_left (A := s) (Matrix.of x) hs
  measurable_toFun := (HU.lmulM_cont s).measurable
  measurable_invFun := (HU.lmulM_cont s⁻¹).measurable

/- English proof (translation)
Use `hD.haarW.1` as an intermediate fact. Use `hD.haarW'.1` as an intermediate fact. Rewrite using `[nuR, Measure.map_apply (meas_chartF hD.sec) (s := {x : Mt k r | Matrix.of x ∉ UWb k r}) HU.amb_closed.isOpen_compl.measurableSet]`. Conclude with `measure_mono_null (fun q hq hg => hq (mem_chart hD hg)) (src_null hD)`.
-/
theorem nu_conc (hD : WbData k r z z' μW μW' a a' μsec) :
    nuR k r z z' μW μW' μsec {x | Matrix.of x ∉ UWb k r} = 0 := by
  have := hD.haarW.1
  have := hD.haarW'.1
  rw [nuR, Measure.map_apply (meas_chartF hD.sec) (s := {x : Mt k r | Matrix.of x ∉ UWb k r})
    HU.amb_closed.isOpen_compl.measurableSet]
  exact measure_mono_null (fun q hq hg => hq (mem_chart hD hg)) (src_null hD)

/- English proof (translation)
Introduce `k r z z' μW μW' a a' μsec hd s hs φ hφ`. Use `hd.haarW.1` as an intermediate fact. Use `hd.haarW'.1` as an intermediate fact. Establish `hσ : SigmaFinite (nuR k r z z' μW μW' μsec)` using `nu_sigmaFinite hd`. Establish `hl : Measurable (lmulM s : Mt k r → Mt k r)` using `(HU.lmulM_cont s).measurable`.

Establish `hσ1 : SigmaFinite ((nuR k r z z' μW μW' μsec).map (lmulM s))` using `(lmulE s (HU.uwb_unit hs)).sigmaFinite_map`. Establish `hC1 : ((nuR k r z z' μW μW' μsec).map (lmulM s)) {x | Matrix.of x ∉ UWb k r} = 0`. Rewrite using `[Measure.map_apply hl (s := {x : Mt k r | Matrix.of x ∉ UWb k r}) HU.amb_closed.isOpen_compl.measurableSet]`. Use `measure_mono_null (fun x (hx : Matrix.of (lmulM s x) ∉ UWb k r) (hx' : Matrix.of x ∈ UWb k r) => hx (HU.uwb_mul hs hx')) (nu_conc hd)` and prove the remaining obligations. Establish `hR1 : ∀ b ∈ UWset k r z', ((nuR k r z z' μW μW' μsec).map (lmulM s)).map (rmulM b) = (nuR k r z z' μW μW' μsec).map (lmulM s)`.

Introduce `b hb`. Establish `hr : Measurable (rmulM b : Mt k r → Mt k r)` using `(rmulM_cont b).measurable`. Establish `e : rmulM b ∘ lmulM s = lmulM s ∘ rmulM b`. Use function extensionality and compare the values at `x`. Use `show (s * Matrix.of x * b : Mat k r) = s * (Matrix.of x * b)`.

Conclude with `Matrix.mul_assoc _ _ _`. Rewrite using `[Measure.map_map hr hl, e, ← Measure.map_map hl hr, hR k r z z' μW μW' a a' μsec hd b hb]`. Establish `hO1 : ((nuR k r z z' μW μW' μsec).map (lmulM s)).map (orbV k r z') = (nuR k r z z' μW μW' μsec).map (orbV k r z')`. Establish `ho : Measurable (orbV k r z')` using `(orbV_cont z').measurable`. Use extensionality with `A hA`.

Rewrite using `[Measure.map_map ho hl, Measure.map_apply (ho.comp hl) hA, Measure.map_apply ho hA, ← lintegral_indicator_one ((ho.comp hl) hA), ← lintegral_indicator_one (ho hA)]`. Establish `e1 : ((orbV k r z' ∘ lmulM s) ⁻¹' A).indicator (1 : Mt k r → ℝ≥0∞) = fun x => A.indicator 1 (s *ᵥ orbV k r z' x)`. Use function extensionality and compare the values at `x`. Use `show ((orbV k r z' ∘ lmulM s) ⁻¹' A).indicator 1 x = A.indicator 1 (s *ᵥ (Matrix.of x *ᵥ z'))`. Rewrite using `[Matrix.mulVec_mulVec]`.

Both sides reduce to the same expression. Establish `e2 : (orbV k r z' ⁻¹' A).indicator (1 : Mt k r → ℝ≥0∞) = fun x => A.indicator 1 (orbV k r z' x)`. Use function extensionality and compare the values at `x`. Both sides reduce to the same expression. Establish `hF : Measurable (A.indicator (1 : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞))` using `measurable_one.indicator hA`.

Rewrite using `[e1, e2, ← repr hd (fun x => A.indicator 1 (s *ᵥ orbV k r z' x)) (hF.comp ((continuous_const.matrix_mulVec continuous_id).measurable.comp ho)), ← repr hd (fun x => A.indicator 1 (orbV k r z' x)) (hF.comp ho), hO k r z z' μW μW' a a' μsec hd s hs _ hF]`. Establish `key` using `hD k r z' μW' hd.haarW' (by rw [hd.massW']; exact ENNReal.ofReal_ne_top) _ _ hσ1 hσ hC1 (nu_conc hd) hR1 (hR k r z z' μW μW' a a' μsec hd) hO1`. Rewrite using `[repr hd (fun x => φ (lmulM s x)) (hφ.comp hl), repr hd _ hφ, ← lintegral_map hφ hl, key]`.
-/
theorem rhsWInv_of (hD : DescUniq) (hR : RInvNu) (hO : OrbInv) : RhsWInv := by
  intro k r z z' μW μW' a a' μsec hd s hs φ hφ
  have := hd.haarW.1
  have := hd.haarW'.1
  have hσ : SigmaFinite (nuR k r z z' μW μW' μsec) := nu_sigmaFinite hd
  have hl : Measurable (lmulM s : Mt k r → Mt k r) := (HU.lmulM_cont s).measurable
  have hσ1 : SigmaFinite ((nuR k r z z' μW μW' μsec).map (lmulM s)) :=
    (lmulE s (HU.uwb_unit hs)).sigmaFinite_map
  have hC1 : ((nuR k r z z' μW μW' μsec).map (lmulM s)) {x | Matrix.of x ∉ UWb k r} = 0 := by
    rw [Measure.map_apply hl (s := {x : Mt k r | Matrix.of x ∉ UWb k r})
      HU.amb_closed.isOpen_compl.measurableSet]
    refine measure_mono_null (fun x (hx : Matrix.of (lmulM s x) ∉ UWb k r) (hx' : Matrix.of x ∈ UWb k r) =>
      hx (HU.uwb_mul hs hx')) (nu_conc hd)
  have hR1 : ∀ b ∈ UWset k r z', ((nuR k r z z' μW μW' μsec).map (lmulM s)).map (rmulM b) =
      (nuR k r z z' μW μW' μsec).map (lmulM s) := by
    intro b hb
    have hr : Measurable (rmulM b : Mt k r → Mt k r) := (rmulM_cont b).measurable
    have e : rmulM b ∘ lmulM s = lmulM s ∘ rmulM b := by
      funext x
      show (s * Matrix.of x * b : Mat k r) = s * (Matrix.of x * b)
      exact Matrix.mul_assoc _ _ _
    rw [Measure.map_map hr hl, e, ← Measure.map_map hl hr, hR k r z z' μW μW' a a' μsec hd b hb]
  have hO1 : ((nuR k r z z' μW μW' μsec).map (lmulM s)).map (orbV k r z') =
      (nuR k r z z' μW μW' μsec).map (orbV k r z') := by
    have ho : Measurable (orbV k r z') := (orbV_cont z').measurable
    ext A hA
    rw [Measure.map_map ho hl, Measure.map_apply (ho.comp hl) hA, Measure.map_apply ho hA,
      ← lintegral_indicator_one ((ho.comp hl) hA), ← lintegral_indicator_one (ho hA)]
    have e1 : ((orbV k r z' ∘ lmulM s) ⁻¹' A).indicator (1 : Mt k r → ℝ≥0∞) =
        fun x => A.indicator 1 (s *ᵥ orbV k r z' x) := by
      funext x
      show ((orbV k r z' ∘ lmulM s) ⁻¹' A).indicator 1 x = A.indicator 1 (s *ᵥ (Matrix.of x *ᵥ z'))
      rw [Matrix.mulVec_mulVec]
      rfl
    have e2 : (orbV k r z' ⁻¹' A).indicator (1 : Mt k r → ℝ≥0∞) = fun x => A.indicator 1 (orbV k r z' x) := by
      funext x
      rfl
    have hF : Measurable (A.indicator (1 : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞)) := measurable_one.indicator hA
    rw [e1, e2, ← repr hd (fun x => A.indicator 1 (s *ᵥ orbV k r z' x))
        (hF.comp ((continuous_const.matrix_mulVec continuous_id).measurable.comp ho)),
      ← repr hd (fun x => A.indicator 1 (orbV k r z' x)) (hF.comp ho), hO k r z z' μW μW' a a' μsec hd s hs _ hF]
  have key := hD k r z' μW' hd.haarW' (by rw [hd.massW']; exact ENNReal.ofReal_ne_top) _ _ hσ1 hσ hC1
    (nu_conc hd) hR1 (hR k r z z' μW μW' a a' μsec hd) hO1
  rw [repr hd (fun x => φ (lmulM s x)) (hφ.comp hl), repr hd _ hφ, ← lintegral_map hφ hl, key]

end PI.RhsWLim.W.RI
