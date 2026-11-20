import Mathlib
import Formalism.PeriodIntegrals.QuotInv

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace PI.QuotInvW

variable {m : ℕ}

def mm (a b : MtM m) : MtM m := fun i j => (Matrix.of a * Matrix.of b) i j

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
lemma continuous_mm : Continuous (fun p : MtM m × MtM m => mm p.1 p.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [mm, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma measurable_mm : Measurable (fun p : MtM m × MtM m => mm p.1 p.2) :=
  continuous_mm.measurable

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma measurable_mm_left (b : MtM m) : Measurable (fun a : MtM m => mm a b) :=
  measurable_mm.comp (measurable_id.prodMk measurable_const)

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma measurable_mm_right (a : MtM m) : Measurable (fun b : MtM m => mm a b) :=
  measurable_mm.comp (measurable_const.prodMk measurable_id)

def minv (a : MtM m) : MtM m := fun i j => (Matrix.of a)⁻¹ i j

def oneM : MtM m := fun i j => (1 : Matrix (Fin m) (Fin m) ℂ) i j

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
lemma mm_oneM (a : MtM m) : mm a oneM = a := by
  funext i j
  show (Matrix.of a * 1 : Matrix (Fin m) (Fin m) ℂ) i j = a i j
  rw [Matrix.mul_one]
  rfl

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. A detailed English derivation is pending.
-/
lemma mm_assoc (a b c : MtM m) : mm (mm a b) c = mm a (mm b c) := by
  change (Matrix.of a * Matrix.of b * Matrix.of c : Matrix (Fin m) (Fin m) ℂ) =
    Matrix.of a * (Matrix.of b * Matrix.of c)
  exact Matrix.mul_assoc _ _ _

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma inv_mul_of {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G) {a : Matrix (Fin m) (Fin m) ℂ}
    (ha : a ∈ G) : a⁻¹ * a = 1 :=
  mul_eq_one_comm.mp (hG.2.2.2 a ha).2

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
lemma measurableSet_mem {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G) :
    MeasurableSet {x : MtM m | Matrix.of x ∈ G} := by
  have hc : Continuous (fun x : MtM m => (Matrix.of x : Matrix (Fin m) (Fin m) ℂ)) := continuous_id
  exact (hG.1.preimage hc).measurableSet

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma mm_mem {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G) {a b : MtM m}
    (ha : Matrix.of a ∈ G) (hb : Matrix.of b ∈ G) : Matrix.of (mm a b) ∈ G :=
  hG.2.2.1 _ ha _ hb

section HidaSetting

variable {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
lemma ae_mem_S (h : QuotientSetting G S μG μS ν) : ∀ᵐ s ∂μS, Matrix.of s ∈ S := by
  have := h.2.2.2.2.1.2.2.1
  rw [ae_iff]
  simpa using this

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma weil (h : QuotientSetting G S μG μS ν) {f : MtM m → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (mm s x) ∂μS) ∂ν :=
  h.2.2.2.2.2.2.2 f hf

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
lemma nu_compl (h : QuotientSetting G S μG μS ν) : ν {x | Matrix.of x ∉ G} = 0 := by
  have hG := h.1
  have hS := h.2.1
  have hSG := h.2.2.1
  have hμG := h.2.2.2.1
  have hμS := h.2.2.2.2.1
  set C : Set (MtM m) := {x | Matrix.of x ∉ G} with hC
  have hCm : MeasurableSet C := (measurableSet_mem hG).compl
  have hW := weil h (measurable_one.indicator hCm)
  rw [lintegral_indicator_one hCm, hμG.2.2.1] at hW
  have hle : ∀ x, C.indicator 1 x * μS Set.univ ≤ ∫⁻ s, C.indicator 1 (mm s x) ∂μS := by
    intro x
    by_cases hx : x ∈ C
    · have hae : ∀ᵐ s ∂μS, C.indicator (1 : MtM m → ℝ≥0∞) (mm s x) = 1 := by
        filter_upwards [ae_mem_S h] with s hs
        have : mm s x ∈ C := by
          intro hsx
          apply hx
          have h1 : (Matrix.of s)⁻¹ * (Matrix.of s * Matrix.of x) ∈ G :=
            hG.2.2.1 _ (hSG (hS.2.2.2 _ hs).1) _ hsx
          rwa [← Matrix.mul_assoc, inv_mul_of hS hs, Matrix.one_mul] at h1
        simp [Set.indicator_of_mem this]
      rw [lintegral_congr_ae hae]
      simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have h2 : ∫⁻ x, C.indicator 1 x * μS Set.univ ∂ν = 0 :=
    nonpos_iff_eq_zero.mp ((lintegral_mono hle).trans hW.symm.le)
  rw [lintegral_mul_const _ (measurable_one.indicator hCm), lintegral_indicator_one hCm,
    mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact h2
  · exact absurd (Measure.measure_univ_eq_zero.mp h2) hμS.2.1

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
lemma ae_mem_G (h : QuotientSetting G S μG μS ν) : ∀ᵐ x ∂ν, Matrix.of x ∈ G := by
  rw [ae_iff]
  simpa using nu_compl h

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma weil_inv (h : QuotientSetting G S μG μS ν) {H f : MtM m → ℝ≥0∞} (hH : Measurable H)
    (hf : Measurable f) (hHi : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → H (mm s x) = H x) :
    ∫⁻ x, H x * f x ∂μG = ∫⁻ x, H x * (∫⁻ s, f (mm s x) ∂μS) ∂ν := by
  have hW := weil h (hH.mul hf)
  simp only [Pi.mul_apply] at hW
  rw [hW]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_G h] with x hx
  rw [← lintegral_const_mul (H x) (f := fun s => f (mm s x)) (hf.comp (measurable_mm_left x))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_S h] with s hs
  rw [show H (mm s x) = H x from hHi _ hs x hx]

end HidaSetting

end PI.QuotInvW
