import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.CptSobProof

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Van {V : Type} [Zero V] (R : ℝ) (f : Mat n → V) : Prop := ∀ y ∈ GLs n, R < lg y → f y = 0

/- English proof (translation)
Establish `h : Continuous (fun g : Mat n => g.det)` using `Continuous.matrix_det continuous_id`. Conclude with `isOpen_ne.preimage h`.
-/
theorem isOpen_GLs : IsOpen (GLs n) := by
  have h : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage h

/- English proof (translation)
The claim follows from `((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero`.
-/
theorem val_mem_GLs (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

/- English proof (translation)
Establish `h` using `hlg.isOpen_inter_preimage isOpen_GLs (isOpen_Ioi (a := R))`. Conclude with `h`.
-/
theorem isOpen_far (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (R : ℝ) :
    IsOpen {y : Mat n | y ∈ GLs n ∧ R < lg y} := by
  have h := hlg.isOpen_inter_preimage isOpen_GLs (isOpen_Ioi (a := R))
  exact h

section Vanish

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {R : ℝ} {f : Mat n → V}

/- English proof (translation)
Introduce `y hy hR`. Establish `he : f =ᶠ[𝓝 y] fun _ => (0 : V)` using `by filter_upwards [(isOpen_far hlg R).mem_nhds ⟨hy, hR⟩] with z hz using h z hz.1 hz.2`. Simplify using `[Rd, he.fderiv_eq]`.
-/
theorem Van.rd (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (X : Mat n) : Van R (Rd X f) := by
  intro y hy hR
  have he : f =ᶠ[𝓝 y] fun _ => (0 : V) := by
    filter_upwards [(isOpen_far hlg R).mem_nhds ⟨hy, hR⟩] with z hz using h z hz.1 hz.2
  simp [Rd, he.fderiv_eq]

/- English proof (translation)
Introduce `y hy hR`. Establish `h1` using `h.rd hlg (Matrix.single a b 1) y hy hR`. Establish `h2` using `h.rd hlg (Matrix.single a b Complex.I) y hy hR`. Apply the tactic sequence `cases s <;> simp [Eu, h1, h2]`.
-/
theorem Van.eu (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (s : Bool) (a b : Fin n) :
    Van R (Eu s a b f) := by
  intro y hy hR
  have h1 := h.rd hlg (Matrix.single a b 1) y hy hR
  have h2 := h.rd hlg (Matrix.single a b Complex.I) y hy hR
  cases s <;> simp [Eu, h1, h2]

/- English proof (translation)
Proceed by induction on `m generalizing a b with`. Consider the case `zero`. Introduce `y hy hR`. Distinguish the cases in `hab : a = b`. Simplify using `[Epow, hab, h y hy hR]`.

Simplify using `[Epow, hab]`. Consider the case `succ m ih`. Introduce `y hy hR`. Simplify using `only [Epow, Finset.sum_apply]`. Conclude with `Finset.sum_eq_zero fun c _ => (ih c b).eu hlg s a c y hy hR`.
-/
theorem Van.epow (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (s : Bool) (m : ℕ) (a b : Fin n) :
    Van R (Epow s m a b f) := by
  induction m generalizing a b with
  | zero =>
    intro y hy hR
    by_cases hab : a = b
    · simp [Epow, hab, h y hy hR]
    · simp [Epow, hab]
  | succ m ih =>
    intro y hy hR
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_eq_zero fun c _ => (ih c b).eu hlg s a c y hy hR

/- English proof (translation)
Introduce `y hy hR`. Simplify using `only [PositivityTheory.RgBcC.gel, Finset.sum_apply]`. Conclude with `Finset.sum_eq_zero fun a _ => h.epow hlg s m a a y hy hR`.
-/
theorem Van.gel (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (s : Bool) (m : ℕ) :
    Van R (gel s m f) := by
  intro y hy hR
  simp only [PositivityTheory.RgBcC.gel, Finset.sum_apply]
  exact Finset.sum_eq_zero fun a _ => h.epow hlg s m a a y hy hR

/- English proof (translation)
Introduce `y hy hR`. Establish `h1` using `h.gel hlg true 2 y hy hR`. Establish `h2` using `h.gel hlg false 2 y hy hR`. Simplify using `[Om, h1, h2]`.
-/
theorem Van.om (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) : Van R (Om f) := by
  intro y hy hR
  have h1 := h.gel hlg true 2 y hy hR
  have h2 := h.gel hlg false 2 y hy hR
  simp [Om, h1, h2]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact h`. Consider the case `cons p w ih => exact ih.rd hlg (bs p)`.
-/
theorem Van.rw (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (w : List (Bool × Fin n × Fin n)) :
    Van R (Rw w f) := by
  induction w with
  | nil => exact h
  | cons p w ih => exact ih.rd hlg (bs p)

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact hf`. Consider the case `cons p w ih => exact ((hC n).1 V _ ih).1 (bs p)`.
-/
theorem rw_smooth (hC : RCalc) (hf : ContDiffOn ℝ ∞ f (GLs n)) (w : List (Bool × Fin n × Fin n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact ((hC n).1 V _ ih).1 (bs p)

end Vanish

/- English proof (translation)
Establish `hcont : Continuous (fun y : G n => g y.val)` using `hc.comp_continuous Units.continuous_val val_mem_GLs`. Establish `hsupp : HasCompactSupport (fun y : G n => g y.val)` using `HasCompactSupport.intro hK fun y hy => hv y.val (val_mem_GLs y) (not_le.1 hy)`. Conclude with `hcont.memLp_of_hasCompactSupport hsupp`.
-/
theorem memLp_of_van [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {R : ℝ} {g : Mat n → V}
    (hK : IsCompact {y : G n | lg y.val ≤ R}) (hc : ContinuousOn g (GLs n)) (hv : Van R g) :
    MemLp (fun y : G n => g y.val) 2 μ := by
  have hcont : Continuous (fun y : G n => g y.val) :=
    hc.comp_continuous Units.continuous_val val_mem_GLs
  have hsupp : HasCompactSupport (fun y : G n => g y.val) :=
    HasCompactSupport.intro hK fun y hy => hv y.val (val_mem_GLs y) (not_le.1 hy)
  exact hcont.memLp_of_hasCompactSupport hsupp

/- English proof (translation)
Introduce `n _ _ μ _ V _ _ hL hC f hf hcpt`. Take `⟨-, -, -, hs, hk, -⟩` from `hL n`. Take `⟨R, hR⟩` from `hcpt`. Establish `hv : Van R f` using `hR`. Conclude with `⟨⟨hf, fun w => memLp_of_van μ (hk R) (rw_smooth hC hf w).continuousOn (hv.rw hs.continuousOn w)⟩, R, hv.om hs.continuousOn⟩`.
-/
theorem cptSob : CptSob := by
  intro n _ _ μ _ V _ _ hL hC f hf hcpt
  obtain ⟨-, -, -, hs, hk, -⟩ := hL n
  obtain ⟨R, hR⟩ := hcpt
  have hv : Van R f := hR
  exact ⟨⟨hf, fun w => memLp_of_van μ (hk R) (rw_smooth hC hf w).continuousOn (hv.rw hs.continuousOn w)⟩,
    R, hv.om hs.continuousOn⟩

end GlobalTheory.CompanionTheory.CptSobProof
