import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConst
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.Jac

open Formalism.QuantumDeterminants

variable {k r : ℕ}

abbrev N1 (k r : ℕ) : Measure (Mt k r) := Formalism.MainNotions.S.haarLie (Nset k r) 1

/- English proof (translation)
Simplify using `[Formalism.MainNotions.S.haarLie]`.
-/
theorem haarLie_eq_smul (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (κ : ℝ≥0∞) :
    Formalism.MainNotions.S.haarLie S κ = κ • Formalism.MainNotions.S.haarLie S 1 := by
  simp [Formalism.MainNotions.S.haarLie]

/- English proof (translation)
The claim follows from `Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top`.
-/
theorem nilradical_measure_is_haar : Formalism.MainNotions.S.IsHaarOn (Nset k r) (N1 k r) :=
  Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top

instance sigmaFiniteNilradicalHaar : SigmaFinite (N1 k r) := (nilradical_measure_is_haar (k := k) (r := r)).1

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z (N1 k r) hz hT (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 k r _ nilradical_measure_is_haar) h hh`.
-/
theorem nilradical_measure_conj_invariant {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : (N1 k r).map (conjM h) = N1 k r :=
  Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z (N1 k r) hz hT (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 k r _ nilradical_measure_is_haar) h hh

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`. Conclude with `continuous_finsetSum _ fun l _ => by fun_prop`.
-/
theorem continuous_matrix_mul_pair : Continuous fun p : Mt k r × Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Mt k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finsetSum _ fun l _ => by fun_prop

/- English proof (translation)
The claim follows from `continuous_matrix_mul_pair.measurable`.
-/
theorem measurable_mt_mul : Measurable fun p : Mt k r × Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Mt k r) :=
  continuous_matrix_mul_pair.measurable

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.B7.measurable_invM`.
-/
theorem meas_inv : Measurable fun x : Mt k r => (fun i j => ((Matrix.of x)⁻¹) i j : Mt k r) :=
  Formalism.FourierDecayAlt.P.B7.measurable_invM

/- English proof (translation)
The claim follows from `measurable_mt_mul.comp (hf.prodMk hg)`.
-/
theorem mulMt_meas {α : Type*} [MeasurableSpace α] {f g : α → Mt k r} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => (fun i j => (Matrix.of (f a) * Matrix.of (g a)) i j : Mt k r) :=
  measurable_mt_mul.comp (hf.prodMk hg)

/- English proof (translation)
The claim follows from `meas_inv.comp hf`.
-/
theorem invMt_meas {α : Type*} [MeasurableSpace α] {f : α → Mt k r} (hf : Measurable f) :
    Measurable fun a => (fun i j => ((Matrix.of (f a))⁻¹) i j : Mt k r) :=
  meas_inv.comp hf

/- English proof (translation)
Establish `e : conjM (k` using `k) (r := r) h = fun x => (fun i j => (Matrix.of (fun i j => (Matrix.of (h : Mt k r) * Matrix.of x) i j : Mt k r) * Matrix.of ((h⁻¹ : Matrix _ _ ℂ) : Mt k r)) i j : Mt k r) := by`. Use function extensionality and compare the values at `x`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `mulMt_meas (mulMt_meas measurable_const measurable_id) measurable_const`.
-/
theorem meas_conjM (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Measurable (conjM (k := k) (r := r) h) := by
  have e : conjM (k := k) (r := r) h = fun x =>
      (fun i j => (Matrix.of (fun i j => (Matrix.of (h : Mt k r) * Matrix.of x) i j : Mt k r) *
        Matrix.of ((h⁻¹ : Matrix _ _ ℂ) : Mt k r)) i j : Mt k r) := by
    funext x; rfl
  rw [e]
  exact mulMt_meas (mulMt_meas measurable_const measurable_id) measurable_const

/- English proof (translation)
Establish `e : (fun p : (Mt k r × Mt k r) × Mt k r => (fun i j => (Matrix.of p.1.1 * x * Matrix.of p.1.2 * (Matrix.of p.2)⁻¹) i j : Mt k r)) = fun p => (fun i j => (Matrix.of (fun i j => (Matrix.of (fun i j => (Matrix.of p.1.1 * Matrix.of (x : Mt k r)) i j : Mt k r) * Matrix.of p.1.2) i j : …`. Use function extensionality and compare the values at `p`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `mulMt_meas (mulMt_meas (mulMt_meas (measurable_fst.comp measurable_fst) measurable_const) (measurable_snd.comp measurable_fst)) (invMt_meas measurable_snd)`.
-/
theorem meas_nxmn (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable fun p : (Mt k r × Mt k r) × Mt k r =>
      (fun i j => (Matrix.of p.1.1 * x * Matrix.of p.1.2 * (Matrix.of p.2)⁻¹) i j : Mt k r) := by
  have e : (fun p : (Mt k r × Mt k r) × Mt k r =>
      (fun i j => (Matrix.of p.1.1 * x * Matrix.of p.1.2 * (Matrix.of p.2)⁻¹) i j : Mt k r)) = fun p =>
      (fun i j => (Matrix.of (fun i j => (Matrix.of (fun i j => (Matrix.of p.1.1 * Matrix.of (x : Mt k r)) i j : Mt k r) *
        Matrix.of p.1.2) i j : Mt k r) * Matrix.of (fun i j => ((Matrix.of p.2)⁻¹) i j : Mt k r)) i j : Mt k r) := by
    funext p; rfl
  rw [e]
  exact mulMt_meas (mulMt_meas (mulMt_meas (measurable_fst.comp measurable_fst) measurable_const)
    (measurable_snd.comp measurable_fst)) (invMt_meas measurable_snd)

/- English proof (translation)
Establish `e : (fun p : ((((Mt k r × Mt k r) × Mt k r) × Mt k r) × Mt k r) => (fun i j => (Matrix.of p.1.1.1.2 * Matrix.of p.1.2 * Matrix.of p.1.1.1.1 * (Matrix.of p.1.1.2 * Matrix.of p.2)⁻¹) i j : Mt k r)) = fun p => (fun i j => (Matrix.of (fun i j => (Matrix.of (fun i j => (Matrix.of p.1. …`. Use function extensionality and compare the values at `p`. Both sides reduce to the same expression. Rewrite using `[e]`. Apply the tactic sequence `refine mulMt_meas (mulMt_meas (mulMt_meas ?_ ?_) ?_) (invMt_meas (mulMt_meas ?_ ?_)) <;> fun_prop`.
-/
theorem meas_hnxhn :
    Measurable fun p : ((((Mt k r × Mt k r) × Mt k r) × Mt k r) × Mt k r) =>
      (fun i j => (Matrix.of p.1.1.1.2 * Matrix.of p.1.2 * Matrix.of p.1.1.1.1 *
        (Matrix.of p.1.1.2 * Matrix.of p.2)⁻¹) i j : Mt k r) := by
  have e : (fun p : ((((Mt k r × Mt k r) × Mt k r) × Mt k r) × Mt k r) =>
      (fun i j => (Matrix.of p.1.1.1.2 * Matrix.of p.1.2 * Matrix.of p.1.1.1.1 *
        (Matrix.of p.1.1.2 * Matrix.of p.2)⁻¹) i j : Mt k r)) = fun p =>
      (fun i j => (Matrix.of (fun i j => (Matrix.of (fun i j => (Matrix.of p.1.1.1.2 * Matrix.of p.1.2) i j : Mt k r) *
        Matrix.of p.1.1.1.1) i j : Mt k r) *
        Matrix.of (fun i j => ((Matrix.of (fun i j => (Matrix.of p.1.1.2 * Matrix.of p.2) i j : Mt k r))⁻¹) i j : Mt k r))
        i j : Mt k r) := by
    funext p; rfl
  rw [e]
  refine mulMt_meas (mulMt_meas (mulMt_meas ?_ ?_) ?_) (invMt_meas (mulMt_meas ?_ ?_)) <;> fun_prop

/- English proof (translation)
Use `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Unfold `bigCell`. Apply the tactic sequence `split_ifs <;> fun_prop`.
-/
theorem meas_bigCell :
    Measurable fun p : (Fin r → ℂ) × (Fin (k + 1) → Fin (k + 1) → ℂ) =>
      (fun i j => bigCell k r p.1 (Matrix.of p.2) i j : Mt k r) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  unfold bigCell
  split_ifs <;> fun_prop

def Jint (φ : Mt k r → ℝ≥0∞) (μW μW' : Measure (Mt k r)) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ℝ≥0∞ :=
  ∫⁻ h, ∫⁻ h', ∫⁻ n, ∫⁻ n', φ (fun i j => (Matrix.of h * Matrix.of n * x * (Matrix.of h' * Matrix.of n')⁻¹) i j)
    ∂(N1 k r) ∂(N1 k r) ∂μW' ∂μW

/- English proof (translation)
Establish `h5` using `hφ.comp (meas_hnxhn (k := k) (r := r))`. Establish `h4` using `h5.lintegral_prod_right' (ν := N1 k r)`. Establish `h3` using `h4.lintegral_prod_right' (ν := N1 k r)`. Establish `h2` using `h3.lintegral_prod_right' (ν := μW')`. Establish `h1` using `h2.lintegral_prod_right' (ν := μW)`.

Conclude with `h1`.
-/
theorem meas_Jint {φ : Mt k r → ℝ≥0∞} (hφ : Measurable φ) (μW μW' : Measure (Mt k r)) [SFinite μW] [SFinite μW'] :
    Measurable fun x : Mt k r => Jint φ μW μW' (Matrix.of x) := by
  have h5 := hφ.comp (meas_hnxhn (k := k) (r := r))
  have h4 := h5.lintegral_prod_right' (ν := N1 k r)
  have h3 := h4.lintegral_prod_right' (ν := N1 k r)
  have h2 := h3.lintegral_prod_right' (ν := μW')
  have h1 := h2.lintegral_prod_right' (ν := μW)
  exact h1

def mm (A B : Mt k r) : Mt k r := fun i j => (Matrix.of A * Matrix.of B) i j

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem of_mm (A B : Mt k r) : Matrix.of (mm A B) = Matrix.of A * Matrix.of B := rfl

/- English proof (translation)
Set `P' : α → Mt k r` to `fun a => P a`. Set `Q' : α → Mt k r` to `fun a => Q a`. Establish `hP' : Continuous P'` using `hP`. Establish `hQ' : Continuous Q'` using `hQ`. Conclude with `mulMt_meas hP'.measurable (invMt_meas hQ'.measurable)`.
-/
theorem meas_PQinv {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    (P Q : α → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hP : Continuous P) (hQ : Continuous Q) :
    Measurable fun a => (fun i j => (P a * (Q a)⁻¹) i j : Mt k r) := by
  let P' : α → Mt k r := fun a => P a
  let Q' : α → Mt k r := fun a => Q a
  have hP' : Continuous P' := hP
  have hQ' : Continuous Q' := hQ
  exact mulMt_meas hP'.measurable (invMt_meas hQ'.measurable)

/- English proof (translation)
Establish `hm : Measurable fun p : Mt k r × Mt k r => mm p.1 p.2` using `measurable_mt_mul`. Establish `e : Formalism.MainNotions.S.muS μW μN = (μW.prod μN).map fun p : Mt k r × Mt k r => mm p.1 p.2` using `rfl`. Rewrite using `[e, lintegral_map hf hm]`. Conclude with `lintegral_prod (fun p : Mt k r × Mt k r => f (mm p.1 p.2)) (hf.comp hm).aemeasurable`.
-/
theorem lintegral_muS (μW μN : Measure (Mt k r)) [SFinite μW] [SFinite μN] {f : Mt k r → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ s, f s ∂(Formalism.MainNotions.S.muS μW μN) = ∫⁻ h, ∫⁻ n, f (mm h n) ∂μN ∂μW := by
  have hm : Measurable fun p : Mt k r × Mt k r => mm p.1 p.2 := measurable_mt_mul
  have e : Formalism.MainNotions.S.muS μW μN = (μW.prod μN).map fun p : Mt k r × Mt k r => mm p.1 p.2 := rfl
  rw [e, lintegral_map hf hm]
  exact lintegral_prod (fun p : Mt k r × Mt k r => f (mm p.1 p.2)) (hf.comp hm).aemeasurable

/- English proof (translation)
Establish `e : Formalism.MainNotions.S.muS μW μN = (μW.prod μN).map fun p : Mt k r × Mt k r => mm p.1 p.2` using `rfl`. Rewrite using `[e]`. Use `infer_instance`.
-/
theorem sFinite_muS (μW μN : Measure (Mt k r)) [SFinite μW] [SFinite μN] : SFinite (Formalism.MainNotions.S.muS μW μN) := by
  have e : Formalism.MainNotions.S.muS μW μN = (μW.prod μN).map fun p : Mt k r × Mt k r => mm p.1 p.2 := rfl
  rw [e]; infer_instance

/- English proof (translation)
Rewrite using `[haarLie_eq_smul]`. Use `sFinite_muS μW' (κ • N1 k r)` as an intermediate fact. Establish `hout : Measurable fun s : Mt k r => ∫⁻ s', φ (fun i j => (Matrix.of s * x * (Matrix.of s')⁻¹) i j) ∂(Formalism.MainNotions.S.muS μW' (κ • N1 k r))`. Establish `: Measurable fun q : Mt k r × Mt k r => φ (fun i j => (Matrix.of q.1 * x * (Matrix.of q.2)⁻¹) i j)` using `hφ.comp (meas_PQinv (fun q : Mt k r × Mt k r => Matrix.of q.1 * x) (fun q => Matrix.of q.2) (by fun_prop) (by fun_prop))`. Conclude with `this.lintegral_prod_right'`.

Rewrite using `[lintegral_muS _ _ hout]`. Simplify using `only [of_mm]`. Establish `step1 : ∀ h n : Mt k r, ∫⁻ s', φ (fun i j => (Matrix.of h * Matrix.of n * x * (Matrix.of s')⁻¹) i j) ∂(Formalism.MainNotions.S.muS μW' (κ • N1 k r)) = ∫⁻ h', ∫⁻ n', φ (fun i j => (Matrix.of h * Matrix.of n * x * (Matrix.of h' * Matrix.of n')⁻¹) i j) ∂(κ • N1 k r) ∂μW'`. Introduce `h n`. Establish `hm : Measurable fun s' : Mt k r => φ (fun i j => (Matrix.of h * Matrix.of n * x * (Matrix.of s')⁻¹) i j)` using `hφ.comp (meas_PQinv (fun _ : Mt k r => Matrix.of h * Matrix.of n * x) (fun s' => Matrix.of s') (by fun_prop) (by fun_prop))`.

Rewrite using `[lintegral_muS _ _ hm]`. Simplify using `only [of_mm]`. Repeatedly rewrite using `[step1]`. Establish `step2 : ∀ h : Mt k r, ∫⁻ n, ∫⁻ h', ∫⁻ n', φ (fun i j => (Matrix.of h * Matrix.of n * x * (Matrix.of h' * Matrix.of n')⁻¹) i j) ∂(κ • N1 k r) ∂μW' ∂(κ • N1 k r) = ∫⁻ h', ∫⁻ n, ∫⁻ n', φ (fun i j => (Matrix.of h * Matrix.of n * x * (Matrix.of h' * Matrix.of n')⁻¹) i j) ∂(κ • N1 k r) …`. Introduce `h`.

Use `lintegral_lintegral_swap ?_` and prove the remaining obligations. Establish `: Measurable fun p : (Mt k r × Mt k r) × Mt k r => φ (fun i j => (Matrix.of h * Matrix.of p.1.1 * x * (Matrix.of p.1.2 * Matrix.of p.2)⁻¹) i j)` using `hφ.comp (meas_PQinv (fun p : (Mt k r × Mt k r) × Mt k r => Matrix.of h * Matrix.of p.1.1 * x) (fun p => Matrix.of p.1.2 * Matrix.of p.2) (by fun_prop) (by fun_prop))`. Conclude with `(this.lintegral_prod_right' (ν := κ • N1 k r)).aemeasurable`. Repeatedly rewrite using `[step2, lintegral_smul_measure, smul_eq_mul, lintegral_const_mul' _ _ hκ]`. Unfold `Jint`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem rhs_eq {φ : Mt k r → ℝ≥0∞} (hφ : Measurable φ) (μW μW' : Measure (Mt k r)) [SFinite μW] [SFinite μW']
    {κ : ℝ≥0∞} (hκ : κ ≠ ⊤) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ∫⁻ s, ∫⁻ s', φ (fun i j => (Matrix.of s * x * (Matrix.of s')⁻¹) i j)
      ∂(Formalism.MainNotions.S.muS μW' (Formalism.MainNotions.S.haarLie (Nset k r) κ)) ∂(Formalism.MainNotions.S.muS μW (Formalism.MainNotions.S.haarLie (Nset k r) κ))
    = κ * κ * Jint φ μW μW' x := by
  rw [haarLie_eq_smul]
  have := sFinite_muS μW' (κ • N1 k r)
  have hout : Measurable fun s : Mt k r => ∫⁻ s', φ (fun i j => (Matrix.of s * x * (Matrix.of s')⁻¹) i j)
      ∂(Formalism.MainNotions.S.muS μW' (κ • N1 k r)) := by
    have : Measurable fun q : Mt k r × Mt k r => φ (fun i j => (Matrix.of q.1 * x * (Matrix.of q.2)⁻¹) i j) :=
      hφ.comp (meas_PQinv (fun q : Mt k r × Mt k r => Matrix.of q.1 * x) (fun q => Matrix.of q.2) (by fun_prop) (by fun_prop))
    exact this.lintegral_prod_right'
  rw [lintegral_muS _ _ hout]
  simp only [of_mm]
  have step1 : ∀ h n : Mt k r, ∫⁻ s', φ (fun i j => (Matrix.of h * Matrix.of n * x * (Matrix.of s')⁻¹) i j)
      ∂(Formalism.MainNotions.S.muS μW' (κ • N1 k r)) =
      ∫⁻ h', ∫⁻ n', φ (fun i j => (Matrix.of h * Matrix.of n * x * (Matrix.of h' * Matrix.of n')⁻¹) i j)
        ∂(κ • N1 k r) ∂μW' := by
    intro h n
    have hm : Measurable fun s' : Mt k r => φ (fun i j => (Matrix.of h * Matrix.of n * x * (Matrix.of s')⁻¹) i j) :=
      hφ.comp (meas_PQinv (fun _ : Mt k r => Matrix.of h * Matrix.of n * x) (fun s' => Matrix.of s') (by fun_prop)
        (by fun_prop))
    rw [lintegral_muS _ _ hm]
    simp only [of_mm]
  simp_rw [step1]
  have step2 : ∀ h : Mt k r, ∫⁻ n, ∫⁻ h', ∫⁻ n', φ (fun i j => (Matrix.of h * Matrix.of n * x *
      (Matrix.of h' * Matrix.of n')⁻¹) i j) ∂(κ • N1 k r) ∂μW' ∂(κ • N1 k r) =
      ∫⁻ h', ∫⁻ n, ∫⁻ n', φ (fun i j => (Matrix.of h * Matrix.of n * x *
      (Matrix.of h' * Matrix.of n')⁻¹) i j) ∂(κ • N1 k r) ∂(κ • N1 k r) ∂μW' := by
    intro h
    refine lintegral_lintegral_swap ?_
    have : Measurable fun p : (Mt k r × Mt k r) × Mt k r =>
        φ (fun i j => (Matrix.of h * Matrix.of p.1.1 * x * (Matrix.of p.1.2 * Matrix.of p.2)⁻¹) i j) :=
      hφ.comp (meas_PQinv (fun p : (Mt k r × Mt k r) × Mt k r => Matrix.of h * Matrix.of p.1.1 * x)
        (fun p => Matrix.of p.1.2 * Matrix.of p.2) (by fun_prop) (by fun_prop))
    exact (this.lintegral_prod_right' (ν := κ • N1 k r)).aemeasurable
  simp_rw [step2, lintegral_smul_measure, smul_eq_mul, lintegral_const_mul' _ _ hκ]
  unfold Jint
  ring

/- English proof (translation)
Establish `h1 : Matrix.det (Matrix.conjTranspose H * Hpk k r * H) = Matrix.det (Hpk k r)` using `congrArg Matrix.det hH`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul]`. Establish `hp` using `(Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r).ne_zero`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`.

Rewrite `h1` using `[h0, mul_zero]`. Conclude with `hp h1.symm`.
-/
theorem unit_of_UH {H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hH : H ∈ UH (Hpk k r)) :
    IsUnit H.det := by
  have h1 : Matrix.det (Matrix.conjTranspose H * Hpk k r * H) = Matrix.det (Hpk k r) := congrArg Matrix.det hH
  rw [Matrix.det_mul, Matrix.det_mul] at h1
  have hp := (Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r).ne_zero
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h1
  exact hp h1.symm

/- English proof (translation)
Use `conv_lhs => rw [← nilradical_measure_conj_invariant hz hT hH]`. Rewrite using `[lintegral_map hG (meas_conjM H)]`.
-/
theorem conj_int {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hH : H ∈ UWset k r z) {G : Mt k r → ℝ≥0∞}
    (hG : Measurable G) : ∫⁻ n, G n ∂(N1 k r) = ∫⁻ n, G (conjM H n) ∂(N1 k r) := by
  conv_lhs => rw [← nilradical_measure_conj_invariant hz hT hH]
  rw [lintegral_map hG (meas_conjM H)]

/- English proof (translation)
Establish `hi : H⁻¹ * H = 1` using `Matrix.nonsing_inv_mul H hd`. Establish `hi' : H'⁻¹ * H' = 1` using `Matrix.nonsing_inv_mul H' hd'`. Simplify using `only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv H' hd', mul_assoc]`. Rewrite using `[← mul_assoc X H, hc, mul_assoc H X, ← mul_assoc H⁻¹ H, hi, one_mul, ← mul_assoc H'⁻¹ H', hi', one_mul]`.
-/
theorem mat_id (H H' N N' X E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hd : IsUnit H.det)
    (hd' : IsUnit H'.det) (hc : X * H = H * X) :
    H * N * H⁻¹ * X * (H * E * H'⁻¹) * (H' * N' * H'⁻¹)⁻¹ = H * N * (X * E) * (H' * N')⁻¹ := by
  have hi : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hd
  have hi' : H'⁻¹ * H' = 1 := Matrix.nonsing_inv_mul H' hd'
  simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv H' hd', mul_assoc]
  rw [← mul_assoc X H, hc, mul_assoc H X, ← mul_assoc H⁻¹ H, hi, one_mul, ← mul_assoc H'⁻¹ H', hi', one_mul]

/- English proof (translation)
Establish `hd` using `unit_of_UH hH.1`. Establish `hd'` using `unit_of_UH hH'.1`. Establish `hc : bigCell k r c 1 * H = H * bigCell k r c 1` using `((Formalism.FourierDecayAlt.P.unipotent_weyl_properties k r).2.2 c H ((Formalism.FourierDecayAlt.P.unipotent_weyl_properties k r).2.1 z hH)).symm`. Establish `hbig : bigCell k r c M = bigCell k r c 1 * Formalism.FourierDecayAlt.B2.embWb k r M` using `(Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c M).1`. Establish `hG : Measurable fun n : Mt k r => ∫⁻ n', φ (fun i j => (Matrix.of n * bigCell k r c 1 * (H * Formalism.FourierDecayAlt.B2.embWb k r M * H'⁻¹) * (Matrix.of n')⁻¹) i j) ∂(N1 k r)`.

Establish `: Measurable fun p : Mt k r × Mt k r => φ (fun i j => (Matrix.of p.1 * bigCell k r c 1 * (H * Formalism.FourierDecayAlt.B2.embWb k r M * H'⁻¹) * (Matrix.of p.2)⁻¹) i j)` using `hφ.comp (meas_PQinv (fun p : Mt k r × Mt k r => Matrix.of p.1 * bigCell k r c 1 * (H * Formalism.FourierDecayAlt.B2.embWb k r M * H'⁻¹)) (fun p => Matrix.of p.2) (by fun_prop) (by fun_prop))`. Conclude with `this.lintegral_prod_right'`. Rewrite using `[conj_int hz hT hH hG]`. Use `lintegral_congr fun n => ?_` and prove the remaining obligations. Establish `hG' : Measurable fun n' : Mt k r => φ (fun i j => (Matrix.of (conjM H n) * bigCell k r c 1 * (H * Formalism.FourierDecayAlt.B2.embWb k r M * H'⁻¹) * (Matrix.of n')⁻¹) i j)` using `hφ.comp (meas_PQinv (fun _ : Mt k r => Matrix.of (conjM H n) * bigCell k r c 1 * (H * Formalism.FourierDecayAlt.B2.embWb k r M * H'⁻¹)) (fun n' => Matrix.of n') (by fun_prop) (by fun_prop))`.

Rewrite using `[conj_int hz' hT' hH' hG']`. Use `lintegral_congr fun n' => ?_` and prove the remaining obligations. Establish `e : Matrix.of (conjM H n) * bigCell k r c 1 * (H * Formalism.FourierDecayAlt.B2.embWb k r M * H'⁻¹) * (Matrix.of (conjM H' n'))⁻¹ = H * Matrix.of n * bigCell k r c M * (H' * Matrix.of n')⁻¹`. Rewrite using `[hbig]`. Conclude with `mat_id H H' (Matrix.of n) (Matrix.of n') (bigCell k r c 1) (Formalism.FourierDecayAlt.B2.embWb k r M) hd hd' hc`.

Simplify using `only [e]`.
-/
theorem psi_conj {φ : Mt k r → ℝ≥0∞} (hφ : Measurable φ) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (hT : 0 < Tz k r z) (hz' : inWb k r z') (hT' : 0 < Tz k r z') {H H' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hH : H ∈ UWset k r z) (hH' : H' ∈ UWset k r z') (c : Fin r → ℂ) (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    ∫⁻ n, ∫⁻ n', φ (fun i j => (Matrix.of n * bigCell k r c 1 * (H * Formalism.FourierDecayAlt.B2.embWb k r M * H'⁻¹) *
      (Matrix.of n')⁻¹) i j) ∂(N1 k r) ∂(N1 k r) =
    ∫⁻ n, ∫⁻ n', φ (fun i j => (H * Matrix.of n * bigCell k r c M * (H' * Matrix.of n')⁻¹) i j) ∂(N1 k r) ∂(N1 k r) := by
  have hd := unit_of_UH hH.1
  have hd' := unit_of_UH hH'.1
  have hc : bigCell k r c 1 * H = H * bigCell k r c 1 :=
    ((Formalism.FourierDecayAlt.P.unipotent_weyl_properties k r).2.2 c H ((Formalism.FourierDecayAlt.P.unipotent_weyl_properties k r).2.1 z hH)).symm
  have hbig : bigCell k r c M = bigCell k r c 1 * Formalism.FourierDecayAlt.B2.embWb k r M :=
    (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c M).1
  have hG : Measurable fun n : Mt k r => ∫⁻ n', φ (fun i j => (Matrix.of n * bigCell k r c 1 *
      (H * Formalism.FourierDecayAlt.B2.embWb k r M * H'⁻¹) * (Matrix.of n')⁻¹) i j) ∂(N1 k r) := by
    have : Measurable fun p : Mt k r × Mt k r => φ (fun i j => (Matrix.of p.1 * bigCell k r c 1 *
        (H * Formalism.FourierDecayAlt.B2.embWb k r M * H'⁻¹) * (Matrix.of p.2)⁻¹) i j) :=
      hφ.comp (meas_PQinv (fun p : Mt k r × Mt k r => Matrix.of p.1 * bigCell k r c 1 *
        (H * Formalism.FourierDecayAlt.B2.embWb k r M * H'⁻¹)) (fun p => Matrix.of p.2) (by fun_prop) (by fun_prop))
    exact this.lintegral_prod_right'
  rw [conj_int hz hT hH hG]
  refine lintegral_congr fun n => ?_
  have hG' : Measurable fun n' : Mt k r => φ (fun i j => (Matrix.of (conjM H n) * bigCell k r c 1 *
      (H * Formalism.FourierDecayAlt.B2.embWb k r M * H'⁻¹) * (Matrix.of n')⁻¹) i j) :=
    hφ.comp (meas_PQinv (fun _ : Mt k r => Matrix.of (conjM H n) * bigCell k r c 1 *
        (H * Formalism.FourierDecayAlt.B2.embWb k r M * H'⁻¹)) (fun n' => Matrix.of n') (by fun_prop) (by fun_prop))
  rw [conj_int hz' hT' hH' hG']
  refine lintegral_congr fun n' => ?_
  have e : Matrix.of (conjM H n) * bigCell k r c 1 * (H * Formalism.FourierDecayAlt.B2.embWb k r M * H'⁻¹) *
      (Matrix.of (conjM H' n'))⁻¹ = H * Matrix.of n * bigCell k r c M * (H' * Matrix.of n')⁻¹ := by
    rw [hbig]
    exact mat_id H H' (Matrix.of n) (Matrix.of n') (bigCell k r c 1) (Formalism.FourierDecayAlt.B2.embWb k r M) hd hd' hc
  simp only [e]

/- English proof (translation)
The claim follows from `ae_iff.2 h.2.2.1`.
-/
theorem ae_memS {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)} {μ : Measure (Mt k r)}
    (h : Formalism.MainNotions.S.IsHaarOn S μ) : ∀ᵐ x ∂μ, Matrix.of x ∈ S := ae_iff.2 h.2.2.1

/- English proof (translation)
Unfold `Jint`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_memS hW] with h hh`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_memS hW'] with h' hh'`.

Conclude with `psi_conj hφ hz hT hz' hT' hh hh' c M`.
-/
theorem hh_psi {φ : Mt k r → ℝ≥0∞} (hφ : Measurable φ) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (hT : 0 < Tz k r z) (hz' : inWb k r z') (hT' : 0 < Tz k r z') {μW μW' : Measure (Mt k r)}
    (hW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) (hW' : Formalism.MainNotions.S.IsHaarOn (UWset k r z') μW') (c : Fin r → ℂ)
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    ∫⁻ h, ∫⁻ h', ∫⁻ n, ∫⁻ n', φ (fun i j => (Matrix.of n * bigCell k r c 1 *
      (Matrix.of h * Formalism.FourierDecayAlt.B2.embWb k r M * (Matrix.of h')⁻¹) * (Matrix.of n')⁻¹) i j) ∂(N1 k r) ∂(N1 k r) ∂μW' ∂μW =
    Jint φ μW μW' (bigCell k r c M) := by
  unfold Jint
  refine lintegral_congr_ae ?_
  filter_upwards [ae_memS hW] with h hh
  refine lintegral_congr_ae ?_
  filter_upwards [ae_memS hW'] with h' hh'
  exact psi_conj hφ hz hT hz' hT' hh hh' c M

/- English proof (translation)
Unfold `Formalism.MainNotions.S.UnitaryVolumeMass.volU`. Conclude with `Finset.prod_pos fun i _ => div_pos (pow_pos (by positivity) _) (Nat.cast_pos.2 (Nat.factorial_pos i))`.
-/
theorem volU_pos (j : ℕ) : 0 < Formalism.MainNotions.S.UnitaryVolumeMass.volU j := by
  unfold Formalism.MainNotions.S.UnitaryVolumeMass.volU
  exact Finset.prod_pos fun i _ => div_pos (pow_pos (by positivity) _) (Nat.cast_pos.2 (Nat.factorial_pos i))

/- English proof (translation)
Unfold `Formalism.FourierDecayAlt.B2.cWeight`. Check the signs of the components of the expression.
-/
theorem cWeight_nonneg (c : Fin r → ℂ) : 0 ≤ Formalism.FourierDecayAlt.B2.cWeight k r c := by
  unfold Formalism.FourierDecayAlt.B2.cWeight; positivity

/- English proof (translation)
Unfold `Formalism.FourierDecayAlt.B2.zWeight`. Use `split_ifs with h`. Conclude with `pow_nonneg (sub_nonneg.2 h) _`. Conclude with `le_refl 0`.
-/
theorem zWeight_nonneg (T T' : ℝ) (ζ : ℂ) : 0 ≤ Formalism.FourierDecayAlt.B2.zWeight k T T' ζ := by
  unfold Formalism.FourierDecayAlt.B2.zWeight
  split_ifs with h
  · exact pow_nonneg (sub_nonneg.2 h) _
  · exact le_refl 0

/- English proof (translation)
Establish `hV` using `volU_pos (k - 1)`. Unfold `wbConst jacConst`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem const_eq {T T' a a' κ : ℝ} (hT : 0 < T) (hT' : 0 < T') (ha : 0 < a) (ha' : 0 < a') (hκ : 0 < κ) :
    2 ^ r * wbConst k T T' a a' = jacConst k r T T' a a' κ * (κ * κ) := by
  have hV := volU_pos (k - 1)
  unfold wbConst jacConst
  field_simp
  ring

/- English proof (translation)
Establish `hV` using `volU_pos (k - 1)`. Unfold `jacConst`. Check the signs of the components of the expression.
-/
theorem jacConst_nonneg {T T' a a' κ : ℝ} (hT : 0 < T) (hT' : 0 < T') (ha : 0 < a) (ha' : 0 < a') (hκ : 0 < κ) :
    0 ≤ jacConst k r T T' a a' κ := by
  have hV := volU_pos (k - 1)
  unfold jacConst; positivity

/- English proof (translation)
Establish `hV` using `volU_pos (k - 1)`. Unfold `wbConst`. Check the signs of the components of the expression.
-/
theorem wbConst_nonneg {T T' a a' : ℝ} (hT : 0 < T) (hT' : 0 < T') (ha : 0 < a) (ha' : 0 < a') :
    0 ≤ wbConst k T T' a a' := by
  have hV := volU_pos (k - 1)
  unfold wbConst; positivity

/- English proof (translation)
Establish `e : {ζ : ℂ | Complex.normSq ζ = t} = Metric.sphere 0 (Real.sqrt t)`. Use extensionality with `ζ`. Simplify using `only [Set.mem_setOf_eq, mem_sphere_iff_norm, sub_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite using `[← h, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]`. Introduce `h`. Rewrite using `[Complex.normSq_eq_norm_sq, h, Real.sq_sqrt ht]`. Rewrite using `[e]`. Conclude with `Measure.addHaar_sphere volume 0 _`.
-/
theorem sphere_null (t : ℝ) (ht : 0 ≤ t) : (volume : Measure ℂ) {ζ | Complex.normSq ζ = t} = 0 := by
  have e : {ζ : ℂ | Complex.normSq ζ = t} = Metric.sphere 0 (Real.sqrt t) := by
    ext ζ
    simp only [Set.mem_setOf_eq, mem_sphere_iff_norm, sub_zero]
    constructor
    · intro h; rw [← h, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    · intro h; rw [Complex.normSq_eq_norm_sq, h, Real.sq_sqrt ht]
  rw [e]
  exact Measure.addHaar_sphere volume 0 _

/- English proof (translation)
Use `set U : Set ℂ := {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ} with hU`. Establish `hUo : IsOpen U` using `isOpen_lt continuous_const Complex.continuous_normSq`. Set `sM : ℂ → (Fin (k + 1) → Fin (k + 1) → ℂ)` to `fun ζ i j => U.piecewise (fun ζ => μsec ζ i j) (fun _ => (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j) ζ`. Establish `hsM : Measurable sM`. Use `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations.

Conclude with `ContinuousOn.measurable_piecewise (hsec.1 i j).continuousOn continuousOn_const hUo.measurableSet`. Establish `hbw : Measurable fun q : (Fin r → ℂ) × ℂ => bcWeight k r (Tz k r z) (Tz k r z') q`. Unfold `bcWeight`. Use `Measurable.ite (measurableSet_le measurable_const (by fun_prop)) (by fun_prop) measurable_const` and prove the remaining obligations. Establish `hJ : Measurable fun q : (Fin r → ℂ) × ℂ => Jint φ μW μW' (bigCell k r q.1 (Matrix.of (sM q.2)))` using `(meas_Jint hφ μW μW').comp (meas_bigCell.comp (measurable_fst.prodMk (hsM.comp measurable_snd)))`.

Establish `hF'' : Measurable fun q : (Fin r → ℂ) × ℂ => ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q) * (C * Jint φ μW μW' (bigCell k r q.1 (Matrix.of (sM q.2))))` using `(ENNReal.measurable_ofReal.comp hbw).mul (measurable_const.mul hJ)`. Use `hF''.aemeasurable.congr ?_` and prove the remaining obligations. Rewrite using `[Filter.EventuallyEq, ae_iff]`. Establish `hnull : ((volume : Measure (Fin r → ℂ)).prod (volume : Measure ℂ)) (Set.univ ×ˢ {ζ : ℂ | Complex.normSq ζ = Tz k r z * Tz k r z'}) = 0`. Rewrite using `[Measure.prod_prod, sphere_null _ (mul_pos hT hT').le, mul_zero]`.

Use `measure_mono_null ?_ hnull` and prove the remaining obligations. Introduce `q hq`. Simplify using `only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and] at hq ⊢`. Assume the negation of the conclusion as `hne`. Apply `hq` to reduce the goal to its premises.

Distinguish the cases in `hin : q.2 ∈ U`. Establish `: Matrix.of (sM q.2) = μsec q.2`. Use extensionality with `i j`. Simplify using `[sM, Set.piecewise, hin]`. Rewrite using `[this]`.

Establish `hlt : Complex.normSq q.2 < Tz k r z * Tz k r z'`. Simplify using `only [hU, Set.mem_setOf_eq, not_lt] at hin`. Conclude with `lt_of_le_of_ne hin hne`. Establish `h0 : bcWeight k r (Tz k r z) (Tz k r z') q = 0`. Unfold `bcWeight`.

Rewrite using `[if_neg (not_le.2 hlt)]`. Simplify using `[h0]`.
-/
theorem aemeas_F {φ : Mt k r → ℝ≥0∞} (hφ : Measurable φ) (μW μW' : Measure (Mt k r)) [SFinite μW] [SFinite μW']
    {z z' : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hsec : IsSection k r z z' μsec) (C : ℝ≥0∞) :
    AEMeasurable (fun q : (Fin r → ℂ) × ℂ => ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q) *
      (C * Jint φ μW μW' (bigCell k r q.1 (μsec q.2)))) ((volume : Measure (Fin r → ℂ)).prod (volume : Measure ℂ)) := by
  set U : Set ℂ := {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_normSq
  let sM : ℂ → (Fin (k + 1) → Fin (k + 1) → ℂ) := fun ζ i j => U.piecewise (fun ζ => μsec ζ i j) (fun _ => (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j) ζ
  have hsM : Measurable sM := by
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    exact ContinuousOn.measurable_piecewise (hsec.1 i j).continuousOn continuousOn_const hUo.measurableSet
  have hbw : Measurable fun q : (Fin r → ℂ) × ℂ => bcWeight k r (Tz k r z) (Tz k r z') q := by
    unfold bcWeight
    refine Measurable.ite (measurableSet_le measurable_const (by fun_prop)) (by fun_prop) measurable_const
  have hJ : Measurable fun q : (Fin r → ℂ) × ℂ => Jint φ μW μW' (bigCell k r q.1 (Matrix.of (sM q.2))) :=
    (meas_Jint hφ μW μW').comp (meas_bigCell.comp (measurable_fst.prodMk (hsM.comp measurable_snd)))
  have hF'' : Measurable fun q : (Fin r → ℂ) × ℂ => ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q) *
      (C * Jint φ μW μW' (bigCell k r q.1 (Matrix.of (sM q.2)))) :=
    (ENNReal.measurable_ofReal.comp hbw).mul (measurable_const.mul hJ)
  refine hF''.aemeasurable.congr ?_
  rw [Filter.EventuallyEq, ae_iff]
  have hnull : ((volume : Measure (Fin r → ℂ)).prod (volume : Measure ℂ))
      (Set.univ ×ˢ {ζ : ℂ | Complex.normSq ζ = Tz k r z * Tz k r z'}) = 0 := by
    rw [Measure.prod_prod, sphere_null _ (mul_pos hT hT').le, mul_zero]
  refine measure_mono_null ?_ hnull
  intro q hq
  simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and] at hq ⊢
  by_contra hne
  apply hq
  by_cases hin : q.2 ∈ U
  · have : Matrix.of (sM q.2) = μsec q.2 := by
      ext i j; simp [sM, Set.piecewise, hin]
    rw [this]
  · have hlt : Complex.normSq q.2 < Tz k r z * Tz k r z' := by
      simp only [hU, Set.mem_setOf_eq, not_lt] at hin
      exact lt_of_le_of_ne hin hne
    have h0 : bcWeight k r (Tz k r z) (Tz k r z') q = 0 := by
      unfold bcWeight; rw [if_neg (not_le.2 hlt)]
    simp [h0]

/- English proof (translation)
Establish `: SigmaFinite μb` using `hμb.1.1`. Establish `h3 : Measurable fun p : (Mt k r × Mt k r) × Mt k r => φ (fun i j => (Matrix.of p.1.1 * bigCell k r c 1 * Matrix.of p.1.2 * (Matrix.of p.2)⁻¹) i j)` using `hφ.comp (meas_PQinv (fun p : (Mt k r × Mt k r) × Mt k r => Matrix.of p.1.1 * bigCell k r c 1 * Matrix.of p.1.2) (fun p => Matrix.of p.2) (by fun_prop) (by fun_prop))`. Rewrite using `[lintegral_lintegral_swap (h3.lintegral_prod_right' (ν := N1 k r)).aemeasurable]`. Establish `h3' : Measurable fun p : (Mt k r × Mt k r) × Mt k r => φ (fun i j => (Matrix.of p.1.2 * bigCell k r c 1 * Matrix.of p.1.1 * (Matrix.of p.2)⁻¹) i j)` using `hφ.comp (meas_PQinv (fun p : (Mt k r × Mt k r) × Mt k r => Matrix.of p.1.2 * bigCell k r c 1 * Matrix.of p.1.1) (fun p => Matrix.of p.2) (by fun_prop) (by fun_prop))`. Establish `hψ : Measurable fun m : Mt k r => ∫⁻ n, ∫⁻ n', φ (fun i j => (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) i j) ∂(N1 k r) ∂(N1 k r)` using `(h3'.lintegral_prod_right' (ν := N1 k r)).lintegral_prod_right' (ν := N1 k r)`.

Rewrite using `[hW k r z z' hk hz hz' hT hT' μb μW μW' hμb hμW hμW' a a' ha ha' hma hma' μsec hsec _ hψ]`. Use `congr 1`. Use `lintegral_congr fun ζ => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `hh_psi hφ hz hT hz' hT' hμW hμW' c (μsec ζ)`.
-/
theorem lhs_c {φ : Mt k r → ℝ≥0∞} (hφ : Measurable φ) (hW : WbHaar) {z z' : Fin (2 * r + k + 1) → ℂ} (hk : 1 ≤ k)
    (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') {μb μW μW' : Measure (Mt k r)}
    (hμb : IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb) (hμW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW)
    (hμW' : Formalism.MainNotions.S.IsHaarOn (UWset k r z') μW') {a a' : ℝ} (ha : 0 < a) (ha' : 0 < a')
    (hma : μW Set.univ = ENNReal.ofReal a) (hma' : μW' Set.univ = ENNReal.ofReal a')
    {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hsec : IsSection k r z z' μsec) (c : Fin r → ℂ) :
    ∫⁻ n, ∫⁻ m, ∫⁻ n', φ (fun i j => (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) i j)
      ∂(N1 k r) ∂μb ∂(N1 k r) =
    ENNReal.ofReal (wbConst k (Tz k r z) (Tz k r z') a a') *
      ∫⁻ ζ : ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.zWeight k (Tz k r z) (Tz k r z') ζ) *
        Jint φ μW μW' (bigCell k r c (μsec ζ)) := by
  have : SigmaFinite μb := hμb.1.1
  have h3 : Measurable fun p : (Mt k r × Mt k r) × Mt k r =>
      φ (fun i j => (Matrix.of p.1.1 * bigCell k r c 1 * Matrix.of p.1.2 * (Matrix.of p.2)⁻¹) i j) :=
    hφ.comp (meas_PQinv (fun p : (Mt k r × Mt k r) × Mt k r => Matrix.of p.1.1 * bigCell k r c 1 * Matrix.of p.1.2)
      (fun p => Matrix.of p.2) (by fun_prop) (by fun_prop))
  rw [lintegral_lintegral_swap (h3.lintegral_prod_right' (ν := N1 k r)).aemeasurable]
  have h3' : Measurable fun p : (Mt k r × Mt k r) × Mt k r =>
      φ (fun i j => (Matrix.of p.1.2 * bigCell k r c 1 * Matrix.of p.1.1 * (Matrix.of p.2)⁻¹) i j) :=
    hφ.comp (meas_PQinv (fun p : (Mt k r × Mt k r) × Mt k r => Matrix.of p.1.2 * bigCell k r c 1 * Matrix.of p.1.1)
      (fun p => Matrix.of p.2) (by fun_prop) (by fun_prop))
  have hψ : Measurable fun m : Mt k r => ∫⁻ n, ∫⁻ n', φ (fun i j => (Matrix.of n * bigCell k r c 1 * Matrix.of m *
      (Matrix.of n')⁻¹) i j) ∂(N1 k r) ∂(N1 k r) :=
    (h3'.lintegral_prod_right' (ν := N1 k r)).lintegral_prod_right' (ν := N1 k r)
  rw [hW k r z z' hk hz hz' hT hT' μb μW μW' hμb hμW hμW' a a' ha ha' hma hma' μsec hsec _ hψ]
  congr 1
  refine lintegral_congr fun ζ => ?_
  congr 1
  exact hh_psi hφ hz hT hz' hT' hμW hμW' c (μsec ζ)

/- English proof (translation)
Introduce `k r z z' hk hz hz' hT hT' μ μW μW' hμ hμW hμW' a a' ha ha' hma hma' κ hκ μsec hsec φ hφ`. Take `⟨μb, hμb⟩` from `(hE k r).2`. Establish `: SigmaFinite μW` using `hμW.1`. Establish `: SigmaFinite μW'` using `hμW'.1`. Use `set T := Tz k r z with hTdef`.

Use `set T' := Tz k r z' with hT'def`. Establish `hR : ∀ q : (Fin r → ℂ) × ℂ, ∫⁻ s, ∫⁻ s', φ (fun i j => (Matrix.of s * bigCell k r q.1 (μsec q.2) * (Matrix.of s')⁻¹) i j) ∂(Formalism.MainNotions.S.muS μW' (Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ))) ∂(Formalism.MainNotions.S.muS μW (Formalism.MainNotions.S.h …` using `fun q => rhs_eq hφ μW μW' ENNReal.ofReal_ne_top _`. Repeatedly rewrite using `[hR]`. Rewrite using `[Measure.volume_eq_prod, lintegral_prod _ (aemeas_F hφ μW μW' hT hT' hsec _)]`. Rewrite using `[hB k r μ μb hμ hμb φ hφ]`.

Repeatedly rewrite using `[lhs_c hφ hW hk hz hz' hT hT' hμb hμW hμW' ha ha' hma hma' hsec]`. Rewrite using `[← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `lintegral_congr fun c => ?_` and prove the remaining obligations. Rewrite using `[← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `lintegral_congr fun ζ => ?_` and prove the remaining obligations.

Establish `hcw` using `cWeight_nonneg (k := k) c`. Establish `hzw` using `zWeight_nonneg (k := k) T T' ζ`. Establish `hwf : bcWeight k r T T' (c, ζ) = Formalism.FourierDecayAlt.B2.cWeight k r c * Formalism.FourierDecayAlt.B2.zWeight k T T' ζ` using `Formalism.FourierDecayAlt.P.weight_factorization k r T T' (c, ζ)`. Establish `key : ENNReal.ofReal (2 ^ r) * ENNReal.ofReal (wbConst k T T' a a') = ENNReal.ofReal (jacConst k r T T' a a' κ) * (ENNReal.ofReal κ * ENNReal.ofReal κ)`. Rewrite using `[← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hκ.le, ← ENNReal.ofReal_mul (jacConst_nonneg hT hT' ha ha' hκ), const_eq hT hT' ha ha' hκ]`.

Rewrite using `[hwf, ENNReal.ofReal_mul hcw]`. Simplify using `only [← hTdef, ← hT'def]`. Use `symm`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem jacGauge_of (hB : BruhatHaar) (hW : WbHaar) (hE : GaugeExists) : JacGauge := by
  intro k r z z' hk hz hz' hT hT' μ μW μW' hμ hμW hμW' a a' ha ha' hma hma' κ hκ μsec hsec φ hφ
  obtain ⟨μb, hμb⟩ := (hE k r).2
  have : SigmaFinite μW := hμW.1
  have : SigmaFinite μW' := hμW'.1
  set T := Tz k r z with hTdef
  set T' := Tz k r z' with hT'def

  have hR : ∀ q : (Fin r → ℂ) × ℂ, ∫⁻ s, ∫⁻ s', φ (fun i j => (Matrix.of s * bigCell k r q.1 (μsec q.2) *
      (Matrix.of s')⁻¹) i j) ∂(Formalism.MainNotions.S.muS μW' (Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ)))
      ∂(Formalism.MainNotions.S.muS μW (Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ))) =
      ENNReal.ofReal κ * ENNReal.ofReal κ * Jint φ μW μW' (bigCell k r q.1 (μsec q.2)) :=
    fun q => rhs_eq hφ μW μW' ENNReal.ofReal_ne_top _
  simp_rw [hR]
  rw [Measure.volume_eq_prod, lintegral_prod _ (aemeas_F hφ μW μW' hT hT' hsec _)]

  rw [hB k r μ μb hμ hμb φ hφ]
  simp_rw [lhs_c hφ hW hk hz hz' hT hT' hμb hμW hμW' ha ha' hma hma' hsec]

  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun c => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ζ => ?_
  have hcw := cWeight_nonneg (k := k) c
  have hzw := zWeight_nonneg (k := k) T T' ζ
  have hwf : bcWeight k r T T' (c, ζ) = Formalism.FourierDecayAlt.B2.cWeight k r c * Formalism.FourierDecayAlt.B2.zWeight k T T' ζ :=
    Formalism.FourierDecayAlt.P.weight_factorization k r T T' (c, ζ)
  have key : ENNReal.ofReal (2 ^ r) * ENNReal.ofReal (wbConst k T T' a a') =
      ENNReal.ofReal (jacConst k r T T' a a' κ) * (ENNReal.ofReal κ * ENNReal.ofReal κ) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hκ.le,
      ← ENNReal.ofReal_mul (jacConst_nonneg hT hT' ha ha' hκ), const_eq hT hT' ha ha' hκ]
  rw [hwf, ENNReal.ofReal_mul hcw]
  simp only [← hTdef, ← hT'def]
  symm
  calc ENNReal.ofReal (jacConst k r T T' a a' κ) * (ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) *
          ENNReal.ofReal (Formalism.FourierDecayAlt.B2.zWeight k T T' ζ) *
          (ENNReal.ofReal κ * ENNReal.ofReal κ * Jint φ μW μW' (bigCell k r c (μsec ζ))))
      = (ENNReal.ofReal (jacConst k r T T' a a' κ) * (ENNReal.ofReal κ * ENNReal.ofReal κ)) *
          (ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) *
          (ENNReal.ofReal (Formalism.FourierDecayAlt.B2.zWeight k T T' ζ) * Jint φ μW μW' (bigCell k r c (μsec ζ)))) := by ring
    _ = (ENNReal.ofReal (2 ^ r) * ENNReal.ofReal (wbConst k T T' a a')) *
          (ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) *
          (ENNReal.ofReal (Formalism.FourierDecayAlt.B2.zWeight k T T' ζ) * Jint φ μW μW' (bigCell k r c (μsec ζ)))) := by rw [key]
    _ = _ := by ring

end Formalism.L2.SG.Pf.Jac

namespace Formalism.L2.SG.Pf

/- English proof (translation)
The claim follows from `Jac.jacGauge_of hB hW hE`.
-/
theorem jacGauge_of (hB : BruhatHaar) (hW : WbHaar) (hE : GaugeExists) : JacGauge := Jac.jacGauge_of hB hW hE

end Formalism.L2.SG.Pf
