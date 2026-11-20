import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceSingleMulSingle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtTwistHomotopyKernel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeIsOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothCholeskyFactorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceActionDeterminantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeasureCongruenceInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeasureLocallyFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeasureDensityFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactGroupDisintegrationStatement

noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise

namespace GlobalTheory.CompanionTheory.ConeHaar

open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
The claim follows from `GlobalTheory.T.positive_cone_isOpen n`.
-/
theorem cone_open (n : ℕ) : IsOpen (cone n) := GlobalTheory.T.positive_cone_isOpen n
/- English proof (translation)
The claim follows from `GlobalTheory.T.smooth_positive_definite_sqrt n`.
-/
theorem cone_chol (n : ℕ) : ∃ σ₀ : Mat n → Mat n, ContDiffOn ℝ ∞ σ₀ {P | P.PosDef} ∧ ∀ P : Mat n, P.PosDef → σ₀ P * (σ₀ P)ᴴ = P :=
  GlobalTheory.T.smooth_positive_definite_sqrt n
/- English proof (translation)
The claim follows from `GlobalTheory.T.congruence_action_determinant n g hg`.
-/
theorem cone_lin (n : ℕ) (g : Mat n) (hg : g.det ≠ 0) : ∃ T : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ),
    (∀ v, hOf (T v) = g * hOf v * gᴴ) ∧ LinearMap.det T = ‖g.det‖ ^ (2 * n) := GlobalTheory.T.congruence_action_determinant n g hg
/- English proof (translation)
The claim follows from `GlobalTheory.T.cone_measure_congruence_invariant n g hg T hT hdet`.
-/
theorem cone_meas (n : ℕ) (g : Mat n) (hg : g.det ≠ 0) (T : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ))
    (hT : ∀ v, hOf (T v) = g * hOf v * gᴴ) (hdet : LinearMap.det T = ‖g.det‖ ^ (2 * n)) :
    Measure.map T (coneMeas n) = coneMeas n := GlobalTheory.T.cone_measure_congruence_invariant n g hg T hT hdet
/- English proof (translation)
The claim follows from `(GlobalTheory.T.cone_measure_locally_finite n).2 C hC hCc`.
-/
theorem cone_fin (n : ℕ) (C : Set (Fin n × Fin n → ℝ)) (hC : IsCompact C) (hCc : C ⊆ cone n) : coneMeas n C < ⊤ :=
  (GlobalTheory.T.cone_measure_locally_finite n).2 C hC hCc
/- English proof (translation)
The claim follows from `(GlobalTheory.T.cone_measure_locally_finite n).1`.
-/
theorem cone_ne (n : ℕ) : coneMeas n ≠ 0 := (GlobalTheory.T.cone_measure_locally_finite n).1
/- English proof (translation)
The claim follows from `(GlobalTheory.T.cone_measure_density_formula n).1`.
-/
theorem cone_ae (n : ℕ) : ∀ᵐ v ∂(coneMeas n), v ∈ cone n := (GlobalTheory.T.cone_measure_density_formula n).1
/- English proof (translation)
The claim follows from `(GlobalTheory.T.cone_measure_density_formula n).2 f`.
-/
theorem cone_int (n : ℕ) (f : (Fin n × Fin n → ℝ) → ℂ) :
    ∫ v, f v ∂(coneMeas n) = ∫ v in cone n, f v * ((hOf v).det ^ n)⁻¹ := (GlobalTheory.T.cone_measure_density_formula n).2 f
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.LengthGL.isCompact_G R`.
-/
theorem cone_cpt (n : ℕ) (R : ℝ) : IsCompact {y : G n | lg y.val ≤ R} := GlobalTheory.CompanionTheory.LengthGL.isCompact_G R

/- English proof (translation)
Use `show (hOf v)ᴴ = hOf v`. Simplify using `[hOf, conjTranspose_sum, conjTranspose_smul, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose]`.
-/
theorem hOf_isHermitian (v : Fin n × Fin n → ℝ) : (hOf v).IsHermitian := by
  show (hOf v)ᴴ = hOf v
  simp [hOf, conjTranspose_sum, conjTranspose_smul, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose]

/- English proof (translation)
Simplify using `only [hOf, Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, GlobalTheory.CompanionTheory.TopClass.trace_hb_mul_hb]`. Simplify using the standard rewrite rules.
-/
theorem trace_hOf_mul (v : Fin n × Fin n → ℝ) (q : Fin n × Fin n) : (hOf v * hb q).trace = (v q : ℂ) := by
  simp only [hOf, Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul,
    GlobalTheory.CompanionTheory.TopClass.trace_hb_mul_hb]
  simp

/- English proof (translation)
Introduce `v w h`. Use function extensionality and compare the values at `q`. Use `trace_hOf_mul v q` as an intermediate fact. Rewrite `this` using `[h, trace_hOf_mul w q]`. Conclude with `(Complex.ofReal_injective this).symm`.
-/
theorem hOf_injective : Function.Injective (hOf (n := n)) := by
  intro v w h
  funext q
  have := trace_hOf_mul v q
  rw [h, trace_hOf_mul w q] at this
  exact (Complex.ofReal_injective this).symm

/- English proof (translation)
Establish `hre : ∀ p, (((hb p * P).trace).re : ℂ) = (P * hb p).trace`. Introduce `p`. Establish `h1 : star (hb p * P).trace = (hb p * P).trace`. Rewrite using `[← Matrix.trace_conjTranspose, conjTranspose_mul, hP.eq, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose, Matrix.trace_mul_comm]`. Establish `h2 : (((hb p * P).trace).re : ℂ) = (hb p * P).trace` using `Complex.conj_eq_iff_real.1 h1 |>.choose_spec ▸ by simp`.

Rewrite using `[h2, Matrix.trace_mul_comm]`. Establish `h` using `(GlobalTheory.CompanionTheory.TopClass.hbB n).sum_repr P`. Simplify using `only [GlobalTheory.CompanionTheory.TopClass.hbB_repr, GlobalTheory.CompanionTheory.TopClass.hbB_apply] at h`. Use `conv_rhs => rw [← h]`. Simplify using `only [hOf, hre]`.
-/
theorem hOf_coords (P : Mat n) (hP : P.IsHermitian) : hOf (fun p => ((hb p * P).trace).re) = P := by
  have hre : ∀ p, (((hb p * P).trace).re : ℂ) = (P * hb p).trace := by
    intro p
    have h1 : star (hb p * P).trace = (hb p * P).trace := by
      rw [← Matrix.trace_conjTranspose, conjTranspose_mul, hP.eq, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose,
        Matrix.trace_mul_comm]
    have h2 : (((hb p * P).trace).re : ℂ) = (hb p * P).trace := Complex.conj_eq_iff_real.1 h1 |>.choose_spec ▸ by simp
    rw [h2, Matrix.trace_mul_comm]
  have h := (GlobalTheory.CompanionTheory.TopClass.hbB n).sum_repr P
  simp only [GlobalTheory.CompanionTheory.TopClass.hbB_repr, GlobalTheory.CompanionTheory.TopClass.hbB_apply] at h
  conv_rhs => rw [← h]
  simp only [hOf, hre]

/- English proof (translation)
Assemble the required witnesses or components as `⟨hOf_isHermitian, hOf_injective, hOf_coords⟩`.
-/
theorem cone_hOf (n : ℕ) : (∀ v : Fin n × Fin n → ℝ, (hOf v).IsHermitian) ∧ Function.Injective (hOf (n := n)) ∧
    ∀ P : Mat n, P.IsHermitian → hOf (fun p => ((hb p * P).trace).re) = P :=
  ⟨hOf_isHermitian, hOf_injective, hOf_coords⟩

/- English proof (translation)
Rewrite using `[convex_iff_forall_pos]`. Introduce `x hx y hy a b ha hb' hab`. Establish `e : hOf (a • x + b • y) = (a : ℂ) • hOf x + (b : ℂ) • hOf y`. Simplify using `only [hOf, Finset.smul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul, smul_smul, ← add_smul, Complex.ofReal_add, Complex.ofReal_mul]`. Use `show (hOf (a • x + b • y)).PosDef`.

Establish `hh : (hOf (a • x + b • y)).IsHermitian` using `hOf_isHermitian _`. Use `Matrix.PosDef.of_dotProduct_mulVec_pos hh fun w hw => ?_` and prove the remaining obligations. Establish `h1 : 0 < star w ⬝ᵥ hOf x *ᵥ w` using `Matrix.PosDef.dotProduct_mulVec_pos hx hw`. Establish `h2 : 0 < star w ⬝ᵥ hOf y *ᵥ w` using `Matrix.PosDef.dotProduct_mulVec_pos hy hw`. Rewrite using `[e, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul]`.

Establish `ha' : (0 : ℂ) < (a : ℂ)` using `by exact_mod_cast ha`. Establish `hb'' : (0 : ℂ) < (b : ℂ)` using `by exact_mod_cast hb'`. Simplify `add_pos (mul_pos ha' h1) (mul_pos hb'' h2)` using `[smul_eq_mul]`.
-/
theorem cone_conv (n : ℕ) : Convex ℝ (cone n) := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb' hab
  have e : hOf (a • x + b • y) = (a : ℂ) • hOf x + (b : ℂ) • hOf y := by
    simp only [hOf, Finset.smul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul, smul_smul,
      ← add_smul, Complex.ofReal_add, Complex.ofReal_mul]
  show (hOf (a • x + b • y)).PosDef
  have hh : (hOf (a • x + b • y)).IsHermitian := hOf_isHermitian _
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hh fun w hw => ?_
  have h1 : 0 < star w ⬝ᵥ hOf x *ᵥ w := Matrix.PosDef.dotProduct_mulVec_pos hx hw
  have h2 : 0 < star w ⬝ᵥ hOf y *ᵥ w := Matrix.PosDef.dotProduct_mulVec_pos hy hw
  rw [e, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul]
  have ha' : (0 : ℂ) < (a : ℂ) := by exact_mod_cast ha
  have hb'' : (0 : ℂ) < (b : ℂ) := by exact_mod_cast hb'
  simpa [smul_eq_mul] using add_pos (mul_pos ha' h1) (mul_pos hb'' h2)

/- English proof (translation)
Establish `hu : IsUnit a.det` using `isUnit_iff_ne_zero.2 ha`. Establish `huH : IsUnit aᴴ.det`. Rewrite using `[Matrix.det_conjTranspose]`. Conclude with `isUnit_iff_ne_zero.2 (star_ne_zero.2 ha)`. Use `⟨⟨a⁻¹ * b, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_nonsing_inv]`. Combine the equalities or inequalities in the displayed calculation. Use `show b = a * (a⁻¹ * b)`. Rewrite using `[← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]`.
-/
theorem cone_unit (n : ℕ) (a b : Mat n) (ha : a.det ≠ 0) (hab : a * aᴴ = b * bᴴ) :
    ∃ u : Matrix.unitaryGroup (Fin n) ℂ, b = a * u.1 := by
  have hu : IsUnit a.det := isUnit_iff_ne_zero.2 ha
  have huH : IsUnit aᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact isUnit_iff_ne_zero.2 (star_ne_zero.2 ha)
  refine ⟨⟨a⁻¹ * b, ?_⟩, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_nonsing_inv]
    calc a⁻¹ * b * (bᴴ * aᴴ⁻¹) = a⁻¹ * (b * bᴴ) * aᴴ⁻¹ := by simp only [Matrix.mul_assoc]
      _ = a⁻¹ * a * (aᴴ * aᴴ⁻¹) := by rw [← hab]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_nonsing_inv _ huH, Matrix.one_mul]
  · show b = a * (a⁻¹ * b)
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

/- English proof (translation)
Establish `hh : (g * P * gᴴ).IsHermitian` using `by show (g * P * gᴴ)ᴴ = _`. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, hP.isHermitian.eq, Matrix.mul_assoc]`. Use `Matrix.PosDef.of_dotProduct_mulVec_pos hh fun x hx => ?_` and prove the remaining obligations. Establish `hinj : gᴴ *ᵥ x ≠ 0`. Introduce `h0`.

Establish `hu : IsUnit gᴴ.det`. Rewrite using `[Matrix.det_conjTranspose]`. Conclude with `isUnit_iff_ne_zero.2 (star_ne_zero.2 hg)`. Apply `hx` to reduce the goal to its premises. Use `congrArg (fun w => gᴴ⁻¹ *ᵥ w) h0` as an intermediate fact.

Simplify `this` using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu]`. Establish `h` using `Matrix.PosDef.dotProduct_mulVec_pos hP hinj`. Establish `e : star x ⬝ᵥ (g * P * gᴴ) *ᵥ x = star (gᴴ *ᵥ x) ⬝ᵥ P *ᵥ (gᴴ *ᵥ x)`. Rewrite using `[star_mulVec, conjTranspose_conjTranspose, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]`. Rewrite using `[e]`.

Conclude with `h`.
-/
theorem cone_congr (n : ℕ) (g P : Mat n) (hg : g.det ≠ 0) (hP : P.PosDef) : (g * P * gᴴ).PosDef := by
  have hh : (g * P * gᴴ).IsHermitian := by
    show (g * P * gᴴ)ᴴ = _
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hP.isHermitian.eq, Matrix.mul_assoc]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hh fun x hx => ?_
  have hinj : gᴴ *ᵥ x ≠ 0 := by
    intro h0
    have hu : IsUnit gᴴ.det := by
      rw [Matrix.det_conjTranspose]; exact isUnit_iff_ne_zero.2 (star_ne_zero.2 hg)
    apply hx
    have := congrArg (fun w => gᴴ⁻¹ *ᵥ w) h0
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu] using this
  have h := Matrix.PosDef.dotProduct_mulVec_pos hP hinj
  have e : star x ⬝ᵥ (g * P * gᴴ) *ᵥ x = star (gᴴ *ᵥ x) ⬝ᵥ P *ᵥ (gᴴ *ᵥ x) := by
    rw [star_mulVec, conjTranspose_conjTranspose, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec]
  rw [e]
  exact h

/- English proof (translation)
Use `cone_congr n g 1 hg Matrix.PosDef.one` as an intermediate fact. Simplify using `using this`.
-/
theorem cone_gram (n : ℕ) (g : Mat n) (hg : g.det ≠ 0) : (g * gᴴ).PosDef := by
  have := cone_congr n g 1 hg Matrix.PosDef.one
  simpa using this

abbrev UK (n : ℕ) := Matrix.unitaryGroup (Fin n) ℂ
def msK (n : ℕ) : MeasurableSpace (UK n) := borel _
attribute [local instance] msK
local instance : BorelSpace (UK n) := ⟨rfl⟩
local instance : CompactSpace (UK n) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
local instance : SecondCountableTopology (Mat n) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
local instance : LocallyCompactSpace (Mat n) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
local instance : SecondCountableTopology (G n) :=
  have : SecondCountableTopology (Mat n)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology
local instance : LocallyCompactSpace (G n) := inferInstanceAs (LocallyCompactSpace (Mat n)ˣ)
local instance : SecondCountableTopology (UK n) :=
  (Topology.IsEmbedding.subtypeVal (p := fun x => x ∈ unitaryGroup (Fin n) ℂ)).secondCountableTopology
local instance : SFinite (coneMeas n) := by unfold coneMeas; infer_instance

def emb : UK n →* G n := Unitary.toUnits

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem emb_val (κ : UK n) : (emb κ).val = κ.1 := rfl

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Use `⟨continuous_subtype_val, ?_⟩` and prove the remaining obligations. Use `show Continuous fun κ : UK n => star κ.1`. Conclude with `continuous_subtype_val.star`.
-/
theorem continuous_emb : Continuous (emb : UK n → G n) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_subtype_val, ?_⟩
  show Continuous fun κ : UK n => star κ.1
  exact continuous_subtype_val.star

/- English proof (translation)
The claim follows from `((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero`.
-/
theorem val_mem (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

/- English proof (translation)
The claim follows from `isOpen_ne.preimage (continuous_id.matrix_det)`.
-/
theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne.preimage (continuous_id.matrix_det)

/- English proof (translation)
Unfold `hOf`. Use `ContDiff.sum fun p _ => ?_` and prove the remaining obligations. Establish `h : ContDiff ℝ ∞ (fun v : Fin n × Fin n → ℝ => ((v p : ℝ) : ℂ))` using `Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ p)`. Conclude with `h.smul contDiff_const`.
-/
theorem contDiff_hOf : ContDiff ℝ ∞ (hOf (n := n)) := by
  unfold hOf
  refine ContDiff.sum fun p _ => ?_
  have h : ContDiff ℝ ∞ (fun v : Fin n × Fin n → ℝ => ((v p : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ p)
  exact h.smul contDiff_const

/- English proof (translation)
Introduce `h0`. Establish `: P.det = 0` using `by rw [← h, Matrix.det_mul, h0, zero_mul]`. Conclude with `hP.det_pos.ne' this`.
-/
theorem det_ne_of_gram {a P : Mat n} (h : a * aᴴ = P) (hP : P.PosDef) : a.det ≠ 0 := by
  intro h0
  have : P.det = 0 := by rw [← h, Matrix.det_mul, h0, zero_mul]
  exact hP.det_pos.ne' this

def sec (σ₀ : Mat n → Mat n) (hσ : ∀ P : Mat n, P.PosDef → σ₀ P * (σ₀ P)ᴴ = P)
    (v : Fin n × Fin n → ℝ) : G n :=
  open Classical in
  if h : v ∈ cone n then Matrix.GeneralLinearGroup.mkOfDetNeZero (σ₀ (hOf v)) (det_ne_of_gram (hσ _ h) h) else 1

/- English proof (translation)
Simplify using `only [sec, dif_pos h]`. Both sides reduce to the same expression.
-/
theorem sec_val (σ₀ : Mat n → Mat n) (hσ : ∀ P : Mat n, P.PosDef → σ₀ P * (σ₀ P)ᴴ = P)
    {v : Fin n × Fin n → ℝ} (h : v ∈ cone n) : (sec σ₀ hσ v).val = σ₀ (hOf v) := by
  simp only [sec, dif_pos h]
  rfl

/- English proof (translation)
Establish `hcont : ContinuousOn (sec σ₀ hσ) (cone n)`. Rewrite using `[continuousOn_iff_continuous_restrict, Units.continuous_iff]`. Establish `h1 : Continuous fun v : cone n => σ₀ (hOf v.1)` using `hc.comp_continuous (contDiff_hOf.continuous.comp continuous_subtype_val) fun v => v.2`. Establish `h2 : (Units.val ∘ (cone n).restrict (sec σ₀ hσ)) = fun v : cone n => σ₀ (hOf v.1)`. Use function extensionality and compare the values at `v`.

Conclude with `sec_val σ₀ hσ v.2`. Establish `h3 : (fun x : cone n => (((cone n).restrict (sec σ₀ hσ) x)⁻¹ : G n).val) = fun v : cone n => (σ₀ (hOf v.1))⁻¹`. Use function extensionality and compare the values at `v`. Use `show (((sec σ₀ hσ v.1)⁻¹ : G n)).val = _`. Rewrite using `[Matrix.coe_units_inv, sec_val σ₀ hσ v.2]`.

Use `⟨h2 ▸ h1, ?_⟩` and prove the remaining obligations. Use `show Continuous fun x : cone n => (((cone n).restrict (sec σ₀ hσ) x)⁻¹ : G n).val`. Rewrite using `[h3]`. Establish `h4 : ∀ v : cone n, (σ₀ (hOf v.1)).det ≠ 0` using `fun v => det_ne_of_gram (hσ _ v.2) v.2`. Simplify using `only [Matrix.inv_def, Ring.inverse_eq_inv']`.

Conclude with `(h1.matrix_det.inv₀ h4).smul h1.matrix_adjugate`. Establish `: sec σ₀ hσ = (cone n).piecewise (sec σ₀ hσ) (fun _ => 1)`. Use function extensionality and compare the values at `v`. Distinguish the cases in `h : v ∈ cone n`. Simplify using `[h]`.

Simplify using `[h, sec]`. Rewrite using `[this]`. Conclude with `hcont.measurable_piecewise continuousOn_const (cone_open n).measurableSet`.
-/
theorem measurable_sec (σ₀ : Mat n → Mat n) (hc : ContinuousOn σ₀ {P | P.PosDef})
    (hσ : ∀ P : Mat n, P.PosDef → σ₀ P * (σ₀ P)ᴴ = P) [MeasurableSpace (G n)] [BorelSpace (G n)] :
    Measurable (sec σ₀ hσ) := by
  classical
  have hcont : ContinuousOn (sec σ₀ hσ) (cone n) := by
    rw [continuousOn_iff_continuous_restrict, Units.continuous_iff]
    have h1 : Continuous fun v : cone n => σ₀ (hOf v.1) :=
      hc.comp_continuous (contDiff_hOf.continuous.comp continuous_subtype_val) fun v => v.2
    have h2 : (Units.val ∘ (cone n).restrict (sec σ₀ hσ)) = fun v : cone n => σ₀ (hOf v.1) := by
      funext v; exact sec_val σ₀ hσ v.2
    have h3 : (fun x : cone n => (((cone n).restrict (sec σ₀ hσ) x)⁻¹ : G n).val) =
        fun v : cone n => (σ₀ (hOf v.1))⁻¹ := by
      funext v
      show (((sec σ₀ hσ v.1)⁻¹ : G n)).val = _
      rw [Matrix.coe_units_inv, sec_val σ₀ hσ v.2]
    refine ⟨h2 ▸ h1, ?_⟩
    show Continuous fun x : cone n => (((cone n).restrict (sec σ₀ hσ) x)⁻¹ : G n).val
    rw [h3]
    have h4 : ∀ v : cone n, (σ₀ (hOf v.1)).det ≠ 0 := fun v => det_ne_of_gram (hσ _ v.2) v.2
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    exact (h1.matrix_det.inv₀ h4).smul h1.matrix_adjugate
  have : sec σ₀ hσ = (cone n).piecewise (sec σ₀ hσ) (fun _ => 1) := by
    funext v
    by_cases h : v ∈ cone n
    · simp [h]
    · simp [h, sec]
  rw [this]
  exact hcont.measurable_piecewise continuousOn_const (cone_open n).measurableSet

def piG (y : G n) : Fin n × Fin n → ℝ := fun p => ((hb p * (y.val * y.valᴴ)).trace).re

/- English proof (translation)
Unfold `piG`. Use `continuous_pi fun p => ?_` and prove the remaining obligations. Use `Complex.continuous_re.comp ?_` and prove the remaining obligations. Establish `h : Continuous fun y : G n => y.val` using `Units.continuous_val`. Conclude with `Continuous.matrix_trace (continuous_const.matrix_mul (h.matrix_mul h.matrix_conjTranspose))`.
-/
theorem continuous_piG : Continuous (piG (n := n)) := by
  unfold piG
  refine continuous_pi fun p => ?_
  refine Complex.continuous_re.comp ?_
  have h : Continuous fun y : G n => y.val := Units.continuous_val
  exact Continuous.matrix_trace (continuous_const.matrix_mul (h.matrix_mul h.matrix_conjTranspose))

/- English proof (translation)
The claim follows from `(cone_hOf n).2.2 _ (Matrix.isHermitian_mul_conjTranspose_self _)`.
-/
theorem hOf_piG (y : G n) : hOf (piG y) = y.val * y.valᴴ :=
  (cone_hOf n).2.2 _ (Matrix.isHermitian_mul_conjTranspose_self _)

/- English proof (translation)
Use `show (hOf (piG y)).PosDef`. Rewrite using `[hOf_piG]`. Conclude with `cone_gram n _ (val_mem y)`.
-/
theorem piG_mem (y : G n) : piG y ∈ cone n := by
  show (hOf (piG y)).PosDef
  rw [hOf_piG]
  exact cone_gram n _ (val_mem y)

/- English proof (translation)
Introduce `n`. Take `⟨σ₀, hσs, hσ⟩` from `cone_chol n`. Use `⟨cone_open n, cone_conv n, fun v => σ₀ (hOf v), ?_, fun v hv => hσ _ hv, ?_⟩` and prove the remaining obligations. Conclude with `hσs.comp contDiff_hOf.contDiffOn fun v hv => hv`. Introduce `_ _ μ _`.

Establish `hms` using `measurable_sec σ₀ hσs.continuousOn hσ`. Establish `hact : ∀ g : G n, ∃ a : (Fin n × Fin n → ℝ) → (Fin n × Fin n → ℝ), Measurable a ∧ Measure.map a (coneMeas n) = coneMeas n ∧ ∀ᵐ x ∂(coneMeas n), ∃ k, g * sec σ₀ hσ x = sec σ₀ hσ (a x) * emb k`. Introduce `g`. Take `⟨T, hT, hdet⟩` from `cone_lin n g.val (val_mem g)`. Use `⟨T, (T.continuous_of_finiteDimensional).measurable, cone_meas n g.val (val_mem g) T hT hdet, ?_⟩` and prove the remaining obligations.

Use `filter_upwards [cone_ae n] with v hv`. Establish `hTv : T v ∈ cone n` using `by show (hOf (T v)).PosDef`. Rewrite using `[hT]`. Conclude with `cone_congr n _ _ (val_mem g) hv`. Take `⟨u, hu⟩` from `cone_unit n (sec σ₀ hσ (T v)).val (g * sec σ₀ hσ v).val (val_mem _) (by`.

Rewrite using `[sec_val σ₀ hσ hTv, hσ _ hTv, hT, Units.val_mul, sec_val σ₀ hσ hv, conjTranspose_mul]`. Use `conv_lhs => rw [← hσ _ hv]`. Simplify using `only [Matrix.mul_assoc])`. Use `⟨u, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[hu]`. Both sides reduce to the same expression. Establish `hfin : ∀ A : Set (G n), IsCompact A → coneMeas n (sec σ₀ hσ ⁻¹' (A * Set.range emb)) < ⊤`. Introduce `A hA`. Establish `hC : IsCompact (piG '' A)` using `hA.image continuous_piG`.

Establish `hCc : piG '' A ⊆ cone n`. Introduce and unpack `_ ⟨y, -, rfl⟩`. Conclude with `piG_mem y`. Establish `hsub : sec σ₀ hσ ⁻¹' (A * Set.range emb) ∩ cone n ⊆ piG '' A`. Introduce and unpack `v ⟨hv, hvc⟩`.

Take `⟨a, ha, _, ⟨k, rfl⟩, hak⟩` from `hv`. Use `⟨a, ha, (cone_hOf n).2.1 ?_⟩` and prove the remaining obligations. Rewrite using `[hOf_piG]`. Establish `h1 : (sec σ₀ hσ v).val = a.val * k.1` using `by rw [← hak]; rfl`. Establish `h2` using `hσ _ hvc`.

Rewrite `h2` using `[← sec_val σ₀ hσ hvc, h1, conjTranspose_mul, mul_assoc, ← mul_assoc k.1]`. Establish `h3 : k.1 * k.1ᴴ = 1` using `Matrix.mem_unitaryGroup_iff.1 k.2`. Rewrite `h2` using `[h3, one_mul]`. Conclude with `h2`. Establish `hz : coneMeas n (cone n)ᶜ = 0` using `cone_ae n`.

Use `lt_of_le_of_lt (measure_mono_ae ?_) (cone_fin n _ hC hCc)` and prove the remaining obligations. Use `filter_upwards [cone_ae n] with v hv hv'`. Conclude with `hsub ⟨hv', hv⟩`. Take `⟨c, hc, H⟩` from `GlobalTheory.T.compact_group_disintegration (emb (n := n)) continuous_emb (coneMeas n) (sec σ₀ hσ) hms (cone_ne n) hact hfin μ`. Use `⟨c, hc, fun F hF ⟨R, hR⟩ hK => ?_⟩` and prove the remaining obligations.

Establish `h1` using `H (fun y => F y.val) (hF.comp_continuous Units.continuous_val val_mem) (HasCompactSupport.intro (cone_cpt n R) fun y hy => hR _ (val_mem y) (not_le.1 hy)) (fun y k => hK _ (val_mem y) k)`. Rewrite using `[h1, cone_int]`. Use `congr 1`. Use `setIntegral_congr_fun (cone_open n).measurableSet fun v hv => ?_` and prove the remaining obligations. Simplify using `only [sec_val σ₀ hσ hv]`.
-/
theorem coneSt : ConeSt := by
  intro n
  obtain ⟨σ₀, hσs, hσ⟩ := cone_chol n
  refine ⟨cone_open n, cone_conv n, fun v => σ₀ (hOf v), ?_, fun v hv => hσ _ hv, ?_⟩
  · exact hσs.comp contDiff_hOf.contDiffOn fun v hv => hv
  intro _ _ μ _
  have hms := measurable_sec σ₀ hσs.continuousOn hσ
  have hact : ∀ g : G n, ∃ a : (Fin n × Fin n → ℝ) → (Fin n × Fin n → ℝ), Measurable a ∧
      Measure.map a (coneMeas n) = coneMeas n ∧ ∀ᵐ x ∂(coneMeas n), ∃ k, g * sec σ₀ hσ x = sec σ₀ hσ (a x) * emb k := by
    intro g
    obtain ⟨T, hT, hdet⟩ := cone_lin n g.val (val_mem g)
    refine ⟨T, (T.continuous_of_finiteDimensional).measurable, cone_meas n g.val (val_mem g) T hT hdet, ?_⟩
    filter_upwards [cone_ae n] with v hv
    have hTv : T v ∈ cone n := by
      show (hOf (T v)).PosDef
      rw [hT]
      exact cone_congr n _ _ (val_mem g) hv
    obtain ⟨u, hu⟩ := cone_unit n (sec σ₀ hσ (T v)).val (g * sec σ₀ hσ v).val (val_mem _) (by
      rw [sec_val σ₀ hσ hTv, hσ _ hTv, hT, Units.val_mul, sec_val σ₀ hσ hv, conjTranspose_mul]
      conv_lhs => rw [← hσ _ hv]
      simp only [Matrix.mul_assoc])
    refine ⟨u, ?_⟩
    apply Units.ext
    rw [hu]
    rfl
  have hfin : ∀ A : Set (G n), IsCompact A → coneMeas n (sec σ₀ hσ ⁻¹' (A * Set.range emb)) < ⊤ := by
    intro A hA
    have hC : IsCompact (piG '' A) := hA.image continuous_piG
    have hCc : piG '' A ⊆ cone n := by
      rintro _ ⟨y, -, rfl⟩
      exact piG_mem y
    have hsub : sec σ₀ hσ ⁻¹' (A * Set.range emb) ∩ cone n ⊆ piG '' A := by
      rintro v ⟨hv, hvc⟩
      obtain ⟨a, ha, _, ⟨k, rfl⟩, hak⟩ := hv
      refine ⟨a, ha, (cone_hOf n).2.1 ?_⟩
      rw [hOf_piG]
      have h1 : (sec σ₀ hσ v).val = a.val * k.1 := by rw [← hak]; rfl
      have h2 := hσ _ hvc
      rw [← sec_val σ₀ hσ hvc, h1, conjTranspose_mul, mul_assoc, ← mul_assoc k.1] at h2
      have h3 : k.1 * k.1ᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 k.2
      rw [h3, one_mul] at h2
      exact h2
    have hz : coneMeas n (cone n)ᶜ = 0 := cone_ae n
    refine lt_of_le_of_lt (measure_mono_ae ?_) (cone_fin n _ hC hCc)
    filter_upwards [cone_ae n] with v hv hv'
    exact hsub ⟨hv', hv⟩
  obtain ⟨c, hc, H⟩ := GlobalTheory.T.compact_group_disintegration (emb (n := n)) continuous_emb (coneMeas n) (sec σ₀ hσ) hms (cone_ne n) hact hfin μ
  refine ⟨c, hc, fun F hF ⟨R, hR⟩ hK => ?_⟩
  have h1 := H (fun y => F y.val) (hF.comp_continuous Units.continuous_val val_mem)
    (HasCompactSupport.intro (cone_cpt n R) fun y hy => hR _ (val_mem y) (not_le.1 hy))
    (fun y k => hK _ (val_mem y) k)
  rw [h1, cone_int]
  congr 1
  refine setIntegral_congr_fun (cone_open n).measurableSet fun v hv => ?_
  simp only [sec_val σ₀ hσ hv]

end GlobalTheory.CompanionTheory.ConeHaar
