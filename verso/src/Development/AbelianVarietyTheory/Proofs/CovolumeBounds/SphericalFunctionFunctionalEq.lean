import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.GramPositiveVolumeContinuousStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.KsetTransitiveStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.HalfVolumeEquivariantStatement

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi.Funct

/- English proof (translation)
Establish `ha' : aᴴ * Hpk k r * a = Hpk k r` using `ha`. Establish `hb' : bᴴ * Hpk k r * b = Hpk k r` using `hb`. Use `show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by rw [ha', hb']`.
-/
lemma gv_mul {k r : ℕ} {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) : a * b ∈ GV k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

/- English proof (translation)
Establish `hm` using `(GlobalTheory.T.gram_positive_volume_continuous k r hk).2.2.1`. Establish `hf' : Continuous (Y` using `Mt k r) fun t => Matrix.of.symm (f t) := hf`. Conclude with `ENNReal.measurable_ofReal.comp (hm.comp hf'.measurable)`.
-/
lemma meas_v {k r : ℕ} (hk : 1 ≤ k) {α : Type} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {f : α → Mat k r} (hf : Continuous f) :
    Measurable fun t => ENNReal.ofReal (vHalf k r (f t)) := by
  have hm := (GlobalTheory.T.gram_positive_volume_continuous k r hk).2.2.1
  have hf' : Continuous (Y := Mt k r) fun t => Matrix.of.symm (f t) := hf
  exact ENNReal.measurable_ofReal.comp (hm.comp hf'.measurable)

/- English proof (translation)
The claim follows from `continuous_id`.
-/
lemma cont_of {k r : ℕ} : Continuous fun κ : Mt k r => (Matrix.of κ : Mat k r) := continuous_id

/- English proof (translation)
Take `⟨κ₀, hκ₀, p, hp, rfl⟩` from `GlobalTheory.T.exists_mem_Kset_mul_mem_Pset_eq k r hk g hg`. Take `⟨hl, hr⟩` from `GlobalTheory.T.half_volume_equivariant k r hk`. Establish `hpos` using `(GlobalTheory.T.gram_positive_volume_continuous k r hk).2.1`. Establish `hae : ∀ᵐ κ ∂μK, (Matrix.of κ : Mat k r) ∈ Kset k r` using `hμ.1.conc`. Establish `hm : Measurable fun κ : Mt k r => ENNReal.ofReal (vHalf k r (x * Matrix.of κ))` using `meas_v hk (continuous_const.matrix_mul cont_of)`.

Establish `hm2 : Measurable fun κ : Mt k r => ENNReal.ofReal (vHalf k r (x * (Matrix.of κ * κ₀)))` using `meas_v hk (continuous_const.matrix_mul (cont_of.matrix_mul continuous_const))`. Establish `hrm : Measurable (rmulF κ₀ : Mt k r → Mt k r)` using `Continuous.measurable (by unfold Formalism.FourierDecayAlt.B.rmulF; exact continuous_id.matrix_mul continuous_const)`. Establish `h1 : XiE k r μK x = ∫⁻ κ : Mt k r, ENNReal.ofReal (vHalf k r (x * (Matrix.of κ * κ₀))) ∂μK`. Unfold `XiE`. Use `conv_lhs => rw [← hμ.1.right κ₀ hκ₀]`.

Rewrite using `[lintegral_map hm hrm]`. Both sides reduce to the same expression. Rewrite using `[h1, ← lintegral_mul_const _ hm2, hl κ₀ hκ₀ p]`. Use `lintegral_congr_ae (hae.mono fun κ hκ => ?_)` and prove the remaining obligations. Establish `hmem : x * (Matrix.of κ * κ₀) ∈ GV k r` using `gv_mul hx (gv_mul hκ.1 hκ₀.1)`.

Establish `e : x * Matrix.of κ * (κ₀ * p) = x * (Matrix.of κ * κ₀) * p`. Simplify using `only [Matrix.mul_assoc]`. Use `show ENNReal.ofReal _ = ENNReal.ofReal _ * ENNReal.ofReal _`. Rewrite using `[e, hr _ hmem p hp, ENNReal.ofReal_mul (hpos _ hmem).le]`.
-/
lemma inner {k r : ℕ} (μK : Measure (Mt k r)) (hk : 1 ≤ k) (hμ : IsKMeas k r μK) {x : Mat k r} (hx : x ∈ GV k r)
    {g : Mat k r} (hg : g ∈ GV k r) :
    (∫⁻ κ : Mt k r, ENNReal.ofReal (vHalf k r (x * Matrix.of κ * g)) ∂μK)
      = XiE k r μK x * ENNReal.ofReal (vHalf k r g) := by
  obtain ⟨κ₀, hκ₀, p, hp, rfl⟩ := GlobalTheory.T.exists_mem_Kset_mul_mem_Pset_eq k r hk g hg
  obtain ⟨hl, hr⟩ := GlobalTheory.T.half_volume_equivariant k r hk
  have hpos := (GlobalTheory.T.gram_positive_volume_continuous k r hk).2.1
  have hae : ∀ᵐ κ ∂μK, (Matrix.of κ : Mat k r) ∈ Kset k r := hμ.1.conc
  have hm : Measurable fun κ : Mt k r => ENNReal.ofReal (vHalf k r (x * Matrix.of κ)) :=
    meas_v hk (continuous_const.matrix_mul cont_of)
  have hm2 : Measurable fun κ : Mt k r => ENNReal.ofReal (vHalf k r (x * (Matrix.of κ * κ₀))) :=
    meas_v hk (continuous_const.matrix_mul (cont_of.matrix_mul continuous_const))
  have hrm : Measurable (rmulF κ₀ : Mt k r → Mt k r) :=
    Continuous.measurable (by unfold Formalism.FourierDecayAlt.B.rmulF; exact continuous_id.matrix_mul continuous_const)
  have h1 : XiE k r μK x = ∫⁻ κ : Mt k r, ENNReal.ofReal (vHalf k r (x * (Matrix.of κ * κ₀))) ∂μK := by
    unfold XiE
    conv_lhs => rw [← hμ.1.right κ₀ hκ₀]
    rw [lintegral_map hm hrm]
    rfl
  rw [h1, ← lintegral_mul_const _ hm2, hl κ₀ hκ₀ p]
  refine lintegral_congr_ae (hae.mono fun κ hκ => ?_)
  have hmem : x * (Matrix.of κ * κ₀) ∈ GV k r := gv_mul hx (gv_mul hκ.1 hκ₀.1)
  have e : x * Matrix.of κ * (κ₀ * p) = x * (Matrix.of κ * κ₀) * p := by
    simp only [Matrix.mul_assoc]
  show ENNReal.ofReal _ = ENNReal.ofReal _ * ENNReal.ofReal _
  rw [e, hr _ hmem p hp, ENNReal.ofReal_mul (hpos _ hmem).le]

end GlobalTheory.HCXi.Funct
