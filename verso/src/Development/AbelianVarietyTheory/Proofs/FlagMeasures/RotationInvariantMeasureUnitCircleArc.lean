import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlkExt

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate NNReal

noncomputable section

namespace GlobalTheory.CircleArc

local instance factTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

def par (x : AddCircle (2 * Real.pi)) : ℂ := (AddCircle.toCircle x : Circle)

/- English proof (translation)
The claim follows from `continuous_subtype_val.comp AddCircle.continuous_toCircle`.
-/
theorem continuous_par : Continuous par :=
  continuous_subtype_val.comp AddCircle.continuous_toCircle

/- English proof (translation)
Introduce `_ _ h` and use `AddCircle.injective_toCircle Real.two_pi_pos.ne' (Circle.ext h)`.
-/
theorem par_injective : Function.Injective par := fun _ _ h =>
  AddCircle.injective_toCircle Real.two_pi_pos.ne' (Circle.ext h)

/- English proof (translation)
Rewrite using `[par, AddCircle.toCircle_apply_mk, div_self Real.two_pi_pos.ne', one_mul, Circle.coe_exp]`.
-/
theorem par_coe (s : ℝ) : par (s : AddCircle (2 * Real.pi)) = Complex.exp (s * Complex.I) := by
  rw [par, AddCircle.toCircle_apply_mk, div_self Real.two_pi_pos.ne', one_mul, Circle.coe_exp]

/- English proof (translation)
Rewrite using `[par, AddCircle.toCircle_add, Circle.coe_mul]`. Both sides reduce to the same expression.
-/
theorem par_add (x y) : par (x + y) = par x * par y := by
  rw [par, AddCircle.toCircle_add, Circle.coe_mul]; rfl

/- English proof (translation)
The claim follows from `Circle.norm_coe _`.
-/
theorem norm_par (x) : ‖par x‖ = 1 := Circle.norm_coe _

/- English proof (translation)
Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Conclude with `norm_par x`. Introduce `hz`.

Use `⟨(z.arg : ℝ), ?_⟩` and prove the remaining obligations. Rewrite using `[par_coe]`. Use `Complex.norm_mul_exp_arg_mul_I z` as an intermediate fact. Rewrite `this` using `[show ‖z‖ = 1 from hz]`. Simplify using `using this`.
-/
theorem range_par : Set.range par = {z | ‖z‖ = 1} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact norm_par x
  · intro hz
    refine ⟨(z.arg : ℝ), ?_⟩
    rw [par_coe]
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [show ‖z‖ = 1 from hz] at this
    simpa using this

/- English proof (translation)
Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Rewrite `hx` using `[mem_ball_zero_iff, QuotientAddGroup.norm_lt_iff]`. Take `⟨s, rfl, hs⟩` from `hx`.

Conclude with `⟨s, mem_ball_zero_iff.2 hs, (par_coe s).symm⟩`. Introduce and unpack `⟨s, hs, rfl⟩`. Use `⟨s, ?_, par_coe s⟩` and prove the remaining obligations. Rewrite using `[mem_ball_zero_iff, QuotientAddGroup.norm_lt_iff]`. Conclude with `⟨s, rfl, mem_ball_zero_iff.1 hs⟩`.
-/
theorem image_ball (r : ℝ) :
    par '' Metric.ball 0 r = (fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Metric.ball 0 r := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_ball_zero_iff, QuotientAddGroup.norm_lt_iff] at hx
    obtain ⟨s, rfl, hs⟩ := hx
    exact ⟨s, mem_ball_zero_iff.2 hs, (par_coe s).symm⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, ?_, par_coe s⟩
    rw [mem_ball_zero_iff, QuotientAddGroup.norm_lt_iff]
    exact ⟨s, rfl, mem_ball_zero_iff.1 hs⟩

/- English proof (translation)
Introduce `τ ρ hfin hsupp hinv hρ hρπ`. Use `haveI : IsFiniteMeasure τ := ⟨hfin⟩`. Establish `hm : MeasurableEmbedding par` using `(continuous_par.isClosedEmbedding par_injective).measurableEmbedding`. Use `set ν : Measure (AddCircle (2 * Real.pi)) := τ.comap par with hν`. Establish `hνa : ∀ S, ν S = τ (par '' S)` using `fun S => hm.comap_apply τ S`.

Use `haveI : IsFiniteMeasure ν := ⟨by rw [hνa]; exact measure_lt_top _ _⟩`. Use `haveI : ν.IsAddLeftInvariant := by`. Prove the components needed by the constructor for the conclusion. Introduce `a`. Use extensionality with `S hS`.

Rewrite using `[Measure.map_apply (measurable_const_add a) hS, hνa, hνa]`. Use `conv_rhs => rw [← hinv (par a) (norm_par a)]`. Rewrite using `[Measure.map_apply (measurable_const_mul _) (hm.measurableSet_image.2 hS)]`. Use `congr 1`. Use extensionality with `z`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨a + x, hx, par_add a x⟩`. Introduce and unpack `⟨y, hy, h⟩`. Use `⟨-a + y, by simpa using hy, ?_⟩` and prove the remaining obligations.

Establish `h0 : par a ≠ 0`. Introduce `h0`. Use `norm_par a` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `at this`.

Apply `mul_left_cancel₀ h0` to reduce the goal to its premises. Rewrite using `[← par_add, add_neg_cancel_left]`. Conclude with `h`. Take `⟨t, ht⟩ : ∃ t : ℝ≥0, ν = t • (volume : Measure (AddCircle (2 * Real.pi)))` from `⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩`. Establish `hu : τ Set.univ = t * ENNReal.ofReal (2 * Real.pi)`.

Establish `h1` using `hνa Set.univ`. Rewrite `h1` using `[ht, Measure.smul_apply, AddCircle.measure_univ, Set.image_univ, range_par, ENNReal.smul_def, smul_eq_mul]`. Rewrite using `[h1]`. Apply `measure_congr` to reduce the goal to its premises. Conclude with `(ae_eq_univ.2 hsupp).symm`.

Rewrite using `[← image_ball, ← hνa, hu, ht, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ← measure_congr AddCircle.closedBall_ae_eq_ball, AddCircle.volume_closedBall, min_eq_right (by linarith), mul_assoc, ← ENNReal.ofReal_mul Real.two_pi_pos.le]`. Use `congr 2`. Use `Real.pi_pos` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem measure_arc : ∀ (τ : Measure ℂ) (ρ : ℝ), τ Set.univ < ⊤ → τ {z | ‖z‖ ≠ 1} = 0 →
    (∀ u : ℂ, ‖u‖ = 1 → τ.map (fun z => u * z) = τ) → 0 < ρ → ρ ≤ Real.pi →
    τ ((fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Metric.ball 0 ρ) =
      τ Set.univ * ENNReal.ofReal (ρ / Real.pi) := by
  intro τ ρ hfin hsupp hinv hρ hρπ
  haveI : IsFiniteMeasure τ := ⟨hfin⟩
  have hm : MeasurableEmbedding par :=
    (continuous_par.isClosedEmbedding par_injective).measurableEmbedding
  set ν : Measure (AddCircle (2 * Real.pi)) := τ.comap par with hν
  have hνa : ∀ S, ν S = τ (par '' S) := fun S => hm.comap_apply τ S
  haveI : IsFiniteMeasure ν := ⟨by rw [hνa]; exact measure_lt_top _ _⟩
  haveI : ν.IsAddLeftInvariant := by
    constructor
    intro a
    ext S hS
    rw [Measure.map_apply (measurable_const_add a) hS, hνa, hνa]
    conv_rhs => rw [← hinv (par a) (norm_par a)]
    rw [Measure.map_apply (measurable_const_mul _) (hm.measurableSet_image.2 hS)]
    congr 1
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨a + x, hx, par_add a x⟩
    · rintro ⟨y, hy, h⟩
      refine ⟨-a + y, by simpa using hy, ?_⟩
      have h0 : par a ≠ 0 := by
        intro h0
        have := norm_par a
        rw [h0] at this
        simp at this
      apply mul_left_cancel₀ h0
      rw [← par_add, add_neg_cancel_left]
      exact h
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, ν = t • (volume : Measure (AddCircle (2 * Real.pi))) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩
  have hu : τ Set.univ = t * ENNReal.ofReal (2 * Real.pi) := by
    have h1 := hνa Set.univ
    rw [ht, Measure.smul_apply, AddCircle.measure_univ, Set.image_univ, range_par,
      ENNReal.smul_def, smul_eq_mul] at h1
    rw [h1]
    apply measure_congr
    exact (ae_eq_univ.2 hsupp).symm
  rw [← image_ball, ← hνa, hu, ht, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    ← measure_congr AddCircle.closedBall_ae_eq_ball, AddCircle.volume_closedBall,
    min_eq_right (by linarith), mul_assoc, ← ENNReal.ofReal_mul Real.two_pi_pos.le]
  congr 2
  have := Real.pi_pos
  field_simp

end GlobalTheory.CircleArc
