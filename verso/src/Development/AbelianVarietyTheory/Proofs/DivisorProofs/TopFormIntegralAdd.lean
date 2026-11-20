import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GluedChartDensityMeasureAddOfCompatibleOn

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

/- English proof (translation)
Establish `key : glueMeas e ρ ≤ glueMeas e ρ'`. Use `iSup_mono fun i => Measure.le_iff.2 fun B hB => ?_` and prove the remaining obligations. Rewrite using `[chartMeas_apply _ _ hB, chartMeas_apply _ _ hB]`. Conclude with `lintegral_mono fun v => h i _`. Conclude with `Measure.le_iff.1 key S hS`.
-/
private theorem glue_mono {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : κ → OpenPartialHomeomorph Y (V n)) {S : Set Y} (hS : MeasurableSet S) {ρ ρ' : κ → Y → ℝ≥0∞}
    (h : ∀ i y, ρ i y ≤ ρ' i y) : glueMeas e ρ S ≤ glueMeas e ρ' S := by
  have key : glueMeas e ρ ≤ glueMeas e ρ' := by
    refine iSup_mono fun i => Measure.le_iff.2 fun B hB => ?_
    rw [chartMeas_apply _ _ hB, chartMeas_apply _ _ hB]
    exact lintegral_mono fun v => h i _
  exact Measure.le_iff.1 key S hS

/- English proof (translation)
Establish `hm : ∀ v : ℝ, ENNReal.ofReal v = ENNReal.ofReal (max v 0)` using `fun v => by`. Break down `le_total v 0 with h | h` into its components or cases. Rewrite using `[max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]`. Rewrite using `[max_eq_left h]`. Establish `conv : ∀ x y z : ℝ, ENNReal.ofReal x + (ENNReal.ofReal y + ENNReal.ofReal z) = ENNReal.ofReal (max x 0 + (max y 0 + max z 0))` using `fun x y z => by`.

Rewrite using `[ENNReal.ofReal_add (le_max_right _ _) (add_nonneg (le_max_right _ _) (le_max_right _ _)), ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _), ← hm, ← hm, ← hm]`. Establish `hs : ∀ v : ℝ, max (1 * v) 0 - max (-1 * v) 0 = v` using `fun v => by`. Break down `le_total v 0 with h | h` into its components or cases. Rewrite using `[max_eq_right (by linarith), max_eq_left (by linarith)]; ring`. Rewrite using `[max_eq_left (by linarith), max_eq_right (by linarith)]; ring`.

Rewrite using `[conv, conv]`. Use `congr 1`. Combine the linear relations using `[hs a, hs b, hs (a + b)]`.
-/
private theorem ofReal_balance (a b : ℝ) :
    ENNReal.ofReal (1 * (a + b)) + (ENNReal.ofReal (-1 * a) + ENNReal.ofReal (-1 * b)) =
      ENNReal.ofReal (-1 * (a + b)) + (ENNReal.ofReal (1 * a) + ENNReal.ofReal (1 * b)) := by
  have hm : ∀ v : ℝ, ENNReal.ofReal v = ENNReal.ofReal (max v 0) := fun v => by
    rcases le_total v 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
    · rw [max_eq_left h]
  have conv : ∀ x y z : ℝ, ENNReal.ofReal x + (ENNReal.ofReal y + ENNReal.ofReal z) =
      ENNReal.ofReal (max x 0 + (max y 0 + max z 0)) := fun x y z => by
    rw [ENNReal.ofReal_add (le_max_right _ _) (add_nonneg (le_max_right _ _) (le_max_right _ _)),
      ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _), ← hm, ← hm, ← hm]
  have hs : ∀ v : ℝ, max (1 * v) 0 - max (-1 * v) 0 = v := fun v => by
    rcases le_total v 0 with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  rw [conv, conv]
  congr 1
  linarith [hs a, hs b, hs (a + b)]

/- English proof (translation)
Introduce `n Y κ _ _ _ _ e hd hcov S hS d d' s t hf hf' hi hi'`. Establish `hsum : IsTopForm e (fun i y => d i y + d' i y) S` using `⟨fun i j y hy h1 h2 => by rw [hf.trans i j y hy h1 h2, hf'.trans i j y hy h1 h2, mul_add], fun i => (hf.meas i).add (hf'.meas i)⟩`. Establish `comp : ∀ {f : κ → Y → ℝ}, IsTopForm e f S → ∀ (c : ℝ) i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source → ENNReal.ofReal (c * f i y) = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ENNReal.ofReal (c * f j y)`. Introduce `f h c i j y hy h1 h2`. Rewrite using `[h.trans i j y hy h1 h2, mul_left_comm, ENNReal.ofReal_mul (by positivity)]`.

Establish `meas : ∀ {f : κ → Y → ℝ}, IsTopForm e f S → ∀ (c : ℝ) i, AEMeasurable (fun v => ENNReal.ofReal (c * f i ((e i).symm v))) (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S))` using `fun h c i => ENNReal.measurable_ofReal.comp_aemeasurable ((h.meas i).const_mul c)`. Establish `h2 : ∀ c : ℝ, glueMeas e (fun i y => ENNReal.ofReal (c * d i y) + ENNReal.ofReal (c * d' i y)) S = glueMeas e (fun i y => ENNReal.ofReal (c * d i y)) S + glueMeas e (fun i y => ENNReal.ofReal (c * d' i y)) S` using `fun c => glueMeas_add_of_compat_on e hd hcov hS _ _ (comp hf c) (comp hf' c) (meas hf c)`. Establish `h3 : ∀ c c' : ℝ, glueMeas e (fun i y => ENNReal.ofReal (c * (d i y + d' i y)) + (ENNReal.ofReal (c' * d i y) + ENNReal.ofReal (c' * d' i y))) S = glueMeas e (fun i y => ENNReal.ofReal (c * (d i y + d' i y))) S + (glueMeas e (fun i y => ENNReal.ofReal (c' * d i y)) S + glueMeas e …` using `fun c c' => by`. Rewrite using `[← h2]`. Use `glueMeas_add_of_compat_on e hd hcov hS _ _ (comp hsum c) ?_ (meas hsum c)` and prove the remaining obligations.

Introduce `i j y hy h1 h2`. Rewrite using `[comp hf c' i j y hy h1 h2, comp hf' c' i j y hy h1 h2, mul_add]`. Establish `hfin : ∀ ε : ℤˣ, glueMeas e (fun i y => ENNReal.ofReal (((ε : ℤ) : ℝ) * (d i y + d' i y))) S ≠ ⊤`. Introduce `ε`. Use `ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hi.1 ε, hi'.1 ε⟩) ?_` and prove the remaining obligations.

Rewrite using `[← h2]`. Use `glue_mono e hS fun i y => ?_` and prove the remaining obligations. Rewrite using `[mul_add]`. Conclude with `ENNReal.ofReal_add_le`. Use `⟨hfin, ?_⟩` and prove the remaining obligations.

Establish `hbal` using `h3 1 (-1)`. Simplify using `only [ofReal_balance] at hbal`. Rewrite `hbal` using `[h3]`. Establish `a1` using `hfin 1`. Establish `a2` using `hfin (-1)`.

Establish `b1` using `hi.1 1`. Establish `b2` using `hi.1 (-1)`. Establish `c1` using `hi'.1 1`. Establish `c2` using `hi'.1 (-1)`. Establish `e1` using `hi.2`.

Establish `e2` using `hi'.2`. Simplify using `only [measureReal_def, Units.val_one, Int.cast_one, Units.val_neg, Int.cast_neg] at a1 a2 b1 b2 c1 c2 e1 e2 ⊢`. Establish `hr` using `congrArg ENNReal.toReal hbal`. Rewrite `hr` using `[ENNReal.toReal_add a2 (ENNReal.add_ne_top.2 ⟨b1, c1⟩), ENNReal.toReal_add b1 c1, ENNReal.toReal_add a1 (ENNReal.add_ne_top.2 ⟨b2, c2⟩), ENNReal.toReal_add b2 c2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hasInt_add : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {d d' : κ → Y → ℝ} {s t : ℝ}, IsTopForm e d S → IsTopForm e d' S → HasInt e d S s → HasInt e d' S t → HasInt e (fun i y => d i y + d' i y) S (s + t) := by
  intro n Y κ _ _ _ _ e hd hcov S hS d d' s t hf hf' hi hi'
  have hsum : IsTopForm e (fun i y => d i y + d' i y) S :=
    ⟨fun i j y hy h1 h2 => by rw [hf.trans i j y hy h1 h2, hf'.trans i j y hy h1 h2, mul_add],
      fun i => (hf.meas i).add (hf'.meas i)⟩
  have comp : ∀ {f : κ → Y → ℝ}, IsTopForm e f S → ∀ (c : ℝ) i j y, y ∈ S → y ∈ (e i).source →
      y ∈ (e j).source → ENNReal.ofReal (c * f i y) =
        ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ENNReal.ofReal (c * f j y) := by
    intro f h c i j y hy h1 h2
    rw [h.trans i j y hy h1 h2, mul_left_comm, ENNReal.ofReal_mul (by positivity)]
  have meas : ∀ {f : κ → Y → ℝ}, IsTopForm e f S → ∀ (c : ℝ) i,
      AEMeasurable (fun v => ENNReal.ofReal (c * f i ((e i).symm v)))
        (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S)) := fun h c i =>
    ENNReal.measurable_ofReal.comp_aemeasurable ((h.meas i).const_mul c)
  have h2 : ∀ c : ℝ, glueMeas e (fun i y => ENNReal.ofReal (c * d i y) + ENNReal.ofReal (c * d' i y)) S =
      glueMeas e (fun i y => ENNReal.ofReal (c * d i y)) S +
        glueMeas e (fun i y => ENNReal.ofReal (c * d' i y)) S := fun c =>
    glueMeas_add_of_compat_on e hd hcov hS _ _ (comp hf c) (comp hf' c) (meas hf c)
  have h3 : ∀ c c' : ℝ, glueMeas e (fun i y => ENNReal.ofReal (c * (d i y + d' i y)) +
      (ENNReal.ofReal (c' * d i y) + ENNReal.ofReal (c' * d' i y))) S =
      glueMeas e (fun i y => ENNReal.ofReal (c * (d i y + d' i y))) S +
        (glueMeas e (fun i y => ENNReal.ofReal (c' * d i y)) S +
          glueMeas e (fun i y => ENNReal.ofReal (c' * d' i y)) S) := fun c c' => by
    rw [← h2]
    refine glueMeas_add_of_compat_on e hd hcov hS _ _ (comp hsum c) ?_ (meas hsum c)
    intro i j y hy h1 h2
    rw [comp hf c' i j y hy h1 h2, comp hf' c' i j y hy h1 h2, mul_add]
  have hfin : ∀ ε : ℤˣ,
      glueMeas e (fun i y => ENNReal.ofReal (((ε : ℤ) : ℝ) * (d i y + d' i y))) S ≠ ⊤ := by
    intro ε
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hi.1 ε, hi'.1 ε⟩) ?_
    rw [← h2]
    refine glue_mono e hS fun i y => ?_
    rw [mul_add]
    exact ENNReal.ofReal_add_le
  refine ⟨hfin, ?_⟩
  have hbal := h3 1 (-1)
  simp only [ofReal_balance] at hbal
  rw [h3] at hbal
  have a1 := hfin 1
  have a2 := hfin (-1)
  have b1 := hi.1 1
  have b2 := hi.1 (-1)
  have c1 := hi'.1 1
  have c2 := hi'.1 (-1)
  have e1 := hi.2
  have e2 := hi'.2
  simp only [measureReal_def, Units.val_one, Int.cast_one, Units.val_neg, Int.cast_neg] at a1 a2 b1 b2 c1 c2 e1 e2 ⊢
  have hr := congrArg ENNReal.toReal hbal
  rw [ENNReal.toReal_add a2 (ENNReal.add_ne_top.2 ⟨b1, c1⟩), ENNReal.toReal_add b1 c1,
    ENNReal.toReal_add a1 (ENNReal.add_ne_top.2 ⟨b2, c2⟩), ENNReal.toReal_add b2 c2] at hr
  linarith

end GlobalTheory.GoodTop
