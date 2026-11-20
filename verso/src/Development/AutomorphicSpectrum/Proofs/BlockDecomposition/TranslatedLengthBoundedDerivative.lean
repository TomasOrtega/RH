import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

variable {n : ℕ}

def lmulCLM (a : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => a * y
      map_add' := mul_add a
      map_smul' := fun r y => by simp }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lmulCLM_apply (a y : Mat n) : lmulCLM a y = a * y := rfl

/- English proof (translation)
Establish `hxu : IsUnit x.det` using `isUnit_iff_ne_zero.2 hx`. Establish `h1 : IsUnit (x⁻¹).det` using `Matrix.isUnit_nonsing_inv_det x hxu`. Use `show (x⁻¹ * y).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero h1.ne_zero hy`.
-/
theorem inv_mul_mem_GLs {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x⁻¹ * y ∈ GLs n := by
  have hxu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have h1 : IsUnit (x⁻¹).det := Matrix.isUnit_nonsing_inv_det x hxu
  show (x⁻¹ * y).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero h1.ne_zero hy

/- English proof (translation)
Introduce `hL n`. Take `⟨-, -, -, hsm, hcpt, -, C₀, hC₀⟩` from `hL n`. Use `⟨2 * |C₀|, by positivity, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hxu : IsUnit x.det` using `isUnit_iff_ne_zero.2 hx`. Establish `hsm' : ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n)` using `hsm.comp (lmulCLM x⁻¹).contDiff.contDiffOn (fun y hy => inv_mul_mem_GLs hx hy)`.

Use `⟨hsm', fun R => ?_, fun y hy p => ?_⟩` and prove the remaining obligations. Establish `hxU : IsUnit x` using `(Matrix.isUnit_iff_isUnit_det x).2 hxu`. Set `X : G n` to `hxU.unit`. Establish `hXv : (X : Mat n) = x` using `rfl`. Establish `hXi : ((X⁻¹ : G n) : Mat n) = x⁻¹`.

Rewrite using `[Matrix.coe_units_inv, hXv]`. Establish `hset : {y : G n | lg (x⁻¹ * y.val) ≤ R} = (fun z : G n => X * z) '' {z : G n | lg z.val ≤ R}`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Use `⟨X⁻¹ * y, ?_, by simp⟩` and prove the remaining obligations. Use `show lg ((X⁻¹ * y : G n) : Mat n) ≤ R`. Rewrite using `[Units.val_mul, hXi]`. Conclude with `hy`. Introduce and unpack `⟨z, hz, rfl⟩ show lg (x⁻¹ * ((X * z : G n) : Mat n)) ≤ R`.

Rewrite using `[Units.val_mul, ← hXi, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]`. Conclude with `hz`. Rewrite using `[hset]`. Conclude with `(hcpt R).image (continuous_const.mul continuous_id)`. Establish `hw : x⁻¹ * y ∈ GLs n` using `inv_mul_mem_GLs hx hy`.

Establish `hdiff : DifferentiableAt ℝ lg (x⁻¹ * y)` using `(hsm.contDiffAt (isOpen_GLs.mem_nhds hw)).differentiableAt (by simp)`. Establish `hder : fderiv ℝ (fun y : Mat n => lg (x⁻¹ * y)) y = (fderiv ℝ lg (x⁻¹ * y)).comp (lmulCLM x⁻¹)` using `((hdiff.hasFDerivAt).comp y (lmulCLM x⁻¹).hasFDerivAt).fderiv`. Establish `hCle : C₀ ≤ |C₀|` using `le_abs_self C₀`. Rewrite using `[hder, ContinuousLinearMap.comp_apply, lmulCLM_apply, ← mul_assoc]`. Take `⟨b, i, j⟩` from `p`.

Establish `h1` using `abs_le.1 (hC₀ _ hw (b, i, j))`. Establish `h2` using `abs_le.1 (hC₀ _ hw (b, j, i))`. Consider the cases of `b`. Establish `e : hm ((false, i, j) : Ix n) = bs (false, i, j) - bs (false, j, i)`. Simplify using `[hm, bs]`.

Rewrite using `[e, mul_sub, map_sub, abs_le]`. Apply the tactic sequence `constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]`. Establish `e : hm ((true, i, j) : Ix n) = bs (true, i, j) + bs (true, j, i)`. Simplify using `[hm, bs]`. Rewrite using `[e, mul_add, map_add, abs_le]`.

Apply the tactic sequence `constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]`.
-/
theorem lg_left_facts : LgFacts → ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ GLs n,
    ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) ∧
    (∀ R : ℝ, IsCompact {y : G n | lg (x⁻¹ * y.val) ≤ R}) ∧
    ∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ (fun y : Mat n => lg (x⁻¹ * y)) y (y * hm p)| ≤ C := by
  intro hL n
  obtain ⟨-, -, -, hsm, hcpt, -, C₀, hC₀⟩ := hL n
  refine ⟨2 * |C₀|, by positivity, fun x hx => ?_⟩
  have hxu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have hsm' : ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) :=
    hsm.comp (lmulCLM x⁻¹).contDiff.contDiffOn (fun y hy => inv_mul_mem_GLs hx hy)
  refine ⟨hsm', fun R => ?_, fun y hy p => ?_⟩
  · have hxU : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 hxu
    let X : G n := hxU.unit
    have hXv : (X : Mat n) = x := rfl
    have hXi : ((X⁻¹ : G n) : Mat n) = x⁻¹ := by
      rw [Matrix.coe_units_inv, hXv]
    have hset : {y : G n | lg (x⁻¹ * y.val) ≤ R} = (fun z : G n => X * z) '' {z : G n | lg z.val ≤ R} := by
      ext y
      constructor
      · intro hy
        refine ⟨X⁻¹ * y, ?_, by simp⟩
        show lg ((X⁻¹ * y : G n) : Mat n) ≤ R
        rw [Units.val_mul, hXi]
        exact hy
      · rintro ⟨z, hz, rfl⟩
        show lg (x⁻¹ * ((X * z : G n) : Mat n)) ≤ R
        rw [Units.val_mul, ← hXi, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
        exact hz
    rw [hset]
    exact (hcpt R).image (continuous_const.mul continuous_id)
  · have hw : x⁻¹ * y ∈ GLs n := inv_mul_mem_GLs hx hy
    have hdiff : DifferentiableAt ℝ lg (x⁻¹ * y) :=
      (hsm.contDiffAt (isOpen_GLs.mem_nhds hw)).differentiableAt (by simp)
    have hder : fderiv ℝ (fun y : Mat n => lg (x⁻¹ * y)) y
        = (fderiv ℝ lg (x⁻¹ * y)).comp (lmulCLM x⁻¹) :=
      ((hdiff.hasFDerivAt).comp y (lmulCLM x⁻¹).hasFDerivAt).fderiv
    have hCle : C₀ ≤ |C₀| := le_abs_self C₀
    rw [hder, ContinuousLinearMap.comp_apply, lmulCLM_apply, ← mul_assoc]
    obtain ⟨b, i, j⟩ := p
    have h1 := abs_le.1 (hC₀ _ hw (b, i, j))
    have h2 := abs_le.1 (hC₀ _ hw (b, j, i))
    cases b
    · have e : hm ((false, i, j) : Ix n) = bs (false, i, j) - bs (false, j, i) := by
        simp [hm, bs]
      rw [e, mul_sub, map_sub, abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · have e : hm ((true, i, j) : Ix n) = bs (true, i, j) + bs (true, j, i) := by
        simp [hm, bs]
      rw [e, mul_add, map_add, abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end GlobalTheory.CompanionTheory.WaveSpd
