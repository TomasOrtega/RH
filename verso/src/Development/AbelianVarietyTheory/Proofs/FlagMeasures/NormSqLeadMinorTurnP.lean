import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
open Formalism.QuantumDeterminants Formalism.MainNotions.S.ThB MeasureTheory Matrix

noncomputable section

namespace GlobalTheory.FrameTurn

section Conj

variable {m : ℕ}

def cj (d : Fin m → ℂ) (g : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  diagonal (star d) * g * diagonal d

/- English proof (translation)
Simplify using `[cj, Matrix.mul_diagonal, Matrix.diagonal_mul]`.
-/
theorem cj_apply (d : Fin m → ℂ) (g : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
    cj d g i j = star (d i) * g i j * d j := by
  simp [cj, Matrix.mul_diagonal, Matrix.diagonal_mul]

def Uni (d : Fin m → ℂ) : Prop := ∀ i, star (d i) * d i = 1

/- English proof (translation)
Introduce `i` and use `by have := h i simp only [Pi.star_apply, star_star] rw [mul_comm]; exact this`.
-/
theorem Uni.st {d : Fin m → ℂ} (h : Uni d) : Uni (star d) := fun i => by
  have := h i
  simp only [Pi.star_apply, star_star]
  rw [mul_comm]; exact this

/- English proof (translation)
Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `h i`.
-/
theorem Uni.l {d : Fin m → ℂ} (h : Uni d) : diagonal (star d) * diagonal d = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; exact h i

/- English proof (translation)
Use `h.st.l` as an intermediate fact. Rewrite `this` using `[star_star]`. Then use the resulting hypothesis.
-/
theorem Uni.r {d : Fin m → ℂ} (h : Uni d) : diagonal d * diagonal (star d) = 1 := by
  have := h.st.l
  rwa [star_star] at this

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv h.l`.
-/
theorem Uni.inv {d : Fin m → ℂ} (h : Uni d) : (diagonal d)⁻¹ = diagonal (star d) :=
  Matrix.inv_eq_left_inv h.l

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv h.r`.
-/
theorem Uni.inv' {d : Fin m → ℂ} (h : Uni d) : (diagonal (star d))⁻¹ = diagonal d :=
  Matrix.inv_eq_left_inv h.r

/- English proof (translation)
Establish `h1 : ‖star (d i) * d i‖ = ‖(1 : ℂ)‖` using `by rw [h i]`. Rewrite `h1` using `[norm_mul, norm_star, norm_one]`. Use polynomial arithmetic with `[norm_nonneg (d i)]`.
-/
theorem Uni.nrm {d : Fin m → ℂ} (h : Uni d) (i : Fin m) : ‖d i‖ = 1 := by
  have h1 : ‖star (d i) * d i‖ = ‖(1 : ℂ)‖ := by rw [h i]
  rw [norm_mul, norm_star, norm_one] at h1
  nlinarith [norm_nonneg (d i)]

/- English proof (translation)
Unfold `cj`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h.r]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`.
-/
theorem cj_mul {d : Fin m → ℂ} (h : Uni d) (a b : Matrix (Fin m) (Fin m) ℂ) : cj d (a * b) = cj d a * cj d b := by
  unfold cj
  calc diagonal (star d) * (a * b) * diagonal d
      = diagonal (star d) * a * (diagonal d * diagonal (star d)) * b * diagonal d := by
        rw [h.r]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

/- English proof (translation)
Unfold `cj`. Rewrite using `[Matrix.mul_inv_rev, Matrix.mul_inv_rev, h.inv, h.inv', Matrix.mul_assoc]`.
-/
theorem cj_inv {d : Fin m → ℂ} (h : Uni d) (a : Matrix (Fin m) (Fin m) ℂ) : cj d a⁻¹ = (cj d a)⁻¹ := by
  unfold cj
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, h.inv, h.inv', Matrix.mul_assoc]

/- English proof (translation)
Unfold `cj`. Rewrite using `[star_star]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cj_star_cj {d : Fin m → ℂ} (h : Uni d) (a : Matrix (Fin m) (Fin m) ℂ) : cj (star d) (cj d a) = a := by
  unfold cj
  rw [star_star]
  calc diagonal d * (diagonal (star d) * a * diagonal d) * diagonal (star d)
      = (diagonal d * diagonal (star d)) * a * (diagonal d * diagonal (star d)) := by simp only [Matrix.mul_assoc]
    _ = a := by rw [h.r]; simp

/- English proof (translation)
Use `cj_star_cj h.st a` as an intermediate fact. Rewrite `this` using `[star_star]`. Then use the resulting hypothesis.
-/
theorem cj_cj_star {d : Fin m → ℂ} (h : Uni d) (a : Matrix (Fin m) (Fin m) ℂ) : cj d (cj (star d) a) = a := by
  have := cj_star_cj h.st a
  rwa [star_star] at this

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [conjTranspose_apply, cj_apply, star_mul', star_star]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cj_conjTranspose (d : Fin m → ℂ) (a : Matrix (Fin m) (Fin m) ℂ) : (cj d a)ᴴ = cj d aᴴ := by
  ext i j
  simp only [conjTranspose_apply, cj_apply, star_mul', star_star]
  ring

/- English proof (translation)
Unfold `cj`. Rewrite using `[Matrix.mul_one, h.l]`.
-/
theorem cj_one {d : Fin m → ℂ} (h : Uni d) : cj d 1 = 1 := by
  unfold cj; rw [Matrix.mul_one, h.l]

/- English proof (translation)
Simplify using `only [cj, Matrix.mulVec_mulVec, Matrix.mul_assoc]`.
-/
theorem cj_mulVec (d : Fin m → ℂ) (a : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) :
    cj d a *ᵥ v = diagonal (star d) *ᵥ (a *ᵥ (diagonal d *ᵥ v)) := by
  simp only [cj, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/- English proof (translation)
Rewrite `hg`, the goal using `[Matrix.mem_unitaryGroup_iff']`. Rewrite `hg`, the goal using `[star_eq_conjTranspose]`. Rewrite using `[cj_conjTranspose, ← cj_mul h, hg, cj_one h]`.
-/
theorem cj_mem_unitary {d : Fin m → ℂ} (h : Uni d) {g : Matrix (Fin m) (Fin m) ℂ}
    (hg : g ∈ Matrix.unitaryGroup (Fin m) ℂ) : cj d g ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hg ⊢
  rw [star_eq_conjTranspose] at hg ⊢
  rw [cj_conjTranspose, ← cj_mul h, hg, cj_one h]

/- English proof (translation)
Unfold `cj`. Rewrite using `[← h.inv]`. Conclude with `Matrix.exp_conj' _ _ (IsUnit.of_mul_eq_one _ h.r)`.
-/
theorem cj_exp {d : Fin m → ℂ} (h : Uni d) (X : Matrix (Fin m) (Fin m) ℂ) :
    NormedSpace.exp (cj d X) = cj d (NormedSpace.exp X) := by
  unfold cj
  rw [← h.inv]
  exact Matrix.exp_conj' _ _ (IsUnit.of_mul_eq_one _ h.r)

/- English proof (translation)
Unfold `cj`. Simplify using the standard rewrite rules.
-/
theorem cj_smul (d : Fin m → ℂ) (c : ℂ) (X : Matrix (Fin m) (Fin m) ℂ) : cj d (c • X) = c • cj d X := by
  unfold cj; simp

/- English proof (translation)
Simplify using `only [cj_apply, Matrix.of_apply]`. Use `fun_prop`.
-/
theorem measurable_cj (d : Fin m → ℂ) :
    Measurable (fun x : Fin m → Fin m → ℂ => (fun i j => cj d (Matrix.of x) i j : Fin m → Fin m → ℂ)) := by
  simp only [cj_apply, Matrix.of_apply]
  fun_prop

def cjE {d : Fin m → ℂ} (h : Uni d) : (Fin m → Fin m → ℂ) ≃ᵐ (Fin m → Fin m → ℂ) where
  toFun x := fun i j => cj d (Matrix.of x) i j
  invFun x := fun i j => cj (star d) (Matrix.of x) i j
  left_inv x := cj_star_cj h (Matrix.of x)
  right_inv x := cj_cj_star h (Matrix.of x)
  measurable_toFun := measurable_cj d
  measurable_invFun := measurable_cj (star d)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem of_cjE {d : Fin m → ℂ} (h : Uni d) (x : Fin m → Fin m → ℂ) :
    Matrix.of (cjE h x) = cj d (Matrix.of x) := rfl

def cjR (d : Fin m → ℂ) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun x := (WithLp.equiv 2 _).symm (realifyFun (cj d (unrealify x)))
  map_add' x y := by
    ext ⟨i, j, b⟩
    cases b <;> simp [realifyFun, cj_apply, unrealify] <;> ring
  map_smul' c x := by
    ext ⟨i, j, b⟩
    cases b <;> simp [realifyFun, cj_apply, unrealify] <;> ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[unrealify, realifyFun]`.
-/
theorem unrealify_realify (X : Matrix (Fin m) (Fin m) ℂ) :
    unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  ext i j
  simp [unrealify, realifyFun]

/- English proof (translation)
The claim follows from `unrealify_realify _`.
-/
theorem unrealify_cjR (d : Fin m → ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (cjR d x) = cj d (unrealify x) := unrealify_realify _

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_bool, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]`.

Simplify using `only [unrealify, Real.norm_eq_abs, sq_abs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_sq_unrealify (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    ‖x‖ ^ 2 = ∑ i, ∑ j, ‖unrealify x i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [unrealify, Real.norm_eq_abs, sq_abs]
  ring

/- English proof (translation)
Establish `: ‖cjR d x‖ ^ 2 = ‖x‖ ^ 2`. Rewrite using `[norm_sq_unrealify, norm_sq_unrealify, unrealify_cjR]`. Simplify using `only [cj_apply, norm_mul, norm_star, h.nrm, one_mul, mul_one]`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this`.
-/
theorem norm_cjR {d : Fin m → ℂ} (h : Uni d) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    ‖cjR d x‖ = ‖x‖ := by
  have : ‖cjR d x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_unrealify, norm_sq_unrealify, unrealify_cjR]
    simp only [cj_apply, norm_mul, norm_star, h.nrm, one_mul, mul_one]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/- English proof (translation)
Introduce `x hx`. Establish `: lieE S ≤ (lieE S).comap (cjR d)`. Unfold `lieE`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨X, hX, rfl⟩`.

Use `Submodule.subset_span ⟨cj d X, fun t => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← cj_smul, cj_exp h]`. Conclude with `hS _ (hX t)`. Use `show _ = (WithLp.equiv 2 _).symm (realifyFun (cj d (unrealify _)))`. Rewrite using `[unrealify_realify]`.

Conclude with `this hx`.
-/
theorem cjR_mem {d : Fin m → ℂ} (h : Uni d) {S : Set (Matrix (Fin m) (Fin m) ℂ)} (hS : ∀ g ∈ S, cj d g ∈ S) :
    ∀ x ∈ lieE S, cjR d x ∈ lieE S := by
  intro x hx
  have : lieE S ≤ (lieE S).comap (cjR d) := by
    unfold lieE
    rw [Submodule.span_le]
    rintro _ ⟨X, hX, rfl⟩
    refine Submodule.subset_span ⟨cj d X, fun t => ?_, ?_⟩
    · rw [← cj_smul, cj_exp h]; exact hS _ (hX t)
    · show _ = (WithLp.equiv 2 _).symm (realifyFun (cj d (unrealify _)))
      rw [unrealify_realify]
  exact this hx

end Conj

/- English proof (translation)
Unfold `haarLie`. Rewrite using `[Measure.map_smul]`. Use `congr 1`. Use `set E : lieE S → Mt k r := fun x => fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j with hE`. Distinguish the cases in `hm : AEMeasurable E volume`.

Set `Φ₀ : lieE S →ₗᵢ[ℝ] lieE S` to `⟨(cjR d).restrict (cjR_mem h hS), fun x => norm_cjR h x⟩`. Set `Φ : lieE S ≃ₗᵢ[ℝ] lieE S` to `Φ₀.toLinearIsometryEquiv rfl`. Establish `hΦ` using `Φ.measurePreserving`. Establish `e : (cjE h) ∘ E = E ∘ Φ`. Use function extensionality and compare the values at `x`.

Use `show cj d (NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _))) = NormedSpace.exp (unrealify (cjR d x))`. Rewrite using `[unrealify_cjR, cj_exp h]`. Rewrite using `[AEMeasurable.map_map_of_aemeasurable (cjE h).measurable.aemeasurable hm, e, ← AEMeasurable.map_map_of_aemeasurable (by rwa [hΦ.map_eq]) hΦ.measurable.aemeasurable, hΦ.map_eq]`. Rewrite using `[Measure.map_of_not_aemeasurable hm, Measure.map_zero]`.
-/
theorem haarLie_map_cj {k r : ℕ} {d : Fin (2 * r + k + 1) → ℂ} (h : Uni d) {S : Set (Mx k r)}
    (hS : ∀ g ∈ S, cj d g ∈ S) (κ : ENNReal) : (haarLie S κ).map (cjE h) = haarLie S κ := by
  unfold haarLie
  rw [Measure.map_smul]
  congr 1
  set E : lieE S → Mt k r := fun x => fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j with hE
  by_cases hm : AEMeasurable E volume
  · let Φ₀ : lieE S →ₗᵢ[ℝ] lieE S := ⟨(cjR d).restrict (cjR_mem h hS), fun x => norm_cjR h x⟩
    let Φ : lieE S ≃ₗᵢ[ℝ] lieE S := Φ₀.toLinearIsometryEquiv rfl
    have hΦ := Φ.measurePreserving
    have e : (cjE h) ∘ E = E ∘ Φ := by
      funext x
      show cj d (NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _))) = NormedSpace.exp (unrealify (cjR d x))
      rw [unrealify_cjR, cj_exp h]
    rw [AEMeasurable.map_map_of_aemeasurable (cjE h).measurable.aemeasurable hm, e,
      ← AEMeasurable.map_map_of_aemeasurable (by rwa [hΦ.map_eq]) hΦ.measurable.aemeasurable, hΦ.map_eq]
  · rw [Measure.map_of_not_aemeasurable hm, Measure.map_zero]

section Tor

variable {k r : ℕ}

structure Tor (k r : ℕ) (d : Fin (2 * r + k + 1) → ℂ) : Prop where
  uni : Uni d
  sym : ∀ i j : Fin (2 * r + k + 1), i.val + j.val = 2 * r + k → i.val < r → d i = d j
  mid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → d i = 1

variable {d : Fin (2 * r + k + 1) → ℂ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.uni.st, fun i j a b => by simp only [Pi.star_apply, h.sym i j a b], fun i a b => by simp only [Pi.star_apply, h.mid i a b, star_one]⟩`.
-/
theorem Tor.st (h : Tor k r d) : Tor k r (star d) :=
  ⟨h.uni.st, fun i j a b => by simp only [Pi.star_apply, h.sym i j a b],
    fun i a b => by simp only [Pi.star_apply, h.mid i a b, star_one]⟩

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[cj_apply]`. Unfold `Hpk`. Use `split_ifs with h1 h2 h3 h4`. Rewrite using `[← h.sym i j h1.2 h1.1, mul_one, h.uni i]`.

Rewrite using `[h.sym j i (by omega) h2.1, mul_one, h.uni i]`. Rewrite using `[← h3.2.2, h.mid i h3.1 h3.2.1]`. Simplify using the standard rewrite rules. Rewrite using `[← h3.2.2, h.mid i h3.1 h3.2.1]`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem cj_Hpk (h : Tor k r d) : cj d (Hpk k r) = Hpk k r := by
  ext i j
  rw [cj_apply]
  unfold Hpk
  split_ifs with h1 h2 h3 h4
  · rw [← h.sym i j h1.2 h1.1, mul_one, h.uni i]
  · rw [h.sym j i (by omega) h2.1, mul_one, h.uni i]
  · rw [← h3.2.2, h.mid i h3.1 h3.2.1]; simp
  · rw [← h3.2.2, h.mid i h3.1 h3.2.1]; simp
  · simp

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Use `show (cj d g)ᴴ * Hpk k r * cj d g = Hpk k r`. Rewrite using `[cj_conjTranspose]`. Use `conv_lhs => rw [← cj_Hpk h]`. Rewrite using `[← cj_mul h.uni, ← cj_mul h.uni, hg', cj_Hpk h]`.
-/
theorem cj_mem_UH (h : Tor k r d) {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : cj d g ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  show (cj d g)ᴴ * Hpk k r * cj d g = Hpk k r
  rw [cj_conjTranspose]
  conv_lhs => rw [← cj_Hpk h]
  rw [← cj_mul h.uni, ← cj_mul h.uni, hg', cj_Hpk h]

/- English proof (translation)
Use `⟨cj_mem_UH h hg.1, fun a i hi => ?_, fun i j h1 h2 h3 => ?_⟩` and prove the remaining obligations. Rewrite using `[cj_apply, hg.2.1 a i hi] split_ifs with e`. Rewrite using `[← e, mul_one, h.uni i]`. Simplify using the standard rewrite rules. Rewrite using `[cj_apply, hg.2.2 i j h1 h2 h3] split_ifs with e`.

Rewrite using `[← e, mul_one, h.uni i]`. Simplify using the standard rewrite rules.
-/
theorem cj_mem_N (h : Tor k r d) {g : Mx k r} (hg : g ∈ Nset k r) : cj d g ∈ Nset k r := by
  refine ⟨cj_mem_UH h hg.1, fun a i hi => ?_, fun i j h1 h2 h3 => ?_⟩
  · rw [cj_apply, hg.2.1 a i hi]
    split_ifs with e
    · rw [← e, mul_one, h.uni i]
    · simp
  · rw [cj_apply, hg.2.2 i j h1 h2 h3]
    split_ifs with e
    · rw [← e, mul_one, h.uni i]
    · simp

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[mulVec_diagonal]`. Distinguish the cases in `hi : i.val < r ∨ r + k < i.val`. Rewrite using `[hz i hi, mul_zero]`. Rewrite using `[h.mid i (by omega) (by omega), one_mul]`.
-/
theorem diag_wb (h : Tor k r d) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : diagonal d *ᵥ z = z := by
  funext i
  rw [mulVec_diagonal]
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hz i hi, mul_zero]
  · rw [h.mid i (by omega) (by omega), one_mul]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Rewrite using `[mulVec_diagonal]`. Distinguish the cases in `e : j = i`. Substitute `e` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[bvec, e]`.
-/
theorem diag_bvec {m : ℕ} (d : Fin m → ℂ) (i : Fin m) : diagonal d *ᵥ bvec i = d i • bvec i := by
  funext j
  rw [mulVec_diagonal]
  by_cases e : j = i
  · subst e; simp
  · simp [bvec, e]

/- English proof (translation)
Rewrite using `[cj_mulVec, diag_bvec, mulVec_smul, hg, mulVec_smul, diag_bvec, smul_smul, Pi.star_apply, mul_comm, h i, one_smul]`.
-/
theorem cj_fix {m : ℕ} {d : Fin m → ℂ} (h : Uni d) {g : Matrix (Fin m) (Fin m) ℂ} {i : Fin m}
    (hg : g *ᵥ bvec i = bvec i) : cj d g *ᵥ bvec i = bvec i := by
  rw [cj_mulVec, diag_bvec, mulVec_smul, hg, mulVec_smul, diag_bvec, smul_smul, Pi.star_apply, mul_comm, h i, one_smul]

/- English proof (translation)
Use `⟨cj_mem_UH h hg.1, fun a => ⟨cj_fix h.uni (hg.2.1 a).1, cj_fix h.uni (hg.2.1 a).2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[cj_mulVec, diag_wb h hz, hg.2.2, diag_wb h.st hz]`.
-/
theorem cj_mem_UW (h : Tor k r d) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {g : Mx k r}
    (hg : g ∈ UWset k r z) : cj d g ∈ UWset k r z := by
  refine ⟨cj_mem_UH h hg.1, fun a => ⟨cj_fix h.uni (hg.2.1 a).1, cj_fix h.uni (hg.2.1 a).2⟩, ?_⟩
  rw [cj_mulVec, diag_wb h hz, hg.2.2, diag_wb h.st hz]

/- English proof (translation)
Use `⟨cj_mem_UH h hg.1, fun a => ⟨cj_fix h.uni (hg.2.1 a).1, cj_fix h.uni (hg.2.1 a).2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[cj_mulVec, mulVec_smul, diag_bvec, h.mid (wI k r (Fin.last k)) (by simp [wI]) (by simp [wI]), one_smul, hg.2.2, diag_wb h.st hz]`.
-/
theorem cj_frame (h : Tor k r d) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {g : Mx k r}
    (hg : IsFrameW k r z g) : IsFrameW k r z (cj d g) := by
  refine ⟨cj_mem_UH h hg.1, fun a => ⟨cj_fix h.uni (hg.2.1 a).1, cj_fix h.uni (hg.2.1 a).2⟩, ?_⟩
  rw [cj_mulVec, mulVec_smul, diag_bvec, h.mid (wI k r (Fin.last k)) (by simp [wI]) (by simp [wI]), one_smul, hg.2.2,
    diag_wb h.st hz]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[cj_apply]`. Unfold `blockW`. Use `split_ifs with h1 h2 h3`. Rewrite using `[h.mid i h1.1 (by omega), h.mid j h2.1 (by omega)]; simp`.

Simplify using the standard rewrite rules. Rewrite using `[← h3, mul_one, h.uni i]`. Simplify using the standard rewrite rules.
-/
theorem cj_blockW (h : Tor k r d) (x : Matrix (Fin k) (Fin k) ℂ) : cj d (blockW k r x) = blockW k r x := by
  ext i j
  rw [cj_apply]
  unfold blockW
  split_ifs with h1 h2 h3
  · rw [h.mid i h1.1 (by omega), h.mid j h2.1 (by omega)]; simp
  · simp
  · rw [← h3, mul_one, h.uni i]
  · simp

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[cj_apply]`. Unfold `bigCell`. Use `split_ifs with h1 h2 h3 h4 h5`. Establish `: d j = d i` using `h.sym j i (by rw [h2]; simp only [esI]; omega) h1`.

Rewrite using `[this, mul_right_comm, h.uni i, one_mul]`. Simplify using the standard rewrite rules. Rewrite using `[h.mid i h4.1 h4.2, h.mid j (by omega) h3]; simp`. Simplify using the standard rewrite rules. Establish `: d i = d j` using `h.sym i j (by omega) (by omega)`.

Rewrite using `[← this, mul_right_comm, h.uni i, one_mul]`. Simplify using the standard rewrite rules.
-/
theorem cj_bigCell (h : Tor k r d) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    cj d (bigCell k r c μ) = bigCell k r c μ := by
  ext i j
  rw [cj_apply]
  unfold bigCell
  split_ifs with h1 h2 h3 h4 h5
  · have : d j = d i := h.sym j i (by rw [h2]; simp only [esI]; omega) h1
    rw [this, mul_right_comm, h.uni i, one_mul]
  · simp
  · rw [h.mid i h4.1 h4.2, h.mid j (by omega) h3]; simp
  · simp
  · have : d i = d j := h.sym i j (by omega) (by omega)
    rw [← this, mul_right_comm, h.uni i, one_mul]
  · simp

/- English proof (translation)
Take `⟨g, hg, hU⟩` from `hπ`. Use `⟨cj d g, cj_frame h hz hg, ?_⟩` and prove the remaining obligations. Establish `e : ∀ x, cj (star d) (cj d g * blockW k r x * (cj d g)⁻¹) = g * blockW k r x * g⁻¹` using `fun x => by conv_lhs => rw [← cj_blockW h x]`. Rewrite using `[← cj_inv h.uni, ← cj_mul h.uni, ← cj_mul h.uni, cj_star_cj h.uni]`. Simplify using `only [e]`.

Conclude with `hU`.
-/
theorem isHCTypeW_cj (h : Tor k r d) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {u : Fin k → ℝ} {π : Mx k r → (H →L[ℂ] H)}
    (hπ : IsHCTypeW k r z u π) : IsHCTypeW k r z u (fun g => π (cj (star d) g)) := by
  obtain ⟨g, hg, hU⟩ := hπ
  refine ⟨cj d g, cj_frame h hz hg, ?_⟩
  have e : ∀ x, cj (star d) (cj d g * blockW k r x * (cj d g)⁻¹) = g * blockW k r x * g⁻¹ := fun x => by
    conv_lhs => rw [← cj_blockW h x]
    rw [← cj_inv h.uni, ← cj_mul h.uni, ← cj_mul h.uni, cj_star_cj h.uni]
  simp only [e]
  exact hU

/- English proof (translation)
Take `⟨P, ⟨⟨hP1, hP2⟩, hP3⟩, hD⟩` from `hσ`. Use `⟨P * diagonal d, ⟨⟨hP1.mul (IsUnit.of_mul_eq_one _ h.uni.r), ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Use `cj_Hpk h` as an intermediate fact. Rewrite using `[← this, ← hP2, conjTranspose_mul, diagonal_conjTranspose, cj]`. Simplify using `only [Matrix.mul_assoc]`.

Use `mul_mem hP3 ?_` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose, h.uni.l]`. Establish `e : ∀ g, cj (star d) ((P * diagonal d)⁻¹ * g * (P * diagonal d)) = P⁻¹ * g * P` using `fun g => by conv_rhs => rw [← cj_star_cj h.uni (P⁻¹ * g * P)]`. Use `congr 1`. Rewrite using `[Matrix.mul_inv_rev, h.uni.inv, cj]`.

Simplify using `only [Matrix.mul_assoc]`. Simplify using `only [e]`. Conclude with `hD`.
-/
theorem isDSHpk_cj (h : Tor k r d) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hσ : IsDSHpk k r ε lam σ) : IsDSHpk k r ε lam (fun g => σ (cj (star d) g)) := by
  obtain ⟨P, ⟨⟨hP1, hP2⟩, hP3⟩, hD⟩ := hσ
  refine ⟨P * diagonal d, ⟨⟨hP1.mul (IsUnit.of_mul_eq_one _ h.uni.r), ?_⟩, ?_⟩, ?_⟩
  · have := cj_Hpk h
    rw [← this, ← hP2, conjTranspose_mul, diagonal_conjTranspose, cj]
    simp only [Matrix.mul_assoc]
  · refine mul_mem hP3 ?_
    rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose, h.uni.l]
  · have e : ∀ g, cj (star d) ((P * diagonal d)⁻¹ * g * (P * diagonal d)) = P⁻¹ * g * P := fun g => by
      conv_rhs => rw [← cj_star_cj h.uni (P⁻¹ * g * P)]
      congr 1
      rw [Matrix.mul_inv_rev, h.uni.inv, cj]
      simp only [Matrix.mul_assoc]
    simp only [e]
    exact hD

/- English proof (translation)
Take `⟨S, h1, h2, h3⟩` from `hv`. Conclude with `⟨S, h1, h2, fun g hg x hx => h3 _ ⟨cj_mem_UH h.st hg.1, cj_mem_unitary h.uni.st hg.2⟩ x hx⟩`.
-/
theorem isKFin_cj (h : Tor k r d) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx k r → (H →L[ℂ] H)} {v : H} (hv : IsKFinHpk (k := k) (r := r) σ v) :
    IsKFinHpk (k := k) (r := r) (fun g => σ (cj (star d) g)) v := by
  obtain ⟨S, h1, h2, h3⟩ := hv
  exact ⟨S, h1, h2, fun g hg x hx => h3 _ ⟨cj_mem_UH h.st hg.1, cj_mem_unitary h.uni.st hg.2⟩ x hx⟩

/- English proof (translation)
Use `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Use `show Measurable fun x : Mt k r => (s * Matrix.of x) i j`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`. Use `fun_prop`.
-/
theorem measurable_lmulM (s : Mx k r) : Measurable (lmulM (k := k) (r := r) s) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  show Measurable fun x : Mt k r => (s * Matrix.of x) i j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

/- English proof (translation)
Take `⟨⟨h1, h2, h3, h4⟩, h5⟩` from `hμ`. Establish `hu : (μ.map (cjE h)) Set.univ = 1` using `by rw [MeasurableEquiv.map_apply, Set.preimage_univ, h5]`. Use `⟨⟨(cjE h).sigmaFinite_map, fun e => by simp [e] at hu, ?_, fun s hs => ?_⟩, hu⟩` and prove the remaining obligations. Rewrite using `[MeasurableEquiv.map_apply]`. Conclude with `measure_mono_null (fun x hx hx' => hx (hS _ hx')) h3`.

Establish `e : lmulM s ∘ cjE h = cjE h ∘ lmulM (cj (star d) s)`. Use function extensionality and compare the values at `x`. Use `show s * cj d (Matrix.of x) = cj d (cj (star d) s * Matrix.of x)`. Rewrite using `[cj_mul h, cj_cj_star h]`. Rewrite using `[Measure.map_map (measurable_lmulM s) (cjE h).measurable, e, ← Measure.map_map (cjE h).measurable (measurable_lmulM _), h4 _ (hS' s hs)]`.
-/
theorem isHaarOn_cj (h : Uni d) {S : Set (Mx k r)} (hS : ∀ g ∈ S, cj d g ∈ S) (hS' : ∀ g ∈ S, cj (star d) g ∈ S)
    {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ ∧ μ Set.univ = 1) :
    IsHaarOn S (μ.map (cjE h)) ∧ (μ.map (cjE h)) Set.univ = 1 := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hμ
  have hu : (μ.map (cjE h)) Set.univ = 1 := by rw [MeasurableEquiv.map_apply, Set.preimage_univ, h5]
  refine ⟨⟨(cjE h).sigmaFinite_map, fun e => by simp [e] at hu, ?_, fun s hs => ?_⟩, hu⟩
  · rw [MeasurableEquiv.map_apply]
    exact measure_mono_null (fun x hx hx' => hx (hS _ hx')) h3
  · have e : lmulM s ∘ cjE h = cjE h ∘ lmulM (cj (star d) s) := by
      funext x
      show s * cj d (Matrix.of x) = cj d (cj (star d) s * Matrix.of x)
      rw [cj_mul h, cj_cj_star h]
    rw [Measure.map_map (measurable_lmulM s) (cjE h).measurable, e,
      ← Measure.map_map (cjE h).measurable (measurable_lmulM _), h4 _ (hS' s hs)]

/- English proof (translation)
Unfold `herm`. Establish `e : Hpk k r * diagonal (star d) = diagonal (star d) * Hpk k r` using `by conv_rhs => rw [← cj_Hpk h.st, cj, star_star, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.uni.l, Matrix.one_mul]`. Rewrite using `[mulVec_mulVec, e, ← mulVec_mulVec, star_mulVec, diagonal_conjTranspose, dotProduct_mulVec]`.
-/
theorem herm_diag (h : Tor k r d) (y x : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (diagonal (star d) *ᵥ y) x = herm (Hpk k r) y (diagonal d *ᵥ x) := by
  unfold herm
  have e : Hpk k r * diagonal (star d) = diagonal (star d) * Hpk k r := by
    conv_rhs => rw [← cj_Hpk h.st, cj, star_star, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.uni.l, Matrix.one_mul]
  rw [mulVec_mulVec, e, ← mulVec_mulVec, star_mulVec, diagonal_conjTranspose, dotProduct_mulVec]

end Tor

section Turn

variable {k r : ℕ}

def dT (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := (-Complex.I) ^ ((r - i.val) + (i.val - (r + k)))

/- English proof (translation)
Rewrite using `[star_pow, ← mul_pow]`. Simplify using the standard rewrite rules.
-/
theorem uni_pow (n : ℕ) : star ((-Complex.I) ^ n) * (-Complex.I) ^ n = 1 := by
  rw [star_pow, ← mul_pow]
  simp

/- English proof (translation)
Use `⟨fun i => uni_pow _, fun i j h1 h2 => ?_, fun i h1 h2 => ?_⟩` and prove the remaining obligations. Unfold `dT`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Unfold `dT`.

Establish `: (r - i.val) + (i.val - (r + k)) = 0` using `by omega`. Rewrite using `[this, pow_zero]`.
-/
theorem tor_dT (k r : ℕ) : Tor k r (dT k r) := by
  refine ⟨fun i => uni_pow _, fun i j h1 h2 => ?_, fun i h1 h2 => ?_⟩
  · unfold dT; congr 1; omega
  · unfold dT
    have : (r - i.val) + (i.val - (r + k)) = 0 := by omega
    rw [this, pow_zero]

/- English proof (translation)
Unfold `dT`. Use `congr 1`. Simplify using `only [eI]`. Use linear arithmetic over natural numbers and integers.
-/
theorem dT_eI (a : Fin r) : dT k r (eI k r a) = (-Complex.I) ^ (r - a.val) := by
  unfold dT; congr 1; simp only [eI]; omega

/- English proof (translation)
Unfold `fvec`. Use `split_ifs with h`. Rewrite using `[diag_bvec, dT_eI]`. Establish `: r - a.val = 0` using `by omega`. Rewrite using `[diag_wb (tor_dT k r) hz, this, pow_zero, one_smul]`.
-/
theorem diag_fvec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : Fin (r + 1)) :
    diagonal (dT k r) *ᵥ fvec k r z a = (-Complex.I) ^ (r - a.val) • fvec k r z a := by
  unfold fvec
  split_ifs with h
  · rw [diag_bvec, dT_eI]
  · have : r - a.val = 0 := by omega
    rw [diag_wb (tor_dT k r) hz, this, pow_zero, one_smul]

/- English proof (translation)
Unfold `ell`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[cj_apply, dT_eI, dT_eI]`.

Establish `: r - a.val = (r - (a.val + 1)) + 1` using `by omega`. Rewrite using `[this, pow_succ, star_mul', mul_right_comm, mul_right_comm _ (star (-Complex.I)), uni_pow]`. Simplify using the standard rewrite rules. Establish `: r - a.val = 1` using `by have := a.isLt; omega`. Rewrite using `[cj_mulVec, diag_wb (tor_dT k r) hz, mulVec_diagonal, Pi.star_apply, dT_eI, this]`.

Simplify using the standard rewrite rules.
-/
theorem ell_cj {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (g : Mx k r) :
    ell k r z (cj (dT k r) g) = Complex.I * ell k r z g := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [cj_apply, dT_eI, dT_eI]
    have : r - a.val = (r - (a.val + 1)) + 1 := by omega
    rw [this, pow_succ, star_mul', mul_right_comm, mul_right_comm _ (star (-Complex.I)), uni_pow]
    simp
  · have : r - a.val = 1 := by have := a.isLt; omega
    rw [cj_mulVec, diag_wb (tor_dT k r) hz, mulVec_diagonal, Pi.star_apply, dT_eI, this]
    simp

/- English proof (translation)
Unfold `psi`. Rewrite using `[ell_cj hz]`. Establish `: -Complex.I * c * (Complex.I * ell k r z g) = c * ell k r z g`. Take the linear combination `(-(c * ell k r z g)) * Complex.I_mul_I`. Rewrite using `[this]`.
-/
theorem psi_cj {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) (g : Mx k r) :
    psi k r z (-Complex.I * c) (cj (dT k r) g) = psi k r z c g := by
  unfold psi
  rw [ell_cj hz]
  have : -Complex.I * c * (Complex.I * ell k r z g) = c * ell k r z g := by
    linear_combination (-(c * ell k r z g)) * Complex.I_mul_I
  rw [this]

/- English proof (translation)
Unfold `ZhatO Formalism.QuantumDeterminants.Zhat`. Rewrite using `[cj_mulVec, herm_diag (tor_dT k r), diag_fvec hz, diag_fvec hz', mulVec_smul]`. Unfold `herm`. Rewrite using `[mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc]`. Use `congr 1`.

Establish `e : 2 * r = (r - a.val) + (r - b.val) + (a.val + b.val)` using `by have := a.isLt; have := b.isLt; omega`. Establish `e2 : Complex.I ^ (a.val + b.val) * (-Complex.I) ^ (a.val + b.val) = 1` using `by rw [← mul_pow]; simp`. Rewrite using `[e, pow_add, mul_assoc (Complex.I ^ _), e2, mul_one, pow_add, star_pow, neg_pow Complex.I (r - b.val)]`. Simplify using `only [star_neg, Complex.star_def, Complex.conj_I, neg_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Zhat_cj {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (g : Mx k r)
    (a b : Fin (r + 1)) :
    Formalism.QuantumDeterminants.Zhat k r z z' (cj (dT k r) g) a b =
      Complex.I ^ (2 * r) * (-Complex.I) ^ (a.val + b.val) * ZhatO k r z z' g a b := by
  unfold ZhatO Formalism.QuantumDeterminants.Zhat
  rw [cj_mulVec, herm_diag (tor_dT k r), diag_fvec hz, diag_fvec hz', mulVec_smul]
  unfold herm
  rw [mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc]
  congr 1
  have e : 2 * r = (r - a.val) + (r - b.val) + (a.val + b.val) := by have := a.isLt; have := b.isLt; omega
  have e2 : Complex.I ^ (a.val + b.val) * (-Complex.I) ^ (a.val + b.val) = 1 := by rw [← mul_pow]; simp
  rw [e, pow_add, mul_assoc (Complex.I ^ _), e2, mul_one, pow_add, star_pow, neg_pow Complex.I (r - b.val)]
  simp only [star_neg, Complex.star_def, Complex.conj_I, neg_neg]
  ring

/- English proof (translation)
Unfold `flagMat`. Use `split_ifs with h1 h2`. Rewrite using `[cj_mulVec, diag_fvec hz, mulVec_smul, mulVec_diagonal, Pi.star_apply, dT_eI, Pi.smul_apply, smul_eq_mul, mul_assoc]`. Rewrite using `[← h2, uni_pow, one_mul]`. Simplify using the standard rewrite rules.
-/
theorem flagMat_cj {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (g : Mx k r) (a b : Fin (r + 1)) :
    flagMat k r z (cj (dT k r) g) a b =
      (star ((-Complex.I) ^ (r - a.val)) * (-Complex.I) ^ (r - b.val)) * flagMat k r z g a b := by
  unfold flagMat
  split_ifs with h1 h2
  · rw [cj_mulVec, diag_fvec hz, mulVec_smul, mulVec_diagonal, Pi.star_apply, dT_eI, Pi.smul_apply, smul_eq_mul, mul_assoc]
  · rw [← h2, uni_pow, one_mul]
  · simp

def turnB (w : ℂ) (bs : List (ℂ × ℕ)) : List (ℂ × ℕ) :=
  bs.foldr (fun b (F : ℂ → List (ℂ × ℕ)) w =>
    (w * (-Complex.I) ^ (b.2 - 1) * b.1, b.2) :: F (w * (-Complex.I) ^ (2 * b.2))) (fun _ => []) w

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem turnB_nil (w : ℂ) : turnB w [] = [] := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem turnB_cons (w t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) :
    turnB w ((t, s) :: bs) = (w * (-Complex.I) ^ (s - 1) * t, s) :: turnB (w * (-Complex.I) ^ (2 * s)) bs := rfl

/- English proof (translation)
Proceed by induction on `bs with`. Consider the case `nil => intro w`. Both sides reduce to the same expression. Consider the case `cons b bs ih => intro w`. Take `⟨t, s⟩` from `b`.

Simplify using `[turnB_cons, ih]`.
-/
theorem turnB_snd (bs : List (ℂ × ℕ)) : ∀ w, (turnB w bs).map Prod.snd = bs.map Prod.snd := by
  induction bs with
  | nil => intro w; rfl
  | cons b bs ih => intro w; obtain ⟨t, s⟩ := b; simp [turnB_cons, ih]

/- English proof (translation)
Proceed by induction on `bs with`. Consider the case `nil => intro w _ _ b hb`. Simplify using `[turnB_nil] at hb`. Consider the case `cons b bs ih`. Introduce `w hw h b' hb'`.

Take `⟨t, s⟩` from `b`. Establish `hI : (-Complex.I) ≠ 0` using `neg_ne_zero.2 Complex.I_ne_zero`. Establish `h0` using `h (t, s) (by simp)`. Rewrite `hb'` using `[turnB_cons, List.mem_cons]`. Break down `hb' with rfl | hb'` into its components or cases.

Conclude with `⟨mul_ne_zero (mul_ne_zero hw (pow_ne_zero _ hI)) h0.1, h0.2⟩`. Conclude with `ih _ (mul_ne_zero hw (pow_ne_zero _ hI)) (fun b hb => h b (List.mem_cons_of_mem _ hb)) _ hb'`.
-/
theorem turnB_ok (bs : List (ℂ × ℕ)) : ∀ w, w ≠ 0 → (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    ∀ b ∈ turnB w bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := by
  induction bs with
  | nil => intro w _ _ b hb; simp [turnB_nil] at hb
  | cons b bs ih =>
    intro w hw h b' hb'
    obtain ⟨t, s⟩ := b
    have hI : (-Complex.I) ≠ 0 := neg_ne_zero.2 Complex.I_ne_zero
    have h0 := h (t, s) (by simp)
    rw [turnB_cons, List.mem_cons] at hb'
    rcases hb' with rfl | hb'
    · exact ⟨mul_ne_zero (mul_ne_zero hw (pow_ne_zero _ hI)) h0.1, h0.2⟩
    · exact ih _ (mul_ne_zero hw (pow_ne_zero _ hI)) (fun b hb => h b (List.mem_cons_of_mem _ hb)) _ hb'

/- English proof (translation)
Proceed by induction on `bs with`. Consider the case `nil => intro w i j`. Simplify using `[turnB_nil, ptEntry]`. Consider the case `cons b bs ih`. Introduce `w i j`.

Take `⟨t, s⟩` from `b`. Rewrite using `[turnB_cons, ptEntry, ptEntry]`. Use `split_ifs with h1 h2 h3`. Establish `: s - 1 = i + j` using `by omega`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Establish `: i + j = 2 * s + (i - s + (j - s))` using `by omega`. Rewrite using `[ih, this, pow_add _ (2 * s), mul_assoc w]`. Simplify using the standard rewrite rules.
-/
theorem ptEntry_turnB (bs : List (ℂ × ℕ)) : ∀ w i j,
    ptEntry (turnB w bs) i j = w * (-Complex.I) ^ (i + j) * ptEntry bs i j := by
  induction bs with
  | nil => intro w i j; simp [turnB_nil, ptEntry]
  | cons b bs ih =>
    intro w i j
    obtain ⟨t, s⟩ := b
    rw [turnB_cons, ptEntry, ptEntry]
    split_ifs with h1 h2 h3
    · have : s - 1 = i + j := by omega
      rw [this]
    · simp
    · have : i + j = 2 * s + (i - s + (j - s)) := by omega
      rw [ih, this, pow_add _ (2 * s), mul_assoc w]
    · simp

/- English proof (translation)
Proceed by induction on `bs with`. Consider the case `nil => intro w p`. Both sides reduce to the same expression. Consider the case `cons b bs ih => intro w p`. Take `⟨t, s⟩` from `b`.

Rewrite using `[turnB_cons, blockIdx, blockIdx, ih]`.
-/
theorem blockIdx_turnB (bs : List (ℂ × ℕ)) : ∀ w p, blockIdx (turnB w bs) p = blockIdx bs p := by
  induction bs with
  | nil => intro w p; rfl
  | cons b bs ih => intro w p; obtain ⟨t, s⟩ := b; rw [turnB_cons, blockIdx, blockIdx, ih]

/- English proof (translation)
Proceed by induction on `bs with`. Consider the case `nil => intro w a _`. Both sides reduce to the same expression. Consider the case `cons b bs ih`. Introduce `w a hw`.

Take `⟨t, s⟩` from `b`. Establish `e : ‖w * (-Complex.I) ^ (s - 1) * t‖ = ‖t‖` using `by simp [hw]`. Rewrite using `[turnB_cons, ptWeightFrom, ptWeightFrom, ih _ _ (by simp [hw]), Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, e]`.
-/
theorem ptWeightFrom_turnB (T T' : ℝ) (bs : List (ℂ × ℕ)) : ∀ w a, ‖w‖ = 1 →
    ptWeightFrom k r T T' a (turnB w bs) = ptWeightFrom k r T T' a bs := by
  induction bs with
  | nil => intro w a _; rfl
  | cons b bs ih =>
    intro w a hw
    obtain ⟨t, s⟩ := b
    have e : ‖w * (-Complex.I) ^ (s - 1) * t‖ = ‖t‖ := by simp [hw]
    rw [turnB_cons, ptWeightFrom, ptWeightFrom, ih _ _ (by simp [hw]), Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, e]

def turnP (p : Point ℂ (r + 1)) : Point ℂ (r + 1) :=
  ⟨turnB (Complex.I ^ (2 * r)) p.1, turnB_ok _ _ (pow_ne_zero _ Complex.I_ne_zero) p.2.1, by rw [turnB_snd]; exact p.2.2⟩

/- English proof (translation)
The claim follows from `ptEntry_turnB _ _ _ _`.
-/
theorem ptMat_turnP (p : Point ℂ (r + 1)) (a b : Fin (r + 1)) :
    ptMat (turnP p) a b = Complex.I ^ (2 * r) * (-Complex.I) ^ (a.val + b.val) * ptMat p a b :=
  ptEntry_turnB _ _ _ _

/- English proof (translation)
The claim follows from `ptWeightFrom_turnB _ _ _ _ _ (by simp)`.
-/
theorem ptWeight_turnP (T T' : ℝ) (p : Point ℂ (r + 1)) : ptWeight k r T T' (turnP p) = ptWeight k r T T' p :=
  ptWeightFrom_turnB _ _ _ _ _ (by simp)

/- English proof (translation)
Unfold `rootPat turnP`. Simplify using `only [blockIdx_turnB]`.
-/
theorem rootPat_turnP (p : Point ℂ (r + 1)) : rootPat (turnP p) = rootPat p := by
  unfold rootPat turnP
  simp only [blockIdx_turnB]

/- English proof (translation)
Unfold `leadMinor`. Establish `e : (ptMat (turnP p)).submatrix (Fin.castLE hl) (Fin.castLE hl) = Matrix.of (fun i j : Fin l => (Complex.I ^ (2 * r) * (-Complex.I) ^ i.val) * (Matrix.of (fun i j : Fin l => (-Complex.I) ^ j.val * ((ptMat p).submatrix (Fin.castLE hl) (Fin.castLE hl)) i j)) i j)`. Use extensionality with `a b`. Simplify using `only [submatrix_apply, ptMat_turnP, of_apply, Fin.val_castLE, pow_add]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, Matrix.det_mul_column, Matrix.det_mul_row, map_mul, map_mul, map_prod, map_prod]`. Simplify using the standard rewrite rules.
-/
theorem normSq_leadMinor_turnP (p : Point ℂ (r + 1)) (l : ℕ) (hl : l ≤ r + 1) :
    Complex.normSq (leadMinor (ptMat (turnP p)) l hl) = Complex.normSq (leadMinor (ptMat p) l hl) := by
  unfold leadMinor
  have e : (ptMat (turnP p)).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.of (fun i j : Fin l => (Complex.I ^ (2 * r) * (-Complex.I) ^ i.val) *
        (Matrix.of (fun i j : Fin l => (-Complex.I) ^ j.val *
          ((ptMat p).submatrix (Fin.castLE hl) (Fin.castLE hl)) i j)) i j) := by
    ext a b
    simp only [submatrix_apply, ptMat_turnP, of_apply, Fin.val_castLE, pow_add]
    ring
  rw [e, Matrix.det_mul_column, Matrix.det_mul_row, map_mul, map_mul, map_prod, map_prod]
  simp

/- English proof (translation)
Unfold `Gpt`. Rewrite using `[normSq_leadMinor_turnP, normSq_leadMinor_turnP]`.
-/
theorem GPoint_turnP (T T' : ℝ) (p : Point ℂ (r + 1)) : Gpt T T' (turnP p) = Gpt T T' p := by
  unfold Gpt
  rw [normSq_leadMinor_turnP, normSq_leadMinor_turnP]

def turnL (L : LocBessel k r) : LocBessel k r :=
  { L with
    σ := fun g => L.σ (cj (star (dT k r)) g)
    hσ := isDSHpk_cj (tor_dT k r) L.hσ
    π := fun g => L.π (cj (star (dT k r)) g)
    hπ := isHCTypeW_cj (tor_dT k r) L.hz.1 L.hπ
    π' := fun g => L.π' (cj (star (dT k r)) g)
    hπ' := isHCTypeW_cj (tor_dT k r) L.hz'.1 L.hπ'
    c := -Complex.I * L.c
    μW := L.μW.map (cjE (tor_dT k r).uni)
    μW' := L.μW'.map (cjE (tor_dT k r).uni)
    hμW := isHaarOn_cj _ (fun _ => cj_mem_UW (tor_dT k r) L.hz.1) (fun _ => cj_mem_UW (tor_dT k r).st L.hz.1) L.hμW
    hμW' := isHaarOn_cj _ (fun _ => cj_mem_UW (tor_dT k r) L.hz'.1) (fun _ => cj_mem_UW (tor_dT k r).st L.hz'.1) L.hμW' }

def turnF (L : LocBessel k r) (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) : Mx k r → ((turnL L).Wq →L[ℂ] (turnL L).Wp) :=
  fun g => f (cj (star (dT k r)) g)

/- English proof (translation)
Take `⟨P, Q, h1, h2, h3⟩` from `hf`. Conclude with `⟨P, Q, fun w => isKFin_cj (tor_dT k r) (h1 w), fun w => isKFin_cj (tor_dT k r) (h2 w), fun g => h3 _⟩`.
-/
theorem isKFinCoef_turn (L : LocBessel k r) {f : Mx k r → (L.Wq →L[ℂ] L.Wp)} (hf : IsKFinCoefH L.σ f) :
    IsKFinCoefH (turnL L).σ (turnF L f) := by
  obtain ⟨P, Q, h1, h2, h3⟩ := hf
  exact ⟨P, Q, fun w => isKFin_cj (tor_dT k r) (h1 w), fun w => isKFin_cj (tor_dT k r) (h2 w), fun g => h3 _⟩

def cj4 (k r : ℕ) : PairSp k r ≃ᵐ PairSp k r :=
  ((cjE (tor_dT k r).uni).prodCongr (cjE (tor_dT k r).uni)).prodCongr
    ((cjE (tor_dT k r).uni).prodCongr (cjE (tor_dT k r).uni))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conj_four_apply (p : PairSp k r) : cj4 k r p =
    ((cjE (tor_dT k r).uni p.1.1, cjE (tor_dT k r).uni p.1.2), (cjE (tor_dT k r).uni p.2.1, cjE (tor_dT k r).uni p.2.2)) :=
  rfl

/- English proof (translation)
Establish `: SFinite L.μN` using `by unfold LocBessel.μN haarLie; infer_instance`. Use `L.hμW.1.1` as an intermediate fact. Use `L.hμW'.1.1` as an intermediate fact. Establish `hN : (turnL L).μN = L.μN.map (cjE (tor_dT k r).uni)` using `(haarLie_map_cj (tor_dT k r).uni (fun _ => cj_mem_N (tor_dT k r)) L.κN).symm`. Establish `hm` using `(cjE (tor_dT k r).uni).measurable`.

Unfold `pairMeas`. Rewrite using `[hN]`. Use `show ((L.μW.map _).prod _).prod ((L.μW'.map _).prod _) = _`. Rewrite using `[Measure.map_prod_map _ _ hm hm, Measure.map_prod_map _ _ hm hm, Measure.map_prod_map _ _ (hm.prodMap hm) (hm.prodMap hm)]`. Both sides reduce to the same expression.
-/
theorem pairMeas_turn (L : LocBessel k r) : pairMeas (turnL L) = (pairMeas L).map (cj4 k r) := by
  have : SFinite L.μN := by unfold LocBessel.μN haarLie; infer_instance
  have := L.hμW.1.1
  have := L.hμW'.1.1
  have hN : (turnL L).μN = L.μN.map (cjE (tor_dT k r).uni) :=
    (haarLie_map_cj (tor_dT k r).uni (fun _ => cj_mem_N (tor_dT k r)) L.κN).symm
  have hm := (cjE (tor_dT k r).uni).measurable
  unfold pairMeas
  rw [hN]
  show ((L.μW.map _).prod _).prod ((L.μW'.map _).prod _) = _
  rw [Measure.map_prod_map _ _ hm hm, Measure.map_prod_map _ _ hm hm,
    Measure.map_prod_map _ _ (hm.prodMap hm) (hm.prodMap hm)]
  rfl

/- English proof (translation)
Establish `h` using `(tor_dT k r).uni`. Rewrite using `[conj_four_apply]`. Unfold `besselIntg turnF`. Simplify using `only [of_cjE]`. Rewrite using `[← cj_inv h, ← cj_inv h, ← cj_inv h, ← cj_mul h, ← cj_mul h, ← cj_mul h, ← cj_mul h, cj_star_cj h]`.

Use `show (psi k r L.z (-Complex.I * L.c) _ * star (psi k r L.z' (-Complex.I * L.c) _)) • (L.π (cj _ _)).comp ((f _).comp (L.π' (cj _ _))) = _`. Rewrite using `[psi_cj L.hz.1, psi_cj L.hz'.1, cj_star_cj h, cj_star_cj h]`.
-/
theorem besselIntg_turn (L : LocBessel k r) (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (g : Mx k r) (p : PairSp k r) :
    besselIntg (turnL L) (turnF L f) (cj (dT k r) g) (cj4 k r p) = besselIntg L f g p := by
  have h := (tor_dT k r).uni
  rw [conj_four_apply]
  unfold besselIntg turnF
  simp only [of_cjE]
  rw [← cj_inv h, ← cj_inv h, ← cj_inv h, ← cj_mul h, ← cj_mul h, ← cj_mul h, ← cj_mul h, cj_star_cj h]
  show (psi k r L.z (-Complex.I * L.c) _ * star (psi k r L.z' (-Complex.I * L.c) _)) •
    (L.π (cj _ _)).comp ((f _).comp (L.π' (cj _ _))) = _
  rw [psi_cj L.hz.1, psi_cj L.hz'.1, cj_star_cj h, cj_star_cj h]

/- English proof (translation)
Unfold `OrbInt`. Rewrite using `[integral_map_equiv]`. Simplify using `only [besselIntg_turn]`. Both sides reduce to the same expression.
-/
theorem orbInt_turn (L : LocBessel k r) (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (g : Mx k r) (ν : Measure (PairSp k r)) :
    OrbInt (turnL L) (turnF L f) (cj (dT k r) g) (ν.map (cj4 k r)) = OrbInt L f g ν := by
  unfold OrbInt
  rw [integral_map_equiv]
  simp only [besselIntg_turn]
  rfl

/- English proof (translation)
Establish `e : ∀ c μ, (turnL L).J (turnF L f) (bigCell k r c μ) = L.J f (bigCell k r c μ)` using `fun c μ => by`. Use `orbInt_turn L f (bigCell k r c μ) (pairMeas L)` as an intermediate fact. Rewrite `this` using `[← pairMeas_turn, cj_bigCell (tor_dT k r)]`. Conclude with `this`. Unfold `jNorm2`.

Simplify using `only [e]`. Both sides reduce to the same expression.
-/
theorem jNorm2_turn (L : LocBessel k r) (f : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : jNorm2 (turnL L) (turnF L f) μsec = jNorm2 L f μsec := by
  have e : ∀ c μ, (turnL L).J (turnF L f) (bigCell k r c μ) = L.J f (bigCell k r c μ) := fun c μ => by
    have := orbInt_turn L f (bigCell k r c μ) (pairMeas L)
    rw [← pairMeas_turn, cj_bigCell (tor_dT k r)] at this
    exact this
  unfold jNorm2
  simp only [e]
  rfl

end Turn

section Orb

variable {k r : ℕ}

/- English proof (translation)
Use `⟨cj_mem_N h ha.1, ?_⟩` and prove the remaining obligations. Rewrite using `[← cj_inv h.uni, ← cj_mul h.uni, ← cj_mul h.uni]`. Conclude with `cj_mem_N h ha.2`.
-/
theorem cj_mem_RStab {d : Fin (2 * r + k + 1) → ℂ} (h : Tor k r d) {g a : Mx k r} (ha : a ∈ RStab k r g) :
    cj d a ∈ RStab k r (cj d g) := by
  refine ⟨cj_mem_N h ha.1, ?_⟩
  rw [← cj_inv h.uni, ← cj_mul h.uni, ← cj_mul h.uni]
  exact cj_mem_N h ha.2

/- English proof (translation)
Introduce `a ha`. Establish `h` using `tor_dT k r`. Establish `h1` using `cj_mem_RStab h.st ha`. Rewrite `h1` using `[cj_star_cj h.uni]`. Establish `h2` using `hg _ h1`.

Rewrite `h2` using `[← psi_cj L.hz.1, ← psi_cj L.hz'.1, cj_mul h.uni, cj_mul h.uni, cj_cj_star h.uni, cj_inv h.uni]`. Conclude with `h2`.
-/
theorem isRelStab_turn (L : LocBessel k r) {g : Mx k r} (hg : IsRelStab L g) :
    IsRelStab (turnL L) (cj (dT k r) g) := by
  intro a ha
  have h := tor_dT k r
  have h1 := cj_mem_RStab h.st ha
  rw [cj_star_cj h.uni] at h1
  have h2 := hg _ h1
  rw [← psi_cj L.hz.1, ← psi_cj L.hz'.1, cj_mul h.uni, cj_mul h.uni, cj_cj_star h.uni, cj_inv h.uni] at h2
  exact h2

/- English proof (translation)
Use `measurable_pi_lambda _ fun q => ?_` and prove the remaining obligations. Unfold `flagMat`. Use `split_ifs`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply] fun_prop`. Conclude with `measurable_const`.

Conclude with `measurable_const`.
-/
theorem measurable_flag (z : Fin (2 * r + k + 1) → ℂ) (S : Finset (Fin (r + 1) × Fin (r + 1))) :
    Measurable (fun x : Mt k r => fun q : S => flagMat k r z (Matrix.of x) q.1.1 q.1.2) := by
  refine measurable_pi_lambda _ fun q => ?_
  unfold flagMat
  split_ifs
  · simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop
  · exact measurable_const
  · exact measurable_const

/- English proof (translation)
The claim follows from `(rotation ⟨u, by simpa [Submonoid.unitSphere] using hu⟩).measurePreserving`.
-/
theorem mp_mul_unit {u : ℂ} (hu : ‖u‖ = 1) : MeasurePreserving (fun x : ℂ => u * x) volume volume :=
  (rotation ⟨u, by simpa [Submonoid.unitSphere] using hu⟩).measurePreserving

/- English proof (translation)
Establish `hp : MeasurePreserving (fun (y : S → ℂ) (q : S) => (star ((-Complex.I) ^ (r - q.1.1.val)) * (-Complex.I) ^ (r - q.1.2.val)) * y q) volume volume` using `volume_preserving_pi fun q : S => mp_mul_unit (by simp)`. Establish `e : (fun x : Mt k r => fun q : S => flagMat k r z (Matrix.of x) q.1.1 q.1.2) ∘ cjE (tor_dT k r).uni = (fun (y : S → ℂ) (q : S) => (star ((-Complex.I) ^ (r - q.1.1.val)) * (-Complex.I) ^ (r - q.1.2.val)) * y q) ∘ (fun x : Mt k r => fun q : S => flagMat k r z (Matrix.of x) q.1.1 q. …`. Use function extensionality and compare the values at `x q`. Conclude with `flagMat_cj hz (Matrix.of x) _ _`. Rewrite using `[Measure.map_map (measurable_flag z S) (cjE _).measurable, e, ← Measure.map_map hp.measurable (measurable_flag z S), hμ, Measure.map_smul, hp.map_eq]`.
-/
theorem root_map_turn {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (S : Finset (Fin (r + 1) × Fin (r + 1)))
    (μ : Measure (Mt k r)) (c : ENNReal)
    (hμ : μ.map (fun x : Mt k r => fun q : S => flagMat k r z (Matrix.of x) q.1.1 q.1.2) = c • volume) :
    (μ.map (cjE (tor_dT k r).uni)).map (fun x : Mt k r => fun q : S => flagMat k r z (Matrix.of x) q.1.1 q.1.2) =
      c • volume := by
  have hp : MeasurePreserving (fun (y : S → ℂ) (q : S) =>
      (star ((-Complex.I) ^ (r - q.1.1.val)) * (-Complex.I) ^ (r - q.1.2.val)) * y q) volume volume :=
    volume_preserving_pi fun q : S => mp_mul_unit (by simp)
  have e : (fun x : Mt k r => fun q : S => flagMat k r z (Matrix.of x) q.1.1 q.1.2) ∘ cjE (tor_dT k r).uni =
      (fun (y : S → ℂ) (q : S) => (star ((-Complex.I) ^ (r - q.1.1.val)) * (-Complex.I) ^ (r - q.1.2.val)) * y q) ∘
        (fun x : Mt k r => fun q : S => flagMat k r z (Matrix.of x) q.1.1 q.1.2) := by
    funext x q
    exact flagMat_cj hz (Matrix.of x) _ _
  rw [Measure.map_map (measurable_flag z S) (cjE _).measurable, e,
    ← Measure.map_map hp.measurable (measurable_flag z S), hμ, Measure.map_smul, hp.map_eq]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[MeasurableEquiv.map_apply]`. Conclude with `measure_mono_null (fun x hx hx' => hx (cj_mem_RStab (tor_dT k r) hx')) hμ.1`. Establish `hc : ‖(turnL L).c‖ = ‖L.c‖` using `by show ‖-Complex.I * L.c‖ = _`. Simplify using the standard rewrite rules.

Establish `key : ∀ S : Finset (Fin (r + 1) × Fin (r + 1)), S = rootPat p → (μ.map (cjE (tor_dT k r).uni)).map (fun x : Mt k r => fun q : S => flagMat k r L.z (Matrix.of x) q.1.1 q.1.2) = ENNReal.ofReal ((‖L.c‖ / (2 * Real.pi)) ^ S.card) • volume`. Introduce and unpack `S rfl`. Conclude with `root_map_turn L.hz.1 _ _ _ hμ.2`. Rewrite using `[hc]`. Conclude with `key _ (rootPat_turnP p)`.
-/
theorem isRootMeas_turn (L : LocBessel k r) {p : Point ℂ (r + 1)} {g : Mx k r} {μ : Measure (Mt k r)}
    (hμ : IsRootMeas L p g μ) :
    IsRootMeas (turnL L) (turnP p) (cj (dT k r) g) (μ.map (cjE (tor_dT k r).uni)) := by
  refine ⟨?_, ?_⟩
  · rw [MeasurableEquiv.map_apply]
    exact measure_mono_null (fun x hx hx' => hx (cj_mem_RStab (tor_dT k r) hx')) hμ.1
  · have hc : ‖(turnL L).c‖ = ‖L.c‖ := by
      show ‖-Complex.I * L.c‖ = _
      simp
    have key : ∀ S : Finset (Fin (r + 1) × Fin (r + 1)), S = rootPat p →
        (μ.map (cjE (tor_dT k r).uni)).map (fun x : Mt k r => fun q : S => flagMat k r L.z (Matrix.of x) q.1.1 q.1.2) =
          ENNReal.ofReal ((‖L.c‖ / (2 * Real.pi)) ^ S.card) • volume := by
      rintro S rfl
      exact root_map_turn L.hz.1 _ _ _ hμ.2
    rw [hc]
    exact key _ (rootPat_turnP p)

/- English proof (translation)
Introduce `f hf`. Establish `h` using `(tor_dT k r).uni`. Rewrite using `[pairMeas_turn, lintegral_map_equiv, lintegral_map_equiv, hν (fun x => f (cj4 k r x)) (hf.comp (cj4 k r).measurable)]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[lintegral_map_equiv]`.

Use `lintegral_congr fun a => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[conj_four_apply, conj_four_apply]`. Unfold `stabAct`. Simplify using `only [of_cjE]`.

Rewrite using `[← cj_inv h, ← cj_mul h, ← cj_mul h, ← cj_mul h, ← cj_mul h]`. Both sides reduce to the same expression.
-/
theorem isOrbQuot_turn (L : LocBessel k r) {g : Mx k r} {μ : Measure (Mt k r)} {ν : Measure (PairSp k r)}
    (hν : IsOrbQuot L g μ ν) :
    IsOrbQuot (turnL L) (cj (dT k r) g) (μ.map (cjE (tor_dT k r).uni)) (ν.map (cj4 k r)) := by
  intro f hf
  have h := (tor_dT k r).uni
  rw [pairMeas_turn, lintegral_map_equiv, lintegral_map_equiv, hν (fun x => f (cj4 k r x)) (hf.comp (cj4 k r).measurable)]
  refine lintegral_congr fun x => ?_
  rw [lintegral_map_equiv]
  refine lintegral_congr fun a => ?_
  congr 1
  rw [conj_four_apply, conj_four_apply]
  unfold stabAct
  simp only [of_cjE]
  rw [← cj_inv h, ← cj_mul h, ← cj_mul h, ← cj_mul h, ← cj_mul h]
  rfl

/- English proof (translation)
Unfold `Bridge.orbSqO orbSq`. Use `iSup_le fun g => iSup_le fun μ => iSup_le fun ν => iSup_le fun hh => ?_` and prove the remaining obligations. Take `⟨h1, h2, h3, h4⟩` from `hh`. Use `le_iSup_of_le (cj (dT k r) g) (le_iSup_of_le (μ.map (cjE (tor_dT k r).uni)) (le_iSup_of_le (ν.map (cj4 k r)) (le_iSup_of_le ⟨⟨cj_mem_UH (tor_dT k r) h1.1, ?_⟩, isRelStab_turn L h2, isRootMeas_turn L h3, isOrbQuot_turn L h4⟩ ?_)))` and prove the remaining obligations. Use extensionality with `a b`.

Rewrite using `[ptMat_turnP, ← h1.2]`. Conclude with `Zhat_cj L.hz.1 L.hz'.1 g a b`. Rewrite using `[orbInt_turn]`. Conclude with `le_rfl`.
-/
theorem orbSqO_le_turn (L : LocBessel k r) (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (p : Point ℂ (r + 1)) :
    Bridge.orbSqO L f p ≤ orbSq (turnL L) (turnF L f) (turnP p) := by
  unfold Bridge.orbSqO orbSq
  refine iSup_le fun g => iSup_le fun μ => iSup_le fun ν => iSup_le fun hh => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hh
  refine le_iSup_of_le (cj (dT k r) g) (le_iSup_of_le (μ.map (cjE (tor_dT k r).uni)) (le_iSup_of_le (ν.map (cj4 k r))
    (le_iSup_of_le ⟨⟨cj_mem_UH (tor_dT k r) h1.1, ?_⟩, isRelStab_turn L h2, isRootMeas_turn L h3, isOrbQuot_turn L h4⟩ ?_)))
  · ext a b
    rw [ptMat_turnP, ← h1.2]
    exact Zhat_cj L.hz.1 L.hz'.1 g a b
  · rw [orbInt_turn]
    exact le_rfl

end Orb

/- English proof (translation)
Introduce `a b hab`. Establish `h1` using `h a b hab`. Establish `h2 : ∀ s, |lam s - lam0 s| ≤ δ` using `fun s => (Finset.single_le_sum (f := fun s => |lam s - lam0 s|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)).trans hd`. Establish `h3 : |lam0 a - lam0 b| ≤ |lam a - lam b| + |lam a - lam0 a| + |lam b - lam0 b|`. Establish `e : lam0 a - lam0 b = (lam a - lam b) - (lam a - lam0 a) + (lam b - lam0 b)` using `by ring`.

Rewrite using `[e]`. Conclude with `(abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)`. Combine the linear relations using `[h2 a, h2 b]`.
-/
theorem gap_near {n : ℕ} {ε : Fin n → Bool} {lam lam0 : Fin n → ℝ} {x y δ : ℝ} (h : GapAtLeast ε lam0 x)
    (hd : l1dist lam lam0 ≤ δ) (hy : y + 2 * δ ≤ x) : GapAtLeast ε lam y := by
  intro a b hab
  have h1 := h a b hab
  have h2 : ∀ s, |lam s - lam0 s| ≤ δ := fun s =>
    (Finset.single_le_sum (f := fun s => |lam s - lam0 s|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)).trans hd
  have h3 : |lam0 a - lam0 b| ≤ |lam a - lam b| + |lam a - lam0 a| + |lam b - lam0 b| := by
    have e : lam0 a - lam0 b = (lam a - lam b) - (lam a - lam0 a) + (lam b - lam0 b) := by ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
  linarith [h2 a, h2 b]

/- English proof (translation)
Establish `h1 : (1 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ)` using `by exact_mod_cast (by omega : 1 ≤ 2 * r + 2)`. Establish `h2 : ((2 * r + 2 : ℕ) : ℝ) ^ 3 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2)`. Rewrite using `[← Real.rpow_natCast]`. Conclude with `Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)`. Establish `h3 : k ≤ (2 * r + k + 1) ^ 3` using `(by omega : k ≤ 2 * r + k + 1).trans (Nat.le_self_pow (by norm_num) _)`.

Establish `h4 : (k : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3` using `by exact_mod_cast h3`. Rewrite using `[mul_comm]`. Use `mul_le_mul h2 (h4.trans (le_add_of_nonneg_left (by positivity))) (by positivity) (by positivity)` and prove the remaining obligations.
-/
theorem size_le (k r : ℕ) : (k : ℝ) * ((2 * r + 2 : ℕ) : ℝ) ^ 3 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
    (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) := by
  have h1 : (1 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + 2)
  have h2 : ((2 * r + 2 : ℕ) : ℝ) ^ 3 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
  have h3 : k ≤ (2 * r + k + 1) ^ 3 := (by omega : k ≤ 2 * r + k + 1).trans (Nat.le_self_pow (by norm_num) _)
  have h4 : (k : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by exact_mod_cast h3
  rw [mul_comm]
  refine mul_le_mul h2 (h4.trans (le_add_of_nonneg_left (by positivity))) (by positivity) (by positivity)

/- English proof (translation)
Establish `h1 : 1 ≤ max 1 (1 / G)` using `le_max_left _ _`. Use `max_le (by nlinarith) ?_` and prove the remaining obligations. Rewrite using `[one_div, mul_inv, ← one_div G]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem max_inv_scale {s B G : ℝ} (hB : 1 ≤ B) (hs : 0 < s) (hsB : s⁻¹ ≤ B) :
    max 1 (1 / (s * G)) ≤ B * max 1 (1 / G) := by
  have h1 : 1 ≤ max 1 (1 / G) := le_max_left _ _
  refine max_le (by nlinarith) ?_
  rw [one_div, mul_inv, ← one_div G]
  calc s⁻¹ * (1 / G) ≤ s⁻¹ * max 1 (1 / G) := mul_le_mul_of_nonneg_left (le_max_right _ _) (inv_pos.2 hs).le
    _ ≤ _ := mul_le_mul_of_nonneg_right hsB (by linarith)

/- English proof (translation)
Introduce `Ch Cgf Cf hCh hCf`. Use `⟨2 * Ch * Cf + Ch, by positivity, fun Cn => ⟨Cgf + 2 * |Cn|, fun Cs hCs D hFr => ?_⟩⟩` and prove the remaining obligations. Introduce `L lam0 f ka b hb hka hka1 hka2 hc hκ hε hκ0 hStd hl1 hf`. Establish `hm : D.R.m = 2 * D.R.rS + 2`. Take `⟨t, ht⟩` from `D.R.m_even`.

Establish `h2` using `D.R.two_le_m`. Simplify using `only [Ranks.rS]`. Use linear arithmetic over natural numbers and integers. Rewrite `hl1`, the goal using `[hm]`. Establish `hb1 : 1 ≤ b` using `(Real.one_le_exp zero_le_one).trans hb`.

Establish `hb0 : 0 < b` using `by linarith`. Establish `hgap : GapAtLeast L.ε L.lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3))`. Use `gap_near hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hl1 ?_` and prove the remaining obligations. Establish `h1` using `size_le D.R.k D.R.rS`. Establish `h0 : 0 ≤ (D.R.k : ℝ) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3` using `by positivity`.

Rewrite using `[mul_assoc Cgf, mul_assoc Cs, mul_assoc Cn]`. Generalize the expression as in `(D.R.k : ℝ) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 = Y at h1 h0 ⊢`. Generalize the expression as in `((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3) = X at h1 ⊢`. Establish `h2 : Cn * Y ≤ |Cn| * X` using `(mul_le_mul_of_nonneg_right (le_abs_self Cn) h0).trans (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))`. Establish `h3 : (Cgf + 2 * |Cn|) * X ≤ Cs * X` using `mul_le_mul_of_nonneg_right hCs (h0.trans h1)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc' : (turnL L).c = cOfDpsi (ka : ℂ)` using `by show -Complex.I * L.c = _`. Rewrite using `[hc, cOfDpsi]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨L₁, f₁, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, hsec⟩` from `hFr (turnL L) (turnF L f) ka ka⁻¹ (ka ^ D.R.rS) hka (inv_pos.2 hka) (pow_pos hka _) hc' hκ0 hκ hε hgap (isKFinCoef_turn L hf)`. Establish `eT : ∀ T : ℝ, (ka ^ D.R.rS) ^ 2 * T = T * ka ^ (2 * D.R.rS)` using `fun T => by ring`. Use `⟨L₁, f₁, e1, e2, e3, e4, by rw [e5, inv_mul_cancel₀ hka.ne'], e6, e7, e8.trans (eT _), e9.trans (eT _), e10, fun μsec hμ => ?_⟩` and prove the remaining obligations. Take `⟨μsec₁, hμ₁, K₁, hK, hj, hpt⟩` from `hsec μsec hμ`. Rewrite `hj` using `[jNorm2_turn]`.

Use `⟨μsec₁, hμ₁, K₁, hK, hj.le, fun h0 => ?_, fun p hp => ?_⟩` and prove the remaining obligations. Rewrite using `[hj]`. Conclude with `mul_ne_zero (ENNReal.ofReal_pos.2 hK).ne' h0`. Take `⟨p₁, -, hG, -, hw⟩` from `hpt (turnP p) (by rw [GPoint_turnP]; exact hp)`. Rewrite `hG` using `[GPoint_turnP]`.

Rewrite `hw` using `[ptWeight_turnP]`. Use `set M : ℝ := ((2 * D.R.rS + 2 : ℕ) : ℝ) with hM`. Establish `hrM : (D.R.rS : ℝ) ≤ M` using `by rw [hM]; exact_mod_cast (by omega : D.R.rS ≤ 2 * D.R.rS + 2)`. Establish `hM0 : 0 ≤ M` using `by positivity`. Establish `hs : ka⁻¹ ^ (2 * D.R.rS * (D.R.rS + 1)) * (ka ^ D.R.rS) ^ (4 * (D.R.rS + 1)) = ka ^ (2 * D.R.rS * (D.R.rS + 1))`.

Establish `: D.R.rS * (4 * (D.R.rS + 1)) = 2 * D.R.rS * (D.R.rS + 1) + 2 * D.R.rS * (D.R.rS + 1)` using `by ring`. Rewrite using `[← pow_mul, this, pow_add, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hka.ne', one_pow, one_mul]`. Rewrite `hG` using `[hs]`. Establish `hpw : ∀ {x : ℝ} (n : ℕ), 0 ≤ x → x ≤ b ^ Ch → x ^ n ≤ b ^ (Ch * n)` using `fun n h0 h1 => by`. Rewrite using `[Real.rpow_mul hb0.le, Real.rpow_natCast]`.

Conclude with `pow_le_pow_left₀ h0 h1 n`. Establish `hCC : 0 ≤ Ch * Cf` using `mul_nonneg hCh hCf`. Use `⟨p₁, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hG]`. Conclude with `mul_ne_zero (pow_pos hka _).ne' hp`.

Rewrite using `[hG]`. Use `max_inv_scale (Real.one_le_rpow hb1 (by positivity)) (pow_pos hka _) ?_` and prove the remaining obligations. Rewrite using `[← inv_pow]`. Use `(hpw _ (inv_pos.2 hka).le hka2).trans (Real.rpow_le_rpow_of_exponent_le hb1 ?_)` and prove the remaining obligations. Establish `h1 : ((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℝ) ≤ M ^ 2`.

Rewrite using `[hM]; exact_mod_cast (by nlinarith : 2 * D.R.rS * (D.R.rS + 1) ≤ (2 * D.R.rS + 2) ^ 2)`. Establish `h2` using `mul_le_mul_of_nonneg_left h1 hCh`. Establish `h3 : 0 ≤ Ch * Cf * M ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `h1 : max ka⁻¹ ka⁻¹⁻¹ ≤ b ^ Ch` using `max_le hka2 (by rwa [inv_inv])`.

Establish `h2 : max (ka ^ D.R.rS) (ka ^ D.R.rS)⁻¹ ≤ b ^ (Ch * D.R.rS)` using `max_le (hpw _ hka.le hka1) (by rw [← inv_pow]; exact hpw _ (inv_pos.2 hka).le hka2)`. Establish `h3 : max ka⁻¹ ka⁻¹⁻¹ ^ (Cf * M ^ 2) * max (ka ^ D.R.rS) (ka ^ D.R.rS)⁻¹ ^ (Cf * M) ≤ b ^ ((2 * Ch * Cf + Ch) * M ^ 2)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_mul hb0.le, ← Real.rpow_mul hb0.le, ← Real.rpow_add hb0]`. Use `_ ≤ _ := by`.

Use `Real.rpow_le_rpow_of_exponent_le hb1 ?_` and prove the remaining obligations. Establish `h4` using `mul_le_mul_of_nonneg_left hrM (mul_nonneg hCC hM0)`. Establish `h5 : 0 ≤ Ch * M ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[ENNReal.ofReal_mul hK.le, ENNReal.ofReal_mul (Real.rpow_nonneg hb0.le _), mul_assoc, mul_assoc]`.

Use `le_trans ?_ (hw.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal h3) _))` and prove the remaining obligations. Conclude with `mul_le_mul_right (mul_le_mul_right (orbSqO_le_turn L f p) _) _`.
-/
theorem frameChange_of_frames : ∀ Ch Cgf Cf : ℝ, 0 ≤ Ch → 0 ≤ Cf → ∃ Cf' : ℝ, 0 ≤ Cf' ∧ ∀ Cn : ℝ, ∃ Cs₀ : ℝ,
    ∀ Cs ≥ Cs₀, ∀ D : D7, OnePlaceEstimates.FrameBesselBound D Cgf Cf → Bridge.FrameChange D Ch Cs Cn Cf' := by
  intro Ch Cgf Cf hCh hCf
  refine ⟨2 * Ch * Cf + Ch, by positivity, fun Cn => ⟨Cgf + 2 * |Cn|, fun Cs hCs D hFr => ?_⟩⟩
  intro L lam0 f ka b hb hka hka1 hka2 hc hκ hε hκ0 hStd hl1 hf
  have hm : D.R.m = 2 * D.R.rS + 2 := by
    obtain ⟨t, ht⟩ := D.R.m_even
    have h2 := D.R.two_le_m
    simp only [Ranks.rS]
    omega
  rw [hm] at hl1 ⊢
  have hb1 : 1 ≤ b := (Real.one_le_exp zero_le_one).trans hb
  have hb0 : 0 < b := by linarith
  have hgap : GapAtLeast L.ε L.lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 +
        ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) := by
    refine gap_near hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hl1 ?_
    have h1 := size_le D.R.k D.R.rS
    have h0 : 0 ≤ (D.R.k : ℝ) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 := by positivity
    rw [mul_assoc Cgf, mul_assoc Cs, mul_assoc Cn]
    generalize (D.R.k : ℝ) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 = Y at h1 h0 ⊢
    generalize ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 +
        ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3) = X at h1 ⊢
    have h2 : Cn * Y ≤ |Cn| * X :=
      (mul_le_mul_of_nonneg_right (le_abs_self Cn) h0).trans (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
    have h3 : (Cgf + 2 * |Cn|) * X ≤ Cs * X := mul_le_mul_of_nonneg_right hCs (h0.trans h1)
    linarith
  have hc' : (turnL L).c = cOfDpsi (ka : ℂ) := by
    show -Complex.I * L.c = _
    rw [hc, cOfDpsi]; push_cast; ring
  obtain ⟨L₁, f₁, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, hsec⟩ :=
    hFr (turnL L) (turnF L f) ka ka⁻¹ (ka ^ D.R.rS) hka (inv_pos.2 hka) (pow_pos hka _) hc' hκ0 hκ hε hgap
      (isKFinCoef_turn L hf)
  have eT : ∀ T : ℝ, (ka ^ D.R.rS) ^ 2 * T = T * ka ^ (2 * D.R.rS) := fun T => by ring
  refine ⟨L₁, f₁, e1, e2, e3, e4, by rw [e5, inv_mul_cancel₀ hka.ne'], e6, e7, e8.trans (eT _), e9.trans (eT _), e10,
    fun μsec hμ => ?_⟩
  obtain ⟨μsec₁, hμ₁, K₁, hK, hj, hpt⟩ := hsec μsec hμ
  rw [jNorm2_turn] at hj
  refine ⟨μsec₁, hμ₁, K₁, hK, hj.le, fun h0 => ?_, fun p hp => ?_⟩
  · rw [hj]
    exact mul_ne_zero (ENNReal.ofReal_pos.2 hK).ne' h0
  obtain ⟨p₁, -, hG, -, hw⟩ := hpt (turnP p) (by rw [GPoint_turnP]; exact hp)
  rw [GPoint_turnP] at hG
  rw [ptWeight_turnP] at hw
  set M : ℝ := ((2 * D.R.rS + 2 : ℕ) : ℝ) with hM
  have hrM : (D.R.rS : ℝ) ≤ M := by rw [hM]; exact_mod_cast (by omega : D.R.rS ≤ 2 * D.R.rS + 2)
  have hM0 : 0 ≤ M := by positivity
  have hs : ka⁻¹ ^ (2 * D.R.rS * (D.R.rS + 1)) * (ka ^ D.R.rS) ^ (4 * (D.R.rS + 1)) = ka ^ (2 * D.R.rS * (D.R.rS + 1)) := by
    have : D.R.rS * (4 * (D.R.rS + 1)) = 2 * D.R.rS * (D.R.rS + 1) + 2 * D.R.rS * (D.R.rS + 1) := by ring
    rw [← pow_mul, this, pow_add, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hka.ne', one_pow, one_mul]
  rw [hs] at hG
  have hpw : ∀ {x : ℝ} (n : ℕ), 0 ≤ x → x ≤ b ^ Ch → x ^ n ≤ b ^ (Ch * n) := fun n h0 h1 => by
    rw [Real.rpow_mul hb0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ h0 h1 n
  have hCC : 0 ≤ Ch * Cf := mul_nonneg hCh hCf
  refine ⟨p₁, ?_, ?_, ?_⟩
  · rw [hG]; exact mul_ne_zero (pow_pos hka _).ne' hp
  · rw [hG]
    refine max_inv_scale (Real.one_le_rpow hb1 (by positivity)) (pow_pos hka _) ?_
    rw [← inv_pow]
    refine (hpw _ (inv_pos.2 hka).le hka2).trans (Real.rpow_le_rpow_of_exponent_le hb1 ?_)
    have h1 : ((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℝ) ≤ M ^ 2 := by
      rw [hM]; exact_mod_cast (by nlinarith : 2 * D.R.rS * (D.R.rS + 1) ≤ (2 * D.R.rS + 2) ^ 2)
    have h2 := mul_le_mul_of_nonneg_left h1 hCh
    have h3 : 0 ≤ Ch * Cf * M ^ 2 := by positivity
    nlinarith
  · have h1 : max ka⁻¹ ka⁻¹⁻¹ ≤ b ^ Ch := max_le hka2 (by rwa [inv_inv])
    have h2 : max (ka ^ D.R.rS) (ka ^ D.R.rS)⁻¹ ≤ b ^ (Ch * D.R.rS) :=
      max_le (hpw _ hka.le hka1) (by rw [← inv_pow]; exact hpw _ (inv_pos.2 hka).le hka2)
    have h3 : max ka⁻¹ ka⁻¹⁻¹ ^ (Cf * M ^ 2) * max (ka ^ D.R.rS) (ka ^ D.R.rS)⁻¹ ^ (Cf * M) ≤ b ^ ((2 * Ch * Cf + Ch) * M ^ 2) := by
      calc _ ≤ (b ^ Ch) ^ (Cf * M ^ 2) * (b ^ (Ch * D.R.rS)) ^ (Cf * M) :=
            mul_le_mul (Real.rpow_le_rpow (le_max_of_le_left (inv_pos.2 hka).le) h1 (by positivity))
              (Real.rpow_le_rpow (le_max_of_le_left (pow_pos hka _).le) h2 (by positivity))
              (Real.rpow_nonneg (le_max_of_le_left (pow_pos hka _).le) _) (by positivity)
        _ = b ^ (Ch * (Cf * M ^ 2) + Ch * D.R.rS * (Cf * M)) := by
            rw [← Real.rpow_mul hb0.le, ← Real.rpow_mul hb0.le, ← Real.rpow_add hb0]
        _ ≤ _ := by
            refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
            have h4 := mul_le_mul_of_nonneg_left hrM (mul_nonneg hCC hM0)
            have h5 : 0 ≤ Ch * M ^ 2 := by positivity
            nlinarith
    rw [ENNReal.ofReal_mul hK.le, ENNReal.ofReal_mul (Real.rpow_nonneg hb0.le _), mul_assoc, mul_assoc]
    refine le_trans ?_ (hw.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal h3) _))
    exact mul_le_mul_right (mul_le_mul_right (orbSqO_le_turn L f p) _) _

end GlobalTheory.FrameTurn
