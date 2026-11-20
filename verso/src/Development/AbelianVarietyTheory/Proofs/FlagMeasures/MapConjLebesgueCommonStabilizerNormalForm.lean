import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousUpperOff

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.RConj

open GlobalTheory.Amp.Rad GlobalTheory.Amp.USplit

variable {k r : ℕ}

/- English proof (translation)
Use `set f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := (Matrix.toLin' g).restrictScalars ℝ with hf`. Establish `hdet : LinearMap.det f = 1`. Rewrite using `[hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hg]`. Establish `hfun : (⇑f) = fun v : ι → ℂ => g *ᵥ v`. Use function extensionality and compare the values at `v`.

Simplify using `[hf, Matrix.toLin'_apply]`. Rewrite using `[← hfun]`. Use `⟨f.continuous_of_finiteDimensional.measurable, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; norm_num), hdet]`. Simplify using the standard rewrite rules.
-/
theorem mulVec_mp {ι : Type*} [Fintype ι] [DecidableEq ι] {g : Matrix ι ι ℂ} (hg : Complex.normSq g.det = 1) :
    MeasurePreserving (fun v : ι → ℂ => g *ᵥ v) volume volume := by
  set f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := (Matrix.toLin' g).restrictScalars ℝ with hf
  have hdet : LinearMap.det f = 1 := by
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hg]
  have hfun : (⇑f) = fun v : ι → ℂ => g *ᵥ v := by
    funext v
    simp [hf, Matrix.toLin'_apply]
  rw [← hfun]
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; norm_num), hdet]
  simp

/- English proof (translation)
Use `set f : ℂ →ₗ[ℝ] ℂ := (LinearMap.mulLeft ℝ a).comp Complex.conjAe.toLinearEquiv.toLinearMap with hf`. Establish `hn : Complex.normSq a = 1`. Rewrite using `[Complex.normSq_eq_norm_sq, ha]`. Evaluate the numerical expressions. Establish `hm : LinearMap.det (LinearMap.mulLeft ℝ a) = Complex.normSq a`.

Rewrite using `[← Algebra.norm_complex_apply, Algebra.norm_apply]`. Both sides reduce to the same expression. Establish `hdet : LinearMap.det f = -1`. Rewrite using `[hf, LinearMap.det_comp, hm, Complex.det_conjAe, hn]`. Evaluate the numerical expressions.

Establish `hfun : (⇑f) = fun z : ℂ => a * star z`. Use function extensionality and compare the values at `z`. Simplify using `[hf]`. Rewrite using `[← hfun]`. Use `⟨f.continuous_of_finiteDimensional.measurable, ?_⟩` and prove the remaining obligations.

Rewrite using `[Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; norm_num), hdet]`. Simplify using the standard rewrite rules.
-/
theorem mul_star_mp {a : ℂ} (ha : ‖a‖ = 1) : MeasurePreserving (fun z : ℂ => a * star z) volume volume := by
  set f : ℂ →ₗ[ℝ] ℂ := (LinearMap.mulLeft ℝ a).comp Complex.conjAe.toLinearEquiv.toLinearMap with hf
  have hn : Complex.normSq a = 1 := by
    rw [Complex.normSq_eq_norm_sq, ha]; norm_num
  have hm : LinearMap.det (LinearMap.mulLeft ℝ a) = Complex.normSq a := by
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl
  have hdet : LinearMap.det f = -1 := by
    rw [hf, LinearMap.det_comp, hm, Complex.det_conjAe, hn]; norm_num
  have hfun : (⇑f) = fun z : ℂ => a * star z := by
    funext z
    simp [hf]
  rw [← hfun]
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; norm_num), hdet]
  simp

/- English proof (translation)
Establish `hM' : Mᴴ * Hb k * M = Hb k` using `hM`. Establish `h` using `congrArg Matrix.det hM'`. Simplify using `only [Matrix.det_mul, Matrix.det_conjTranspose] at h`. Establish `hH : (Hb k).det ≠ 0`. Rewrite using `[show Hb k = Matrix.diagonal fun j => if j = Fin.last k then (-1 : ℂ) else 1 from rfl, Matrix.det_diagonal]`.

Apply the tactic sequence `exact Finset.prod_ne_zero_iff.mpr fun j _ => by split_ifs <;> norm_num`. Establish `h2 : star M.det * M.det = 1`. Apply `mul_right_cancel₀ hH` to reduce the goal to its premises. Rewrite using `[one_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h3 : (Complex.normSq M.det : ℂ) = 1`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Conclude with `h2`. Conclude with `h3` after adjusting the coercions.
-/
theorem normSq_det_of_mem {M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hM : M ∈ UH (Hb k)) :
    Complex.normSq M.det = 1 := by
  have hM' : Mᴴ * Hb k * M = Hb k := hM
  have h := congrArg Matrix.det hM'
  simp only [Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hH : (Hb k).det ≠ 0 := by
    rw [show Hb k = Matrix.diagonal fun j => if j = Fin.last k then (-1 : ℂ) else 1 from rfl,
      Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => by split_ifs <;> norm_num
  have h2 : star M.det * M.det = 1 := by
    apply mul_right_cancel₀ hH
    rw [one_mul]
    calc star M.det * M.det * (Hb k).det = star M.det * (Hb k).det * M.det := by ring
      _ = (Hb k).det := h
  have h3 : (Complex.normSq M.det : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact h2
  exact_mod_cast h3

/- English proof (translation)
Establish `htri : (upper x).BlockTriangular id` using `fun a b hab => upper_of_gt x hab`. Rewrite using `[Matrix.det_of_upperTriangular htri]`. Simplify using `[upper_diag]`.
-/
theorem isUnit_upper (x : UT r → ℂ) : IsUnit (upper x).det := by
  have htri : (upper x).BlockTriangular id := fun a b hab => upper_of_gt x hab
  rw [Matrix.det_of_upperTriangular htri]
  simp [upper_diag]

/- English proof (translation)
Use `letI := Matrix.invertibleOfIsUnitDet u hu`. Establish `htri : u.BlockTriangular f` using `fun i j hij => h i j hij`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular htri hab`.
-/
theorem inv_zero_of {α : Type*} [LinearOrder α] (f : Fin r → α) (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det)
    (h : ∀ a b, f b < f a → u a b = 0) {a b : Fin r} (hab : f b < f a) : u⁻¹ a b = 0 := by
  letI := Matrix.invertibleOfIsUnitDet u hu
  have htri : u.BlockTriangular f := fun i j hij => h i j hij
  exact Matrix.blockTriangular_inv_of_blockTriangular htri hab

/- English proof (translation)
Use `inv_zero_of (fun c : Fin r => c) (upper x) (isUnit_upper x) ?_ h` and prove the remaining obligations. Introduce `a' b' hlt`. Conclude with `upper_of_gt x hlt`.
-/
theorem inv_upper_gt (x : UT r → ℂ) {a b : Fin r} (h : b < a) : (upper x)⁻¹ a b = 0 := by
  refine inv_zero_of (fun c : Fin r => c) (upper x) (isUnit_upper x) ?_ h
  intro a' b' hlt
  exact upper_of_gt x hlt

/- English proof (translation)
Establish `h1 : ((upper x)⁻¹ * upper x) a a = 1`. Rewrite using `[Matrix.nonsing_inv_mul _ (isUnit_upper x), Matrix.one_apply_eq]`. Rewrite `h1` using `[Matrix.mul_apply, Finset.sum_eq_single a]`. Simplify `h1` using `[upper_diag]`. Introduce `c _ hc`.

Break down `lt_or_gt_of_ne hc with hlt | hgt` into its components or cases. Rewrite using `[inv_upper_gt x hlt, zero_mul]`. Rewrite using `[upper_of_gt x hgt, mul_zero]`. Introduce `hna`. Conclude with `absurd (Finset.mem_univ a) hna`.
-/
theorem inv_upper_diag (x : UT r → ℂ) (a : Fin r) : (upper x)⁻¹ a a = 1 := by
  have h1 : ((upper x)⁻¹ * upper x) a a = 1 := by
    rw [Matrix.nonsing_inv_mul _ (isUnit_upper x), Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
  · simpa [upper_diag] using h1
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with hlt | hgt
    · rw [inv_upper_gt x hlt, zero_mul]
    · rw [upper_of_gt x hgt, mul_zero]
  · intro hna
    exact absurd (Finset.mem_univ a) hna

/- English proof (translation)
Establish `h0 : (upper x * (upper x)⁻¹) a b = 0`. Rewrite using `[Matrix.mul_nonsing_inv _ (isUnit_upper x)]`. Conclude with `Matrix.one_apply_ne (ne_of_lt h)`. Rewrite `h0` using `[Matrix.mul_apply]`. Establish `hterm : ∀ c, upper x a c * (upper x)⁻¹ c b = ((if c = a then (upper x)⁻¹ a b else 0) + (if c = b then upper x a b else 0)) + (if a < c ∧ c < b then upper x a c * (upper x)⁻¹ c b else 0)`.

Introduce `c`. Break down `lt_trichotomy c a with hca | hca | hac` into its components or cases. Establish `n1 : ¬ (a < c ∧ c < b)` using `fun hh => absurd (hh.1.trans hca) (lt_irrefl _)`. Rewrite using `[upper_of_gt x hca, zero_mul, if_neg (ne_of_lt hca), if_neg (ne_of_lt (hca.trans h)), if_neg n1]`. Expand and normalize the polynomial expressions, which then agree.

Establish `n1 : ¬ (a < c ∧ c < b)` using `fun hh => absurd hh.1 (by rw [hca]; exact lt_irrefl _)`. Establish `n2 : c ≠ b` using `by rw [hca]; exact ne_of_lt h`. Rewrite using `[if_pos hca, if_neg n2, if_neg n1, hca, upper_diag, one_mul]`. Expand and normalize the polynomial expressions, which then agree. Break down `lt_trichotomy c b with hcb | hcb | hbc` into its components or cases.

Rewrite using `[if_neg (ne_of_gt hac), if_neg (ne_of_lt hcb), if_pos ⟨hac, hcb⟩]`. Expand and normalize the polynomial expressions, which then agree. Establish `n1 : ¬ (a < c ∧ c < b)` using `fun hh => absurd hh.2 (by rw [hcb]; exact lt_irrefl _)`. Rewrite using `[if_neg (ne_of_gt hac), if_pos hcb, if_neg n1, hcb, inv_upper_diag, mul_one]`. Expand and normalize the polynomial expressions, which then agree.

Establish `n1 : ¬ (a < c ∧ c < b)` using `fun hh => absurd (hh.2.trans hbc) (lt_irrefl _)`. Rewrite using `[inv_upper_gt x hbc, mul_zero, if_neg (ne_of_gt hac), if_neg (ne_of_gt hbc), if_neg n1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h0` using `[Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]`. Take the linear combination `-h0`.
-/
theorem inv_upper_lt (x : UT r → ℂ) {a b : Fin r} (h : a < b) :
    -(upper x)⁻¹ a b - upper x a b = ∑ c, if a < c ∧ c < b then upper x a c * (upper x)⁻¹ c b else 0 := by
  have h0 : (upper x * (upper x)⁻¹) a b = 0 := by
    rw [Matrix.mul_nonsing_inv _ (isUnit_upper x)]
    exact Matrix.one_apply_ne (ne_of_lt h)
  rw [Matrix.mul_apply] at h0
  have hterm : ∀ c, upper x a c * (upper x)⁻¹ c b =
      ((if c = a then (upper x)⁻¹ a b else 0) + (if c = b then upper x a b else 0)) +
        (if a < c ∧ c < b then upper x a c * (upper x)⁻¹ c b else 0) := by
    intro c
    rcases lt_trichotomy c a with hca | hca | hac
    · have n1 : ¬ (a < c ∧ c < b) := fun hh => absurd (hh.1.trans hca) (lt_irrefl _)
      rw [upper_of_gt x hca, zero_mul, if_neg (ne_of_lt hca), if_neg (ne_of_lt (hca.trans h)), if_neg n1]
      ring
    · have n1 : ¬ (a < c ∧ c < b) := fun hh => absurd hh.1 (by rw [hca]; exact lt_irrefl _)
      have n2 : c ≠ b := by rw [hca]; exact ne_of_lt h
      rw [if_pos hca, if_neg n2, if_neg n1, hca, upper_diag, one_mul]
      ring
    · rcases lt_trichotomy c b with hcb | hcb | hbc
      · rw [if_neg (ne_of_gt hac), if_neg (ne_of_lt hcb), if_pos ⟨hac, hcb⟩]
        ring
      · have n1 : ¬ (a < c ∧ c < b) := fun hh => absurd hh.2 (by rw [hcb]; exact lt_irrefl _)
        rw [if_neg (ne_of_gt hac), if_pos hcb, if_neg n1, hcb, inv_upper_diag, mul_one]
        ring
      · have n1 : ¬ (a < c ∧ c < b) := fun hh => absurd (hh.2.trans hbc) (lt_irrefl _)
        rw [inv_upper_gt x hbc, mul_zero, if_neg (ne_of_gt hac), if_neg (ne_of_gt hbc), if_neg n1]
        ring
  rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)] at h0
  linear_combination -h0

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `a b hab hm _`. Establish `: a.val < b.val` using `hab`.

Use linear arithmetic over natural numbers and integers. Consider the case `succ m ih`. Introduce `a b hab hm hn`. Rewrite using `[inv_upper_lt x hab, inv_upper_lt y hab]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hc : a < c ∧ c < b`. Rewrite using `[if_pos hc, if_pos hc]`. Establish `hac' : a.val < c.val` using `hc.1`. Establish `hcb' : c.val < b.val` using `hc.2`. Establish `e1 : upper x a c = upper y a c` using `hxy a c hc.1 (by omega)`.

Establish `e2 : upper x c b = upper y c b` using `hxy c b hc.2 (by omega)`. Establish `e3` using `ih c b hc.2 (by omega) (by omega)`. Establish `e4 : (upper x)⁻¹ c b = (upper y)⁻¹ c b`. Rewrite `e3` using `[e2]`. Take the linear combination `-e3`.

Rewrite using `[e1, e4]`. Rewrite using `[if_neg hc, if_neg hc]`.
-/
theorem inv_upper_congr (x y : UT r → ℂ) (n : ℕ)
    (hxy : ∀ a b : Fin r, a < b → b.val - a.val < n → upper x a b = upper y a b) :
    ∀ (m : ℕ) (a b : Fin r), a < b → b.val - a.val ≤ m → b.val - a.val ≤ n →
      -(upper x)⁻¹ a b - upper x a b = -(upper y)⁻¹ a b - upper y a b := by
  intro m
  induction m with
  | zero =>
    intro a b hab hm _
    have : a.val < b.val := hab
    omega
  | succ m ih =>
    intro a b hab hm hn
    rw [inv_upper_lt x hab, inv_upper_lt y hab]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : a < c ∧ c < b
    · rw [if_pos hc, if_pos hc]
      have hac' : a.val < c.val := hc.1
      have hcb' : c.val < b.val := hc.2
      have e1 : upper x a c = upper y a c := hxy a c hc.1 (by omega)
      have e2 : upper x c b = upper y c b := hxy c b hc.2 (by omega)
      have e3 := ih c b hc.2 (by omega) (by omega)
      have e4 : (upper x)⁻¹ c b = (upper y)⁻¹ c b := by
        rw [e2] at e3
        linear_combination -e3
      rw [e1, e4]
    · rw [if_neg hc, if_neg hc]

/- English proof (translation)
Unfold `upperIn`. Establish `hb : (upper fun p : UT r => if h : β p.1.1 = β p.1.2 then x ⟨p, h⟩ else 0).BlockTriangular id` using `fun a b hab => upper_of_gt _ hab`. Rewrite using `[Matrix.det_of_upperTriangular hb]`. Conclude with `Finset.prod_eq_one fun a _ => upper_diag _ a`.
-/
private lemma det_upperIn_eq_one (β : Fin r → ℕ) (x : UTin β → ℂ) : (upperIn β x).det = 1 := by
  unfold upperIn
  have hb : (upper fun p : UT r => if h : β p.1.1 = β p.1.2 then x ⟨p, h⟩ else 0).BlockTriangular id :=
    fun a b hab => upper_of_gt _ hab
  rw [Matrix.det_of_upperTriangular hb]
  exact Finset.prod_eq_one fun a _ => upper_diag _ a

/- English proof (translation)
Establish `hfun : (fun x : UTin β → ℂ => (upperIn β x)⁻¹) = fun x => (upperIn β x).adjugate`. Use function extensionality and compare the values at `x`. Rewrite using `[Matrix.inv_def, det_upperIn_eq_one, Ring.inverse_one, one_smul]`. Rewrite using `[hfun]`. Conclude with `(continuous_upperIn β).matrix_adjugate`.
-/
theorem continuous_inv_upperIn (β : Fin r → ℕ) : Continuous fun x : UTin β → ℂ => (upperIn β x)⁻¹ := by
  have hfun : (fun x : UTin β → ℂ => (upperIn β x)⁻¹) = fun x => (upperIn β x).adjugate := by
    funext x
    rw [Matrix.inv_def, det_upperIn_eq_one, Ring.inverse_one, one_smul]
  rw [hfun]
  exact (continuous_upperIn β).matrix_adjugate

/- English proof (translation)
Take `⟨⟨⟨a, b⟩, hab⟩, hβ⟩` from `p`. Unfold `upperIn`. Rewrite using `[upper_of_lt _ hab]`. Conclude with `dif_pos hβ`.
-/
theorem upperIn_lt (β : Fin r → ℕ) (x : UTin β → ℂ) (p : UTin β) : upperIn β x p.1.1.1 p.1.1.2 = x p := by
  obtain ⟨⟨⟨a, b⟩, hab⟩, hβ⟩ := p
  unfold upperIn
  rw [upper_of_lt _ hab]
  exact dif_pos hβ

/- English proof (translation)
Unfold `upperIn`. Break down `lt_trichotomy a b with hab | hab | hab` into its components or cases. Rewrite using `[upper_of_lt _ hab]`. Conclude with `dif_neg h`. Conclude with `absurd (congrArg β hab) h`.

Conclude with `upper_of_gt _ hab`.
-/
theorem upperIn_ne (β : Fin r → ℕ) (x : UTin β → ℂ) {a b : Fin r} (h : β a ≠ β b) : upperIn β x a b = 0 := by
  unfold upperIn
  rcases lt_trichotomy a b with hab | hab | hab
  · rw [upper_of_lt _ hab]
    exact dif_neg h
  · exact absurd (congrArg β hab) h
  · exact upper_of_gt _ hab

/- English proof (translation)
Use `haveI : Invertible (upperIn β x) := Matrix.invertibleOfIsUnitDet _ (isUnit_upper _)`. Establish `h1 : (upperIn β x).BlockTriangular β` using `fun i j hij => upperIn_ne β x (ne_of_gt hij)`. Establish `h2 : (upperIn β x).BlockTriangular (fun i => OrderDual.toDual (β i))` using `fun i j hij => upperIn_ne β x (ne_of_lt (OrderDual.toDual_lt_toDual.mp hij))`. Break down `lt_or_gt_of_ne h with hlt | hlt` into its components or cases. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular h2 (OrderDual.toDual_lt_toDual.mpr hlt)`.

Conclude with `Matrix.blockTriangular_inv_of_blockTriangular h1 hlt`.
-/
theorem inv_upperIn_ne (β : Fin r → ℕ) (x : UTin β → ℂ) {a b : Fin r} (h : β a ≠ β b) : (upperIn β x)⁻¹ a b = 0 := by
  haveI : Invertible (upperIn β x) := Matrix.invertibleOfIsUnitDet _ (isUnit_upper _)
  have h1 : (upperIn β x).BlockTriangular β := fun i j hij => upperIn_ne β x (ne_of_gt hij)
  have h2 : (upperIn β x).BlockTriangular (fun i => OrderDual.toDual (β i)) :=
    fun i j hij => upperIn_ne β x (ne_of_lt (OrderDual.toDual_lt_toDual.mp hij))
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact Matrix.blockTriangular_inv_of_blockTriangular h2 (OrderDual.toDual_lt_toDual.mpr hlt)
  · exact Matrix.blockTriangular_inv_of_blockTriangular h1 hlt

def shearInv (j : ℕ) (β : Fin r → ℕ) (x : UTin β → ℂ) : UTin β → ℂ := fun p =>
  if p.1.1.1.val < j then -(upperIn β x)⁻¹ p.1.1.1 p.1.1.2 else x p

/- English proof (translation)
Use `Formalism.FourierDecayAlt.P.ShearMeasurability.shear_mp (fun p : UTin β => p.1.1.2.val - p.1.1.1.val) (shearInv j β) ?_ ?_` and prove the remaining obligations. Use `Continuous.measurable (continuous_pi fun p => ?_)` and prove the remaining obligations. Distinguish the cases in `hp : p.1.1.1.val < j`. Simplify using `only [shearInv, hp, if_true]`. Conclude with `((continuous_apply p.1.1.2).comp ((continuous_apply p.1.1.1).comp (continuous_inv_upperIn β))).neg`.

Simplify using `only [shearInv, hp, if_false]`. Conclude with `continuous_apply p`. Introduce `q x y hxy`. Distinguish the cases in `hq : q.1.1.1.val < j`. Simplify using `only [shearInv, hq, if_true]`.

Rewrite using `[← upperIn_lt β x q, ← upperIn_lt β y q]`. Unfold `upperIn`. Use `inv_upper_congr _ _ (q.1.1.2.val - q.1.1.1.val) (fun a b hab hlt => ?_) _ _ _ q.1.2 le_rfl le_rfl` and prove the remaining obligations. Rewrite using `[upper_of_lt _ hab, upper_of_lt _ hab]`. Distinguish the cases in `hβ : β a = β b`.

Simplify using `only [dif_pos hβ]`. Conclude with `hxy ⟨⟨(a, b), hab⟩, hβ⟩ hlt`. Simplify using `only [dif_neg hβ]`. Simplify using `only [shearInv, hq, if_false, sub_self]`.
-/
theorem shearInv_mp (j : ℕ) (β : Fin r → ℕ) : MeasurePreserving (shearInv j β) volume volume := by
  refine Formalism.FourierDecayAlt.P.ShearMeasurability.shear_mp (fun p : UTin β => p.1.1.2.val - p.1.1.1.val) (shearInv j β) ?_ ?_
  · refine Continuous.measurable (continuous_pi fun p => ?_)
    by_cases hp : p.1.1.1.val < j
    · simp only [shearInv, hp, if_true]
      exact ((continuous_apply p.1.1.2).comp ((continuous_apply p.1.1.1).comp
        (continuous_inv_upperIn β))).neg
    · simp only [shearInv, hp, if_false]
      exact continuous_apply p
  · intro q x y hxy
    by_cases hq : q.1.1.1.val < j
    · simp only [shearInv, hq, if_true]
      rw [← upperIn_lt β x q, ← upperIn_lt β y q]
      unfold upperIn
      refine inv_upper_congr _ _ (q.1.1.2.val - q.1.1.1.val) (fun a b hab hlt => ?_) _ _ _ q.1.2 le_rfl le_rfl
      rw [upper_of_lt _ hab, upper_of_lt _ hab]
      by_cases hβ : β a = β b
      · simp only [dif_pos hβ]
        exact hxy ⟨⟨(a, b), hab⟩, hβ⟩ hlt
      · simp only [dif_neg hβ]
    · simp only [shearInv, hq, if_false, sub_self]

def HasBlocks (g : Mat k r) (D Y Z : Matrix (Fin r) (Fin r) ℂ) (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop :=
  (∀ a b, g (eI k r a) (eI k r b) = D a b) ∧ (∀ a n, g (eI k r a) (wI k r n) = 0) ∧
  (∀ a b, g (eI k r a) (esI k r b) = Y a b) ∧ (∀ n b, g (wI k r n) (eI k r b) = 0) ∧
  (∀ m n, g (wI k r m) (wI k r n) = M m n) ∧ (∀ n b, g (wI k r n) (esI k r b) = 0) ∧
  (∀ a b, g (esI k r a) (eI k r b) = Z a b) ∧ (∀ a n, g (esI k r a) (wI k r n) = 0) ∧
  (∀ a b, g (esI k r a) (esI k r b) = D a b)

section
variable (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) (m n : Fin (k + 1))
/- English proof (translation)
Establish `ha` using `a.isLt`. Unfold `uEmb`. Apply the tactic sequence `split_ifs <;> first`. Consider the case `rfl`. Consider the case `(exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)`.
-/
theorem u_ew : uEmb k r u (eI k r a) (wI k r n) = 0 := by
  have ha := a.isLt
  unfold uEmb
  split_ifs <;> first
    | rfl
    | (exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)
/- English proof (translation)
Establish `hb` using `b.isLt`. Unfold `uEmb`. Apply the tactic sequence `split_ifs <;> first`. Consider the case `rfl`. Consider the case `(exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)`.
-/
theorem u_we : uEmb k r u (wI k r m) (eI k r b) = 0 := by
  have hb := b.isLt
  unfold uEmb
  split_ifs <;> first
    | rfl
    | (exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)
/- English proof (translation)
Unfold `uEmb`. Apply the tactic sequence `split_ifs <;> first`. Consider the case `rfl`. Consider the case `(exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)`.
-/
theorem u_ww : uEmb k r u (wI k r m) (wI k r n) = if m = n then 1 else 0 := by
  unfold uEmb
  split_ifs <;> first
    | rfl
    | (exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)
/- English proof (translation)
Establish `hb` using `b.isLt`. Unfold `uEmb`. Apply the tactic sequence `split_ifs <;> first`. Consider the case `rfl`. Consider the case `(exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)`.
-/
theorem u_ws : uEmb k r u (wI k r m) (esI k r b) = 0 := by
  have hb := b.isLt
  unfold uEmb
  split_ifs <;> first
    | rfl
    | (exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)
/- English proof (translation)
Establish `ha` using `a.isLt`. Unfold `uEmb`. Apply the tactic sequence `split_ifs <;> first`. Consider the case `rfl`. Consider the case `(exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)`.
-/
theorem u_sw : uEmb k r u (esI k r a) (wI k r n) = 0 := by
  have ha := a.isLt
  unfold uEmb
  split_ifs <;> first
    | rfl
    | (exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)
/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Unfold `uEmb`. Use `split_ifs with h1 h2`. It suffices to derive a contradiction.

Simplify using `only [esI] at h1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[conjTranspose_apply]`. Establish `key : ∀ x y : Fin r, x.val = b.val → y.val = a.val → u⁻¹ x y = u⁻¹ b a`. Introduce `x y hx hy`.

Rewrite using `[Fin.ext hx, Fin.ext hy]`. Conclude with `congrArg star (key _ _ (by simp only [esI]; omega) (by simp only [esI]; omega))`. It suffices to derive a contradiction. Apply `h2` to reduce the goal to its premises. Simplify using `only [esI]`.

Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction. Apply `h2` to reduce the goal to its premises. Simplify using `only [esI]`. Use linear arithmetic over natural numbers and integers.
-/
theorem u_ss : uEmb k r u (esI k r a) (esI k r b) = (u⁻¹)ᴴ a b := by
  have ha := a.isLt
  have hb := b.isLt
  unfold uEmb
  split_ifs with h1 h2
  · exfalso; simp only [esI] at h1; omega
  · rw [conjTranspose_apply]
    have key : ∀ x y : Fin r, x.val = b.val → y.val = a.val → u⁻¹ x y = u⁻¹ b a := by
      intro x y hx hy
      rw [Fin.ext hx, Fin.ext hy]
    exact congrArg star (key _ _ (by simp only [esI]; omega) (by simp only [esI]; omega))
  · exfalso; apply h2; simp only [esI]; omega
  · exfalso; apply h2; simp only [esI]; omega

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Unfold `uEmb`. Apply the tactic sequence `split_ifs <;> first`. Consider the case `rfl`.

Consider the case `(exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)`.
-/
private lemma uEmb_eI_eI (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    uEmb k r u (eI k r a) (eI k r b) = u a b := by
  have ha := a.isLt
  have hb := b.isLt
  unfold uEmb
  split_ifs <;> first
    | rfl
    | (exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Unfold `uEmb`. Apply the tactic sequence `split_ifs <;> first`. Consider the case `rfl`.

Consider the case `(exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)`.
-/
private lemma uEmb_eI_esI (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    uEmb k r u (eI k r a) (esI k r b) = 0 := by
  have ha := a.isLt
  have hb := b.isLt
  unfold uEmb
  split_ifs <;> first
    | rfl
    | (exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Unfold `uEmb`. Apply the tactic sequence `split_ifs <;> first`. Consider the case `rfl`.

Consider the case `(exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)`.
-/
private lemma uEmb_esI_eI (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    uEmb k r u (esI k r a) (eI k r b) = 0 := by
  have ha := a.isLt
  have hb := b.isLt
  unfold uEmb
  split_ifs <;> first
    | rfl
    | (exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)
end

/- English proof (translation)
Take `⟨hee, hew, hes, hwe, hww, hws, hse, hsw, hss⟩` from `hg`. Use extensionality with `i j`. Apply the tactic sequence `induction i using cases3 <;> induction j using cases3 <;>`. Simplify using `only [Matrix.mul_apply, sum3, hee, hew, hes, hwe, hww, hws, hse, hsw, hss, uEmb_eI_eI, uEmb_eI_esI, uEmb_esI_eI, u_ew, u_we, u_ww, u_ws, u_sw, u_ss, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_ite, ite_mul, mul_one, one_mul, Finset.sum_ite_eq, Finset.sum_it …`. Apply the tactic sequence `all_goals first`.

Consider the case `rfl`. Consider the case `simpa only [Matrix.mul_apply] using congrFun (congrFun h1 _) _`. Consider the case `simpa only [Matrix.mul_apply] using congrFun (congrFun h2 _) _`. Consider the case `simpa only [Matrix.mul_apply] using congrFun (congrFun h3 _) _`. Consider the case `simpa only [Matrix.mul_apply] using congrFun (congrFun h4 _) _`.
-/
theorem conj_u {g : Mat k r} {D Y Z : Matrix (Fin r) (Fin r) ℂ} {M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hg : HasBlocks g D Y Z M) {u u' : Matrix (Fin r) (Fin r) ℂ} (h1 : D * u = u' * D) (h2 : Y * (u⁻¹)ᴴ = u' * Y)
    (h3 : Z * u = (u'⁻¹)ᴴ * Z) (h4 : D * (u⁻¹)ᴴ = (u'⁻¹)ᴴ * D) : g * uEmb k r u = uEmb k r u' * g := by
  obtain ⟨hee, hew, hes, hwe, hww, hws, hse, hsw, hss⟩ := hg
  ext i j
  induction i using cases3 <;> induction j using cases3 <;>
    simp only [Matrix.mul_apply, sum3, hee, hew, hes, hwe, hww, hws, hse, hsw, hss, uEmb_eI_eI, uEmb_eI_esI,
      uEmb_esI_eI, u_ew, u_we, u_ww, u_ws, u_sw, u_ss, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
      zero_add, mul_ite, ite_mul, mul_one, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  all_goals first
    | rfl
    | simpa only [Matrix.mul_apply] using congrFun (congrFun h1 _) _
    | simpa only [Matrix.mul_apply] using congrFun (congrFun h2 _) _
    | simpa only [Matrix.mul_apply] using congrFun (congrFun h3 _) _
    | simpa only [Matrix.mul_apply] using congrFun (congrFun h4 _) _

/- English proof (translation)
Establish `hui1 : u * u⁻¹ = 1` using `Matrix.mul_nonsing_inv u hu`. Establish `hui2 : u⁻¹ * u = 1` using `Matrix.nonsing_inv_mul u hu`. Establish `hA1 : (u⁻¹)ᴴ * uᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, hui1, Matrix.conjTranspose_one]`. Establish `hZhF : Zᴴ * F = 0`. Establish `h0` using `congrArg Matrix.conjTranspose hFZ`.

Rewrite `h0` using `[Matrix.conjTranspose_mul, hF, Matrix.conjTranspose_zero]`. Then use the resulting hypothesis. Establish `hYhF : Yᴴ * F = 0`. Establish `h0` using `congrArg Matrix.conjTranspose hFY`. Rewrite `h0` using `[Matrix.conjTranspose_mul, hF, Matrix.conjTranspose_zero]`. Then use the resulting hypothesis. Establish `hZhY : Zᴴ * Y = 1 - F`.

Establish `h0` using `congrArg Matrix.conjTranspose hYZ`. Rewrite `h0` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hF]`. Then use the resulting hypothesis. Establish `huiF : u⁻¹ * F = F * u⁻¹`. Combine the equalities or inequalities in the displayed calculation. Establish `hAF : (u⁻¹)ᴴ * F = F * (u⁻¹)ᴴ`.

Establish `h0` using `congrArg Matrix.conjTranspose huiF`. Rewrite `h0` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hF]`. Conclude with `h0.symm`. Establish `t1 : Y * (u⁻¹)ᴴ * Zᴴ * (Y * uᴴ * Zᴴ) = 1 - F`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Y * ((u⁻¹)ᴴ * uᴴ) * Zᴴ - Y * (F * (u⁻¹)ᴴ) * uᴴ * Zᴴ := by`. Rewrite using `[hZhY, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.sub_mul, ← hAF]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Y * Zᴴ := by`.

Rewrite using `[hA1, Matrix.mul_one, ← Matrix.mul_assoc Y F, hYF, Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul, sub_zero]`. Use `_ = 1 - F := hZY`. Establish `t2 : Y * (u⁻¹)ᴴ * Zᴴ * (F * u⁻¹) = 0`. Combine the equalities or inequalities in the displayed calculation. Establish `t3 : F * u * (Y * uᴴ * Zᴴ) = 0`.

Combine the equalities or inequalities in the displayed calculation. Establish `t4 : F * u * (F * u⁻¹) = F`. Combine the equalities or inequalities in the displayed calculation. Establish `hinv : (Y * (u⁻¹)ᴴ * Zᴴ + F * u) * (Y * uᴴ * Zᴴ + F * u⁻¹) = 1`. Rewrite using `[Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, t1, t2, t3, t4]`.

Normalize the expressions using the abelian group laws. Establish `hvinv : (Y * (u⁻¹)ᴴ * Zᴴ + F * u)⁻¹ = Y * uᴴ * Zᴴ + F * u⁻¹` using `Matrix.inv_eq_right_inv hinv`. Establish `hvH : (Y * uᴴ * Zᴴ + F * u⁻¹)ᴴ = Z * u * Yᴴ + (u⁻¹)ᴴ * F`. Rewrite using `[Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose, hF]`. Simplify using `only [Matrix.mul_assoc]`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul]`. Use `congr 1`. Establish `e0 : Y * (u⁻¹)ᴴ * Zᴴ * F = 0` using `by rw [Matrix.mul_assoc, hZhF, Matrix.mul_zero]`. Rewrite using `[Matrix.add_mul, e0, zero_add, Matrix.mul_assoc, huF, ← Matrix.mul_assoc, hFF]`.

Establish `e1 : Y * (u⁻¹)ᴴ * Zᴴ * Y = Y * (u⁻¹)ᴴ`. Rewrite using `[Matrix.mul_assoc, hZhY, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, hAF, ← Matrix.mul_assoc, hYF, Matrix.zero_mul, sub_zero]`. Establish `e2 : F * u * Y = 0` using `by rw [← huF, Matrix.mul_assoc, hFY, Matrix.mul_zero]`. Rewrite using `[Matrix.add_mul, e1, e2, add_zero]`. Establish `e1 : Z * u * Yᴴ * Z = Z * u`.

Rewrite using `[Matrix.mul_assoc, hYZ, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, huF, ← Matrix.mul_assoc, hZF, Matrix.zero_mul, sub_zero]`. Establish `e2 : (u⁻¹)ᴴ * F * Z = 0` using `by rw [Matrix.mul_assoc, hFZ, Matrix.mul_zero]`. Rewrite using `[hvinv, hvH, Matrix.add_mul, e1, e2, add_zero]`. Rewrite using `[hvinv, hvH, Matrix.smul_mul, Matrix.mul_smul]`. Use `congr 1`.

Rewrite using `[Matrix.add_mul, Matrix.mul_assoc (Z * u), hYhF, Matrix.mul_zero, zero_add, Matrix.mul_assoc, hFF, hAF]`.
-/
theorem alg {Y Z F u : Matrix (Fin r) (Fin r) ℂ} (c : ℂ) (hu : IsUnit u.det) (hF : Fᴴ = F) (hFF : F * F = F)
    (hYZ : Yᴴ * Z = 1 - F) (hZY : Y * Zᴴ = 1 - F) (hFY : F * Y = 0) (hYF : Y * F = 0) (hFZ : F * Z = 0) (hZF : Z * F = 0)
    (huF : u * F = F * u) :
    (c • F) * u = (Y * (u⁻¹)ᴴ * Zᴴ + F * u) * (c • F) ∧ Y * (u⁻¹)ᴴ = (Y * (u⁻¹)ᴴ * Zᴴ + F * u) * Y ∧
    Z * u = ((Y * (u⁻¹)ᴴ * Zᴴ + F * u)⁻¹)ᴴ * Z ∧ (c • F) * (u⁻¹)ᴴ = ((Y * (u⁻¹)ᴴ * Zᴴ + F * u)⁻¹)ᴴ * (c • F) := by
  have hui1 : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv u hu
  have hui2 : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul u hu
  have hA1 : (u⁻¹)ᴴ * uᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hui1, Matrix.conjTranspose_one]
  have hZhF : Zᴴ * F = 0 := by
    have h0 := congrArg Matrix.conjTranspose hFZ
    rwa [Matrix.conjTranspose_mul, hF, Matrix.conjTranspose_zero] at h0
  have hYhF : Yᴴ * F = 0 := by
    have h0 := congrArg Matrix.conjTranspose hFY
    rwa [Matrix.conjTranspose_mul, hF, Matrix.conjTranspose_zero] at h0
  have hZhY : Zᴴ * Y = 1 - F := by
    have h0 := congrArg Matrix.conjTranspose hYZ
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hF] at h0
  have huiF : u⁻¹ * F = F * u⁻¹ := by
    calc u⁻¹ * F = u⁻¹ * F * (u * u⁻¹) := by rw [hui1, Matrix.mul_one]
      _ = u⁻¹ * (F * u) * u⁻¹ := by simp only [Matrix.mul_assoc]
      _ = u⁻¹ * (u * F) * u⁻¹ := by rw [huF]
      _ = F * u⁻¹ := by rw [← Matrix.mul_assoc u⁻¹, hui2, Matrix.one_mul]
  have hAF : (u⁻¹)ᴴ * F = F * (u⁻¹)ᴴ := by
    have h0 := congrArg Matrix.conjTranspose huiF
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hF] at h0
    exact h0.symm
  have t1 : Y * (u⁻¹)ᴴ * Zᴴ * (Y * uᴴ * Zᴴ) = 1 - F := by
    calc Y * (u⁻¹)ᴴ * Zᴴ * (Y * uᴴ * Zᴴ) = Y * (u⁻¹)ᴴ * (Zᴴ * Y) * uᴴ * Zᴴ := by
          simp only [Matrix.mul_assoc]
      _ = Y * ((u⁻¹)ᴴ * uᴴ) * Zᴴ - Y * (F * (u⁻¹)ᴴ) * uᴴ * Zᴴ := by
          rw [hZhY, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.sub_mul, ← hAF]
          simp only [Matrix.mul_assoc]
      _ = Y * Zᴴ := by
          rw [hA1, Matrix.mul_one, ← Matrix.mul_assoc Y F, hYF, Matrix.zero_mul, Matrix.zero_mul,
            Matrix.zero_mul, sub_zero]
      _ = 1 - F := hZY
  have t2 : Y * (u⁻¹)ᴴ * Zᴴ * (F * u⁻¹) = 0 := by
    calc Y * (u⁻¹)ᴴ * Zᴴ * (F * u⁻¹) = Y * (u⁻¹)ᴴ * (Zᴴ * F) * u⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hZhF, Matrix.mul_zero, Matrix.zero_mul]
  have t3 : F * u * (Y * uᴴ * Zᴴ) = 0 := by
    calc F * u * (Y * uᴴ * Zᴴ) = u * (F * Y) * uᴴ * Zᴴ := by rw [← huF]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hFY, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]
  have t4 : F * u * (F * u⁻¹) = F := by
    calc F * u * (F * u⁻¹) = F * (u * F) * u⁻¹ := by simp only [Matrix.mul_assoc]
      _ = F := by rw [huF, ← Matrix.mul_assoc, hFF, Matrix.mul_assoc, hui1, Matrix.mul_one]
  have hinv : (Y * (u⁻¹)ᴴ * Zᴴ + F * u) * (Y * uᴴ * Zᴴ + F * u⁻¹) = 1 := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, t1, t2, t3, t4]
    abel
  have hvinv : (Y * (u⁻¹)ᴴ * Zᴴ + F * u)⁻¹ = Y * uᴴ * Zᴴ + F * u⁻¹ := Matrix.inv_eq_right_inv hinv
  have hvH : (Y * uᴴ * Zᴴ + F * u⁻¹)ᴴ = Z * u * Yᴴ + (u⁻¹)ᴴ * F := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose, hF]
    simp only [Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    have e0 : Y * (u⁻¹)ᴴ * Zᴴ * F = 0 := by rw [Matrix.mul_assoc, hZhF, Matrix.mul_zero]
    rw [Matrix.add_mul, e0, zero_add, Matrix.mul_assoc, huF, ← Matrix.mul_assoc, hFF]
  · have e1 : Y * (u⁻¹)ᴴ * Zᴴ * Y = Y * (u⁻¹)ᴴ := by
      rw [Matrix.mul_assoc, hZhY, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, hAF,
        ← Matrix.mul_assoc, hYF, Matrix.zero_mul, sub_zero]
    have e2 : F * u * Y = 0 := by rw [← huF, Matrix.mul_assoc, hFY, Matrix.mul_zero]
    rw [Matrix.add_mul, e1, e2, add_zero]
  · have e1 : Z * u * Yᴴ * Z = Z * u := by
      rw [Matrix.mul_assoc, hYZ, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, huF,
        ← Matrix.mul_assoc, hZF, Matrix.zero_mul, sub_zero]
    have e2 : (u⁻¹)ᴴ * F * Z = 0 := by rw [Matrix.mul_assoc, hFZ, Matrix.mul_zero]
    rw [hvinv, hvH, Matrix.add_mul, e1, e2, add_zero]
  · rw [hvinv, hvH, Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    rw [Matrix.add_mul, Matrix.mul_assoc (Z * u), hYhF, Matrix.mul_zero, zero_add, Matrix.mul_assoc, hFF, hAF]

/- English proof (translation)
Establish `hM' : Mᴴ * Hb k * M = Hb k` using `hM`. Use `show star (M *ᵥ w) ⬝ᵥ (Hb k *ᵥ (M *ᵥ v)) = star w ⬝ᵥ (Hb k *ᵥ v)`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM']`.
-/
theorem herm_mulVec {M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hM : M ∈ UH (Hb k)) (v w : Fin (k + 1) → ℂ) :
    herm (Hb k) (M *ᵥ v) (M *ᵥ w) = herm (Hb k) v w := by
  have hM' : Mᴴ * Hb k * M = Hb k := hM
  show star (M *ᵥ w) ⬝ᵥ (Hb k *ᵥ (M *ᵥ v)) = star w ⬝ᵥ (Hb k *ᵥ v)
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM']

/- English proof (translation)
Use `show star (d • w) ⬝ᵥ (Hb k *ᵥ (c • v)) = c * star d * (star w ⬝ᵥ (Hb k *ᵥ v))`. Rewrite using `[star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_smul (c d : ℂ) (v w : Fin (k + 1) → ℂ) :
    herm (Hb k) (c • v) (d • w) = c * star d * herm (Hb k) v w := by
  show star (d • w) ⬝ᵥ (Hb k *ᵥ (c • v)) = c * star d * (star w ⬝ᵥ (Hb k *ᵥ v))
  rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/- English proof (translation)
Establish `hU : ∀ l, ∑ m, star (M m l) * sg k m * M m n = if l = n then sg k l else 0`. Introduce `l`. Establish `h` using `congrFun (congrFun hM l) n`. Rewrite using `[← Hb_apply, ← h]`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Hb_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `m _`. Simplify using `only [Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_mul]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `l _`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑ l, star (v l) * ∑ m, star (M m l) * sg k m * M m n := by`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [Finset.mul_sum]`.

Use `_ = star (v n) * sg k n := by`. Simplify using `only [hU, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
private lemma sum_star_mulVec_mul_sg_mul_eq {M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hM : M ∈ UH (Hb k))
    (v : Fin (k + 1) → ℂ) (n : Fin (k + 1)) :
    ∑ m, star ((M *ᵥ v) m) * sg k m * M m n = star (v n) * sg k n := by
  have hU : ∀ l, ∑ m, star (M m l) * sg k m * M m n = if l = n then sg k l else 0 := by
    intro l
    have h := congrFun (congrFun hM l) n
    rw [← Hb_apply, ← h]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Hb_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  calc ∑ m, star ((M *ᵥ v) m) * sg k m * M m n
      = ∑ m, ∑ l, star (v l) * (star (M m l) * sg k m * M m n) := by
        apply Finset.sum_congr rfl
        intro m _
        simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        ring
    _ = ∑ l, star (v l) * ∑ m, star (M m l) * sg k m * M m n := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ = star (v n) * sg k n := by
        simp only [hU, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

def Fj (r j : ℕ) : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a => if j ≤ a.val then 1 else 0

/- English proof (translation)
Take `⟨hee, hew, hes, hwe, hww, hws, hse, hsw, hss⟩` from `hg`. Establish `hD : ∀ a b : Fin r, (c • Fj r j) a b = if a = b then (if j ≤ a.val then c else 0) else 0`. Introduce `a b`. Simplify using `only [Fj, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hcc : star c * c = 1`. Establish `h2 : Complex.normSq c = 1` using `by rw [Complex.normSq_eq_norm_sq, hc]; norm_num`. Rewrite using `[Complex.star_def, ← Complex.normSq_eq_conj_mul_self, h2]`. Simplify using the standard rewrite rules. Establish `hB' : ∀ a : Fin r, a.val < j → star c • M *ᵥ B a = 0`.

Introduce `a h`. Rewrite using `[hB a h, mulVec_zero, smul_zero]`. Establish `hv1 : ∀ a b : Fin r, ∑ x, (S a x - herm (Hb k) (star c • M *ᵥ B x) (star c • M *ᵥ B a) / 2) * Z x b = 0`. Introduce `a b`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `x _`. Distinguish the cases in `h : j ≤ x.val`. Rewrite using `[hZ x b (Or.inl h), mul_zero]`. Use `push_neg at h`. Rewrite using `[hS a x (Or.inr h), hB' x h]`.

Simplify using `[herm]`. Use extensionality with `x y`. Apply the tactic sequence `induction x using cases3 <;> induction y using cases3 <;>`. Simplify using `only [Matrix.mul_apply, sum3, hee, hew, hes, hwe, hww, hws, hse, hsw, hss, hD, pEl_ee, pEl_ew, pEl_es, pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_ite, ite_mul, mul_one, one_mul, Finset.sum_ite_eq, Finset.sum_ …`. Apply the tactic sequence `all_goals first`.

Consider the case `rfl`. Consider the case `(rw [hv1, add_zero]; split_ifs <;> simp_all)`. Consider the case `(rename_i a n`. Distinguish the cases in `h : j ≤ a.val`. Rewrite using `[if_pos h, ← sum_star_mulVec_mul_sg_mul_eq hM (B a) n, ← Finset.sum_neg_distrib, Finset.mul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `x _`. Simplify using `only [Pi.smul_apply, smul_eq_mul, star_mul', star_star]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h, hB' a (by omega)] simp)`.

Consider the case `(rename_i a b`. Rewrite using `[add_comm]`. Use `congr 1`. Apply the tactic sequence `by_cases ha : j ≤ a.val <;> by_cases hb : j ≤ b.val`. Simplify using `only [ha, hb, if_true, herm_smul, herm_mulVec hM, star_star, hcc, one_mul]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [ha, hb, if_true, if_false, hS a b (Or.inr (by omega)), hB b (by omega)]`. Simplify using `[herm]`. Simplify using `only [ha, hb, if_true, if_false, hS a b (Or.inl (by omega)), hB' a (by omega)]`. Simplify using `[herm]`.

Simplify using `only [ha, hb, if_false])`. Consider the case `(rename_i m a`. Rewrite using `[ite_self, zero_add]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `x _`. Distinguish the cases in `h : j ≤ x.val`. Rewrite using `[hZ x a (Or.inl h), mul_zero]`. Rewrite using `[hB' x (by omega)] simp)`. Consider the case `(rename_i m b`.

Distinguish the cases in `h : j ≤ b.val`. Rewrite using `[if_pos h]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]`. Take the linear combination `-(∑ x, M m x * B b x) * hcc`. Rewrite using `[if_neg h, hB b (by omega)] simp)`.

Consider the case `(rw [ite_self, zero_add])`. Consider the case `(rename_i a n`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `x _`. Distinguish the cases in `h : j ≤ x.val`.

Rewrite using `[hZ a x (Or.inr h), zero_mul]`. Rewrite using `[hB x (by omega)] simp)`. Consider the case `(rename_i a b`. Establish `hz : ∑ x, Z a x * (S x b - herm (Hb k) (B b) (B x) / 2) = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `x _`. Distinguish the cases in `h : j ≤ x.val`. Rewrite using `[hZ a x (Or.inr h), zero_mul]`. Rewrite using `[hS x b (Or.inl (by omega)), hB x (by omega)]`. Simplify using `[herm]`.

Simplify using `only [hz, zero_add, add_zero]`. Apply the tactic sequence `split_ifs <;> simp_all)`. Consider the case `(clear hee hew hes hwe hww hws hse hsw hss hD hZ hS hB hc hM hv1; done)`.
-/
theorem conj_p {j : ℕ} {g : Mat k r} {c : ℂ} {Y Z : Matrix (Fin r) (Fin r) ℂ} {M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hg : HasBlocks g (c • Fj r j) Y Z M) (hc : ‖c‖ = 1) (hM : M ∈ UH (Hb k))
    (hZ : ∀ a b : Fin r, j ≤ a.val ∨ j ≤ b.val → Z a b = 0)
    (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (hB : ∀ a : Fin r, a.val < j → B a = 0)
    (hS : ∀ a b : Fin r, a.val < j ∨ b.val < j → S a b = 0) :
    g * pEl k r B S = pEl k r (fun a => star c • M *ᵥ B a) S * g := by
  obtain ⟨hee, hew, hes, hwe, hww, hws, hse, hsw, hss⟩ := hg
  have hD : ∀ a b : Fin r, (c • Fj r j) a b = if a = b then (if j ≤ a.val then c else 0) else 0 := by
    intro a b
    simp only [Fj, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs <;> simp
  have hcc : star c * c = 1 := by
    have h2 : Complex.normSq c = 1 := by rw [Complex.normSq_eq_norm_sq, hc]; norm_num
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, h2]; simp
  have hB' : ∀ a : Fin r, a.val < j → star c • M *ᵥ B a = 0 := by
    intro a h
    rw [hB a h, mulVec_zero, smul_zero]
  have hv1 : ∀ a b : Fin r,
      ∑ x, (S a x - herm (Hb k) (star c • M *ᵥ B x) (star c • M *ᵥ B a) / 2) * Z x b = 0 := by
    intro a b
    apply Finset.sum_eq_zero
    intro x _
    by_cases h : j ≤ x.val
    · rw [hZ x b (Or.inl h), mul_zero]
    · push_neg at h
      rw [hS a x (Or.inr h), hB' x h]
      simp [herm]
  ext x y
  induction x using cases3 <;> induction y using cases3 <;>
    simp only [Matrix.mul_apply, sum3, hee, hew, hes, hwe, hww, hws, hse, hsw, hss, hD, pEl_ee, pEl_ew, pEl_es,
      pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
      zero_add, mul_ite, ite_mul, mul_one, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  all_goals first
    | rfl
    | (rw [hv1, add_zero]; split_ifs <;> simp_all)
    | (rename_i a n
       by_cases h : j ≤ a.val
       · rw [if_pos h, ← sum_star_mulVec_mul_sg_mul_eq hM (B a) n, ← Finset.sum_neg_distrib, Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro x _
         simp only [Pi.smul_apply, smul_eq_mul, star_mul', star_star]
         ring
       · rw [if_neg h, hB' a (by omega)]
         simp)
    | (rename_i a b
       rw [add_comm]
       congr 1
       by_cases ha : j ≤ a.val <;> by_cases hb : j ≤ b.val
       · simp only [ha, hb, if_true, herm_smul, herm_mulVec hM, star_star, hcc, one_mul]
         ring
       · simp only [ha, hb, if_true, if_false, hS a b (Or.inr (by omega)), hB b (by omega)]
         simp [herm]
       · simp only [ha, hb, if_true, if_false, hS a b (Or.inl (by omega)), hB' a (by omega)]
         simp [herm]
       · simp only [ha, hb, if_false])
    | (rename_i m a
       rw [ite_self, zero_add]
       symm
       apply Finset.sum_eq_zero
       intro x _
       by_cases h : j ≤ x.val
       · rw [hZ x a (Or.inl h), mul_zero]
       · rw [hB' x (by omega)]
         simp)
    | (rename_i m b
       by_cases h : j ≤ b.val
       · rw [if_pos h]
         simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
         linear_combination -(∑ x, M m x * B b x) * hcc
       · rw [if_neg h, hB b (by omega)]
         simp)
    | (rw [ite_self, zero_add])
    | (rename_i a n
       apply Finset.sum_eq_zero
       intro x _
       by_cases h : j ≤ x.val
       · rw [hZ a x (Or.inr h), zero_mul]
       · rw [hB x (by omega)]
         simp)
    | (rename_i a b
       have hz : ∑ x, Z a x * (S x b - herm (Hb k) (B b) (B x) / 2) = 0 := by
         apply Finset.sum_eq_zero
         intro x _
         by_cases h : j ≤ x.val
         · rw [hZ a x (Or.inr h), zero_mul]
         · rw [hS x b (Or.inl (by omega)), hB x (by omega)]
           simp [herm]
       simp only [hz, zero_add, add_zero]
       split_ifs <;> simp_all)
    | (clear hee hew hes hwe hww hws hse hsw hss hD hZ hS hB hc hM hv1; done)

/- English proof (translation)
Take `⟨-, hdet, hblk, hrow⟩` from `h`. Establish `hex : ∀ a : Fin j, ∃ b : Fin j, Z (Fin.castLE hj a) (Fin.castLE hj b) ≠ 0`. Introduce `a`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`.

Conclude with `hdet (Matrix.det_eq_zero_of_row_eq_zero a fun b => hno b)`. Use `choose τ hτ using hex`. Establish `hβτ : ∀ a, β (Fin.castLE hj a) = β (Fin.castLE hj (τ a))` using `fun a => hblk a (τ a) (hτ a)`. Establish `huniq : ∀ a b : Fin j, Z (Fin.castLE hj a) (Fin.castLE hj b) ≠ 0 → b = τ a` using `fun a b hb => ((hrow a (τ a) a b (hτ a) hb rfl).2.1 rfl).symm`. Establish `hτinj : Function.Injective τ`.

Introduce `a a' he`. Assume the negation of the conclusion as `hne`. Establish `hb : β (Fin.castLE hj a) = β (Fin.castLE hj a')` using `by rw [hβτ a, hβτ a', he]`. Break down `lt_or_gt_of_ne hne with hlt | hlt` into its components or cases. Establish `h1` using `(hrow a (τ a) a' (τ a') (hτ a) (hτ a') hb).2.2 hlt`.

Rewrite `h1` using `[he]`. Conclude with `lt_irrefl _ h1`. Establish `h1` using `(hrow a' (τ a') a (τ a) (hτ a') (hτ a) hb.symm).2.2 hlt`. Rewrite `h1` using `[he]`. Conclude with `lt_irrefl _ h1`.

Set `f : Fin r → Fin r` to `fun a => if ha : a.val < j then Fin.castLE hj (τ ⟨a.val, ha⟩) else a`. Establish `hf_c : ∀ a0 : Fin j, f (Fin.castLE hj a0) = Fin.castLE hj (τ a0)` using `fun a0 => dif_pos a0.isLt`. Establish `hf_ge : ∀ a : Fin r, ¬ a.val < j → f a = a` using `fun a ha => dif_neg ha`. Establish `hlift : ∀ a : Fin r, a.val < j → ∃ a0 : Fin j, Fin.castLE hj a0 = a` using `fun a ha => ⟨⟨a.val, ha⟩, Fin.ext rfl⟩`. Establish `hfinj : Function.Injective f`.

Introduce `a a' he`. Apply the tactic sequence `by_cases ha : a.val < j <;> by_cases ha' : a'.val < j`. Take `⟨a0, rfl⟩` from `hlift a ha`. Take `⟨a1, rfl⟩` from `hlift a' ha'`. Rewrite `he` using `[hf_c, hf_c]`.

Rewrite using `[hτinj (Fin.castLE_injective hj he)]`. Take `⟨a0, rfl⟩` from `hlift a ha`. Rewrite `he` using `[hf_c, hf_ge a' ha']`. Conclude with `absurd (he ▸ (τ a0).isLt) ha'`. Take `⟨a1, rfl⟩` from `hlift a' ha'`.

Rewrite `he` using `[hf_c, hf_ge a ha]`. Conclude with `absurd (he.symm ▸ (τ a1).isLt) ha`. Rewrite `he` using `[hf_ge a ha, hf_ge a' ha']`. Then use the resulting hypothesis. Use `⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`.

Simplify using `only [Equiv.ofBijective_apply]`. Distinguish the cases in `ha : a.val < j`. Take `⟨a0, rfl⟩` from `hlift a ha`. Rewrite using `[hf_c]`. Conclude with `⟨fun _ => ha, fun _ => (τ a0).isLt⟩`.

Rewrite using `[hf_ge a ha]`. Introduce `a`. Simplify using `only [Equiv.ofBijective_apply]`. Distinguish the cases in `ha : a.val < j`. Take `⟨a0, rfl⟩` from `hlift a ha`.

Rewrite using `[hf_c, hβτ a0]`. Rewrite using `[hf_ge a ha]`. Introduce `a ha`. Simplify using `only [Equiv.ofBijective_apply]`. Take `⟨a0, rfl⟩` from `hlift a ha`.

Rewrite using `[hf_c]`. Use `⟨hτ a0, fun b hb hne => ?_⟩` and prove the remaining obligations. Take `⟨b0, rfl⟩` from `hlift b hb`. Assume the negation of the conclusion as `hz`. Conclude with `hne (by rw [huniq a0 b0 hz])`.

Introduce `a a' ha ha' hβ`. Simplify using `only [Equiv.ofBijective_apply]`. Take `⟨a0, rfl⟩` from `hlift a ha`. Take `⟨a1, rfl⟩` from `hlift a' ha'`. Rewrite using `[hf_c, hf_c]`.

Take `⟨hn, -, hlt⟩` from `hrow a0 (τ a0) a1 (τ a1) (hτ a0) (hτ a1) hβ`. Use `⟨hn, fun hlt' => ?_⟩` and prove the remaining obligations. Establish `h2` using `hlt (Fin.lt_def.mpr (Fin.lt_def.mp hlt'))`. Conclude with `Fin.lt_def.mpr (Fin.lt_def.mp h2)`.
-/
theorem exists_perm {j : ℕ} (hj : j ≤ r) (β : Fin r → ℕ) (Z : Matrix (Fin r) (Fin r) ℂ)
    (h : BlockAnti (fun a : Fin j => β (Fin.castLE hj a)) (Z.submatrix (Fin.castLE hj) (Fin.castLE hj))) :
    ∃ σ : Equiv.Perm (Fin r), (∀ a, (σ a).val < j ↔ a.val < j) ∧ (∀ a, β (σ a) = β a) ∧
      (∀ a : Fin r, a.val < j → Z a (σ a) ≠ 0 ∧ ∀ b : Fin r, b.val < j → b ≠ σ a → Z a b = 0) ∧
      ∀ a a' : Fin r, a.val < j → a'.val < j → β a = β a' → ‖Z a (σ a)‖ = ‖Z a' (σ a')‖ ∧ (a < a' → σ a' < σ a) := by
  obtain ⟨-, hdet, hblk, hrow⟩ := h
  have hex : ∀ a : Fin j, ∃ b : Fin j, Z (Fin.castLE hj a) (Fin.castLE hj b) ≠ 0 := by
    intro a
    by_contra hno
    push_neg at hno
    exact hdet (Matrix.det_eq_zero_of_row_eq_zero a fun b => hno b)
  choose τ hτ using hex
  have hβτ : ∀ a, β (Fin.castLE hj a) = β (Fin.castLE hj (τ a)) := fun a => hblk a (τ a) (hτ a)
  have huniq : ∀ a b : Fin j, Z (Fin.castLE hj a) (Fin.castLE hj b) ≠ 0 → b = τ a := fun a b hb =>
    ((hrow a (τ a) a b (hτ a) hb rfl).2.1 rfl).symm
  have hτinj : Function.Injective τ := by
    intro a a' he
    by_contra hne
    have hb : β (Fin.castLE hj a) = β (Fin.castLE hj a') := by rw [hβτ a, hβτ a', he]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := (hrow a (τ a) a' (τ a') (hτ a) (hτ a') hb).2.2 hlt
      rw [he] at h1
      exact lt_irrefl _ h1
    · have h1 := (hrow a' (τ a') a (τ a) (hτ a') (hτ a) hb.symm).2.2 hlt
      rw [he] at h1
      exact lt_irrefl _ h1
  let f : Fin r → Fin r := fun a => if ha : a.val < j then Fin.castLE hj (τ ⟨a.val, ha⟩) else a
  have hf_c : ∀ a0 : Fin j, f (Fin.castLE hj a0) = Fin.castLE hj (τ a0) := fun a0 => dif_pos a0.isLt
  have hf_ge : ∀ a : Fin r, ¬ a.val < j → f a = a := fun a ha => dif_neg ha
  have hlift : ∀ a : Fin r, a.val < j → ∃ a0 : Fin j, Fin.castLE hj a0 = a := fun a ha =>
    ⟨⟨a.val, ha⟩, Fin.ext rfl⟩
  have hfinj : Function.Injective f := by
    intro a a' he
    by_cases ha : a.val < j <;> by_cases ha' : a'.val < j
    · obtain ⟨a0, rfl⟩ := hlift a ha
      obtain ⟨a1, rfl⟩ := hlift a' ha'
      rw [hf_c, hf_c] at he
      rw [hτinj (Fin.castLE_injective hj he)]
    · obtain ⟨a0, rfl⟩ := hlift a ha
      rw [hf_c, hf_ge a' ha'] at he
      exact absurd (he ▸ (τ a0).isLt) ha'
    · obtain ⟨a1, rfl⟩ := hlift a' ha'
      rw [hf_c, hf_ge a ha] at he
      exact absurd (he.symm ▸ (τ a1).isLt) ha
    · rwa [hf_ge a ha, hf_ge a' ha'] at he
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj), ?_, ?_, ?_, ?_⟩
  · intro a
    simp only [Equiv.ofBijective_apply]
    by_cases ha : a.val < j
    · obtain ⟨a0, rfl⟩ := hlift a ha
      rw [hf_c]
      exact ⟨fun _ => ha, fun _ => (τ a0).isLt⟩
    · rw [hf_ge a ha]
  · intro a
    simp only [Equiv.ofBijective_apply]
    by_cases ha : a.val < j
    · obtain ⟨a0, rfl⟩ := hlift a ha
      rw [hf_c, hβτ a0]
    · rw [hf_ge a ha]
  · intro a ha
    simp only [Equiv.ofBijective_apply]
    obtain ⟨a0, rfl⟩ := hlift a ha
    rw [hf_c]
    refine ⟨hτ a0, fun b hb hne => ?_⟩
    obtain ⟨b0, rfl⟩ := hlift b hb
    by_contra hz
    exact hne (by rw [huniq a0 b0 hz])
  · intro a a' ha ha' hβ
    simp only [Equiv.ofBijective_apply]
    obtain ⟨a0, rfl⟩ := hlift a ha
    obtain ⟨a1, rfl⟩ := hlift a' ha'
    rw [hf_c, hf_c]
    obtain ⟨hn, -, hlt⟩ := hrow a0 (τ a0) a1 (τ a1) (hτ a0) (hτ a1) hβ
    refine ⟨hn, fun hlt' => ?_⟩
    have h2 := hlt (Fin.lt_def.mpr (Fin.lt_def.mp hlt'))
    exact Fin.lt_def.mpr (Fin.lt_def.mp h2)

/- English proof (translation)
Establish `hv' : v ∈ Submodule.span ℂ (Set.range fun a : {a : Fin r // a.val < j} => bvec (esI k r a.1))` using `hv`. Use `clear hv`. Proceed by induction on `hv' using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`.

Conclude with `Pi.single_eq_of_ne (hi a.1 a.2) 1`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp [hx, hy]`. Consider the case `smul c x _ hx => simp [hx]`.
-/
theorem apply_of_mem_XstJ {j : ℕ} {v : Fin (2 * r + k + 1) → ℂ} (hv : v ∈ XstJ k r j) {i : Fin (2 * r + k + 1)}
    (hi : ∀ b : Fin r, b.val < j → i ≠ esI k r b) : v i = 0 := by
  have hv' : v ∈ Submodule.span ℂ (Set.range fun a : {a : Fin r // a.val < j} => bvec (esI k r a.1)) := hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact Pi.single_eq_of_ne (hi a.1 a.2) 1
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

/- English proof (translation)
Use `show (g *ᵥ Pi.single x 1) i = g i x`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem mulVec_bvec (g : Mat k r) (x i : Fin (2 * r + k + 1)) : (g *ᵥ bvec x) i = g i x := by
  show (g *ᵥ Pi.single x 1) i = g i x
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/- English proof (translation)
Use extensionality with `i j`. Establish `h1 : (Hpk k r * Hpk k r) i j = (Hpk k r *ᵥ (Hpk k r *ᵥ Pi.single j 1)) i`. Rewrite using `[Matrix.mulVec_mulVec]`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite using `[h1]`.

Simplify using `only [Formalism.QuantumDeterminants.gn_Hpk_mulVec, Pi.single_apply, Matrix.one_apply, Fin.ext_iff, Fin.val_mk]`. Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega) | norm_num`.
-/
theorem H_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  have h1 : (Hpk k r * Hpk k r) i j = (Hpk k r *ᵥ (Hpk k r *ᵥ Pi.single j 1)) i := by
    rw [Matrix.mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [h1]
  simp only [Formalism.QuantumDeterminants.gn_Hpk_mulVec, Pi.single_apply, Matrix.one_apply, Fin.ext_iff, Fin.val_mk]
  have hi := i.isLt
  have hj := j.isLt
  split_ifs <;> first | rfl | (exfalso; omega) | norm_num

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `hH : (Hpk k r).det * (Hpk k r).det = 1`. Rewrite using `[← Matrix.det_mul, H_sq, Matrix.det_one]`. Establish `h` using `congrArg Matrix.det hg'`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul]`.

Use `isUnit_iff_ne_zero.mpr fun h0 => ?_` and prove the remaining obligations. Rewrite `h` using `[h0, mul_zero]`. Conclude with `left_ne_zero_of_mul_eq_one hH h.symm`.
-/
theorem isUnit_det_of_mem {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hH : (Hpk k r).det * (Hpk k r).det = 1 := by
    rw [← Matrix.det_mul, H_sq, Matrix.det_one]
  have h := congrArg Matrix.det hg'
  rw [Matrix.det_mul, Matrix.det_mul] at h
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, mul_zero] at h
  exact left_ne_zero_of_mul_eq_one hH h.symm

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Rewrite using `[← congrFun (congrFun hg' x) i]`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, sum3, H_ee, H_ew, H_es, H_we, H_ww, H_ws, H_se, H_sw, H_ss, mul_zero, zero_mul, mul_ite, ite_mul, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero, zero_ad …`.
-/
theorem pairing {g : Mat k r} (hg : g ∈ GG k r) (x i : Fin (2 * r + k + 1)) :
    ∑ a, star (g (esI k r a) x) * g (eI k r a) i + ∑ n, star (g (wI k r n) x) * sg k n * g (wI k r n) i +
      ∑ a, star (g (eI k r a) x) * g (esI k r a) i = Hpk k r x i := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [← congrFun (congrFun hg' x) i]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, sum3, H_ee, H_ew, H_es, H_we,
    H_ww, H_ws, H_se, H_sw, H_ss, mul_zero, zero_mul, mul_ite, ite_mul, mul_one, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero, zero_add]

/- English proof (translation)
Establish `e` using `congrFun h i`. Rewrite `e` using `[mulVec_bvec]`. Rewrite using `[e]`. Distinguish the cases in `hi : i = x`. Substitute `hi` using the available equality.

Simplify using `[bvec]`. Simplify using `[bvec, Pi.single_apply, hi]`.
-/
private theorem apply_eq_ite_of_mulVec_bvec_eq_smul {g : Mat k r} {c : ℂ} {x : Fin (2 * r + k + 1)}
    (h : g *ᵥ bvec x = c • bvec x) (i : Fin (2 * r + k + 1)) : g i x = if i = x then c else 0 := by
  have e := congrFun h i
  rw [mulVec_bvec] at e
  rw [e]
  by_cases hi : i = x
  · subst hi; simp [bvec]
  · simp [bvec, Pi.single_apply, hi]

/- English proof (translation)
Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Establish `h1 : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, H_sq]`.
-/
private theorem inv_eq_Hpk_mul_conjTranspose_mul_Hpk {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, H_sq]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, sum3]`. Simplify using `only [H_ee, H_we, H_se, mul_zero, Finset.sum_const_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[Matrix.mul_apply]`. Simplify using `[Matrix.conjTranspose_apply]`.
-/
private theorem Hpk_conj_apply_eI_eq_sum (g : Mat k r) (i : Fin (2 * r + k + 1)) (a : Fin r) :
    (Hpk k r * gᴴ * Hpk k r) i (eI k r a) = ∑ p, Hpk k r i p * star (g (esI k r a) p) := by
  rw [Matrix.mul_apply, sum3]
  simp only [H_ee, H_we, H_se, mul_zero, Finset.sum_const_zero, zero_add, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Matrix.mul_apply]
  simp [Matrix.conjTranspose_apply]

/- English proof (translation)
Rewrite using `[sum3]`. Simplify using `[H_ee, H_we, H_se]`.
-/
private theorem sum_mul_Hpk_eI_eq_apply_esI (f : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    ∑ i, f i * Hpk k r i (eI k r b) = f (esI k r b) := by
  rw [sum3]; simp [H_ee, H_we, H_se]

/- English proof (translation)
Rewrite using `[sum3]`. Simplify using `[H_we, H_ww, H_ws]`.
-/
private theorem sum_Hpk_wI_mul_eq_sg_mul (f : Fin (2 * r + k + 1) → ℂ) (n : Fin (k + 1)) :
    ∑ p, Hpk k r (wI k r n) p * f p = sg k n * f (wI k r n) := by
  rw [sum3]; simp [H_we, H_ww, H_ws]

/- English proof (translation)
Rewrite using `[sum3]`. Simplify using `[H_ee, H_ew, H_es]`.
-/
private theorem sum_Hpk_eI_mul_eq_apply_esI (f : Fin (2 * r + k + 1) → ℂ) (x : Fin r) :
    ∑ p, Hpk k r (eI k r x) p * f p = f (esI k r x) := by
  rw [sum3]; simp [H_ee, H_ew, H_es]

/- English proof (translation)
Take `⟨hgG, hc, -, -, -, hXJ, hfix, hBA⟩` from `h`. Take `⟨σ, s1, s2, s3, s4⟩` from `exists_perm hj β (Zr k r g) hBA`. Use `set t : Fin r → ℂ := fun a => Zr k r g a (σ a) with ht`. Establish `cE : ∀ b : Fin r, j ≤ b.val → ∀ i, g i (eI k r b) = if i = eI k r b then c else 0` using `fun b hb i => apply_eq_ite_of_mulVec_bvec_eq_smul (hfix b hb).1 i`. Establish `cS : ∀ b : Fin r, j ≤ b.val → ∀ i, g i (esI k r b) = if i = esI k r b then c else 0` using `fun b hb i => apply_eq_ite_of_mulVec_bvec_eq_smul (hfix b hb).2 i`.

Establish `cL : ∀ b : Fin r, b.val < j → ∀ i, (∀ a : Fin r, a.val < j → i ≠ esI k r a) → g i (eI k r b) = 0`. Introduce `b hb i hi`. Establish `e` using `apply_of_mem_XstJ (hXJ b hb).2 hi`. Rewrite `e` using `[mulVec_bvec]`. Then use the resulting hypothesis. Establish `hinv` using `inv_eq_Hpk_mul_conjTranspose_mul_Hpk hgG`.

Establish `rSw : ∀ a : Fin r, a.val < j → ∀ n, g (esI k r a) (wI k r n) = 0`. Introduce `a ha n`. Establish `h0` using `apply_of_mem_XstJ (hXJ a ha).1 (i := wI k r n) (fun b _ => wI_ne_esI n b)`. Rewrite `h0` using `[mulVec_bvec, hinv, Hpk_conj_apply_eI_eq_sum, sum_Hpk_wI_mul_eq_sg_mul]`. Apply the tactic sequence `have hs : sg k n ≠ 0 := by rw [sg]; split_ifs <;> norm_num`.

Establish `h1` using `(mul_eq_zero.mp h0).resolve_left hs`. Simplify using `using h1`. Establish `rSs : ∀ a : Fin r, a.val < j → ∀ x, g (esI k r a) (esI k r x) = 0`. Introduce `a ha x`. Establish `h0` using `apply_of_mem_XstJ (hXJ a ha).1 (i := eI k r x) (fun b _ => eI_ne_esI x b)`.

Rewrite `h0` using `[mulVec_bvec, hinv, Hpk_conj_apply_eI_eq_sum, sum_Hpk_eI_mul_eq_apply_esI]`. Simplify using `using h0`. Establish `rS : ∀ a : Fin r, a.val < j → ∀ p, g (esI k r a) p = if p = eI k r (σ a) then t a else 0`. Introduce `a ha p`. Use `cases3 (P := fun p => g (esI k r a) p = if p = eI k r (σ a) then t a else 0) ?_ ?_ ?_ p` and prove the remaining obligations.

Introduce `x`. Distinguish the cases in `hx : x = σ a`. Substitute `hx` using the available equality. Simplify using `[ht, Zr]`. Rewrite using `[if_neg (by rw [eI_inj]; exact hx)]`.

Distinguish the cases in `hxj : x.val < j`. Conclude with `(s3 a ha).2 x hxj hx`. Rewrite using `[cE x (by omega) (esI k r a), if_neg (esI_ne_eI a x)]`. Introduce `n`. Rewrite using `[if_neg (wI_ne_eI n (σ a)), rSw a ha n]`.

Introduce `x`. Rewrite using `[if_neg (esI_ne_eI x (σ a)), rSs a ha x]`. Establish `cLs : ∀ a : Fin r, a.val < j → ∀ i, star (g i (eI k r (σ a))) = if i = esI k r a then star (t a) else 0`. Introduce `a ha i`. Establish `hσ : (σ a).val < j` using `(s1 a).mpr ha`.

Use `cases3 (P := fun i => star (g i (eI k r (σ a))) = if i = esI k r a then star (t a) else 0) ?_ ?_ ?_ i` and prove the remaining obligations. Introduce `x`. Rewrite using `[if_neg (eI_ne_esI x a), cL (σ a) hσ _ (fun a' _ => eI_ne_esI x a'), star_zero]`. Introduce `n`. Rewrite using `[if_neg (wI_ne_esI n a), cL (σ a) hσ _ (fun a' _ => wI_ne_esI n a'), star_zero]`.

Introduce `x`. Distinguish the cases in `hxj : x.val < j`. Rewrite using `[rS x hxj]`. Distinguish the cases in `hxa : x = a`. Substitute `hxa` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg (by rw [eI_inj]; exact fun h => hxa (σ.injective h).symm), if_neg (by rw [esI_inj]; exact hxa), star_zero]`. Rewrite using `[cL (σ a) hσ _ (fun a' ha' h => hxj (by rw [esI_inj] at h; rw [h]; exact ha')), if_neg (by rw [esI_inj]; rintro rfl; exact hxj ha), star_zero]`. Establish `rElo : ∀ a : Fin r, a.val < j → ∀ y, star (t a) * g (eI k r a) y = Hpk k r (eI k r (σ a)) y`. Introduce `a ha y`.

Establish `e` using `pairing hgG (eI k r (σ a)) y`. Simplify using `only [cLs a ha] at e`. Rewrite using `[← e]`. Simplify using `[esI_inj, eI_ne_esI, wI_ne_esI]`. Establish `rEhi : ∀ a : Fin r, j ≤ a.val → ∀ y, star c * g (eI k r a) y = Hpk k r (esI k r a) y`.

Introduce `a ha y`. Establish `e` using `pairing hgG (esI k r a) y`. Establish `hs : ∀ i, star (g i (esI k r a)) = if i = esI k r a then star c else 0`. Apply the tactic sequence `intro i; rw [cS a ha]; split_ifs <;> simp`. Simplify using `only [hs] at e`.

Rewrite using `[← e]`. Simplify using `[esI_inj, wI_ne_esI, eI_ne_esI]`. Establish `rShi : ∀ a : Fin r, j ≤ a.val → ∀ y, star c * g (esI k r a) y = Hpk k r (eI k r a) y`. Introduce `a ha y`. Establish `e` using `pairing hgG (eI k r a) y`.

Establish `hs : ∀ i, star (g i (eI k r a)) = if i = eI k r a then star c else 0`. Apply the tactic sequence `intro i; rw [cE a ha]; split_ifs <;> simp`. Simplify using `only [hs] at e`. Rewrite using `[← e]`. Simplify using `[eI_inj, wI_ne_eI, esI_ne_eI]`.

Establish `hcc : star c * c = 1`. Establish `h1` using `Complex.normSq_eq_conj_mul_self (z := c)`. Rewrite `h1` using `[Complex.normSq_eq_norm_sq, hc]`. Simplify using `using h1.symm`. Establish `solC : ∀ X Y : ℂ, star c * X = Y → X = c * Y` using `fun X Y h => by`.

Rewrite using `[← h, ← mul_assoc, mul_comm c, hcc, one_mul]`. Establish `gEw : ∀ (a : Fin r) n, g (eI k r a) (wI k r n) = 0`. Introduce `a n`. Distinguish the cases in `ha : a.val < j`. Establish `e` using `rElo a ha (wI k r n)`.

Rewrite `e` using `[H_ew]`. Conclude with `(mul_eq_zero.mp e).resolve_left (star_ne_zero.mpr (s3 a ha).1)`. Rewrite using `[solC _ _ (rEhi a (by omega) (wI k r n)), H_sw, mul_zero]`. Establish `gSw : ∀ (a : Fin r) n, g (esI k r a) (wI k r n) = 0`. Introduce `a n`.

Distinguish the cases in `ha : a.val < j`. Conclude with `rSw a ha n`. Rewrite using `[solC _ _ (rShi a (by omega) (wI k r n)), H_ew, mul_zero]`. Establish `hmul : g * (Hpk k r * gᴴ * Hpk k r) = 1`. Rewrite using `[← hinv]`.

Conclude with `Matrix.mul_nonsing_inv g (isUnit_det_of_mem hgG)`. Establish `gWs : ∀ n (b : Fin r), g (wI k r n) (esI k r b) = 0`. Introduce `n b`. Distinguish the cases in `hb : j ≤ b.val`. Rewrite using `[cS b hb, if_neg (wI_ne_esI n b)]`.

Take `⟨a, rfl⟩` from `σ.surjective b`. Establish `ha : a.val < j` using `(s1 a).mp (by omega)`. Establish `e` using `congrFun (congrFun hmul (wI k r n)) (eI k r a)`. Rewrite `e` using `[Matrix.mul_apply, Matrix.one_apply_ne (wI_ne_eI n a)]`. Establish `inner : ∀ i, (Hpk k r * gᴴ * Hpk k r) i (eI k r a) = Hpk k r i (eI k r (σ a)) * star (t a)`.

Introduce `i`. Rewrite using `[Hpk_conj_apply_eI_eq_sum, Finset.sum_eq_single (eI k r (σ a))]`. Rewrite using `[rS a ha, if_pos rfl]`. Introduce `p _ hp`. Rewrite using `[rS a ha, if_neg hp, star_zero, mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite `e` using `[inner, ← mul_assoc]`. Rewrite `e` using `[← Finset.sum_mul, sum_mul_Hpk_eI_eq_apply_esI]`. Conclude with `(mul_eq_zero.mp e).resolve_right (star_ne_zero.mpr (s3 a ha).1)`.

Use `⟨σ, t, Matrix.of fun m n => g (wI k r m) (wI k r n), s1, s2, fun a ha => (s3 a ha).1, s4, ?_, ?_⟩` and prove the remaining obligations. Use `show (_ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ᴴ * Hb k * _ = Hb k`. Use extensionality with `m m'`. Establish `e` using `pairing hgG (wI k r m) (wI k r m')`. Simplify using `only [gEw, gSw, star_zero, zero_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero, H_ww] at e`.

Rewrite using `[Hb_apply, ← e, Matrix.mul_apply]`. Use `Finset.sum_congr rfl (fun n _ => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single n]`. Simplify using `[Hb_apply, Matrix.conjTranspose_apply, Matrix.of_apply, mul_assoc]`. Introduce `n' _ hn'`.

Simplify using `[Hb_apply, hn']`. Simplify using the standard rewrite rules. Use `⟨?_, gEw, ?_, ?_, fun m n => rfl, gWs, ?_, gSw, ?_⟩` and prove the remaining obligations. Introduce `a b`. Simplify using `only [Matrix.smul_apply, Fj, Matrix.diagonal_apply, smul_eq_mul]`.

Distinguish the cases in `hb : j ≤ b.val`. Rewrite using `[cE b hb]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `[hb]`.

Simplify using `[eI_inj, hab]`. Rewrite using `[cL b (by omega) _ (fun a' _ => eI_ne_esI a a')]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `[hb]`.

Simplify using `[hab]`. Introduce `a b`. Simplify using `only [Matrix.of_apply]`. Distinguish the cases in `ha : a.val < j`. Establish `e` using `rElo a ha (esI k r b)`.

Rewrite `e` using `[H_es]`. Establish `hst : star (t a) ≠ 0` using `star_ne_zero.mpr (s3 a ha).1`. Rewrite using `[show g (eI k r a) (esI k r b) = (star (t a))⁻¹ * (if σ a = b then 1 else 0) by`. Rewrite using `[← e, ← mul_assoc, inv_mul_cancel₀ hst, one_mul]]`. Distinguish the cases in `hb : b = σ a`.

Substitute `hb` using the available equality. Simplify using `[ha]`. Rewrite using `[if_neg (fun h => hb h.symm), mul_zero, if_neg (fun h => hb h.2)]`. Rewrite using `[solC _ _ (rEhi a (by omega) (esI k r b)), H_ss, mul_zero]; simp [ha]`. Introduce `n b`.

Distinguish the cases in `hb : j ≤ b.val`. Rewrite using `[cE b hb, if_neg (wI_ne_eI n b)]`. Conclude with `cL b (by omega) _ (fun a' _ => wI_ne_esI n a')`. Introduce `a b`. Simplify using `only [Matrix.of_apply]`.

Distinguish the cases in `ha : a.val < j`. Rewrite using `[rS a ha]`. Distinguish the cases in `hb : b = σ a`. Substitute `hb` using the available equality. Simplify using `[ha]`.

Rewrite using `[if_neg (by rw [eI_inj]; exact hb)]; simp [hb]`. Rewrite using `[solC _ _ (rShi a (by omega) (eI k r b)), H_ee, mul_zero]; simp [ha]`. Introduce `a b`. Simplify using `only [Matrix.smul_apply, Fj, Matrix.diagonal_apply, smul_eq_mul]`. Distinguish the cases in `ha : a.val < j`.

Rewrite using `[rSs a ha b]`. Distinguish the cases in `hab : a = b`. Substitute `hab; simp [show ¬ j ≤ a.val by omega]` using the available equality. Simplify using `[hab]`. Rewrite using `[solC _ _ (rShi a (by omega) (esI k r b)), H_es]`.

Distinguish the cases in `hab : a = b`. Substitute `hab; simp [show j ≤ a.val by omega]` using the available equality. Simplify using `[hab]`.
-/
theorem exists_blocks {j : ℕ} (hj : j ≤ r) {β : Fin r → ℕ} {c : ℂ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : Mat k r}
    (h : IsNormal0 k r hj β c z z' g) :
    ∃ (σ : Equiv.Perm (Fin r)) (t : Fin r → ℂ) (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
      (∀ a, (σ a).val < j ↔ a.val < j) ∧ (∀ a, β (σ a) = β a) ∧ (∀ a : Fin r, a.val < j → t a ≠ 0) ∧
      (∀ a a' : Fin r, a.val < j → a'.val < j → β a = β a' → ‖t a‖ = ‖t a'‖ ∧ (a < a' → σ a' < σ a)) ∧ M ∈ UH (Hb k) ∧
      HasBlocks g (c • Fj r j) (Matrix.of fun a b => if a.val < j ∧ b = σ a then (star (t a))⁻¹ else 0)
        (Matrix.of fun a b => if a.val < j ∧ b = σ a then t a else 0) M := by
  obtain ⟨hgG, hc, -, -, -, hXJ, hfix, hBA⟩ := h
  obtain ⟨σ, s1, s2, s3, s4⟩ := exists_perm hj β (Zr k r g) hBA
  set t : Fin r → ℂ := fun a => Zr k r g a (σ a) with ht
  have cE : ∀ b : Fin r, j ≤ b.val → ∀ i, g i (eI k r b) = if i = eI k r b then c else 0 :=
    fun b hb i => apply_eq_ite_of_mulVec_bvec_eq_smul (hfix b hb).1 i
  have cS : ∀ b : Fin r, j ≤ b.val → ∀ i, g i (esI k r b) = if i = esI k r b then c else 0 :=
    fun b hb i => apply_eq_ite_of_mulVec_bvec_eq_smul (hfix b hb).2 i
  have cL : ∀ b : Fin r, b.val < j → ∀ i, (∀ a : Fin r, a.val < j → i ≠ esI k r a) → g i (eI k r b) = 0 := by
    intro b hb i hi
    have e := apply_of_mem_XstJ (hXJ b hb).2 hi
    rwa [mulVec_bvec] at e
  have hinv := inv_eq_Hpk_mul_conjTranspose_mul_Hpk hgG
  have rSw : ∀ a : Fin r, a.val < j → ∀ n, g (esI k r a) (wI k r n) = 0 := by
    intro a ha n
    have h0 := apply_of_mem_XstJ (hXJ a ha).1 (i := wI k r n) (fun b _ => wI_ne_esI n b)
    rw [mulVec_bvec, hinv, Hpk_conj_apply_eI_eq_sum, sum_Hpk_wI_mul_eq_sg_mul] at h0
    have hs : sg k n ≠ 0 := by rw [sg]; split_ifs <;> norm_num
    have h1 := (mul_eq_zero.mp h0).resolve_left hs
    simpa using h1
  have rSs : ∀ a : Fin r, a.val < j → ∀ x, g (esI k r a) (esI k r x) = 0 := by
    intro a ha x
    have h0 := apply_of_mem_XstJ (hXJ a ha).1 (i := eI k r x) (fun b _ => eI_ne_esI x b)
    rw [mulVec_bvec, hinv, Hpk_conj_apply_eI_eq_sum, sum_Hpk_eI_mul_eq_apply_esI] at h0
    simpa using h0
  have rS : ∀ a : Fin r, a.val < j → ∀ p, g (esI k r a) p = if p = eI k r (σ a) then t a else 0 := by
    intro a ha p
    refine cases3 (P := fun p => g (esI k r a) p = if p = eI k r (σ a) then t a else 0) ?_ ?_ ?_ p
    · intro x
      by_cases hx : x = σ a
      · subst hx; simp [ht, Zr]
      · rw [if_neg (by rw [eI_inj]; exact hx)]
        by_cases hxj : x.val < j
        · exact (s3 a ha).2 x hxj hx
        · rw [cE x (by omega) (esI k r a), if_neg (esI_ne_eI a x)]
    · intro n; rw [if_neg (wI_ne_eI n (σ a)), rSw a ha n]
    · intro x; rw [if_neg (esI_ne_eI x (σ a)), rSs a ha x]
  have cLs : ∀ a : Fin r, a.val < j → ∀ i,
      star (g i (eI k r (σ a))) = if i = esI k r a then star (t a) else 0 := by
    intro a ha i
    have hσ : (σ a).val < j := (s1 a).mpr ha
    refine cases3 (P := fun i => star (g i (eI k r (σ a))) = if i = esI k r a then star (t a) else 0)
      ?_ ?_ ?_ i
    · intro x; rw [if_neg (eI_ne_esI x a), cL (σ a) hσ _ (fun a' _ => eI_ne_esI x a'), star_zero]
    · intro n; rw [if_neg (wI_ne_esI n a), cL (σ a) hσ _ (fun a' _ => wI_ne_esI n a'), star_zero]
    · intro x
      by_cases hxj : x.val < j
      · rw [rS x hxj]
        by_cases hxa : x = a
        · subst hxa; simp
        · rw [if_neg (by rw [eI_inj]; exact fun h => hxa (σ.injective h).symm),
            if_neg (by rw [esI_inj]; exact hxa), star_zero]
      · rw [cL (σ a) hσ _ (fun a' ha' h => hxj (by rw [esI_inj] at h; rw [h]; exact ha')),
          if_neg (by rw [esI_inj]; rintro rfl; exact hxj ha), star_zero]
  have rElo : ∀ a : Fin r, a.val < j → ∀ y, star (t a) * g (eI k r a) y = Hpk k r (eI k r (σ a)) y := by
    intro a ha y
    have e := pairing hgG (eI k r (σ a)) y
    simp only [cLs a ha] at e
    rw [← e]
    simp [esI_inj, eI_ne_esI, wI_ne_esI]
  have rEhi : ∀ a : Fin r, j ≤ a.val → ∀ y, star c * g (eI k r a) y = Hpk k r (esI k r a) y := by
    intro a ha y
    have e := pairing hgG (esI k r a) y
    have hs : ∀ i, star (g i (esI k r a)) = if i = esI k r a then star c else 0 := by
      intro i; rw [cS a ha]; split_ifs <;> simp
    simp only [hs] at e
    rw [← e]; simp [esI_inj, wI_ne_esI, eI_ne_esI]
  have rShi : ∀ a : Fin r, j ≤ a.val → ∀ y, star c * g (esI k r a) y = Hpk k r (eI k r a) y := by
    intro a ha y
    have e := pairing hgG (eI k r a) y
    have hs : ∀ i, star (g i (eI k r a)) = if i = eI k r a then star c else 0 := by
      intro i; rw [cE a ha]; split_ifs <;> simp
    simp only [hs] at e
    rw [← e]; simp [eI_inj, wI_ne_eI, esI_ne_eI]
  have hcc : star c * c = 1 := by
    have h1 := Complex.normSq_eq_conj_mul_self (z := c)
    rw [Complex.normSq_eq_norm_sq, hc] at h1
    simpa using h1.symm
  have solC : ∀ X Y : ℂ, star c * X = Y → X = c * Y := fun X Y h => by
    rw [← h, ← mul_assoc, mul_comm c, hcc, one_mul]
  have gEw : ∀ (a : Fin r) n, g (eI k r a) (wI k r n) = 0 := by
    intro a n
    by_cases ha : a.val < j
    · have e := rElo a ha (wI k r n); rw [H_ew] at e
      exact (mul_eq_zero.mp e).resolve_left (star_ne_zero.mpr (s3 a ha).1)
    · rw [solC _ _ (rEhi a (by omega) (wI k r n)), H_sw, mul_zero]
  have gSw : ∀ (a : Fin r) n, g (esI k r a) (wI k r n) = 0 := by
    intro a n
    by_cases ha : a.val < j
    · exact rSw a ha n
    · rw [solC _ _ (rShi a (by omega) (wI k r n)), H_ew, mul_zero]
  have hmul : g * (Hpk k r * gᴴ * Hpk k r) = 1 := by
    rw [← hinv]; exact Matrix.mul_nonsing_inv g (isUnit_det_of_mem hgG)
  have gWs : ∀ n (b : Fin r), g (wI k r n) (esI k r b) = 0 := by
    intro n b
    by_cases hb : j ≤ b.val
    · rw [cS b hb, if_neg (wI_ne_esI n b)]
    · obtain ⟨a, rfl⟩ := σ.surjective b
      have ha : a.val < j := (s1 a).mp (by omega)
      have e := congrFun (congrFun hmul (wI k r n)) (eI k r a)
      rw [Matrix.mul_apply, Matrix.one_apply_ne (wI_ne_eI n a)] at e
      have inner : ∀ i, (Hpk k r * gᴴ * Hpk k r) i (eI k r a) = Hpk k r i (eI k r (σ a)) * star (t a) := by
        intro i
        rw [Hpk_conj_apply_eI_eq_sum, Finset.sum_eq_single (eI k r (σ a))]
        · rw [rS a ha, if_pos rfl]
        · intro p _ hp; rw [rS a ha, if_neg hp, star_zero, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp_rw [inner, ← mul_assoc] at e
      rw [← Finset.sum_mul, sum_mul_Hpk_eI_eq_apply_esI] at e
      exact (mul_eq_zero.mp e).resolve_right (star_ne_zero.mpr (s3 a ha).1)
  refine ⟨σ, t, Matrix.of fun m n => g (wI k r m) (wI k r n), s1, s2, fun a ha => (s3 a ha).1, s4, ?_, ?_⟩
  · show (_ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ᴴ * Hb k * _ = Hb k
    ext m m'
    have e := pairing hgG (wI k r m) (wI k r m')
    simp only [gEw, gSw, star_zero, zero_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero, H_ww] at e
    rw [Hb_apply, ← e, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Matrix.mul_apply, Finset.sum_eq_single n]
    · simp [Hb_apply, Matrix.conjTranspose_apply, Matrix.of_apply, mul_assoc]
    · intro n' _ hn'; simp [Hb_apply, hn']
    · simp
  · refine ⟨?_, gEw, ?_, ?_, fun m n => rfl, gWs, ?_, gSw, ?_⟩
    · intro a b
      simp only [Matrix.smul_apply, Fj, Matrix.diagonal_apply, smul_eq_mul]
      by_cases hb : j ≤ b.val
      · rw [cE b hb]
        by_cases hab : a = b
        · subst hab; simp [hb]
        · simp [eI_inj, hab]
      · rw [cL b (by omega) _ (fun a' _ => eI_ne_esI a a')]
        by_cases hab : a = b
        · subst hab; simp [hb]
        · simp [hab]
    · intro a b
      simp only [Matrix.of_apply]
      by_cases ha : a.val < j
      · have e := rElo a ha (esI k r b)
        rw [H_es] at e
        have hst : star (t a) ≠ 0 := star_ne_zero.mpr (s3 a ha).1
        rw [show g (eI k r a) (esI k r b) = (star (t a))⁻¹ * (if σ a = b then 1 else 0) by
          rw [← e, ← mul_assoc, inv_mul_cancel₀ hst, one_mul]]
        by_cases hb : b = σ a
        · subst hb; simp [ha]
        · rw [if_neg (fun h => hb h.symm), mul_zero, if_neg (fun h => hb h.2)]
      · rw [solC _ _ (rEhi a (by omega) (esI k r b)), H_ss, mul_zero]; simp [ha]
    · intro n b
      by_cases hb : j ≤ b.val
      · rw [cE b hb, if_neg (wI_ne_eI n b)]
      · exact cL b (by omega) _ (fun a' _ => wI_ne_esI n a')
    · intro a b
      simp only [Matrix.of_apply]
      by_cases ha : a.val < j
      · rw [rS a ha]
        by_cases hb : b = σ a
        · subst hb; simp [ha]
        · rw [if_neg (by rw [eI_inj]; exact hb)]; simp [hb]
      · rw [solC _ _ (rShi a (by omega) (eI k r b)), H_ee, mul_zero]; simp [ha]
    · intro a b
      simp only [Matrix.smul_apply, Fj, Matrix.diagonal_apply, smul_eq_mul]
      by_cases ha : a.val < j
      · rw [rSs a ha b]
        by_cases hab : a = b
        · subst hab; simp [show ¬ j ≤ a.val by omega]
        · simp [hab]
      · rw [solC _ _ (rShi a (by omega) (esI k r b)), H_es]
        by_cases hab : a = b
        · subst hab; simp [show j ≤ a.val by omega]
        · simp [hab]

/- English proof (translation)
Establish `hb_of : ∀ p : UTin β, p.1.1.1.val < j → p.1.1.2.val < j` using `fun p h => (hβ _ _ p.2).mp h`. Establish `hlt : ∀ p : UTin β, p.1.1.1.val < j → σ p.1.1.2 < σ p.1.1.1` using `fun p h => (s4 _ _ h (hb_of p h) p.2).2 p.1.2`. Establish `hbeta : ∀ p : UTin β, β (σ p.1.1.2) = β (σ p.1.1.1)` using `fun p => by rw [s2, s2]; exact p.2.symm`. Set `τ : UTin β → UTin β` to `fun p => if h : p.1.1.1.val < j then ⟨⟨(σ p.1.1.2, σ p.1.1.1), hlt p h⟩, hbeta p⟩ else p`. Establish `hτ : Function.Injective τ`.

Introduce `p q hpq`. Distinguish the cases in `hp : p.1.1.1.val < j`. Distinguish the cases in `hq : q.1.1.1.val < j`. Simplify using `only [τ, dif_pos hp, dif_pos hq] at hpq`. Establish `h1` using `congrArg (fun u : UTin β => u.1.1) hpq`.

Simplify using `only [Prod.mk.injEq] at h1`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `Prod.ext (σ.injective h1.2) (σ.injective h1.1)`. Simplify using `only [τ, dif_pos hp, dif_neg hq] at hpq`.

Establish `h1` using `congrArg (fun u : UTin β => u.1.1.1.val) hpq`. Simplify using `only at h1`. Conclude with `absurd (by rw [← h1]; exact (s1 _).mpr (hb_of p hp)) hq`. Distinguish the cases in `hq : q.1.1.1.val < j`. Simplify using `only [τ, dif_neg hp, dif_pos hq] at hpq`.

Establish `h1` using `congrArg (fun u : UTin β => u.1.1.1.val) hpq`. Simplify using `only at h1`. Conclude with `absurd (by rw [h1]; exact (s1 _).mpr (hb_of q hq)) hp`. Simplify using `only [τ, dif_neg hp, dif_neg hq] at hpq`. Conclude with `hpq`.

Set `e : UTin β ≃ UTin β` to `Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτ)`. Set `A : UTin β → ℂ` to `fun p => -((star (t p.1.1.1))⁻¹ * star (t p.1.1.2))`. Set `F : UTin β → ℂ → ℂ` to `fun p z => if p.1.1.1.val < j then A p * star z else z`. Establish `hF : ∀ p, MeasurePreserving (F p) volume volume`. Introduce `p`.

Distinguish the cases in `hp : p.1.1.1.val < j`. Establish `hb` using `hb_of p hp`. Establish `hA : ‖A p‖ = 1`. Simplify using `only [A, norm_neg, norm_mul, norm_inv, norm_star]`. Rewrite using `[(s4 _ _ hp hb p.2).1]`.

Conclude with `inv_mul_cancel₀ (norm_ne_zero_iff.mpr (s3 _ hb))`. Establish `hFp : F p = fun z => A p * star z` using `by funext z; simp only [F, if_pos hp]`. Rewrite using `[hFp]`. Conclude with `mul_star_mp hA`. Establish `hFp : F p = id` using `by funext z; simp only [F, if_neg hp, id]`.

Rewrite using `[hFp]`. Conclude with `MeasurePreserving.id volume`. Establish `hP : MeasurePreserving (fun y : UTin β → ℂ => fun p => y (e p)) volume volume`. Establish `h0` using `volume_preserving_arrowCongr' e.symm (MeasurableEquiv.refl ℂ) (MeasurePreserving.id volume)`. Conclude with `h0`.

Establish `hC : MeasurePreserving (fun w : UTin β → ℂ => fun p => F p (w p)) volume volume` using `volume_preserving_pi hF`. Establish `key : ∀ (w : UTin β → ℂ) (a b : Fin r), upperIn β w a b = if h : a < b then (if h' : β a = β b then w ⟨⟨(a, b), h⟩, h'⟩ else 0) else if a = b then 1 else 0`. Introduce `w a b`. Both sides reduce to the same expression. Use `⟨fun x => fun p => F p (shearInv j β x (e p)), (hC.comp hP).comp (shearInv_mp j β), ?_⟩` and prove the remaining obligations.

Introduce `x a b`. Establish `hdiag : ∀ c, (upperIn β x)⁻¹ c c = 1` using `fun c => inv_upper_diag _ c`. Establish `hgt : ∀ c d, d < c → (upperIn β x)⁻¹ c d = 0` using `fun c d h => inv_upper_gt _ h`. Use `beta_reduce`. Rewrite using `[key]`.

Break down `lt_trichotomy a b with hab | rfl | hab` into its components or cases. Rewrite using `[dif_pos hab]`. Distinguish the cases in `hβab : β a = β b`. Rewrite using `[dif_pos hβab]`. Distinguish the cases in `ha : a.val < j`.

Establish `hb : b.val < j` using `(hβ a b hβab).mp ha`. Establish `hσ : (σ b).val < j` using `(s1 b).mpr hb`. Simplify using `only [F, e, Equiv.ofBijective_apply, τ, A, dif_pos ha, if_pos ha, shearInv, dif_pos hσ, if_pos hσ, if_pos (And.intro ha hb), if_neg (show ¬ j ≤ a.val by omega), star_neg, add_zero]`. Expand and normalize the polynomial expressions, which then agree. Establish `hja : j ≤ a.val` using `by omega`.

Simplify using `only [F, e, Equiv.ofBijective_apply, τ, dif_neg ha, if_neg ha, shearInv, if_neg (show ¬ (a.val < j ∧ b.val < j) from fun h => ha h.1), if_pos hja, zero_add]`. Rewrite using `[key, dif_pos hab, dif_pos hβab]`. Rewrite using `[dif_neg hβab]`. Establish `h1 : (upperIn β x)⁻¹ (σ b) (σ a) = 0` using `inv_upperIn_ne β x (by rw [s2, s2]; exact fun h => hβab h.symm)`. Rewrite using `[h1, key, dif_pos hab, dif_neg hβab]`.

Simplify using the standard rewrite rules. Rewrite using `[dif_neg (lt_irrefl _), if_pos rfl, hdiag]`. Distinguish the cases in `ha : a.val < j`. Rewrite using `[if_pos ⟨ha, ha⟩, if_neg (show ¬ j ≤ a.val by omega), star_one, mul_one, inv_mul_cancel₀ (star_ne_zero.mpr (s3 a ha)), add_zero]`. Rewrite using `[if_neg (fun h : a.val < j ∧ a.val < j => ha h.1), if_pos (show j ≤ a.val by omega), key, dif_neg (lt_irrefl _), if_pos rfl, zero_add]`.

Rewrite using `[dif_neg (not_lt.mpr hab.le), if_neg (ne_of_gt hab)]`. Establish `h2 : upperIn β x a b = 0` using `by rw [key, dif_neg (not_lt.mpr hab.le), if_neg (ne_of_gt hab)]`. Distinguish the cases in `hj2 : a.val < j ∧ b.val < j`. Establish `h1 : (upperIn β x)⁻¹ (σ b) (σ a) = 0`. Distinguish the cases in `hβab : β a = β b`.

Conclude with `hgt _ _ ((s4 b a hj2.2 hj2.1 hβab.symm).2 hab)`. Conclude with `inv_upperIn_ne β x (by rw [s2, s2]; exact fun h => hβab h.symm)`. Rewrite using `[h1, h2]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hj2, h2]`.

Simplify using the standard rewrite rules.
-/
theorem exists_phi {j : ℕ} {β : Fin r → ℕ} (hβ : ∀ a b : Fin r, β a = β b → (a.val < j ↔ b.val < j))
    (σ : Equiv.Perm (Fin r)) (t : Fin r → ℂ) (s1 : ∀ a, (σ a).val < j ↔ a.val < j) (s2 : ∀ a, β (σ a) = β a)
    (s3 : ∀ a : Fin r, a.val < j → t a ≠ 0)
    (s4 : ∀ a a' : Fin r, a.val < j → a'.val < j → β a = β a' → ‖t a‖ = ‖t a'‖ ∧ (a < a' → σ a' < σ a)) :
    ∃ Φ : (UTin β → ℂ) → (UTin β → ℂ), MeasurePreserving Φ volume volume ∧ ∀ x a b, upperIn β (Φ x) a b =
      (if a.val < j ∧ b.val < j then (star (t a))⁻¹ * star ((upperIn β x)⁻¹ (σ b) (σ a)) * star (t b) else 0) +
        (if j ≤ a.val then upperIn β x a b else 0) := by
  have hb_of : ∀ p : UTin β, p.1.1.1.val < j → p.1.1.2.val < j := fun p h => (hβ _ _ p.2).mp h
  have hlt : ∀ p : UTin β, p.1.1.1.val < j → σ p.1.1.2 < σ p.1.1.1 :=
    fun p h => (s4 _ _ h (hb_of p h) p.2).2 p.1.2
  have hbeta : ∀ p : UTin β, β (σ p.1.1.2) = β (σ p.1.1.1) := fun p => by rw [s2, s2]; exact p.2.symm
  let τ : UTin β → UTin β := fun p =>
    if h : p.1.1.1.val < j then ⟨⟨(σ p.1.1.2, σ p.1.1.1), hlt p h⟩, hbeta p⟩ else p
  have hτ : Function.Injective τ := by
    intro p q hpq
    by_cases hp : p.1.1.1.val < j
    · by_cases hq : q.1.1.1.val < j
      · simp only [τ, dif_pos hp, dif_pos hq] at hpq
        have h1 := congrArg (fun u : UTin β => u.1.1) hpq
        simp only [Prod.mk.injEq] at h1
        apply Subtype.ext; apply Subtype.ext
        exact Prod.ext (σ.injective h1.2) (σ.injective h1.1)
      · simp only [τ, dif_pos hp, dif_neg hq] at hpq
        have h1 := congrArg (fun u : UTin β => u.1.1.1.val) hpq
        simp only at h1
        exact absurd (by rw [← h1]; exact (s1 _).mpr (hb_of p hp)) hq
    · by_cases hq : q.1.1.1.val < j
      · simp only [τ, dif_neg hp, dif_pos hq] at hpq
        have h1 := congrArg (fun u : UTin β => u.1.1.1.val) hpq
        simp only at h1
        exact absurd (by rw [h1]; exact (s1 _).mpr (hb_of q hq)) hp
      · simp only [τ, dif_neg hp, dif_neg hq] at hpq
        exact hpq
  let e : UTin β ≃ UTin β := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτ)
  let A : UTin β → ℂ := fun p => -((star (t p.1.1.1))⁻¹ * star (t p.1.1.2))
  let F : UTin β → ℂ → ℂ := fun p z => if p.1.1.1.val < j then A p * star z else z
  have hF : ∀ p, MeasurePreserving (F p) volume volume := by
    intro p
    by_cases hp : p.1.1.1.val < j
    · have hb := hb_of p hp
      have hA : ‖A p‖ = 1 := by
        simp only [A, norm_neg, norm_mul, norm_inv, norm_star]
        rw [(s4 _ _ hp hb p.2).1]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (s3 _ hb))
      have hFp : F p = fun z => A p * star z := by funext z; simp only [F, if_pos hp]
      rw [hFp]; exact mul_star_mp hA
    · have hFp : F p = id := by funext z; simp only [F, if_neg hp, id]
      rw [hFp]; exact MeasurePreserving.id volume
  have hP : MeasurePreserving (fun y : UTin β → ℂ => fun p => y (e p)) volume volume := by
    have h0 := volume_preserving_arrowCongr' e.symm (MeasurableEquiv.refl ℂ) (MeasurePreserving.id volume)
    exact h0
  have hC : MeasurePreserving (fun w : UTin β → ℂ => fun p => F p (w p)) volume volume :=
    volume_preserving_pi hF
  have key : ∀ (w : UTin β → ℂ) (a b : Fin r), upperIn β w a b =
      if h : a < b then (if h' : β a = β b then w ⟨⟨(a, b), h⟩, h'⟩ else 0) else if a = b then 1 else 0 := by
    intro w a b; rfl
  refine ⟨fun x => fun p => F p (shearInv j β x (e p)), (hC.comp hP).comp (shearInv_mp j β), ?_⟩
  intro x a b
  have hdiag : ∀ c, (upperIn β x)⁻¹ c c = 1 := fun c => inv_upper_diag _ c
  have hgt : ∀ c d, d < c → (upperIn β x)⁻¹ c d = 0 := fun c d h => inv_upper_gt _ h
  beta_reduce
  rw [key]
  rcases lt_trichotomy a b with hab | rfl | hab
  · rw [dif_pos hab]
    by_cases hβab : β a = β b
    · rw [dif_pos hβab]
      by_cases ha : a.val < j
      · have hb : b.val < j := (hβ a b hβab).mp ha
        have hσ : (σ b).val < j := (s1 b).mpr hb
        simp only [F, e, Equiv.ofBijective_apply, τ, A, dif_pos ha, if_pos ha, shearInv, dif_pos hσ,
          if_pos hσ, if_pos (And.intro ha hb), if_neg (show ¬ j ≤ a.val by omega), star_neg, add_zero]
        ring
      · have hja : j ≤ a.val := by omega
        simp only [F, e, Equiv.ofBijective_apply, τ, dif_neg ha, if_neg ha, shearInv,
          if_neg (show ¬ (a.val < j ∧ b.val < j) from fun h => ha h.1), if_pos hja, zero_add]
        rw [key, dif_pos hab, dif_pos hβab]
    · rw [dif_neg hβab]
      have h1 : (upperIn β x)⁻¹ (σ b) (σ a) = 0 :=
        inv_upperIn_ne β x (by rw [s2, s2]; exact fun h => hβab h.symm)
      rw [h1, key, dif_pos hab, dif_neg hβab]; simp
  · rw [dif_neg (lt_irrefl _), if_pos rfl, hdiag]
    by_cases ha : a.val < j
    · rw [if_pos ⟨ha, ha⟩, if_neg (show ¬ j ≤ a.val by omega), star_one, mul_one,
        inv_mul_cancel₀ (star_ne_zero.mpr (s3 a ha)), add_zero]
    · rw [if_neg (fun h : a.val < j ∧ a.val < j => ha h.1), if_pos (show j ≤ a.val by omega), key,
        dif_neg (lt_irrefl _), if_pos rfl, zero_add]
  · rw [dif_neg (not_lt.mpr hab.le), if_neg (ne_of_gt hab)]
    have h2 : upperIn β x a b = 0 := by rw [key, dif_neg (not_lt.mpr hab.le), if_neg (ne_of_gt hab)]
    by_cases hj2 : a.val < j ∧ b.val < j
    · have h1 : (upperIn β x)⁻¹ (σ b) (σ a) = 0 := by
        by_cases hβab : β a = β b
        · exact hgt _ _ ((s4 b a hj2.2 hj2.1 hβab.symm).2 hab)
        · exact inv_upperIn_ne β x (by rw [s2, s2]; exact fun h => hβab h.symm)
      rw [h1, h2]; simp
    · rw [if_neg hj2, h2]; simp

/- English proof (translation)
Unfold `rEl`. Use `Continuous.matrix_mul ?_ ?_` and prove the remaining obligations. Use `continuous_pi fun i => continuous_pi fun i' => ?_` and prove the remaining obligations. Establish `hU : Continuous fun q : (UTin β → ℂ) × PTop k r j => upperIn β q.1`. Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations.

Simplify using `only [upperIn, upper]`. Apply the tactic sequence `split_ifs <;> first | exact (continuous_apply _).comp continuous_fst | exact continuous_const`. Establish `hI : Continuous fun q : (UTin β → ℂ) × PTop k r j => (upperIn β q.1)⁻¹` using `(continuous_inv_upperIn β).comp continuous_fst`. Simplify using `only [uEmb]`. Use `split_ifs`.

Conclude with `(continuous_apply _).comp ((continuous_apply _).comp hU)`. Conclude with `continuous_star.comp ((continuous_apply _).comp ((continuous_apply _).comp hI))`. Conclude with `continuous_const`. Conclude with `continuous_const`. Use `continuous_pi fun i => continuous_pi fun i' => ?_` and prove the remaining obligations.

Simplify using `only [pTop, pOf, pEl, skewM, herm, bvec, dotProduct, Matrix.mulVec]`. Apply the tactic sequence `split_ifs <;> fun_prop`.
-/
theorem continuous_rEl (j : ℕ) (β : Fin r → ℕ) : Continuous (rEl k r j β) := by
  unfold rEl
  refine Continuous.matrix_mul ?_ ?_
  · refine continuous_pi fun i => continuous_pi fun i' => ?_
    have hU : Continuous fun q : (UTin β → ℂ) × PTop k r j => upperIn β q.1 := by
      refine continuous_pi fun a => continuous_pi fun b => ?_
      simp only [upperIn, upper]
      split_ifs <;> first | exact (continuous_apply _).comp continuous_fst | exact continuous_const
    have hI : Continuous fun q : (UTin β → ℂ) × PTop k r j => (upperIn β q.1)⁻¹ :=
      (continuous_inv_upperIn β).comp continuous_fst
    simp only [uEmb]
    split_ifs
    · exact (continuous_apply _).comp ((continuous_apply _).comp hU)
    · exact continuous_star.comp ((continuous_apply _).comp ((continuous_apply _).comp hI))
    · exact continuous_const
    · exact continuous_const
  · refine continuous_pi fun i => continuous_pi fun i' => ?_
    simp only [pTop, pOf, pEl, skewM, herm, bvec, dotProduct, Matrix.mulVec]
    split_ifs <;> fun_prop

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `ha : a.val < j`. Simplify using `[hP, ha]`. Simplify using `[hP, ha]`.
-/
private lemma perm_weighted_mul_apply {r j : ℕ} (σ : Equiv.Perm (Fin r)) (P A : Matrix (Fin r) (Fin r) ℂ) (f : Fin r → ℂ)
    (hP : ∀ a b, P a b = if a.val < j ∧ b = σ a then f a else 0) (a b : Fin r) :
    (P * A) a b = if a.val < j then f a * A (σ a) b else 0 := by
  rw [Matrix.mul_apply]
  by_cases ha : a.val < j
  · simp [hP, ha]
  · simp [hP, ha]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `hb : b.val < j`. Rewrite using `[if_pos hb, Finset.sum_eq_single (σ b)]`. Simplify using `[Matrix.conjTranspose_apply, hP, hb]`. Introduce `d _ hd`.

Simplify using `[Matrix.conjTranspose_apply, hP, hd]`. Simplify using the standard rewrite rules. Simplify using `[Matrix.conjTranspose_apply, hP, hb]`.
-/
private lemma mul_perm_weighted_conjTranspose_apply {r j : ℕ} (σ : Equiv.Perm (Fin r)) (P A : Matrix (Fin r) (Fin r) ℂ) (f : Fin r → ℂ)
    (hP : ∀ a b, P a b = if a.val < j ∧ b = σ a then f a else 0) (a b : Fin r) :
    (A * Pᴴ) a b = if b.val < j then A a (σ b) * star (f b) else 0 := by
  rw [Matrix.mul_apply]
  by_cases hb : b.val < j
  · rw [if_pos hb, Finset.sum_eq_single (σ b)]
    · simp [Matrix.conjTranspose_apply, hP, hb]
    · intro d _ hd
      simp [Matrix.conjTranspose_apply, hP, hd]
    · simp
  · simp [Matrix.conjTranspose_apply, hP, hb]

/- English proof (translation)
Establish `h' : (σ.symm a).val < j ↔ a.val < j` using `by simpa using (s1 (σ.symm a)).symm`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (σ.symm a)]`. Distinguish the cases in `ha : a.val < j`. Simplify using `[Matrix.conjTranspose_apply, hP, ha, h']`. Simplify using `[Matrix.conjTranspose_apply, hP, ha, h']`.

Introduce `c _ hc`. Establish `hne : a ≠ σ c` using `fun h => hc (by rw [h, Equiv.symm_apply_apply])`. Simplify using `[Matrix.conjTranspose_apply, hP, hne]`. Simplify using the standard rewrite rules.
-/
private lemma perm_weighted_conjTranspose_mul_apply {r j : ℕ} (σ : Equiv.Perm (Fin r)) (s1 : ∀ a, (σ a).val < j ↔ a.val < j)
    (P A : Matrix (Fin r) (Fin r) ℂ) (f : Fin r → ℂ)
    (hP : ∀ a b, P a b = if a.val < j ∧ b = σ a then f a else 0) (a b : Fin r) :
    (Pᴴ * A) a b = if a.val < j then star (f (σ.symm a)) * A (σ.symm a) b else 0 := by
  have h' : (σ.symm a).val < j ↔ a.val < j := by simpa using (s1 (σ.symm a)).symm
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm a)]
  · by_cases ha : a.val < j
    · simp [Matrix.conjTranspose_apply, hP, ha, h']
    · simp [Matrix.conjTranspose_apply, hP, ha, h']
  · intro c _ hc
    have hne : a ≠ σ c := fun h => hc (by rw [h, Equiv.symm_apply_apply])
    simp [Matrix.conjTranspose_apply, hP, hne]
  · simp

/- English proof (translation)
Introduce `k r j hj z z' g₀ β c _ _ _ hN`. Take `⟨σ, t, M, s1, s2, s3, s4, hM, hB⟩` from `exists_blocks hj hN`. Use `set Ym : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => if a.val < j ∧ b = σ a then (star (t a))⁻¹ else 0 with hYm`. Use `set Zm : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => if a.val < j ∧ b = σ a then t a else 0 with hZm`. Establish `hYP : ∀ a b, Ym a b = if a.val < j ∧ b = σ a then (star (t a))⁻¹ else 0` using `fun _ _ => rfl`.

Establish `hZP : ∀ a b, Zm a b = if a.val < j ∧ b = σ a then t a else 0` using `fun _ _ => rfl`. Establish `hc : ‖c‖ = 1` using `hN.2.1`. Establish `hβ : ∀ a b : Fin r, β a = β b → (a.val < j ↔ b.val < j)`. Introduce `a b hab`. Establish `h5` using `hN.2.2.2.2.1`.

Prove the components needed by the constructor for the conclusion. Introduce `ha`. Assume the negation of the conclusion as `hb`. Use `(h5 a b (not_lt.mp hb)).1 hab` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Introduce `hb`. Assume the negation of the conclusion as `ha`. Use `(h5 b a (not_lt.mp ha)).1 hab.symm` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨Φ, hΦ, hΦu⟩` from `exists_phi hβ σ t s1 s2 s3 s4`.

Establish `hF : (Fj r j)ᴴ = Fj r j`. Use extensionality with `a b`. Simplify using `only [Fj, Matrix.conjTranspose_apply, Matrix.diagonal_apply]`. Distinguish the cases in `hab : a = b`. Apply the tactic sequence `subst hab; split_ifs <;> simp`.

Simplify using `[hab, Ne.symm hab]`. Establish `hFF : Fj r j * Fj r j = Fj r j`. Simplify using `only [Fj, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hFY : Fj r j * Ym = 0`. Use extensionality with `a b`. Simplify using `only [Fj, Matrix.diagonal_mul, hYP, Matrix.zero_apply]`. Distinguish the cases in `ha : a.val < j`.

Establish `: ¬ j ≤ a.val` using `by omega`. Simplify using `[this]`. Simplify using `[ha]`. Establish `hFZ : Fj r j * Zm = 0`. Use extensionality with `a b`.

Simplify using `only [Fj, Matrix.diagonal_mul, hZP, Matrix.zero_apply]`. Distinguish the cases in `ha : a.val < j`. Establish `: ¬ j ≤ a.val` using `by omega`. Simplify using `[this]`. Simplify using `[ha]`.

Establish `hYF : Ym * Fj r j = 0`. Use extensionality with `a b`. Simplify using `only [Fj, Matrix.mul_diagonal, hYP, Matrix.zero_apply]`. Distinguish the cases in `ha : a.val < j`. Distinguish the cases in `hb : b = σ a`.

Substitute `hb` using the available equality. Establish `: ¬ j ≤ (σ a).val` using `by have := (s1 a).2 ha; omega`. Simplify using `[this]`. Simplify using `[hb]`. Simplify using `[ha]`.

Establish `hZF : Zm * Fj r j = 0`. Use extensionality with `a b`. Simplify using `only [Fj, Matrix.mul_diagonal, hZP, Matrix.zero_apply]`. Distinguish the cases in `ha : a.val < j`. Distinguish the cases in `hb : b = σ a`.

Substitute `hb` using the available equality. Establish `: ¬ j ≤ (σ a).val` using `by have := (s1 a).2 ha; omega`. Simplify using `[this]`. Simplify using `[hb]`. Simplify using `[ha]`.

Establish `hYZ : Ymᴴ * Zm = 1 - Fj r j`. Use extensionality with `a b`. Rewrite using `[perm_weighted_conjTranspose_mul_apply σ s1 Ym Zm _ hYP, hZP]`. Establish `h' : (σ.symm a).val < j ↔ a.val < j` using `by simpa using (s1 (σ.symm a)).symm`. Simplify using `only [Matrix.sub_apply, Matrix.one_apply, Fj, Matrix.diagonal_apply, Equiv.apply_symm_apply, h']`.

Distinguish the cases in `ha : a.val < j`. Establish `ht` using `s3 _ ((h').2 ha)`. Distinguish the cases in `hab : b = a`. Substitute `hab` using the available equality. Simplify using `[ha, ht, not_le.mpr ha]`.

Simplify using `[ha, hab, Ne.symm hab]`. Establish `hja : j ≤ a.val` using `by omega`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `[ha, hja]`.

Simplify using `[ha, hab]`. Establish `hZY : Ym * Zmᴴ = 1 - Fj r j`. Use extensionality with `a b`. Rewrite using `[mul_perm_weighted_conjTranspose_apply σ Zm Ym _ hZP, hYP]`. Simplify using `only [Matrix.sub_apply, Matrix.one_apply, Fj, Matrix.diagonal_apply]`.

Distinguish the cases in `hb : b.val < j`. Establish `ht` using `s3 _ hb`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `[hb, ht, not_le.mpr hb]`.

Establish `: ¬ (σ b = σ a)` using `fun h => hab (σ.injective h).symm`. Simplify using `[hb, hab, this]`. Establish `hjb : j ≤ b.val` using `by omega`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using `[hb, hjb]`. Simplify using `[hb, hab]`. Establish `huF : ∀ x : UTin β → ℂ, upperIn β x * Fj r j = Fj r j * upperIn β x`. Introduce `x`. Use extensionality with `a b`.

Simplify using `only [Fj, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Distinguish the cases in `hab : β a = β b`. Establish `hiff` using `hβ a b hab`. Distinguish the cases in `ha : j ≤ a.val`. Establish `hb : j ≤ b.val`.

Assume the negation of the conclusion as `h`. Conclude with `absurd (hiff.2 (by omega)) (by omega)`. Simplify using `[ha, hb]`. Establish `hb : ¬ j ≤ b.val`. Introduce `h`.

Conclude with `absurd (hiff.1 (by omega)) (by omega)`. Simplify using `[ha, hb]`. Rewrite using `[upperIn_ne β x hab]`. Simplify using the standard rewrite rules. Establish `hU : ∀ x : UTin β → ℂ, g₀ * uEmb k r (upperIn β x) = uEmb k r (upperIn β (Φ x)) * g₀`.

Introduce `x`. Establish `hu : IsUnit (upperIn β x).det` using `isUnit_upper _`. Take `⟨h1, h2, h3, h4⟩` from `alg c hu hF hFF hYZ hZY hFY hYF hFZ hZF (huF x)`. Establish `key : Ym * ((upperIn β x)⁻¹)ᴴ * Zmᴴ + Fj r j * upperIn β x = upperIn β (Φ x)`. Use extensionality with `a b`.

Rewrite using `[hΦu, Matrix.add_apply, Matrix.mul_assoc, perm_weighted_mul_apply σ Ym _ _ hYP, mul_perm_weighted_conjTranspose_apply σ Zm _ _ hZP]`. Simplify using `only [Fj, Matrix.diagonal_mul, Matrix.conjTranspose_apply]`. Apply the tactic sequence `by_cases ha : a.val < j <;> by_cases hb : b.val < j <;> simp [ha, hb] <;> ring_nf <;> omega`. Rewrite using `[← key]`. Conclude with `conj_u hB h1 h2 h3 h4`.

Establish `hZ0 : ∀ a b : Fin r, j ≤ a.val ∨ j ≤ b.val → Zm a b = 0`. Introduce `a b hab`. Rewrite using `[hZP]`. Use `split_ifs with h`. Take `⟨ha, rfl⟩` from `h`.

Use `(s1 a).2 ha` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Set `L : PTop k r j → PTop k r j` to `fun q => (fun a => star c • M *ᵥ q.1 a, q.2)`. Establish `hP : ∀ q : PTop k r j, g₀ * pTop k r j q = pTop k r j (L q) * g₀`.

Introduce `q`. Establish `e1 : pTop k r j q = pEl k r (fun a => if h : j ≤ a.val then q.1 ⟨a, h⟩ else 0) (skewM (fun p => if h : j ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0) (fun a => if h : j ≤ a.val then q.2.2 ⟨a, h⟩ else 0))` using `rfl`. Establish `e2 : pTop k r j (L q) = pEl k r (fun a => star c • M *ᵥ (if h : j ≤ a.val then q.1 ⟨a, h⟩ else 0)) (skewM (fun p => if h : j ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0) (fun a => if h : j ≤ a.val then q.2.2 ⟨a, h⟩ else 0))`. Simplify using `only [pTop, pOf, L]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[e1, e2]`. Use `conj_p hB hc hM hZ0 _ _ ?_ ?_` and prove the remaining obligations. Introduce `a ha`.

Rewrite using `[dif_neg (by omega)]`. Introduce `a b hab`. Simplify using `only [skewM]`. Distinguish the cases in `h1 : a < b`. Establish `ha : ¬ j ≤ a.val`.

Use `Fin.lt_iff_val_lt_val.mp h1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `[h1, ha]`. Distinguish the cases in `h2 : b < a`. Establish `hb : ¬ j ≤ b.val`.

Use `Fin.lt_iff_val_lt_val.mp h2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `[h1, h2, hb]`. Establish `hab' : a = b` using `le_antisymm (not_lt.mp h2) (not_lt.mp h1)`. Substitute `hab'` using the available equality.

Establish `ha : ¬ j ≤ a.val` using `by omega`. Simplify using `[ha]`. Establish `hLmp : MeasurePreserving L volume volume`. Establish `hdet : Complex.normSq (star c • M).det = 1`. Establish `hs : Complex.normSq (star c) = 1`.

Rewrite using `[Complex.normSq_eq_norm_sq, norm_star, hc]`. Evaluate the numerical expressions. Rewrite using `[Matrix.det_smul, map_mul, map_pow, hs, one_pow, one_mul, normSq_det_of_mem hM]`. Establish `h0 : MeasurePreserving (fun v : Fin (k + 1) → ℂ => (star c • M) *ᵥ v) volume volume` using `mulVec_mp hdet`. Establish `e : (fun v : Fin (k + 1) → ℂ => (star c • M) *ᵥ v) = fun v => star c • M *ᵥ v`.

Use function extensionality and compare the values at `v i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`. Establish `h1 : MeasurePreserving (fun v : Fin (k + 1) → ℂ => star c • M *ᵥ v) volume volume` using `e ▸ h0`. Establish `h2 : MeasurePreserving (fun B : {a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ => fun a => star c • M *ᵥ B a) volume volume`. Simplify `measurePreserving_pi (fun _ => (volume : Measure (Fin (k + 1) → ℂ))) (fun _ => (volume : Measure (Fin (k + 1) → ℂ))) (fun _ => h1)` using `[volume_pi]`.

Establish `h3` using `h2.prod (MeasurePreserving.id (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ))))`. Conclude with `h3`. Use `haveI : SFinite (volume : Measure (PTop k r j)) := by haveI : SFinite ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ℂ)).prod (volume : Measure ({a : Fin r // j ≤ a.val} → ℝ))) := inferInstance haveI : SFinite (volume : Measure ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ)) := …`. Conclude with `(inferInstance : SFinite ((volume : Measure ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ)).prod ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ℂ)).prod (volume : Measure ({a : Fin r // j ≤ a.val} → ℝ)))))`. Use `haveI : OpensMeasurableSpace ((UTin β → ℂ) × PTop k r j) := by haveI : OpensMeasurableSpace (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ)) := inferInstance haveI : OpensMeasurableSpace (PTop k r j) := inferInstance infer_instance`.

Set `Ψ : (UTin β → ℂ) × PTop k r j → (UTin β → ℂ) × PTop k r j` to `fun q => (Φ q.1, L q.2)`. Establish `hΨ : MeasurePreserving Ψ (volume.prod volume) (volume.prod volume)` using `hΦ.prod hLmp`. Establish `hg : IsUnit g₀.det` using `isUnit_det_of_mem hN.1`. Establish `hcomp : (conjM g₀) ∘ (fun q => Matrix.of.symm (rEl k r j β q)) = (fun q => Matrix.of.symm (rEl k r j β q)) ∘ Ψ`. Use function extensionality and compare the values at `q`.

Simplify using `only [Function.comp, conjM, rEl, Equiv.apply_symm_apply]`. Use `show g₀ * (uEmb k r (upperIn β q.1) * pTop k r j q.2) * g₀⁻¹ = uEmb k r (upperIn β (Φ q.1)) * pTop k r j (L q.2)`. Rewrite using `[← Matrix.mul_assoc, hU, Matrix.mul_assoc (uEmb k r (upperIn β (Φ q.1))) g₀, hP, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.mul_one]`. Establish `hmR : Measurable fun q : (UTin β → ℂ) × PTop k r j => Matrix.of.symm (rEl k r j β q)`. Establish `hcR : Continuous fun q : (UTin β → ℂ) × PTop k r j => Matrix.of.symm (rEl k r j β q)` using `continuous_rEl j β`.

Use the proof step `hcR.measurable`. Establish `hmC : Measurable (conjM (k` using `k) (r := r) g₀) := by`. Establish `hc2 : Continuous fun x : Mt k r => Matrix.of x` using `continuous_id`. Establish `hc3 : Continuous (conjM (k` using `k) (r := r) g₀) := by`. Unfold `conjM`.

Conclude with `(continuous_const.matrix_mul hc2).matrix_mul continuous_const`. Conclude with `hc3.measurable`. Unfold `lebR0`. Rewrite using `[Measure.volume_eq_prod, Measure.map_map hmC hmR, hcomp, ← Measure.map_map hmR hΨ.measurable, hΨ.map_eq]`.
-/
theorem lebR0_map_conjM_eq_of_isNormalZero : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → (lebR0 k r j β).map (conjM g₀) = lebR0 k r j β := by
  intro k r j hj z z' g₀ β c _ _ _ hN
  obtain ⟨σ, t, M, s1, s2, s3, s4, hM, hB⟩ := exists_blocks hj hN
  set Ym : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => if a.val < j ∧ b = σ a then (star (t a))⁻¹ else 0 with hYm
  set Zm : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => if a.val < j ∧ b = σ a then t a else 0 with hZm
  have hYP : ∀ a b, Ym a b = if a.val < j ∧ b = σ a then (star (t a))⁻¹ else 0 := fun _ _ => rfl
  have hZP : ∀ a b, Zm a b = if a.val < j ∧ b = σ a then t a else 0 := fun _ _ => rfl
  have hc : ‖c‖ = 1 := hN.2.1
  have hβ : ∀ a b : Fin r, β a = β b → (a.val < j ↔ b.val < j) := by
    intro a b hab
    have h5 := hN.2.2.2.2.1
    constructor
    · intro ha
      by_contra hb
      have := (h5 a b (not_lt.mp hb)).1 hab
      omega
    · intro hb
      by_contra ha
      have := (h5 b a (not_lt.mp ha)).1 hab.symm
      omega
  obtain ⟨Φ, hΦ, hΦu⟩ := exists_phi hβ σ t s1 s2 s3 s4
  have hF : (Fj r j)ᴴ = Fj r j := by
    ext a b
    simp only [Fj, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab; split_ifs <;> simp
    · simp [hab, Ne.symm hab]
  have hFF : Fj r j * Fj r j = Fj r j := by
    simp only [Fj, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    split_ifs <;> simp
  have hFY : Fj r j * Ym = 0 := by
    ext a b
    simp only [Fj, Matrix.diagonal_mul, hYP, Matrix.zero_apply]
    by_cases ha : a.val < j
    · have : ¬ j ≤ a.val := by omega
      simp [this]
    · simp [ha]
  have hFZ : Fj r j * Zm = 0 := by
    ext a b
    simp only [Fj, Matrix.diagonal_mul, hZP, Matrix.zero_apply]
    by_cases ha : a.val < j
    · have : ¬ j ≤ a.val := by omega
      simp [this]
    · simp [ha]
  have hYF : Ym * Fj r j = 0 := by
    ext a b
    simp only [Fj, Matrix.mul_diagonal, hYP, Matrix.zero_apply]
    by_cases ha : a.val < j
    · by_cases hb : b = σ a
      · subst hb
        have : ¬ j ≤ (σ a).val := by have := (s1 a).2 ha; omega
        simp [this]
      · simp [hb]
    · simp [ha]
  have hZF : Zm * Fj r j = 0 := by
    ext a b
    simp only [Fj, Matrix.mul_diagonal, hZP, Matrix.zero_apply]
    by_cases ha : a.val < j
    · by_cases hb : b = σ a
      · subst hb
        have : ¬ j ≤ (σ a).val := by have := (s1 a).2 ha; omega
        simp [this]
      · simp [hb]
    · simp [ha]
  have hYZ : Ymᴴ * Zm = 1 - Fj r j := by
    ext a b
    rw [perm_weighted_conjTranspose_mul_apply σ s1 Ym Zm _ hYP, hZP]
    have h' : (σ.symm a).val < j ↔ a.val < j := by simpa using (s1 (σ.symm a)).symm
    simp only [Matrix.sub_apply, Matrix.one_apply, Fj, Matrix.diagonal_apply, Equiv.apply_symm_apply, h']
    by_cases ha : a.val < j
    · have ht := s3 _ ((h').2 ha)
      by_cases hab : b = a
      · subst hab; simp [ha, ht, not_le.mpr ha]
      · simp [ha, hab, Ne.symm hab]
    · have hja : j ≤ a.val := by omega
      by_cases hab : a = b
      · subst hab; simp [ha, hja]
      · simp [ha, hab]
  have hZY : Ym * Zmᴴ = 1 - Fj r j := by
    ext a b
    rw [mul_perm_weighted_conjTranspose_apply σ Zm Ym _ hZP, hYP]
    simp only [Matrix.sub_apply, Matrix.one_apply, Fj, Matrix.diagonal_apply]
    by_cases hb : b.val < j
    · have ht := s3 _ hb
      by_cases hab : a = b
      · subst hab; simp [hb, ht, not_le.mpr hb]
      · have : ¬ (σ b = σ a) := fun h => hab (σ.injective h).symm
        simp [hb, hab, this]
    · have hjb : j ≤ b.val := by omega
      by_cases hab : a = b
      · subst hab; simp [hb, hjb]
      · simp [hb, hab]
  have huF : ∀ x : UTin β → ℂ, upperIn β x * Fj r j = Fj r j * upperIn β x := by
    intro x
    ext a b
    simp only [Fj, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hab : β a = β b
    · have hiff := hβ a b hab
      by_cases ha : j ≤ a.val
      · have hb : j ≤ b.val := by
          by_contra h
          exact absurd (hiff.2 (by omega)) (by omega)
        simp [ha, hb]
      · have hb : ¬ j ≤ b.val := by
          intro h
          exact absurd (hiff.1 (by omega)) (by omega)
        simp [ha, hb]
    · rw [upperIn_ne β x hab]; simp
  have hU : ∀ x : UTin β → ℂ, g₀ * uEmb k r (upperIn β x) = uEmb k r (upperIn β (Φ x)) * g₀ := by
    intro x
    have hu : IsUnit (upperIn β x).det := isUnit_upper _
    obtain ⟨h1, h2, h3, h4⟩ := alg c hu hF hFF hYZ hZY hFY hYF hFZ hZF (huF x)
    have key : Ym * ((upperIn β x)⁻¹)ᴴ * Zmᴴ + Fj r j * upperIn β x = upperIn β (Φ x) := by
      ext a b
      rw [hΦu, Matrix.add_apply, Matrix.mul_assoc, perm_weighted_mul_apply σ Ym _ _ hYP,
        mul_perm_weighted_conjTranspose_apply σ Zm _ _ hZP]
      simp only [Fj, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
      by_cases ha : a.val < j <;> by_cases hb : b.val < j <;> simp [ha, hb] <;> ring_nf <;> omega
    rw [← key]
    exact conj_u hB h1 h2 h3 h4
  have hZ0 : ∀ a b : Fin r, j ≤ a.val ∨ j ≤ b.val → Zm a b = 0 := by
    intro a b hab
    rw [hZP]
    split_ifs with h
    · obtain ⟨ha, rfl⟩ := h
      have := (s1 a).2 ha
      omega
    · rfl
  let L : PTop k r j → PTop k r j := fun q => (fun a => star c • M *ᵥ q.1 a, q.2)
  have hP : ∀ q : PTop k r j, g₀ * pTop k r j q = pTop k r j (L q) * g₀ := by
    intro q
    have e1 : pTop k r j q = pEl k r (fun a => if h : j ≤ a.val then q.1 ⟨a, h⟩ else 0)
        (skewM (fun p => if h : j ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0) (fun a => if h : j ≤ a.val then q.2.2 ⟨a, h⟩ else 0)) := rfl
    have e2 : pTop k r j (L q) = pEl k r (fun a => star c • M *ᵥ (if h : j ≤ a.val then q.1 ⟨a, h⟩ else 0))
        (skewM (fun p => if h : j ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0) (fun a => if h : j ≤ a.val then q.2.2 ⟨a, h⟩ else 0)) := by
      simp only [pTop, pOf, L]
      congr 1
      funext a
      split_ifs <;> simp
    rw [e1, e2]
    refine conj_p hB hc hM hZ0 _ _ ?_ ?_
    · intro a ha
      rw [dif_neg (by omega)]
    · intro a b hab
      simp only [skewM]
      by_cases h1 : a < b
      · have ha : ¬ j ≤ a.val := by
          have := Fin.lt_iff_val_lt_val.mp h1
          omega
        simp [h1, ha]
      · by_cases h2 : b < a
        · have hb : ¬ j ≤ b.val := by
            have := Fin.lt_iff_val_lt_val.mp h2
            omega
          simp [h1, h2, hb]
        · have hab' : a = b := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
          subst hab'
          have ha : ¬ j ≤ a.val := by omega
          simp [ha]
  have hLmp : MeasurePreserving L volume volume := by
    have hdet : Complex.normSq (star c • M).det = 1 := by
      have hs : Complex.normSq (star c) = 1 := by
        rw [Complex.normSq_eq_norm_sq, norm_star, hc]
        norm_num
      rw [Matrix.det_smul, map_mul, map_pow, hs, one_pow, one_mul, normSq_det_of_mem hM]
    have h0 : MeasurePreserving (fun v : Fin (k + 1) → ℂ => (star c • M) *ᵥ v) volume volume := mulVec_mp hdet
    have e : (fun v : Fin (k + 1) → ℂ => (star c • M) *ᵥ v) = fun v => star c • M *ᵥ v := by
      funext v i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    have h1 : MeasurePreserving (fun v : Fin (k + 1) → ℂ => star c • M *ᵥ v) volume volume := e ▸ h0
    have h2 : MeasurePreserving (fun B : {a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ => fun a => star c • M *ᵥ B a)
        volume volume := by
      simpa [volume_pi] using measurePreserving_pi (fun _ => (volume : Measure (Fin (k + 1) → ℂ)))
        (fun _ => (volume : Measure (Fin (k + 1) → ℂ))) (fun _ => h1)
    have h3 := h2.prod (MeasurePreserving.id (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ))))
    exact h3
  haveI : SFinite (volume : Measure (PTop k r j)) := by
    haveI : SFinite ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ℂ)).prod
      (volume : Measure ({a : Fin r // j ≤ a.val} → ℝ))) := inferInstance
    haveI : SFinite (volume : Measure ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ)) := inferInstance
    exact (inferInstance : SFinite ((volume : Measure ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ)).prod
      ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ℂ)).prod (volume : Measure ({a : Fin r // j ≤ a.val} → ℝ)))))
  haveI : OpensMeasurableSpace ((UTin β → ℂ) × PTop k r j) := by
    haveI : OpensMeasurableSpace (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ)) := inferInstance
    haveI : OpensMeasurableSpace (PTop k r j) := inferInstance
    infer_instance
  let Ψ : (UTin β → ℂ) × PTop k r j → (UTin β → ℂ) × PTop k r j := fun q => (Φ q.1, L q.2)
  have hΨ : MeasurePreserving Ψ (volume.prod volume) (volume.prod volume) := hΦ.prod hLmp
  have hg : IsUnit g₀.det := isUnit_det_of_mem hN.1
  have hcomp : (conjM g₀) ∘ (fun q => Matrix.of.symm (rEl k r j β q)) = (fun q => Matrix.of.symm (rEl k r j β q)) ∘ Ψ := by
    funext q
    simp only [Function.comp, conjM, rEl, Equiv.apply_symm_apply]
    show g₀ * (uEmb k r (upperIn β q.1) * pTop k r j q.2) * g₀⁻¹ = uEmb k r (upperIn β (Φ q.1)) * pTop k r j (L q.2)
    rw [← Matrix.mul_assoc, hU, Matrix.mul_assoc (uEmb k r (upperIn β (Φ q.1))) g₀, hP, Matrix.mul_assoc,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.mul_one]
  have hmR : Measurable fun q : (UTin β → ℂ) × PTop k r j => Matrix.of.symm (rEl k r j β q) :=
    have hcR : Continuous fun q : (UTin β → ℂ) × PTop k r j => Matrix.of.symm (rEl k r j β q) := continuous_rEl j β
    hcR.measurable
  have hmC : Measurable (conjM (k := k) (r := r) g₀) := by
    have hc2 : Continuous fun x : Mt k r => Matrix.of x := continuous_id
    have hc3 : Continuous (conjM (k := k) (r := r) g₀) := by
      unfold conjM
      exact (continuous_const.matrix_mul hc2).matrix_mul continuous_const
    exact hc3.measurable
  unfold lebR0
  rw [Measure.volume_eq_prod, Measure.map_map hmC hmR, hcomp, ← Measure.map_map hmR hΨ.measurable, hΨ.map_eq]

end GlobalTheory.Amp.RConj
