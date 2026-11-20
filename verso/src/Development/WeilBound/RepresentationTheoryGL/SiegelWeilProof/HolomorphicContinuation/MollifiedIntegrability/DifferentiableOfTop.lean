import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundAlt

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.WR.T

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def FD (L : List (Fin n × Fin n)) (f : E n → ℂ) : E n → ℂ := L.foldr (fun kl g => Dkl kl.1 kl.2 g) f

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem FD_cons (kl : Fin n × Fin n) (L : List (Fin n × Fin n)) (f : E n → ℂ) :
    FD (kl :: L) f = Dkl kl.1 kl.2 (FD L f) := rfl

/- English proof (translation)
Simplify using `[FD, List.foldr_append]`.
-/
theorem FD_append (L L' : List (Fin n × Fin n)) (f : E n → ℂ) : FD (L ++ L') f = FD L (FD L' f) := by
  simp [FD, List.foldr_append]

/- English proof (translation)
Establish `h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f)` using `(contDiff_infty_iff_fderiv.1 hf).2`. Establish `ha : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ f y (fun a b => (w a b).re))` using `h1.clm_apply contDiff_const`. Establish `hb : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ f y (fun a b => (w a b).im))` using `h1.clm_apply contDiff_const`. Conclude with `ha.add (contDiff_const.mul hb)`.
-/
theorem contDiff_dirC {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : Fin n → Fin n → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (dirC f w) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := (contDiff_infty_iff_fderiv.1 hf).2
  have ha : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ f y (fun a b => (w a b).re)) := h1.clm_apply contDiff_const
  have hb : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ f y (fun a b => (w a b).im)) := h1.clm_apply contDiff_const
  exact ha.add (contDiff_const.mul hb)

/- English proof (translation)
The claim follows from `contDiff_dirC hf _`.
-/
theorem contDiff_Dkl {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k l : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (Dkl k l f) := contDiff_dirC hf _

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact hf`. Consider the case `cons kl L ih => exact contDiff_Dkl ih _ _`.
-/
theorem contDiff_FD {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (L : List (Fin n × Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (FD L f) := by
  induction L with
  | nil => exact hf
  | cons kl L ih => exact contDiff_Dkl ih _ _

/- English proof (translation)
The claim follows from `hf.differentiable (by simp)`.
-/
theorem differentiable_of_top {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Differentiable ℝ f :=
  hf.differentiable (by simp)

/- English proof (translation)
Use function extensionality and compare the values at `y`. Unfold `Dkl dirC`. Establish `hfun : (fun y => ∑ i ∈ s, c i * F i y) = ∑ i ∈ s, (fun y => c i * F i y)`. Use function extensionality and compare the values at `y`. Simplify using `[Finset.sum_apply]`.

Rewrite using `[hfun, fderiv_sum (fun i hi => ((hF i hi) y).const_mul (c i))]`. Establish `e : ∀ i ∈ s, fderiv ℝ (fun y => c i * F i y) y = c i • fderiv ℝ (F i) y` using `fun i hi => fderiv_const_mul ((hF i hi) y) (c i)`. Rewrite using `[Finset.sum_congr rfl e]`. Simplify using `only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => by ring` and prove the remaining obligations.
-/
theorem Dkl_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → E n → ℂ) (hF : ∀ i ∈ s, Differentiable ℝ (F i))
    (k l : Fin n) : Dkl k l (fun y => ∑ i ∈ s, c i * F i y) = fun y => ∑ i ∈ s, c i * Dkl k l (F i) y := by
  funext y
  unfold Dkl dirC
  have hfun : (fun y => ∑ i ∈ s, c i * F i y) = ∑ i ∈ s, (fun y => c i * F i y) := by
    funext y; simp [Finset.sum_apply]
  rw [hfun, fderiv_sum (fun i hi => ((hF i hi) y).const_mul (c i))]
  have e : ∀ i ∈ s, fderiv ℝ (fun y => c i * F i y) y = c i • fderiv ℝ (F i) y :=
    fun i hi => fderiv_const_mul ((hF i hi) y) (c i)
  rw [Finset.sum_congr rfl e]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => rfl`. Consider the case `cons kl L ih`. Rewrite using `[FD_cons, ih]`. Conclude with `Dkl_sum s c (fun i => FD L (F i)) (fun i hi => differentiable_of_top (contDiff_FD (hF i hi) L)) _ _`.
-/
theorem FD_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → E n → ℂ) (hF : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (L : List (Fin n × Fin n)) : FD L (fun y => ∑ i ∈ s, c i * F i y) = fun y => ∑ i ∈ s, c i * FD L (F i) y := by
  induction L with
  | nil => rfl
  | cons kl L ih =>
    rw [FD_cons, ih]
    exact Dkl_sum s c (fun i => FD L (F i)) (fun i hi => differentiable_of_top (contDiff_FD (hF i hi) L)) _ _

def Ls (σ : Equiv.Perm (Fin n)) : List (Fin n × Fin n) := (List.finRange n).map fun k => (k, σ k)

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `only [Delta, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, FD, Ls, List.foldr_map]`.
-/
theorem Delta_eq (f : E n → ℂ) :
    Delta f = fun y => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * FD (Ls σ) f y := by
  funext y
  simp only [Delta, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, FD, Ls, List.foldr_map]

def Good (f : E n → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ ∀ L : List (Fin n × Fin n), ∃ h : E n → ℝ, Integrable h ∧ ∀ y, ‖FD L f y‖ ≤ h y

/- English proof (translation)
Use `⟨contDiff_FD hf.1 L, fun L' => ?_⟩` and prove the remaining obligations. Rewrite using `[← FD_append]`. Conclude with `hf.2 _`.
-/
theorem good_FD {f : E n → ℂ} (hf : Good f) (L : List (Fin n × Fin n)) : Good (FD L f) := by
  refine ⟨contDiff_FD hf.1 L, fun L' => ?_⟩
  rw [← FD_append]
  exact hf.2 _

/- English proof (translation)
Use `⟨?_, fun L => ?_⟩` and prove the remaining obligations. Conclude with `ContDiff.sum fun i hi => contDiff_const.mul (hF i hi).1`. Rewrite using `[FD_sum s c F (fun i hi => (hF i hi).1) L]`. Establish `: ∀ i ∈ s, ∃ h : E n → ℝ, Integrable h ∧ ∀ y, ‖FD L (F i) y‖ ≤ h y` using `fun i hi => (hF i hi).2 L`. Use `choose! h hint hb using this`.

Use `⟨fun y => ∑ i ∈ s, ‖c i‖ * h i y, integrable_finset_sum s fun i hi => (hint i hi).const_mul _, fun y => ?_⟩` and prove the remaining obligations. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hb i hi y) (norm_nonneg _)`.
-/
theorem good_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → E n → ℂ) (hF : ∀ i ∈ s, Good (F i)) :
    Good (fun y => ∑ i ∈ s, c i * F i y) := by
  refine ⟨?_, fun L => ?_⟩
  · exact ContDiff.sum fun i hi => contDiff_const.mul (hF i hi).1
  · rw [FD_sum s c F (fun i hi => (hF i hi).1) L]
    have : ∀ i ∈ s, ∃ h : E n → ℝ, Integrable h ∧ ∀ y, ‖FD L (F i) y‖ ≤ h y := fun i hi => (hF i hi).2 L
    choose! h hint hb using this
    refine ⟨fun y => ∑ i ∈ s, ‖c i‖ * h i y, integrable_finset_sum s fun i hi => (hint i hi).const_mul _, fun y => ?_⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb i hi y) (norm_nonneg _)

/- English proof (translation)
Rewrite using `[Delta_eq]`. Conclude with `good_sum _ _ _ fun σ _ => good_FD hf _`.
-/
theorem good_Delta {f : E n → ℂ} (hf : Good f) : Good (Delta f) := by
  rw [Delta_eq]
  exact good_sum _ _ _ fun σ _ => good_FD hf _

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact hf`. Consider the case `succ k ih => rw [Function.iterate_succ_apply']`. Conclude with `good_Delta ih`.
-/
theorem good_iter {f : E n → ℂ} (hf : Good f) (k : ℕ) : Good (Delta^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact good_Delta ih

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ N ih`. Rewrite using `[ih, hIBP n (Delta^[N] f) t β (good_iter hf N).1 ht hβ (good_iter hf N).2, Function.iterate_succ_apply', pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ibp_iter (hIBP : IBP) {f : E n → ℂ} (hf : Good f) (t : ℝ) (β : E n) (ht : t ≠ 0) (hβ : (herm β).det ≠ 0)
    (N : ℕ) : ∫ y, f y * chr t β y =
      ((-1) ^ n * ((-(Complex.I * t)) ^ n * (herm β).det)⁻¹) ^ N * ∫ y, (Delta^[N] f) y * chr t β y := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, hIBP n (Delta^[N] f) t β (good_iter hf N).1 ht hβ (good_iter hf N).2, Function.iterate_succ_apply', pow_succ]
    ring

end PositivityTheory.Rg.Sw.WR.T
