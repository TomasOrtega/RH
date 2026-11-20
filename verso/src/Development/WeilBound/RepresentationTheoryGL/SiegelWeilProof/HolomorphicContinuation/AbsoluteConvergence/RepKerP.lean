import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ProjSt

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.AbsSt.Proj

namespace RK

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H]
  [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure]

/- English proof (translation)
Conclude with `hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)`.
-/
theorem integ {f : H → ℂ} (hf : Continuous f) : Integrable f μ := by
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/- English proof (translation)
The claim follows from `integ μ (hu.star.mul hw)`.
-/
theorem integ_sm {u w : H → ℂ} (hu : Continuous u) (hw : Continuous w) : Integrable (fun y => star (u y) * w y) μ :=
  integ μ (hu.star.mul hw)

def ip (u w : H → ℂ) : ℂ := ∫ y, star (u y) * w y ∂μ

/- English proof (translation)
Simplify using `only [ip, mul_add]`. Conclude with `integral_add (integ_sm μ hu hw) (integ_sm μ hu hw')`.
-/
theorem ip_add {u w w' : H → ℂ} (hu : Continuous u) (hw : Continuous w) (hw' : Continuous w') :
    ip μ u (fun y => w y + w' y) = ip μ u w + ip μ u w' := by
  simp only [ip, mul_add]
  exact integral_add (integ_sm μ hu hw) (integ_sm μ hu hw')

/- English proof (translation)
Simplify using `only [ip, mul_sub]`. Conclude with `integral_sub (integ_sm μ hu hw) (integ_sm μ hu hw')`.
-/
theorem ip_sub {u w w' : H → ℂ} (hu : Continuous u) (hw : Continuous w) (hw' : Continuous w') :
    ip μ u (fun y => w y - w' y) = ip μ u w - ip μ u w' := by
  simp only [ip, mul_sub]
  exact integral_sub (integ_sm μ hu hw) (integ_sm μ hu hw')

/- English proof (translation)
Unfold `ip`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[integral_finset_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← integral_const_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `y`. Expand and normalize the polynomial expressions, which then agree. Introduce `i _`. Conclude with `integ μ ((continuous_star.comp hu).mul (continuous_const.mul (hw i)))`.
-/
theorem ip_sum_right {ι : Type} (s : Finset ι) {u : H → ℂ} (hu : Continuous u) (c : ι → ℂ) (w : ι → H → ℂ)
    (hw : ∀ i, Continuous (w i)) : ip μ u (fun y => ∑ i ∈ s, c i * w i y) = ∑ i ∈ s, c i * ip μ u (w i) := by
  unfold ip
  simp only [Finset.mul_sum]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  · intro i _
    exact integ μ ((continuous_star.comp hu).mul (continuous_const.mul (hw i)))

/- English proof (translation)
Unfold `ip`. Establish `key : ∀ y, star (∑ i ∈ s, c i * u i y) * w y = ∑ i ∈ s, star (c i) * (star (u i y) * w y)`. Introduce `y`. Rewrite using `[star_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[star_mul']`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [key]`. Rewrite using `[integral_finset_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Conclude with `integral_const_mul _ _`. Introduce `i _`. Conclude with `(integ_sm μ (hu i) hw).const_mul _`.
-/
theorem ip_sum_left {ι : Type} (s : Finset ι) {w : H → ℂ} (hw : Continuous w) (c : ι → ℂ) (u : ι → H → ℂ)
    (hu : ∀ i, Continuous (u i)) : ip μ (fun y => ∑ i ∈ s, c i * u i y) w = ∑ i ∈ s, star (c i) * ip μ (u i) w := by
  unfold ip
  have key : ∀ y, star (∑ i ∈ s, c i * u i y) * w y = ∑ i ∈ s, star (c i) * (star (u i y) * w y) := by
    intro y
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_mul']
    ring
  simp only [key]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_const_mul _ _
  · intro i _
    exact (integ_sm μ (hu i) hw).const_mul _

/- English proof (translation)
Unfold `ip`. Rewrite using `[← integral_mul_left_eq_self (fun y => star (u (a⁻¹ * y)) * w y) a]`. Simplify using `only [inv_mul_cancel_left]`.
-/
theorem ip_left (a : H) (u w : H → ℂ) : ip μ u (fun y => w (a * y)) = ip μ (fun y => u (a⁻¹ * y)) w := by
  unfold ip
  rw [← integral_mul_left_eq_self (fun y => star (u (a⁻¹ * y)) * w y) a]
  simp only [inv_mul_cancel_left]

/- English proof (translation)
Establish `h1 : ∀ y, star (ψ y) * ψ y = ((‖ψ y‖ ^ 2 : ℝ) : ℂ)`. Introduce `y`. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : ip μ ψ ψ = ((∫ y, ‖ψ y‖ ^ 2 ∂μ : ℝ) : ℂ)`. Unfold `ip`. Simplify using `only [h1]`. Conclude with `integral_ofReal`. Rewrite `h` using `[h2, Complex.ofReal_eq_zero]`.

Establish `hc2 : Continuous (fun y => ‖ψ y‖ ^ 2)` using `(continuous_norm.comp hψ).pow 2`. Establish `hae` using `(integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _) (hc2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp h`. Establish `heq` using `(Continuous.ae_eq_iff_eq μ hc2 continuous_zero).mp hae`. Use function extensionality and compare the values at `y`. Simplify using `using congrFun heq y`.
-/
theorem norm_sq_zero {ψ : H → ℂ} (hψ : Continuous ψ) (h : ip μ ψ ψ = 0) : ψ = 0 := by
  have h1 : ∀ y, star (ψ y) * ψ y = ((‖ψ y‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have h2 : ip μ ψ ψ = ((∫ y, ‖ψ y‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    unfold ip
    simp only [h1]
    exact integral_ofReal
  rw [h2, Complex.ofReal_eq_zero] at h
  have hc2 : Continuous (fun y => ‖ψ y‖ ^ 2) := (continuous_norm.comp hψ).pow 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _)
    (hc2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp h
  have heq := (Continuous.ae_eq_iff_eq μ hc2 continuous_zero).mp hae
  funext y
  simpa using congrFun heq y

variable {N : ℕ} (φ : Fin N → H → ℂ)

def gram : Matrix (Fin N) (Fin N) ℂ := fun i j => ip μ (φ i) (φ j)

/- English proof (translation)
Introduce `hdet`. Take `⟨v, hv, hGv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Establish `hψc : Continuous (fun x => ∑ l, v l * φ l x)` using `continuous_finset_sum _ fun l _ => continuous_const.mul (hc l)`. Establish `hip : ip μ (fun x => ∑ l, v l * φ l x) (fun x => ∑ l, v l * φ l x) = 0`. Rewrite using `[ip_sum_left μ Finset.univ hψc v φ hc]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ip_sum_right μ Finset.univ (hc i) v φ hc]`. Establish `hi` using `congrFun hGv i`. Simplify using `only [Matrix.mulVec, dotProduct, gram, Pi.zero_apply] at hi`. Rewrite using `[show ∑ l, v l * ip μ (φ i) (φ l) = ∑ l, ip μ (φ i) (φ l) * v l from Finset.sum_congr rfl fun l _ => mul_comm _ _, hi, mul_zero]`.

Establish `h0` using `norm_sq_zero μ hψc hip`. Apply `hv` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `Fintype.linearIndependent_iff.mp hli v ?_ i` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Simplify `congrFun h0 x` using `[Finset.sum_apply]`.
-/
theorem gram_det (hc : ∀ i, Continuous (φ i)) (hli : LinearIndependent ℂ φ) : (gram μ φ).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hψc : Continuous (fun x => ∑ l, v l * φ l x) :=
    continuous_finset_sum _ fun l _ => continuous_const.mul (hc l)
  have hip : ip μ (fun x => ∑ l, v l * φ l x) (fun x => ∑ l, v l * φ l x) = 0 := by
    rw [ip_sum_left μ Finset.univ hψc v φ hc]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [ip_sum_right μ Finset.univ (hc i) v φ hc]
    have hi := congrFun hGv i
    simp only [Matrix.mulVec, dotProduct, gram, Pi.zero_apply] at hi
    rw [show ∑ l, v l * ip μ (φ i) (φ l) = ∑ l, ip μ (φ i) (φ l) * v l from
      Finset.sum_congr rfl fun l _ => mul_comm _ _, hi, mul_zero]
  have h0 := norm_sq_zero μ hψc hip
  apply hv
  funext i
  refine Fintype.linearIndependent_iff.mp hli v ?_ i
  funext x
  simpa [Finset.sum_apply] using congrFun h0 x

def coef (g : H → ℂ) : Fin N → ℂ := (gram μ φ)⁻¹ *ᵥ fun j => ip μ (φ j) g

def proj (g : H → ℂ) : H → ℂ := fun x => ∑ i, coef μ φ g i * φ i x

/- English proof (translation)
Establish `hG : IsUnit (gram μ φ).det` using `isUnit_iff_ne_zero.mpr (gram_det μ φ hc hli)`. Establish `hw : (fun j => ip μ (φ j) (fun x => ∑ l, d l * φ l x)) = gram μ φ *ᵥ d`. Use function extensionality and compare the values at `j`. Rewrite using `[ip_sum_right μ Finset.univ (hc j) d φ hc]`. Simplify using `only [Matrix.mulVec, dotProduct, gram]`.

Conclude with `Finset.sum_congr rfl fun l _ => mul_comm _ _`. Unfold `coef`. Rewrite using `[hw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec]`.
-/
theorem coef_comb (hc : ∀ i, Continuous (φ i)) (hli : LinearIndependent ℂ φ) (d : Fin N → ℂ) :
    coef μ φ (fun x => ∑ l, d l * φ l x) = d := by
  have hG : IsUnit (gram μ φ).det := isUnit_iff_ne_zero.mpr (gram_det μ φ hc hli)
  have hw : (fun j => ip μ (φ j) (fun x => ∑ l, d l * φ l x)) = gram μ φ *ᵥ d := by
    funext j
    rw [ip_sum_right μ Finset.univ (hc j) d φ hc]
    simp only [Matrix.mulVec, dotProduct, gram]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  unfold coef
  rw [hw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec]

/- English proof (translation)
Unfold `proj`. Rewrite using `[coef_comb μ φ hc hli d]`.
-/
theorem proj_comb (hc : ∀ i, Continuous (φ i)) (hli : LinearIndependent ℂ φ) (d : Fin N → ℂ) :
    proj μ φ (fun x => ∑ l, d l * φ l x) = fun x => ∑ l, d l * φ l x := by
  unfold proj; rw [coef_comb μ φ hc hli d]

/- English proof (translation)
Establish `hG : IsUnit (gram μ φ).det` using `isUnit_iff_ne_zero.mpr (gram_det μ φ hc hli)`. Establish `hpc : Continuous (proj μ φ g)` using `continuous_finset_sum _ fun i _ => continuous_const.mul (hc i)`. Establish `key : gram μ φ *ᵥ coef μ φ g = fun j => ip μ (φ j) g`. Unfold `coef`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec]`.

Establish `hk` using `congrFun key k`. Simplify using `only [Matrix.mulVec, dotProduct, gram] at hk`. Rewrite using `[ip_sub μ (hc k) hg hpc]`. Establish `hp : ip μ (φ k) (proj μ φ g) = ∑ i, coef μ φ g i * ip μ (φ k) (φ i)`. Unfold `proj`.

Conclude with `ip_sum_right μ Finset.univ (hc k) _ φ hc`. Rewrite using `[hp, ← hk]`. Rewrite using `[show ∑ i, coef μ φ g i * ip μ (φ k) (φ i) = ∑ i, ip μ (φ k) (φ i) * coef μ φ g i from Finset.sum_congr rfl fun i _ => mul_comm _ _]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ip_resid (hc : ∀ i, Continuous (φ i)) (hli : LinearIndependent ℂ φ) {g : H → ℂ} (hg : Continuous g) (k : Fin N) :
    ip μ (φ k) (fun x => g x - proj μ φ g x) = 0 := by
  have hG : IsUnit (gram μ φ).det := isUnit_iff_ne_zero.mpr (gram_det μ φ hc hli)
  have hpc : Continuous (proj μ φ g) := continuous_finset_sum _ fun i _ => continuous_const.mul (hc i)
  have key : gram μ φ *ᵥ coef μ φ g = fun j => ip μ (φ j) g := by
    unfold coef
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec]
  have hk := congrFun key k
  simp only [Matrix.mulVec, dotProduct, gram] at hk
  rw [ip_sub μ (hc k) hg hpc]
  have hp : ip μ (φ k) (proj μ φ g) = ∑ i, coef μ φ g i * ip μ (φ k) (φ i) := by
    unfold proj
    exact ip_sum_right μ Finset.univ (hc k) _ φ hc
  rw [hp, ← hk]
  rw [show ∑ i, coef μ φ g i * ip μ (φ k) (φ i) = ∑ i, ip μ (φ k) (φ i) * coef μ φ g i from
    Finset.sum_congr rfl fun i _ => mul_comm _ _]
  ring

/- English proof (translation)
Establish `hw : (fun j => ip μ (φ j) (fun x => g x + g' x)) = (fun j => ip μ (φ j) g) + (fun j => ip μ (φ j) g')`. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.add_apply]`. Conclude with `ip_add μ (hc j) hg hg'`. Establish `hcoef : coef μ φ (fun x => g x + g' x) = coef μ φ g + coef μ φ g'`.

Unfold `coef`. Rewrite using `[hw, Matrix.mulVec_add]`. Use function extensionality and compare the values at `x`. Simplify using `only [proj, hcoef, Pi.add_apply, add_mul, Finset.sum_add_distrib]`.
-/
theorem proj_add (hc : ∀ i, Continuous (φ i)) {g g' : H → ℂ} (hg : Continuous g) (hg' : Continuous g') :
    proj μ φ (fun x => g x + g' x) = fun x => proj μ φ g x + proj μ φ g' x := by
  have hw : (fun j => ip μ (φ j) (fun x => g x + g' x)) =
      (fun j => ip μ (φ j) g) + (fun j => ip μ (φ j) g') := by
    funext j
    simp only [Pi.add_apply]
    exact ip_add μ (hc j) hg hg'
  have hcoef : coef μ φ (fun x => g x + g' x) = coef μ φ g + coef μ φ g' := by
    unfold coef
    rw [hw, Matrix.mulVec_add]
  funext x
  simp only [proj, hcoef, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Establish `hpc : Continuous (proj μ φ g)` using `continuous_finset_sum _ fun i _ => continuous_const.mul (hc i)`. Establish `hcomb : ∃ e : Fin N → ℂ, (fun x => proj μ φ g (a * x)) = fun x => ∑ l, e l * φ l x` using `by choose d hd using fun i => hst i a`. Use `⟨fun l => ∑ i, coef μ φ g i * d i l, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Establish `hx : ∀ i, φ i (a * x) = ∑ l, d i l * φ l x` using `fun i => congrFun (hd i) x`.

Simplify using `only [proj, hx, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Take `⟨e, he⟩` from `hcomb`.

Establish `hgp : Continuous (fun x => g x - proj μ φ g x)` using `hg.sub hpc`. Establish `hr : ∀ k, ip μ (φ k) (fun x => g (a * x) - proj μ φ g (a * x)) = 0`. Introduce `k`. Establish `hl` using `ip_left μ a (φ k) (fun x => g x - proj μ φ g x)`. Rewrite using `[hl]`.

Take `⟨d, hd⟩` from `hst k a⁻¹`. Rewrite using `[hd, ip_sum_left μ Finset.univ hgp d φ hc]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ip_resid μ φ hc hli hg i, mul_zero]`. Establish `hrc : Continuous (fun x => g (a * x) - proj μ φ g (a * x))` using `(hg.comp (continuous_mul_left a)).sub (hpc.comp (continuous_mul_left a))`.

Establish `hcoef0 : coef μ φ (fun x => g (a * x) - proj μ φ g (a * x)) = 0`. Unfold `coef`. Establish `hz : (fun j => ip μ (φ j) (fun x => g (a * x) - proj μ φ g (a * x))) = 0` using `funext hr`. Rewrite using `[hz, Matrix.mulVec_zero]`. Establish `hproj0 : proj μ φ (fun x => g (a * x) - proj μ φ g (a * x)) = fun _ => 0`.

Use function extensionality and compare the values at `x`. Express the relevant statement in the definitionally equal form `∑ i, coef μ φ (fun x => g (a * x) - proj μ φ g (a * x)) i * φ i x = 0`. Rewrite using `[hcoef0]`. Simplify using the standard rewrite rules. Establish `hpp : proj μ φ (fun x => proj μ φ g (a * x)) = fun x => proj μ φ g (a * x)`.

Rewrite using `[he]`. Conclude with `proj_comb μ φ hc hli e`. Establish `hsplit : (fun x => g (a * x)) = fun x => proj μ φ g (a * x) + (g (a * x) - proj μ φ g (a * x))`. Use function extensionality and compare the values at `x`. Expand and normalize the polynomial expressions, which then agree.

Establish `hadd` using `proj_add μ φ hc (hpc.comp (continuous_mul_left a)) hrc`. Simplify using `only [Function.comp_def] at hadd`. Rewrite using `[hsplit, hadd, hpp, hproj0]`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.
-/
theorem proj_left (hc : ∀ i, Continuous (φ i)) (hli : LinearIndependent ℂ φ)
    (hst : ∀ (i : Fin N) (a : H), ∃ d : Fin N → ℂ, (fun x => φ i (a * x)) = fun x => ∑ l, d l * φ l x)
    {g : H → ℂ} (hg : Continuous g) (a : H) :
    proj μ φ (fun x => g (a * x)) = fun x => proj μ φ g (a * x) := by
  have hpc : Continuous (proj μ φ g) := continuous_finset_sum _ fun i _ => continuous_const.mul (hc i)
  have hcomb : ∃ e : Fin N → ℂ, (fun x => proj μ φ g (a * x)) = fun x => ∑ l, e l * φ l x := by
    choose d hd using fun i => hst i a
    refine ⟨fun l => ∑ i, coef μ φ g i * d i l, ?_⟩
    funext x
    have hx : ∀ i, φ i (a * x) = ∑ l, d i l * φ l x := fun i => congrFun (hd i) x
    simp only [proj, hx, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  obtain ⟨e, he⟩ := hcomb
  have hgp : Continuous (fun x => g x - proj μ φ g x) := hg.sub hpc
  have hr : ∀ k, ip μ (φ k) (fun x => g (a * x) - proj μ φ g (a * x)) = 0 := by
    intro k
    have hl := ip_left μ a (φ k) (fun x => g x - proj μ φ g x)
    rw [hl]
    obtain ⟨d, hd⟩ := hst k a⁻¹
    rw [hd, ip_sum_left μ Finset.univ hgp d φ hc]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [ip_resid μ φ hc hli hg i, mul_zero]
  have hrc : Continuous (fun x => g (a * x) - proj μ φ g (a * x)) :=
    (hg.comp (continuous_mul_left a)).sub (hpc.comp (continuous_mul_left a))
  have hcoef0 : coef μ φ (fun x => g (a * x) - proj μ φ g (a * x)) = 0 := by
    unfold coef
    have hz : (fun j => ip μ (φ j) (fun x => g (a * x) - proj μ φ g (a * x))) = 0 := funext hr
    rw [hz, Matrix.mulVec_zero]
  have hproj0 : proj μ φ (fun x => g (a * x) - proj μ φ g (a * x)) = fun _ => 0 := by
    funext x
    change ∑ i, coef μ φ (fun x => g (a * x) - proj μ φ g (a * x)) i * φ i x = 0
    rw [hcoef0]
    simp
  have hpp : proj μ φ (fun x => proj μ φ g (a * x)) = fun x => proj μ φ g (a * x) := by
    rw [he]
    exact proj_comb μ φ hc hli e
  have hsplit : (fun x => g (a * x)) = fun x => proj μ φ g (a * x) + (g (a * x) - proj μ φ g (a * x)) := by
    funext x
    ring
  have hadd := proj_add μ φ hc (hpc.comp (continuous_mul_left a)) hrc
  simp only [Function.comp_def] at hadd
  rw [hsplit, hadd, hpp, hproj0]
  funext x
  simp

end RK

open RK in
/- English proof (translation)
Introduce `H _ _ _ _ _ _ _ μ _ V hfin hcont hinv`. Set `b` to `Module.finBasis ℂ V`. Set `φ : Fin (Module.finrank ℂ V) → H → ℂ` to `fun i => (b i : H → ℂ)`. Establish `hc : ∀ i, Continuous (φ i)` using `fun i => hcont _ (b i).2`. Establish `hli : LinearIndependent ℂ φ` using `b.linearIndependent.map' V.subtype V.ker_subtype`.

Establish `hmem : ∀ ψ ∈ V, ∃ d : Fin (Module.finrank ℂ V) → ℂ, ψ = fun x => ∑ l, d l * φ l x`. Introduce `ψ hψ`. Use `⟨b.repr ⟨ψ, hψ⟩, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun v : V => (v : H → ℂ)) (b.sum_repr ⟨ψ, hψ⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h`.

Use function extensionality and compare the values at `x`. Establish `hx` using `congrFun h x`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx`. Conclude with `hx.symm`. Establish `hst : ∀ (i : Fin (Module.finrank ℂ V)) (a : H), ∃ d : Fin (Module.finrank ℂ V) → ℂ, (fun x => φ i (a * x)) = fun x => ∑ l, d l * φ l x` using `fun i a => hmem _ (hinv _ (b i).2 a)`.

Establish `hcombV : ∀ c : Fin (Module.finrank ℂ V) → ℂ, (fun x => ∑ l, c l * φ l x) ∈ V`. Introduce `c`. Establish `hfun : (fun x => ∑ l, c l * φ l x) = ∑ l, c l • φ l`. Use function extensionality and compare the values at `x`. Simplify using `[Finset.sum_apply]`.

Rewrite using `[hfun]`. Conclude with `V.sum_mem fun l _ => V.smul_mem _ (b l).2`. Establish `key : ∀ f : H → ℂ, Continuous f → ∀ x, ∫ v, star (∑ j, star (∑ i, φ i 1 * (gram μ φ)⁻¹ i j) * φ j v) * f (x * v) ∂μ = proj μ φ f x`. Introduce `f hf x`. Establish `hfx : Continuous (fun v => f (x * v))` using `hf.comp (continuous_mul_left x)`.

Establish `h1 : ∫ v, star (∑ j, star (∑ i, φ i 1 * (gram μ φ)⁻¹ i j) * φ j v) * f (x * v) ∂μ = ip μ (fun v => ∑ j, star (∑ i, φ i 1 * (gram μ φ)⁻¹ i j) * φ j v) (fun v => f (x * v))` using `rfl`. Rewrite using `[h1, ip_sum_left μ Finset.univ hfx _ φ hc]`. Establish `h3` using `congrFun (proj_left μ φ hc hli hst hf x) 1`. Simplify using `only [mul_one] at h3`. Rewrite using `[← h3]`.

Simplify using `only [proj, coef, Matrix.mulVec, dotProduct, star_star, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `⟨fun v => star (∑ j, star (∑ i, φ i 1 * (gram μ φ)⁻¹ i j) * φ j v), ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `continuous_star.comp (continuous_finset_sum _ fun j _ => continuous_const.mul (hc j))`. Introduce `f hf`. Establish `hfun : (fun x => ∫ v, star (∑ j, star (∑ i, φ i 1 * (gram μ φ)⁻¹ i j) * φ j v) * f (x * v) ∂μ) = proj μ φ f` using `funext (key f hf)`. Rewrite using `[hfun]`. Conclude with `hcombV (coef μ φ f)`.

Introduce `ψ hψ x`. Take `⟨d, hd⟩` from `hmem ψ hψ`. Rewrite using `[key ψ (hcont ψ hψ) x, hd, proj_comb μ φ hc hli d]`.
-/
theorem repKer : RepKer := by
  intro H _ _ _ _ _ _ _ μ _ V hfin hcont hinv
  let b := Module.finBasis ℂ V
  let φ : Fin (Module.finrank ℂ V) → H → ℂ := fun i => (b i : H → ℂ)
  have hc : ∀ i, Continuous (φ i) := fun i => hcont _ (b i).2
  have hli : LinearIndependent ℂ φ := b.linearIndependent.map' V.subtype V.ker_subtype
  have hmem : ∀ ψ ∈ V, ∃ d : Fin (Module.finrank ℂ V) → ℂ, ψ = fun x => ∑ l, d l * φ l x := by
    intro ψ hψ
    refine ⟨b.repr ⟨ψ, hψ⟩, ?_⟩
    have h := congrArg (fun v : V => (v : H → ℂ)) (b.sum_repr ⟨ψ, hψ⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    funext x
    have hx := congrFun h x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx
    exact hx.symm
  have hst : ∀ (i : Fin (Module.finrank ℂ V)) (a : H), ∃ d : Fin (Module.finrank ℂ V) → ℂ,
      (fun x => φ i (a * x)) = fun x => ∑ l, d l * φ l x :=
    fun i a => hmem _ (hinv _ (b i).2 a)
  have hcombV : ∀ c : Fin (Module.finrank ℂ V) → ℂ, (fun x => ∑ l, c l * φ l x) ∈ V := by
    intro c
    have hfun : (fun x => ∑ l, c l * φ l x) = ∑ l, c l • φ l := by
      funext x
      simp [Finset.sum_apply]
    rw [hfun]
    exact V.sum_mem fun l _ => V.smul_mem _ (b l).2
  have key : ∀ f : H → ℂ, Continuous f → ∀ x,
      ∫ v, star (∑ j, star (∑ i, φ i 1 * (gram μ φ)⁻¹ i j) * φ j v) * f (x * v) ∂μ = proj μ φ f x := by
    intro f hf x
    have hfx : Continuous (fun v => f (x * v)) := hf.comp (continuous_mul_left x)
    have h1 : ∫ v, star (∑ j, star (∑ i, φ i 1 * (gram μ φ)⁻¹ i j) * φ j v) * f (x * v) ∂μ =
        ip μ (fun v => ∑ j, star (∑ i, φ i 1 * (gram μ φ)⁻¹ i j) * φ j v) (fun v => f (x * v)) := rfl
    rw [h1, ip_sum_left μ Finset.univ hfx _ φ hc]
    have h3 := congrFun (proj_left μ φ hc hli hst hf x) 1
    simp only [mul_one] at h3
    rw [← h3]
    simp only [proj, coef, Matrix.mulVec, dotProduct, star_star, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨fun v => star (∑ j, star (∑ i, φ i 1 * (gram μ φ)⁻¹ i j) * φ j v), ?_, ?_, ?_⟩
  · exact continuous_star.comp (continuous_finset_sum _ fun j _ => continuous_const.mul (hc j))
  · intro f hf
    have hfun : (fun x => ∫ v, star (∑ j, star (∑ i, φ i 1 * (gram μ φ)⁻¹ i j) * φ j v) * f (x * v) ∂μ) =
        proj μ φ f := funext (key f hf)
    rw [hfun]
    exact hcombV (coef μ φ f)
  · intro ψ hψ x
    obtain ⟨d, hd⟩ := hmem ψ hψ
    rw [key ψ (hcont ψ hψ) x, hd, proj_comb μ φ hc hli d]

end PositivityTheory.Rg.Sw.AbsSt.Proj
