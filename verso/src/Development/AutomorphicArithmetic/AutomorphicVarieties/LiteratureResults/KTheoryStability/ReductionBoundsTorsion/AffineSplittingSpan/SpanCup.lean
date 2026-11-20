import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanPrism

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismSpan

open PositivityTheory.KB.SplitAffineSpectral

section General

variable {Y : Type}

/- English proof (translation)
The claim follows from `| 0, F => by funext y simp [dc, Fin.sum_univ_succ] have hCD : (fun j : Fin 1 => y (Fin.succAbove 1 (Fin.succAbove 1 j))) = fun j => y (Fin.succAbove 2 (Fin.succAbove 1 j)) := by funext j; fin_cases j; rfl rw [hCD] ring | m + 1, F => by funext y rw [← Fin.cons_self_tail y, dc_cons …`.
-/
theorem dc_dc : ∀ (m : ℕ) (F : (Fin (m + 1) → Y) → ℝ), dc (dc F) = 0
  | 0, F => by
    funext y
    simp [dc, Fin.sum_univ_succ]
    have hCD : (fun j : Fin 1 => y (Fin.succAbove 1 (Fin.succAbove 1 j))) =
        fun j => y (Fin.succAbove 2 (Fin.succAbove 1 j)) := by
      funext j; fin_cases j; rfl
    rw [hCD]
    ring
  | m + 1, F => by
    funext y
    rw [← Fin.cons_self_tail y, dc_cons]
    have e : (fun w' => dc F (Fin.cons (y 0) w')) = F - dc (fun w' => F (Fin.cons (y 0) w')) := by
      funext w'; rw [dc_cons]; rfl
    rw [e, dc_sub, dc_dc m]
    simp

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `[dc, Finset.sum_neg_distrib]`.
-/
theorem dc_neg {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) : dc (-F) = -dc F := by
  funext y; simp [dc, Finset.sum_neg_distrib]

/- English proof (translation)
The claim follows from `| 0 => rfl | n + 1 => by funext y rw [prism_succ] have : (fun w : Fin (n + 1) → Y => (0 : (Fin (n + 2) → Y) → ℝ) (Fin.cons (y 0) w)) = 0 := rfl rw [this, prism_zero φ (n := n)] simp`.
-/
theorem prism_zero (φ : Y → Y) : ∀ {n : ℕ}, prism φ (0 : (Fin (n + 1) → Y) → ℝ) = 0
  | 0 => rfl
  | n + 1 => by
    funext y
    rw [prism_succ]
    have : (fun w : Fin (n + 1) → Y => (0 : (Fin (n + 2) → Y) → ℝ) (Fin.cons (y 0) w)) = 0 := rfl
    rw [this, prism_zero φ (n := n)]
    simp

end General

section Grp

variable {P : Type} [Group P]

/- English proof (translation)
Introduce `g hg y`. Simplify using `only [dc]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `congrArg _ (hF g hg _)`.
-/
theorem dc_inv (S : Set P) {m : ℕ} (F : (Fin (m + 1) → P) → ℝ) (hF : InvS S F) : InvS S (dc F) := by
  intro g hg y
  simp only [dc]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg _ (hF g hg _)

def tcup (l : Additive P →+ ℝ) {n : ℕ} (e : (Fin (n + 1) → P) → ℝ) : (Fin (n + 2) → P) → ℝ :=
  fun y => l (Additive.ofMul ((y 0)⁻¹ * y 1)) * e (Fin.tail y)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tail_eq' {α : Type} {k : ℕ} (q : Fin (k + 1) → α) : Fin.tail q = fun i => q i.succ := rfl

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `[dc, tcup, Fin.sum_univ_succ, tail_eq']`. Simplify using `only [pow_succ, mul_add, Finset.mul_sum, neg_add, ← Finset.sum_neg_distrib]`. Put the polynomial expressions in normal form.
-/
theorem dc_tcup (l : Additive P →+ ℝ) {n : ℕ} (e : (Fin (n + 1) → P) → ℝ) :
    dc (tcup l e) = -tcup l (dc e) := by
  funext y
  simp [dc, tcup, Fin.sum_univ_succ, tail_eq']
  simp only [pow_succ, mul_add, Finset.mul_sum, neg_add, ← Finset.sum_neg_distrib]
  ring_nf

/- English proof (translation)
Introduce `g hg y`. Simplify using `only [tcup]`. Rewrite using `[show (g * y 0)⁻¹ * (g * y 1) = (y 0)⁻¹ * y 1 by group]`. Use `congr 1`. Conclude with `he g hg (Fin.tail y)`.
-/
theorem tcup_inv (l : Additive P →+ ℝ) (S : Set P) {n : ℕ} (e : (Fin (n + 1) → P) → ℝ) (he : InvS S e) :
    InvS S (tcup l e) := by
  intro g hg y
  simp only [tcup]
  rw [show (g * y 0)⁻¹ * (g * y 1) = (y 0)⁻¹ * y 1 by group]
  congr 1
  exact he g hg (Fin.tail y)

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `[tcup, mul_add]`.
-/
theorem tcup_add (l : Additive P →+ ℝ) {n : ℕ} (e f : (Fin (n + 1) → P) → ℝ) :
    tcup l (e + f) = tcup l e + tcup l f := by
  funext y; simp [tcup, mul_add]

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `only [tcup, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tcup_sum (l : Additive P →+ ℝ) {n k : ℕ} (a : Fin k → ℝ) (F : Fin k → (Fin (n + 1) → P) → ℝ) :
    tcup l (∑ i, a i • F i) = ∑ i, a i • tcup l (F i) := by
  funext y
  simp only [tcup, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `[tcup, cupH, Fin.prod_univ_succ, Fin.tail]`.
-/
theorem tcup_cupH (l : Additive P →+ ℝ) {q : ℕ} (β : Fin q → (Additive P →+ ℝ)) :
    tcup l (cupH β) = cupH (Fin.cons l β) := by
  funext y
  simp [tcup, cupH, Fin.prod_univ_succ, Fin.tail]

end Grp

end PositivityTheory.KB.SplitAffineSpectral.PrismSpan

end
