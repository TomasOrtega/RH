import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.CoreDefs

noncomputable section

open Finset

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

variable {P Q : Type} [Group P] [Group Q]

/- English proof (translation)
Use function extensionality and compare the values at `x y`. Conclude with `congrFun (dc_dc (fun x' => F x' y)) x`.
-/
theorem dh_dh {a b : ℕ} (F : Bi P Q (a + 1) b) : dh (dh F) = 0 := by
  funext x y
  exact congrFun (dc_dc (fun x' => F x' y)) x

/- English proof (translation)
Use function extensionality and compare the values at `x y`. Conclude with `congrFun (dc_dc (F x)) y`.
-/
theorem dv_dv {a b : ℕ} (F : Bi P Q a (b + 1)) : dv (dv F) = 0 := by
  funext x y
  exact congrFun (dc_dc (F x)) y

/- English proof (translation)
Use function extensionality and compare the values at `x y`. Simplify using `only [dh, dv, dc, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dh_dv {a b : ℕ} (F : Bi P Q (a + 1) (b + 1)) : dh (dv F) = dv (dh F) := by
  funext x y
  simp only [dh, dv, dc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Use function extensionality and compare the values at `x y`. Simplify using `only [dh, Pi.add_apply, dc, mul_add, Finset.sum_add_distrib]`.
-/
theorem dh_add {a b : ℕ} (F G : Bi P Q (a + 1) b) : dh (F + G) = dh F + dh G := by
  funext x y; simp only [dh, Pi.add_apply, dc, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Use function extensionality and compare the values at `x y`. Conclude with `congrFun (dc_sub (fun x' => F x' y) (fun x' => G x' y)) x`.
-/
theorem dh_sub {a b : ℕ} (F G : Bi P Q (a + 1) b) : dh (F - G) = dh F - dh G := by
  funext x y
  exact congrFun (dc_sub (fun x' => F x' y) (fun x' => G x' y)) x

/- English proof (translation)
Use function extensionality and compare the values at `x y`. Conclude with `congrFun (dc_smul r (fun x' => F x' y)) x`.
-/
theorem dh_smul {a b : ℕ} (r : ℝ) (F : Bi P Q (a + 1) b) : dh (r • F) = r • dh F := by
  funext x y
  exact congrFun (dc_smul r (fun x' => F x' y)) x

/- English proof (translation)
Use function extensionality and compare the values at `x y`. Conclude with `congrFun (dc_sub (F x) (G x)) y`.
-/
theorem dv_sub {a b : ℕ} (F G : Bi P Q a (b + 1)) : dv (F - G) = dv F - dv G := by
  funext x y
  exact congrFun (dc_sub (F x) (G x)) y

/- English proof (translation)
Use function extensionality and compare the values at `x y`. Conclude with `congrFun (dc_smul r (F x)) y`.
-/
theorem dv_smul {a b : ℕ} (r : ℝ) (F : Bi P Q a (b + 1)) : dv (r • F) = r • dv F := by
  funext x y
  exact congrFun (dc_smul r (F x)) y

section Inv

variable (pr : P →* Q)

/- English proof (translation)
Introduce `g x y`. Use `show F _ _ + G _ _ = F x y + G x y`. Rewrite using `[hF g x y, hG g x y]`.
-/
theorem PInv.add {a b : ℕ} {F G : Bi P Q a b} (hF : PInv pr F) (hG : PInv pr G) : PInv pr (F + G) := by
  intro g x y
  show F _ _ + G _ _ = F x y + G x y
  rw [hF g x y, hG g x y]

/- English proof (translation)
Introduce `g x y`. Use `show F _ _ - G _ _ = F x y - G x y`. Rewrite using `[hF g x y, hG g x y]`.
-/
theorem PInv.sub {a b : ℕ} {F G : Bi P Q a b} (hF : PInv pr F) (hG : PInv pr G) : PInv pr (F - G) := by
  intro g x y
  show F _ _ - G _ _ = F x y - G x y
  rw [hF g x y, hG g x y]

/- English proof (translation)
Introduce `g x y`. Use `show r * F _ _ = r * F x y`. Rewrite using `[hF g x y]`.
-/
theorem PInv.smul {a b : ℕ} (r : ℝ) {F : Bi P Q a b} (hF : PInv pr F) : PInv pr (r • F) := by
  intro g x y
  show r * F _ _ = r * F x y
  rw [hF g x y]

/- English proof (translation)
Introduce `_ _ _` and use `rfl`.
-/
theorem PInv.zero {a b : ℕ} : PInv pr (0 : Bi P Q a b) := fun _ _ _ => rfl

/- English proof (translation)
Introduce `g x y`. Unfold `PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas.dh PositivityTheory.KB.SplitAffineSpectral.dc`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `hF g (fun j => x (i.succAbove j)) y`.
-/
theorem PInv.dh {a b : ℕ} {F : Bi P Q (a + 1) b} (hF : PInv pr F) : PInv pr (dh F) := by
  intro g x y
  unfold PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas.dh PositivityTheory.KB.SplitAffineSpectral.dc
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact hF g (fun j => x (i.succAbove j)) y

/- English proof (translation)
Introduce `g x y`. Unfold `PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas.dv PositivityTheory.KB.SplitAffineSpectral.dc`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `hF g x (fun j => y (i.succAbove j))`.
-/
theorem PInv.dv {a b : ℕ} {F : Bi P Q a (b + 1)} (hF : PInv pr F) : PInv pr (dv F) := by
  intro g x y
  unfold PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas.dv PositivityTheory.KB.SplitAffineSpectral.dc
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact hF g x (fun j => y (i.succAbove j))

end Inv

/- English proof (translation)
Apply the tactic sequence `funext i; refine Fin.cases ?_ (fun k => ?_) i <;> simp`.
-/
theorem cons_mul {Z : Type} [Mul Z] {n : ℕ} (g a : Z) (x : Fin n → Z) :
    (fun i => g * (Fin.cons a x : Fin (n + 1) → Z) i) = Fin.cons (g * a) (fun i => g * x i) := by
  funext i; refine Fin.cases ?_ (fun k => ?_) i <;> simp

/- English proof (translation)
Establish `hcs : ∀ (c : Q) (u : Fin (a + 2) → Q) (k : Fin (a + 2)), (fun j => (Fin.cons c u : Fin (a + 3) → Q) (k.succ.succAbove j)) = Fin.cons c (fun j => u (k.succAbove j))`. Introduce `c u k`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `cases j using Fin.cases <;> simp [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]`. Use `⟨fun x y => F (Fin.cons (pr (y 0)) x) y, ?_, ?_⟩` and prove the remaining obligations.

Introduce `g x y show F (Fin.cons (pr (g * y 0)) (fun i => pr g * x i)) (fun j => g * y j) = F (Fin.cons (pr (y 0)) x) y`. Rewrite using `[map_mul, ← cons_mul]`. Conclude with `hF g _ y`. Use function extensionality and compare the values at `x y`. Establish `h0` using `congrFun (congrFun h (Fin.cons (pr (y 0)) x)) y`.

Simplify using `only [dh, dc] at h0`. Rewrite `h0` using `[Fin.sum_univ_succ]`. Simplify using `only [hcs] at h0`. Simplify using `only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.cons_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_mul, Finset.sum_neg_distrib] at h0`. Use `show F x y = ∑ i : Fin (a + 2), (-1) ^ (i : ℕ) * F (Fin.cons (pr (y 0)) (fun j => x (i.succAbove j))) y`.

Establish `h1 : F x y + -∑ i : Fin (a + 2), (-1) ^ (i : ℕ) * F (Fin.cons (pr (y 0)) (fun j => x (i.succAbove j))) y = 0` using `h0`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem row_exact (pr : P →* Q) {a b : ℕ} (F : Bi P Q (a + 2) (b + 1)) (hF : PInv pr F) (h : dh F = 0) :
    ∃ G : Bi P Q (a + 1) (b + 1), PInv pr G ∧ F = dh G := by
  have hcs : ∀ (c : Q) (u : Fin (a + 2) → Q) (k : Fin (a + 2)),
      (fun j => (Fin.cons c u : Fin (a + 3) → Q) (k.succ.succAbove j)) =
        Fin.cons c (fun j => u (k.succAbove j)) := by
    intro c u k
    funext j
    cases j using Fin.cases <;> simp [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]
  refine ⟨fun x y => F (Fin.cons (pr (y 0)) x) y, ?_, ?_⟩
  · intro g x y
    show F (Fin.cons (pr (g * y 0)) (fun i => pr g * x i)) (fun j => g * y j) = F (Fin.cons (pr (y 0)) x) y
    rw [map_mul, ← cons_mul]
    exact hF g _ y
  · funext x y
    have h0 := congrFun (congrFun h (Fin.cons (pr (y 0)) x)) y
    simp only [dh, dc] at h0
    rw [Fin.sum_univ_succ] at h0
    simp only [hcs] at h0
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.cons_succ, Fin.val_succ,
      pow_succ, mul_neg_one, neg_mul, Finset.sum_neg_distrib] at h0
    show F x y = ∑ i : Fin (a + 2), (-1) ^ (i : ℕ) * F (Fin.cons (pr (y 0)) (fun j => x (i.succAbove j))) y
    have h1 : F x y + -∑ i : Fin (a + 2), (-1) ^ (i : ℕ) * F (Fin.cons (pr (y 0)) (fun j => x (i.succAbove j))) y = 0 := h0
    linarith

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
