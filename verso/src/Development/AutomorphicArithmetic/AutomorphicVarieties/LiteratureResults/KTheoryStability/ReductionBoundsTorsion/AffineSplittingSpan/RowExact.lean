import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.CoreDefs

noncomputable section

open Finset

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

variable {P Q : Type} [Group P] [Group Q]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem dh_dh {a b : ℕ} (F : Bi P Q (a + 1) b) : dh (dh F) = 0 := by
  funext x y
  exact congrFun (dc_dc (fun x' => F x' y)) x

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem dv_dv {a b : ℕ} (F : Bi P Q a (b + 1)) : dv (dv F) = 0 := by
  funext x y
  exact congrFun (dc_dc (F x)) y

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dh_dv {a b : ℕ} (F : Bi P Q (a + 1) (b + 1)) : dh (dv F) = dv (dh F) := by
  funext x y
  simp only [dh, dv, dc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem dh_add {a b : ℕ} (F G : Bi P Q (a + 1) b) : dh (F + G) = dh F + dh G := by
  funext x y; simp only [dh, Pi.add_apply, dc, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem dh_sub {a b : ℕ} (F G : Bi P Q (a + 1) b) : dh (F - G) = dh F - dh G := by
  funext x y
  exact congrFun (dc_sub (fun x' => F x' y) (fun x' => G x' y)) x

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem dh_smul {a b : ℕ} (r : ℝ) (F : Bi P Q (a + 1) b) : dh (r • F) = r • dh F := by
  funext x y
  exact congrFun (dc_smul r (fun x' => F x' y)) x

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem dv_sub {a b : ℕ} (F G : Bi P Q a (b + 1)) : dv (F - G) = dv F - dv G := by
  funext x y
  exact congrFun (dc_sub (F x) (G x)) y

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem dv_smul {a b : ℕ} (r : ℝ) (F : Bi P Q a (b + 1)) : dv (r • F) = r • dv F := by
  funext x y
  exact congrFun (dc_smul r (F x)) y

section Inv

variable (pr : P →* Q)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem PInv.add {a b : ℕ} {F G : Bi P Q a b} (hF : PInv pr F) (hG : PInv pr G) : PInv pr (F + G) := by
  intro g x y
  show F _ _ + G _ _ = F x y + G x y
  rw [hF g x y, hG g x y]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem PInv.sub {a b : ℕ} {F G : Bi P Q a b} (hF : PInv pr F) (hG : PInv pr G) : PInv pr (F - G) := by
  intro g x y
  show F _ _ - G _ _ = F x y - G x y
  rw [hF g x y, hG g x y]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem PInv.smul {a b : ℕ} (r : ℝ) {F : Bi P Q a b} (hF : PInv pr F) : PInv pr (r • F) := by
  intro g x y
  show r * F _ _ = r * F x y
  rw [hF g x y]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Both sides reduce to the same expression.
-/
theorem PInv.zero {a b : ℕ} : PInv pr (0 : Bi P Q a b) := fun _ _ _ => rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem PInv.dh {a b : ℕ} {F : Bi P Q (a + 1) b} (hF : PInv pr F) : PInv pr (dh F) := by
  intro g x y
  unfold PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas.dh PositivityTheory.KB.SplitAffineSpectral.dc
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact hF g (fun j => x (i.succAbove j)) y

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem PInv.dv {a b : ℕ} {F : Bi P Q a (b + 1)} (hF : PInv pr F) : PInv pr (dv F) := by
  intro g x y
  unfold PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas.dv PositivityTheory.KB.SplitAffineSpectral.dc
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact hF g x (fun j => y (i.succAbove j))

end Inv

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem cons_mul {Z : Type} [Mul Z] {n : ℕ} (g a : Z) (x : Fin n → Z) :
    (fun i => g * (Fin.cons a x : Fin (n + 1) → Z) i) = Fin.cons (g * a) (fun i => g * x i) := by
  funext i; refine Fin.cases ?_ (fun k => ?_) i <;> simp

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

A detailed English derivation is pending.
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
