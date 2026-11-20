import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.CoreSteps

noncomputable section

open Finset

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

/- English proof (translation)
Establish `hv` using `fc_val i l`. Establish `hl` using `l.isLt`. Simplify using `only [cat]`. Apply the tactic sequence `split_ifs with h1 h2 h3 h4 h5 h6 <;> first`. Consider the case `(congr 1; ext; simp only [fc_val, Fin.val_mk]; split_ifs <;> omega)`.

Consider the case `(exfalso; split_ifs at hv <;> omega)`. Consider the case `rfl`.
-/
theorem cat_fc_lo {Q : Type} [Group Q] {a c m : ℕ} (h : a + c = m) (x : Fin (a + 1) → Q) (z : Fin (c + 1) → Q)
    (i : ℕ) (hi : i < a + 1) (l : Fin (m + 1)) :
    cat x z (m + 2) (fc i l) = cat (fun l' : Fin a => x (fc i l')) z (m + 1) l := by
  have hv := fc_val i l
  have hl := l.isLt
  simp only [cat]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> first
    | (congr 1; ext; simp only [fc_val, Fin.val_mk]; split_ifs <;> omega)
    | (exfalso; split_ifs at hv <;> omega)
    | rfl

/- English proof (translation)
Establish `hv` using `fc_val (a + 1 + j) l`. Establish `hl` using `l.isLt`. Simplify using `only [cat]`. Apply the tactic sequence `split_ifs with h1 h2 h3 h4 h5 h6 <;> first`. Consider the case `(congr 1; ext; simp only [fc_val, Fin.val_mk]; split_ifs <;> omega)`.

Consider the case `(exfalso; split_ifs at hv <;> omega)`. Consider the case `rfl`.
-/
theorem cat_fc_hi {Q : Type} [Group Q] {a c m : ℕ} (h : a + c = m) (x : Fin (a + 1) → Q) (z : Fin (c + 1) → Q)
    (j : ℕ) (hj : j < c + 1) (l : Fin (m + 1)) :
    cat x z (m + 2) (fc (a + 1 + j) l) = cat x (fun l' : Fin c => z (fc j l')) (m + 1) l := by
  have hv := fc_val (a + 1 + j) l
  have hl := l.isLt
  simp only [cat]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> first
    | (congr 1; ext; simp only [fc_val, Fin.val_mk]; split_ifs <;> omega)
    | (exfalso; split_ifs at hv <;> omega)
    | rfl

/- English proof (translation)
Use `ext`. Rewrite using `[fc_val]`. Use `split_ifs with hl`. Rewrite using `[Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using hl)]`. Both sides reduce to the same expression.

Rewrite using `[Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]`. Both sides reduce to the same expression.
-/
private theorem fin_succAbove_eq_fc {n : ℕ} (i : Fin (n + 1)) (l : Fin n) : i.succAbove l = fc (i : ℕ) l := by
  ext
  rw [fc_val]
  split_ifs with hl
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using hl)]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]
    rfl

/- English proof (translation)
Simplify using `only [dc]`. Repeatedly rewrite using `[fin_succAbove_eq_fc]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun k => (-1 : ℝ) ^ k * F (fun l => cat x z (m + 2) (fc k l))) (m + 2), Fin.sum_univ_eq_sum_range (fun k => (-1 : ℝ) ^ k * F (cat (fun l => x (fc k l)) z (m + 1))) (a + 1), Fin.sum_univ_eq_sum_range (fun k => (-1 : ℝ) ^ k * F (cat x (fun l => z (fc k l …`. Use `congr 1`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations.

Use `congr 2`. Use function extensionality and compare the values at `l`. Conclude with `cat_fc_lo h x z k (Finset.mem_range.1 hk) l`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[pow_add, mul_assoc]`.

Use `congr 3`. Use function extensionality and compare the values at `l`. Conclude with `cat_fc_hi h x z j (Finset.mem_range.1 hj) l`.
-/
theorem dc_cat {Q : Type} [Group Q] {a c m : ℕ} (h : a + c = m) (F : (Fin (m + 1) → Q) → ℝ)
    (x : Fin (a + 1) → Q) (z : Fin (c + 1) → Q) :
    dc F (cat x z (m + 2)) =
      (∑ i : Fin (a + 1), (-1 : ℝ) ^ (i : ℕ) * F (cat (fun l => x (i.succAbove l)) z (m + 1))) +
        (-1 : ℝ) ^ (a + 1) *
          ∑ j : Fin (c + 1), (-1 : ℝ) ^ (j : ℕ) * F (cat x (fun l => z (j.succAbove l)) (m + 1)) := by
  simp only [dc]
  simp_rw [fin_succAbove_eq_fc]
  rw [Fin.sum_univ_eq_sum_range (fun k => (-1 : ℝ) ^ k * F (fun l => cat x z (m + 2) (fc k l))) (m + 2),
    Fin.sum_univ_eq_sum_range (fun k => (-1 : ℝ) ^ k * F (cat (fun l => x (fc k l)) z (m + 1))) (a + 1),
    Fin.sum_univ_eq_sum_range (fun k => (-1 : ℝ) ^ k * F (cat x (fun l => z (fc k l)) (m + 1))) (c + 1),
    show Finset.range (m + 2) = Finset.range ((a + 1) + (c + 1)) by congr 1; omega,
    Finset.sum_range_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    congr 2
    funext l
    exact cat_fc_lo h x z k (Finset.mem_range.1 hk) l
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [pow_add, mul_assoc]
    congr 3
    funext l
    exact cat_fc_hi h x z j (Finset.mem_range.1 hj) l

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[cat]`.
-/
theorem cat_zero_left {Q : Type} [Group Q] {n : ℕ} (x : Fin 0 → Q) (z : Fin n → Q) : cat x z n = z := by
  funext i
  simp [cat]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[cat]`.
-/
theorem cat_zero_right {Q : Type} [Group Q] {n : ℕ} (x : Fin n → Q) (z : Fin 0 → Q) : cat x z n = x := by
  funext i
  simp [cat]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `hi` using `i.isLt`. Simplify using `only [cat]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem cat_mul {Q : Type} [Group Q] {a c n : ℕ} (h : a + c = n) (g : Q) (x : Fin a → Q) (z : Fin c → Q) :
    cat (fun i => g * x i) (fun j => g * z j) n = fun i => g * cat x z n i := by
  funext i
  have hi := i.isLt
  simp only [cat]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Introduce `P Q _ _ pr q b hb`. Use function extensionality and compare the values at `x y`. Establish `h0` using `congrFun hb (cat x (fun j => pr (y j)) (q + 1 + 2))`. Rewrite `h0` using `[dc_cat (a := 0) (c := q + 1) (by omega), Fin.sum_univ_succ (n := 0), Fin.sum_univ_zero]`. Simplify using `only [cat_zero_left, Fin.val_zero, pow_zero, one_mul, zero_add, pow_one, Pi.zero_apply, add_zero] at h0`.

Simplify using `only [Wtop, dv, dc, zz]`. Express the relevant statement in the definitionally equal form `(b fun j => pr (y j)) = ∑ i : Fin (q + 2), (-1 : ℝ) ^ (i : ℕ) * b (cat x (fun j => pr (y (i.succAbove j))) (q + 1 + 1))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem splitA : SplitA := by
  intro P Q _ _ pr q b hb
  funext x y
  have h0 := congrFun hb (cat x (fun j => pr (y j)) (q + 1 + 2))
  rw [dc_cat (a := 0) (c := q + 1) (by omega), Fin.sum_univ_succ (n := 0), Fin.sum_univ_zero] at h0
  simp only [cat_zero_left, Fin.val_zero, pow_zero, one_mul, zero_add,
    pow_one, Pi.zero_apply, add_zero] at h0
  simp only [Wtop, dv, dc, zz]
  change (b fun j => pr (y j)) =
    ∑ i : Fin (q + 2), (-1 : ℝ) ^ (i : ℕ) * b (cat x (fun j => pr (y (i.succAbove j))) (q + 1 + 1))
  linarith

/- English proof (translation)
Introduce `P Q _ _ pr p q b hb`. Use function extensionality and compare the values at `x y`. Establish `h0` using `congrFun hb (cat x (fun j => pr (y j)) (p + q + 2 + 2))`. Rewrite `h0` using `[dc_cat (a := p + 1) (c := q + 1) (by omega)]`. Simplify using `only [Pi.zero_apply] at h0`.

Simplify using `only [dh, dv, dc, zz, Pi.smul_apply, smul_eq_mul]`. Express the relevant statement in the definitionally equal form `∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) * b (cat (fun l => x (i.succAbove l)) (fun j => pr (y j)) (p + q + 2 + 1)) = (-1 : ℝ) ^ (p + 1) * ∑ j : Fin (q + 2), (-1 : ℝ) ^ (j : ℕ) * b (cat x (fun l => pr (y (j.succAbove l))) (p + q + 2 + 1))`. Take the linear combination `h0`.
-/
theorem splitS : SplitS := by
  intro P Q _ _ pr p q b hb
  funext x y
  have h0 := congrFun hb (cat x (fun j => pr (y j)) (p + q + 2 + 2))
  rw [dc_cat (a := p + 1) (c := q + 1) (by omega)] at h0
  simp only [Pi.zero_apply] at h0
  simp only [dh, dv, dc, zz, Pi.smul_apply, smul_eq_mul]
  change ∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) *
      b (cat (fun l => x (i.succAbove l)) (fun j => pr (y j)) (p + q + 2 + 1)) =
    (-1 : ℝ) ^ (p + 1) * ∑ j : Fin (q + 2), (-1 : ℝ) ^ (j : ℕ) *
      b (cat x (fun l => pr (y (j.succAbove l))) (p + q + 2 + 1))
  linear_combination h0

/- English proof (translation)
Introduce `P Q _ _ pr N b hb`. Use function extensionality and compare the values at `x y`. Establish `h0` using `congrFun hb (cat x (fun j => pr (y j)) (N + 1 + 2))`. Rewrite `h0` using `[dc_cat (a := N + 1) (c := 0) (by omega), Fin.sum_univ_succ (n := 0), Fin.sum_univ_zero]`. Simplify using `only [cat_zero_right, Fin.val_zero, pow_zero, one_mul, Pi.zero_apply, add_zero] at h0`.

Simplify using `only [dh, dc, zz, Pi.smul_apply, smul_eq_mul]`. Express the relevant statement in the definitionally equal form `∑ i : Fin (N + 2), (-1 : ℝ) ^ (i : ℕ) * b (cat (fun l => x (i.succAbove l)) (fun j => pr (y j)) (N + 1 + 1)) = _`. Take the linear combination `h0`.
-/
theorem splitB : SplitB := by
  intro P Q _ _ pr N b hb
  funext x y
  have h0 := congrFun hb (cat x (fun j => pr (y j)) (N + 1 + 2))
  rw [dc_cat (a := N + 1) (c := 0) (by omega), Fin.sum_univ_succ (n := 0), Fin.sum_univ_zero] at h0
  simp only [cat_zero_right, Fin.val_zero, pow_zero, one_mul, Pi.zero_apply, add_zero] at h0
  simp only [dh, dc, zz, Pi.smul_apply, smul_eq_mul]
  change ∑ i : Fin (N + 2), (-1 : ℝ) ^ (i : ℕ) * b (cat (fun l => x (i.succAbove l)) (fun j => pr (y j)) (N + 1 + 1)) = _
  linear_combination h0

/- English proof (translation)
Introduce `P Q _ _ pr n a c b hn hb g x y`. Simplify using `only [zz, map_mul]`. Rewrite using `[cat_mul hn]`. Conclude with `hb (pr g) _`.
-/
theorem zInv : ZInv := by
  intro P Q _ _ pr n a c b hn hb g x y
  simp only [zz, map_mul]
  rw [cat_mul hn]
  exact hb (pr g) _

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
