import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.CntSym
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QkDetExpand
import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.Branch
import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.WeylGT

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)

/- English proof (translation)
Establish `h1 : ∀ i : Fin n, ∏ j ∈ Ioi i, F i j = ∏ j : Fin n, if i < j then F i j else 1`. Introduce `i`. Rewrite using `[← prod_filter]`. Use `congr 1`. Use extensionality with `j`.

Simplify using the standard rewrite rules. Repeatedly rewrite using `[h1]`. Rewrite using `[prod_comm, ← Fin.prod_univ_eq_prod_range (fun j => ∏ i ∈ range j, F i j) n]`. Use `prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h2 : ∏ i : Fin n, (if i < j then F i j else 1) = ∏ i ∈ range n, if i < j.1 then F i j else 1`.

Rewrite using `[← Fin.prod_univ_eq_prod_range (fun i => if i < j.1 then F i j else 1) n]`. Use `prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Fin.lt_def]`. Rewrite using `[h2, ← prod_filter]`. Use `congr 1`.

Use extensionality with `i`. Use `j.2` as an intermediate fact. Simplify using `only [mem_range, mem_filter]`. Use linear arithmetic over natural numbers and integers.
-/
lemma qk_prod_conv (n : ℕ) (F : ℕ → ℕ → ℝ) :
    ∏ j ∈ range n, ∏ i ∈ range j, F i j = ∏ i : Fin n, ∏ j ∈ Ioi i, F i j := by
  have h1 : ∀ i : Fin n, ∏ j ∈ Ioi i, F i j = ∏ j : Fin n, if i < j then F i j else 1 := by
    intro i
    rw [← prod_filter]
    congr 1
    ext j
    simp
  simp_rw [h1]
  rw [prod_comm, ← Fin.prod_univ_eq_prod_range (fun j => ∏ i ∈ range j, F i j) n]
  refine prod_congr rfl fun j _ => ?_
  have h2 : ∏ i : Fin n, (if i < j then F i j else 1) = ∏ i ∈ range n, if i < j.1 then F i j else 1 := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => if i < j.1 then F i j else 1) n]
    refine prod_congr rfl fun i _ => ?_
    simp only [Fin.lt_def]
  rw [h2, ← prod_filter]
  congr 1
  ext i
  have := j.2
  simp only [mem_range, mem_filter]
  omega

def qk_v {n : ℕ} (mu : Fin n → ℤ) : Fin n → ℝ := fun i => (i.1 : ℝ) - (mu i : ℝ)

def vandermondeDenominator (n : ℕ) : ℝ := ∏ j ∈ range n, ∏ i ∈ range j, ((j : ℝ) - (i : ℝ))

/- English proof (translation)
Unfold `vandermondeDenominator`. Use `prod_ne_zero_iff.2 fun j _ => prod_ne_zero_iff.2 fun i hi => ?_` and prove the remaining obligations. Establish `: (i : ℝ) < (j : ℝ)` using `by exact_mod_cast mem_range.1 hi`. Conclude with `sub_ne_zero.2 (ne_of_gt this)`.
-/
lemma qk_W_ne (n : ℕ) : vandermondeDenominator n ≠ 0 := by
  unfold vandermondeDenominator
  refine prod_ne_zero_iff.2 fun j _ => prod_ne_zero_iff.2 fun i hi => ?_
  have : (i : ℝ) < (j : ℝ) := by exact_mod_cast mem_range.1 hi
  exact sub_ne_zero.2 (ne_of_gt this)

/- English proof (translation)
Unfold `Formalism.InvariantFactorPaths.BranchingDimensions.weylDim`. Repeatedly rewrite using `[prod_div_distrib]`. Rewrite using `[show (∏ j ∈ range n, ∏ i ∈ range j, ((j : ℝ) - (i : ℝ))) = vandermondeDenominator n from rfl, div_mul_cancel₀ _ (qk_W_ne n), qk_prod_conv n (fun i j => ((Formalism.InvariantFactorPaths.BranchingDimensions.extW mu i - Formalism.InvariantFactorPaths.BranchingDimensions.extW mu j : …`. Unfold `qk_D qk_v`. Use `prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Formalism.InvariantFactorPaths.BranchingDimensions.WGT.extW_val, Formalism.InvariantFactorPaths.BranchingDimensions.WGT.extW_val]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma qk_weyl {n : ℕ} (mu : Fin n → ℤ) :
    Formalism.InvariantFactorPaths.BranchingDimensions.weylDim n (Formalism.InvariantFactorPaths.BranchingDimensions.extW mu) * vandermondeDenominator n = qk_D (qk_v mu) := by
  unfold Formalism.InvariantFactorPaths.BranchingDimensions.weylDim
  simp_rw [prod_div_distrib]
  rw [show (∏ j ∈ range n, ∏ i ∈ range j, ((j : ℝ) - (i : ℝ))) = vandermondeDenominator n from rfl, div_mul_cancel₀ _ (qk_W_ne n),
    qk_prod_conv n (fun i j => ((Formalism.InvariantFactorPaths.BranchingDimensions.extW mu i - Formalism.InvariantFactorPaths.BranchingDimensions.extW mu j : ℤ) : ℝ) + ((j : ℝ) - (i : ℝ)))]
  unfold qk_D qk_v
  refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
  rw [Formalism.InvariantFactorPaths.BranchingDimensions.WGT.extW_val, Formalism.InvariantFactorPaths.BranchingDimensions.WGT.extW_val]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[← qk_weyl, Formalism.InvariantFactorPaths.BranchingDimensions.weyl_dim_eq_gelfand_tsetlin Formalism.InvariantFactorPaths.BranchingDimensions.branchingDimensionFormula n mu h]`.
-/
lemma qk_D_dom {n : ℕ} {mu : Fin n → ℤ} (h : Dominant mu) : qk_D (qk_v mu) = (dGT n mu : ℝ) * vandermondeDenominator n := by
  rw [← qk_weyl, Formalism.InvariantFactorPaths.BranchingDimensions.weyl_dim_eq_gelfand_tsetlin Formalism.InvariantFactorPaths.BranchingDimensions.branchingDimensionFormula n mu h]

/- English proof (translation)
Unfold `qk_D`. Use `prod_eq_zero (mem_univ i) (prod_eq_zero (mem_Ioi.2 hij) ?_)` and prove the remaining obligations. Rewrite using `[h, sub_self]`.
-/
lemma qk_D_zero {n : ℕ} {v : Fin n → ℝ} {i j : Fin n} (hij : i < j) (h : v i = v j) : qk_D v = 0 := by
  unfold qk_D
  refine prod_eq_zero (mem_univ i) (prod_eq_zero (mem_Ioi.2 hij) ?_)
  rw [h, sub_self]

def qk_add {n : ℕ} (mu : Fin n → ℤ) (s : Finset (Fin n)) : Fin n → ℤ := fun a => if a ∈ s then mu a + 1 else mu a

/- English proof (translation)
Use function extensionality and compare the values at `i`. Unfold `qk_v qk_add`. Distinguish the cases in `hi : i ∈ s`. Simplify using `only [hi, if_true, piecewise_eq_of_mem]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hi, if_false, piecewise_eq_of_notMem, not_false_eq_true]`.
-/
lemma qk_v_add {n : ℕ} (mu : Fin n → ℤ) (s : Finset (Fin n)) :
    qk_v (qk_add mu s) = s.piecewise (fun i => qk_v mu i - 1) (qk_v mu) := by
  funext i
  unfold qk_v qk_add
  by_cases hi : i ∈ s
  · simp only [hi, if_true, piecewise_eq_of_mem]
    push_cast
    ring
  · simp only [hi, if_false, piecewise_eq_of_notMem, not_false_eq_true]

/- English proof (translation)
Establish `h1 : ∃ a : Fin n, ∃ ha : a.1 + 1 < n, qk_add mu s a < qk_add mu s ⟨a.1 + 1, ha⟩`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `h (qk_antitone_of_step hc)`. Take `⟨a, ha, hlt⟩` from `h1`.

Establish `hle : mu ⟨a.1 + 1, ha⟩ ≤ mu a` using `hmu (by rw [Fin.le_def]; simp)`. Establish `h2 : qk_add mu s ⟨a.1 + 1, ha⟩ = qk_add mu s a + 1`. Unfold `qk_add at hlt ⊢`. Apply the tactic sequence `split_ifs at hlt ⊢ <;> omega`. Use `qk_D_zero (i := a) (j := ⟨a.1 + 1, ha⟩) (by rw [Fin.lt_def]; simp) ?_` and prove the remaining obligations.

Unfold `qk_v`. Rewrite using `[h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma qk_D_nondom {n : ℕ} {mu : Fin n → ℤ} (hmu : Dominant mu) (s : Finset (Fin n))
    (h : ¬ Dominant (qk_add mu s)) : qk_D (qk_v (qk_add mu s)) = 0 := by
  have h1 : ∃ a : Fin n, ∃ ha : a.1 + 1 < n, qk_add mu s a < qk_add mu s ⟨a.1 + 1, ha⟩ := by
    by_contra hc
    push Not at hc
    exact h (qk_antitone_of_step hc)
  obtain ⟨a, ha, hlt⟩ := h1
  have hle : mu ⟨a.1 + 1, ha⟩ ≤ mu a := hmu (by rw [Fin.le_def]; simp)
  have h2 : qk_add mu s ⟨a.1 + 1, ha⟩ = qk_add mu s a + 1 := by
    unfold qk_add at hlt ⊢
    split_ifs at hlt ⊢ <;> omega
  refine qk_D_zero (i := a) (j := ⟨a.1 + 1, ha⟩) (by rw [Fin.lt_def]; simp) ?_
  unfold qk_v
  rw [h2]
  push_cast
  ring

/- English proof (translation)
Unfold `strVert`. Simplify using `only [mem_filter, Fintype.mem_piFinset, mem_Icc]`.
-/
lemma qk_mem_strVert {n : ℕ} {mu nu : Fin n → ℤ} {b : ℕ} : nu ∈ strVert mu b ↔
    (∀ a, mu a ≤ nu a ∧ nu a ≤ mu a + 1) ∧ Dominant nu ∧ ∑ a, (nu a - mu a) = (b : ℤ) := by
  unfold strVert
  simp only [mem_filter, Fintype.mem_piFinset, mem_Icc]

/- English proof (translation)
Establish `: ∀ a, qk_add mu s a - mu a = if a ∈ s then 1 else 0`. Introduce `a`. Unfold `qk_add`. Apply the tactic sequence `split_ifs <;> ring`. Simplify using `only [this]`.

Simplify using the standard rewrite rules.
-/
lemma qk_add_sum {n : ℕ} (mu : Fin n → ℤ) (s : Finset (Fin n)) : ∑ a, (qk_add mu s a - mu a) = (s.card : ℤ) := by
  have : ∀ a, qk_add mu s a - mu a = if a ∈ s then 1 else 0 := by
    intro a
    unfold qk_add
    split_ifs <;> ring
  simp only [this]
  simp

/- English proof (translation)
Use function extensionality and compare the values at `a`. Unfold `qk_add`. Simplify using `only [mem_filter, mem_univ, true_and]`. Use `split_ifs with h1`. Conclude with `h1.symm`.

Use `h a` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma qk_add_sel {n : ℕ} {mu nu : Fin n → ℤ} (h : ∀ a, mu a ≤ nu a ∧ nu a ≤ mu a + 1) :
    qk_add mu (univ.filter fun a => nu a = mu a + 1) = nu := by
  funext a
  unfold qk_add
  simp only [mem_filter, mem_univ, true_and]
  split_ifs with h1
  · exact h1.symm
  · have := h a
    omega

/- English proof (translation)
Use extensionality with `a`. Apply the tactic sequence `by_cases ha : a ∈ s <;> simp [qk_add, ha]`.
-/
lemma qk_sel_add {n : ℕ} (mu : Fin n → ℤ) (s : Finset (Fin n)) :
    (univ.filter fun a => qk_add mu s a = mu a + 1) = s := by
  ext a
  by_cases ha : a ∈ s <;> simp [qk_add, ha]

/- English proof (translation)
Introduce `n _ mu b hmu`. Establish `hcard : Fintype.card (LamIdx n b) = n.choose b`. Rewrite using `[Fintype.card_finset_len, Fintype.card_fin]`. Rewrite using `[hcard]`. Establish `hW` using `qk_W_ne n`.

Establish `key : ((dMu mu * n.choose b : ℕ) : ℝ) * vandermondeDenominator n = ((∑ nu ∈ strVert mu b, dMu nu : ℕ) : ℝ) * vandermondeDenominator n`. Use `push_cast`. Rewrite using `[sum_mul]`. Establish `e1 : ∑ nu ∈ strVert mu b, (dMu nu : ℝ) * vandermondeDenominator n = ∑ nu ∈ strVert mu b, qk_D (qk_v nu)`. Use `sum_congr rfl fun nu hnu => ?_` and prove the remaining obligations.

Establish `hd` using `(qk_mem_strVert.1 hnu).2.1`. Rewrite using `[qk_D_dom hd, qk_dMu_eq_dGT n nu hd]`. Establish `e2 : ∑ s ∈ (powersetCard b (univ : Finset (Fin n))).filter (fun s => Dominant (qk_add mu s)), qk_D (qk_v (qk_add mu s)) = ∑ nu ∈ strVert mu b, qk_D (qk_v nu)`. Use `sum_nbij' (qk_add mu) (fun nu => univ.filter fun a => nu a = mu a + 1) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `s hs`.

Rewrite `hs` using `[mem_filter, mem_powersetCard]`. Use `qk_mem_strVert.2 ⟨fun a => ?_, hs.2, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `unfold qk_add split_ifs <;> omega`. Rewrite using `[qk_add_sum, hs.1.2]`. Introduce `nu hnu`.

Establish `h` using `qk_mem_strVert.1 hnu`. Rewrite using `[mem_filter, mem_powersetCard, qk_add_sel h.1]`. Use `⟨⟨subset_univ _, ?_⟩, h.2.1⟩` and prove the remaining obligations. Establish `h3` using `qk_add_sum mu (univ.filter fun a => nu a = mu a + 1)`. Rewrite `h3` using `[qk_add_sel h.1, h.2.2]`.

Conclude with `h3.symm` after adjusting the coercions. Introduce `s _`. Conclude with `qk_sel_add mu s`. Introduce `nu hnu`. Conclude with `qk_add_sel (qk_mem_strVert.1 hnu).1`.

Introduce `s _`. Both sides reduce to the same expression. Establish `e3 : ∑ s ∈ (powersetCard b (univ : Finset (Fin n))).filter (fun s => Dominant (qk_add mu s)), qk_D (qk_v (qk_add mu s)) = ∑ s ∈ powersetCard b (univ : Finset (Fin n)), qk_D (qk_v (qk_add mu s))`. Use `sum_filter_of_ne fun s _ hne => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`.

Conclude with `hne (qk_D_nondom hmu s hc)`. Rewrite using `[e1, ← e2, e3]`. Simplify using `only [qk_v_add]`. Rewrite using `[qk_D_shift, qk_D_dom hmu, qk_dMu_eq_dGT n mu hmu]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `mul_right_cancel₀ hW key` after adjusting the coercions.
-/
theorem exterior_power_count_holds : CntLam := by
  classical
  intro n _ mu b hmu
  have hcard : Fintype.card (LamIdx n b) = n.choose b := by
    rw [Fintype.card_finset_len, Fintype.card_fin]
  rw [hcard]
  have hW := qk_W_ne n
  have key : ((dMu mu * n.choose b : ℕ) : ℝ) * vandermondeDenominator n = ((∑ nu ∈ strVert mu b, dMu nu : ℕ) : ℝ) * vandermondeDenominator n := by
    push_cast
    rw [sum_mul]
    have e1 : ∑ nu ∈ strVert mu b, (dMu nu : ℝ) * vandermondeDenominator n = ∑ nu ∈ strVert mu b, qk_D (qk_v nu) := by
      refine sum_congr rfl fun nu hnu => ?_
      have hd := (qk_mem_strVert.1 hnu).2.1
      rw [qk_D_dom hd, qk_dMu_eq_dGT n nu hd]
    have e2 : ∑ s ∈ (powersetCard b (univ : Finset (Fin n))).filter (fun s => Dominant (qk_add mu s)),
        qk_D (qk_v (qk_add mu s)) = ∑ nu ∈ strVert mu b, qk_D (qk_v nu) := by
      refine sum_nbij' (qk_add mu) (fun nu => univ.filter fun a => nu a = mu a + 1) ?_ ?_ ?_ ?_ ?_
      · intro s hs
        rw [mem_filter, mem_powersetCard] at hs
        refine qk_mem_strVert.2 ⟨fun a => ?_, hs.2, ?_⟩
        · unfold qk_add
          split_ifs <;> omega
        · rw [qk_add_sum, hs.1.2]
      · intro nu hnu
        have h := qk_mem_strVert.1 hnu
        rw [mem_filter, mem_powersetCard, qk_add_sel h.1]
        refine ⟨⟨subset_univ _, ?_⟩, h.2.1⟩
        have h3 := qk_add_sum mu (univ.filter fun a => nu a = mu a + 1)
        rw [qk_add_sel h.1, h.2.2] at h3
        exact_mod_cast h3.symm
      · intro s _
        exact qk_sel_add mu s
      · intro nu hnu
        exact qk_add_sel (qk_mem_strVert.1 hnu).1
      · intro s _
        rfl
    have e3 : ∑ s ∈ (powersetCard b (univ : Finset (Fin n))).filter (fun s => Dominant (qk_add mu s)),
        qk_D (qk_v (qk_add mu s)) = ∑ s ∈ powersetCard b (univ : Finset (Fin n)), qk_D (qk_v (qk_add mu s)) := by
      refine sum_filter_of_ne fun s _ hne => ?_
      by_contra hc
      exact hne (qk_D_nondom hmu s hc)
    rw [e1, ← e2, e3]
    simp only [qk_v_add]
    rw [qk_D_shift, qk_D_dom hmu, qk_dMu_eq_dGT n mu hmu]
    ring
  exact_mod_cast mul_right_cancel₀ hW key

end Formalism.InvariantFactorPaths.ColumnFamilies
