import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.SubFlag
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic

noncomputable section

namespace PI.StabSplit.UnipW

def perpX (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop := ∀ i : Fin (2 * r + k + 1), r + k < i.val → v i = 0

def inX (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop := ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0

def Lk (k r : ℕ) : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[bvec, Matrix.mulVec, Pi.single_apply]`.
-/
lemma mulVec_bvec {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) :
    A *ᵥ bvec j = fun i => A i j := by
  funext i
  simp [bvec, Matrix.mulVec, Pi.single_apply]

/- English proof (translation)
Unfold `sig`. Rewrite using `[if_pos (Or.inl h)]`. Use `show r + k < 2 * r + k - i.val`. Use linear arithmetic over natural numbers and integers.
-/
lemma sig_gt {k r : ℕ} (i : Fin (2 * r + k + 1)) (h : i.val < r) : r + k < (sig k r i).val := by
  unfold sig
  rw [if_pos (Or.inl h)]
  show r + k < 2 * r + k - i.val
  omega

/- English proof (translation)
Unfold `sig`. Use `split_ifs with h'`. Use `show r ≤ 2 * r + k - i.val`. Use linear arithmetic over natural numbers and integers. Use `push_neg at h'`.

Conclude with `h'.1`.
-/
lemma sig_ge {k r : ℕ} (i : Fin (2 * r + k + 1)) (h : i.val ≤ r + k) : r ≤ (sig k r i).val := by
  unfold sig
  split_ifs with h'
  · show r ≤ 2 * r + k - i.val
    omega
  · push_neg at h'
    exact h'.1

/- English proof (translation)
Distinguish the cases in `hi : i.val < r ∨ r + k < i.val`. Establish `hsig : sig k r i = ⟨2 * r + k - i.val, by omega⟩`. Unfold `sig`. Rewrite using `[if_pos hi]`. Rewrite using `[hsig]`.

Establish `hj : (j = (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))) ↔ i.val + j.val = 2 * r + k`. Rewrite using `[Fin.ext_iff]`. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Hpk, sgn, hj]`.

Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega) | simp_all`. Establish `hsig : sig k r i = i`. Unfold `sig`. Rewrite using `[if_neg hi]`. Rewrite using `[hsig]`.

Use `push_neg at hi`. Simplify using `only [Hpk, sgn]`. Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality. Simplify using `only [if_true, and_true, eq_self_iff_true]`.

Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Establish `hij' : ¬ i = j` using `fun h => hij h.symm`. Simplify using `only [hij, hij', if_false, and_false]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
private lemma hpk_apply_of_outer_index (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sig k r i then sgn k r i else 0 := by
  by_cases hi : i.val < r ∨ r + k < i.val
  · have hsig : sig k r i = ⟨2 * r + k - i.val, by omega⟩ := by
      unfold sig
      rw [if_pos hi]
    rw [hsig]
    have hj : (j = (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))) ↔ i.val + j.val = 2 * r + k := by
      rw [Fin.ext_iff]
      simp only
      omega
    simp only [Hpk, sgn, hj]
    split_ifs <;> first | rfl | (exfalso; omega) | simp_all
  · have hsig : sig k r i = i := by
      unfold sig
      rw [if_neg hi]
    rw [hsig]
    push_neg at hi
    simp only [Hpk, sgn]
    by_cases hij : j = i
    · subst hij
      simp only [if_true, and_true, eq_self_iff_true]
      split_ifs <;> first | rfl | (exfalso; omega)
    · have hij' : ¬ i = j := fun h => hij h.symm
      simp only [hij, hij', if_false, and_false]
      split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Unfold `herm`. Simplify using `only [dotProduct, Pi.star_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`. Simplify using `only [Matrix.mulVec, dotProduct, hpk_apply_of_outer_index, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
lemma herm_coord {k r : ℕ} (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = ∑ i, star (w i) * (sgn k r i * v (sig k r i)) := by
  unfold herm
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [Matrix.mulVec, dotProduct, hpk_apply_of_outer_index, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- English proof (translation)
Rewrite using `[herm_coord]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Establish `hs : sig k r i = i`. Unfold `sig`.

Rewrite using `[if_neg (by omega)]`. Rewrite using `[hs]`. Distinguish the cases in `hi : i.val < r`. Rewrite using `[hv _ (sig_gt i hi)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hw i (by omega)]`. Simplify using the standard rewrite rules.
-/
lemma star_dotProduct_Hpk_mulVec_eq_sum_sub {k r : ℕ} {v w : Fin (2 * r + k + 1) → ℂ} (hv : perpX k r v) (hw : perpX k r w) :
    herm (Hpk k r) v w =
      ∑ i, if (r ≤ i.val ∧ i.val ≤ r + k) then star (w i) * (sgn k r i * v i) else 0 := by
  rw [herm_coord]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · have hs : sig k r i = i := by
      unfold sig
      rw [if_neg (by omega)]
    rw [hs]
  · by_cases hi : i.val < r
    · rw [hv _ (sig_gt i hi)]
      ring
    · rw [hw i (by omega)]
      simp

/- English proof (translation)
Rewrite using `[herm_coord]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i.val < r`. Rewrite using `[hv _ (sig_gt i hi)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hx i (by omega)]`. Simplify using the standard rewrite rules.
-/
lemma herm_perp_inX {k r : ℕ} {v x : Fin (2 * r + k + 1) → ℂ} (hv : perpX k r v) (hx : inX k r x) :
    herm (Hpk k r) v x = 0 := by
  rw [herm_coord]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val < r
  · rw [hv _ (sig_gt i hi)]
    ring
  · rw [hx i (by omega)]
    simp

/- English proof (translation)
Rewrite using `[herm_coord]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i.val ≤ r + k`. Rewrite using `[hx _ (sig_ge i hi)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hv i (by omega)]`. Simplify using the standard rewrite rules.
-/
lemma herm_inX_perp {k r : ℕ} {v x : Fin (2 * r + k + 1) → ℂ} (hv : perpX k r v) (hx : inX k r x) :
    herm (Hpk k r) x v = 0 := by
  rw [herm_coord]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val ≤ r + k
  · rw [hx _ (sig_ge i hi)]
    ring
  · rw [hv i (by omega)]
    simp

/- English proof (translation)
Unfold `sgn`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma star_sgn {k r : ℕ} (i : Fin (2 * r + k + 1)) : star (sgn k r i) = sgn k r i := by
  unfold sgn
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[star_dotProduct_Hpk_mulVec_eq_sum_sub hw hv, star_dotProduct_Hpk_mulVec_eq_sum_sub hv hw, star_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `split_ifs`. Simplify using `only [star_mul', star_star, star_sgn]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules.
-/
lemma herm_conjW {k r : ℕ} {v w : Fin (2 * r + k + 1) → ℂ} (hv : perpX k r v) (hw : perpX k r w) :
    herm (Hpk k r) w v = star (herm (Hpk k r) v w) := by
  rw [star_dotProduct_Hpk_mulVec_eq_sum_sub hw hv, star_dotProduct_Hpk_mulVec_eq_sum_sub hv hw, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · simp only [star_mul', star_star, star_sgn]
    ring
  · simp

/- English proof (translation)
Rewrite using `[star_dotProduct_Hpk_mulVec_eq_sum_sub hw hw, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Distinguish the cases in `hi : i.val = r + k`. Establish `e : i = Lk k r` using `Fin.ext hi`.

Rewrite using `[e, hL]`. Simplify using the standard rewrite rules. Simplify using `only [sgn, if_neg hi, one_mul]`. Rewrite using `[mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]`. Simplify using the standard rewrite rules.
-/
lemma herm_self_re {k r : ℕ} {w : Fin (2 * r + k + 1) → ℂ} (hw : perpX k r w) (hL : w (Lk k r) = 0) :
    (herm (Hpk k r) w w).re =
      ∑ i, if (r ≤ i.val ∧ i.val ≤ r + k) then Complex.normSq (w i) else 0 := by
  rw [star_dotProduct_Hpk_mulVec_eq_sum_sub hw hw, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · by_cases hi : i.val = r + k
    · have e : i = Lk k r := Fin.ext hi
      rw [e, hL]
      simp
    · simp only [sgn, if_neg hi, one_mul]
      rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  · simp

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun i _ => by split_ifs <;> first | exact Complex.normSq_nonneg _ | exact le_refl _`.
-/
lemma sum_W_nonneg {k r : ℕ} (w : Fin (2 * r + k + 1) → ℂ) :
    0 ≤ ∑ i : Fin (2 * r + k + 1), if (r ≤ i.val ∧ i.val ≤ r + k) then Complex.normSq (w i) else 0 := Finset.sum_nonneg fun i _ => by
    split_ifs <;> first | exact Complex.normSq_nonneg _ | exact le_refl _

/- English proof (translation)
Unfold `herm`. Simplify using `only [Matrix.mulVec_sub, Matrix.mulVec_smul, star_sub, star_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma herm_expand {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (y z : Fin m → ℂ) (c : ℂ) :
    herm H (y - c • z) (y - c • z) =
      herm H y y - star c * herm H y z - c * herm H z y + c * star c * herm H z z := by
  unfold herm
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, star_sub, star_smul, dotProduct_sub,
    sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.mulVec_add, dotProduct_add]`.
-/
lemma herm_add_left {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (a b w : Fin m → ℂ) :
    herm H (a + b) w = herm H a w + herm H b w := by
  unfold herm
  rw [Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Unfold `herm`. Rewrite using `[star_add, add_dotProduct]`.
-/
lemma herm_add_right {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (v a b : Fin m → ℂ) :
    herm H v (a + b) = herm H v a + herm H v b := by
  unfold herm
  rw [star_add, add_dotProduct]

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.mulVec_sub, dotProduct_sub]`.
-/
lemma herm_sub_left {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (a b w : Fin m → ℂ) :
    herm H (a - b) w = herm H a w - herm H b w := by
  unfold herm
  rw [Matrix.mulVec_sub, dotProduct_sub]

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Apply the tactic sequence `first | rw [hg] | rw [← Matrix.mul_assoc, hg]`.
-/
lemma herm_inv {m : ℕ} {H g : Matrix (Fin m) (Fin m) ℂ} (hg : gᴴ * H * g = H) (v w : Fin m → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  first | rw [hg] | rw [← Matrix.mul_assoc, hg]

/- English proof (translation)
Establish `hzp : perpX k r z` using `fun i hi => hz i (Or.inr hi)`. Establish `hzL : z (Lk k r) ≠ 0`. Introduce `h0`. Establish `hnn : 0 ≤ (herm (Hpk k r) z z).re` using `by rw [herm_self_re hzp h0]; exact sum_W_nonneg z`. Unfold `Tz at hT`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set c := y (Lk k r) / z (Lk k r) with hc`. Establish `hwp : perpX k r (y - c • z)` using `fun i hi => by simp [hy i hi, hzp i hi]`. Establish `hwL : (y - c • z) (Lk k r) = 0`. Rewrite using `[Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc, div_mul_cancel₀ _ hzL, sub_self]`.

Establish `hzy : herm (Hpk k r) z y = 0` using `by rw [herm_conjW hy hzp, h2, star_zero]`. Establish `hexp : herm (Hpk k r) (y - c • z) (y - c • z) = (Complex.normSq c : ℂ) * herm (Hpk k r) z z`. Rewrite using `[herm_expand, h1, h2, hzy, Complex.star_def, Complex.mul_conj]`. Expand and normalize the polynomial expressions, which then agree. Establish `hre : (herm (Hpk k r) (y - c • z) (y - c • z)).re = -(Complex.normSq c * Tz k r z)`.

Rewrite using `[hexp, Complex.re_ofReal_mul]`. Unfold `Tz`. Expand and normalize the polynomial expressions, which then agree. Establish `hnn : 0 ≤ (herm (Hpk k r) (y - c • z) (y - c • z)).re`. Rewrite using `[herm_self_re hwp hwL]`.

Conclude with `sum_W_nonneg _`. Establish `hc0 : Complex.normSq c = 0`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < Complex.normSq c` using `lt_of_le_of_ne (Complex.normSq_nonneg c) (Ne.symm hne)`. Use `mul_pos hpos hT` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hyL : y (Lk k r) = 0`. Establish `h0` using `Complex.normSq_eq_zero.mp hc0`. Rewrite `h0` using `[hc, div_eq_zero_iff]`. Conclude with `h0.resolve_right hzL`.

Establish `hsum` using `herm_self_re hy hyL`. Rewrite `hsum` using `[h1, Complex.zero_re]`. Introduce `i hi`. Distinguish the cases in `hik : r + k < i.val`. Conclude with `hy i hik`.

Apply the tactic sequence `have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by split_ifs <;> [exact Complex.normSq_nonneg _; exact le_refl _])).mp hsum.symm i (Finset.mem_univ _)`. Rewrite `hall` using `[if_pos ⟨hi, by omega⟩]`. Conclude with `Complex.normSq_eq_zero.mp hall`.
-/
lemma definite {k r : ℕ} {y z : Fin (2 * r + k + 1) → ℂ} (hy : perpX k r y) (hz : inWb k r z)
    (hT : 0 < Tz k r z) (h1 : herm (Hpk k r) y y = 0) (h2 : herm (Hpk k r) y z = 0) : inX k r y := by
  have hzp : perpX k r z := fun i hi => hz i (Or.inr hi)
  have hzL : z (Lk k r) ≠ 0 := by
    intro h0
    have hnn : 0 ≤ (herm (Hpk k r) z z).re := by rw [herm_self_re hzp h0]; exact sum_W_nonneg z
    unfold Tz at hT; linarith
  set c := y (Lk k r) / z (Lk k r) with hc
  have hwp : perpX k r (y - c • z) := fun i hi => by simp [hy i hi, hzp i hi]
  have hwL : (y - c • z) (Lk k r) = 0 := by
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc, div_mul_cancel₀ _ hzL, sub_self]
  have hzy : herm (Hpk k r) z y = 0 := by rw [herm_conjW hy hzp, h2, star_zero]
  have hexp : herm (Hpk k r) (y - c • z) (y - c • z) = (Complex.normSq c : ℂ) * herm (Hpk k r) z z := by
    rw [herm_expand, h1, h2, hzy, Complex.star_def, Complex.mul_conj]; ring
  have hre : (herm (Hpk k r) (y - c • z) (y - c • z)).re = -(Complex.normSq c * Tz k r z) := by
    rw [hexp, Complex.re_ofReal_mul]; unfold Tz; ring
  have hnn : 0 ≤ (herm (Hpk k r) (y - c • z) (y - c • z)).re := by
    rw [herm_self_re hwp hwL]; exact sum_W_nonneg _
  have hc0 : Complex.normSq c = 0 := by
    by_contra hne
    have hpos : 0 < Complex.normSq c := lt_of_le_of_ne (Complex.normSq_nonneg c) (Ne.symm hne)
    have := mul_pos hpos hT
    linarith
  have hyL : y (Lk k r) = 0 := by
    have h0 := Complex.normSq_eq_zero.mp hc0
    rw [hc, div_eq_zero_iff] at h0
    exact h0.resolve_right hzL
  have hsum := herm_self_re hy hyL
  rw [h1, Complex.zero_re] at hsum
  intro i hi
  by_cases hik : r + k < i.val
  · exact hy i hik
  · have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by
      split_ifs <;> [exact Complex.normSq_nonneg _; exact le_refl _])).mp hsum.symm i (Finset.mem_univ _)
    rw [if_pos ⟨hi, by omega⟩] at hall
    exact Complex.normSq_eq_zero.mp hall

/- English proof (translation)
Introduce `q`. Proceed by induction on `q with`. Consider the case `zero`. Introduce `v _ hv0`. Rewrite `hv0` using `[pow_zero, Matrix.one_mulVec]`.

Substitute `hv0` using the available equality. Introduce `i _`. Simplify using the standard rewrite rules. Consider the case `succ q ih`. Introduce `v hv hq`.

Establish `hv' : perpX k r (g *ᵥ v - v)` using `fun i hi => by`. Simplify using `only [Pi.sub_apply]`. Rewrite using `[hperp v hv i hi, hv i hi, sub_zero]`. Establish `hgv : (g - 1) *ᵥ v = g *ᵥ v - v` using `by rw [Matrix.sub_mulVec, Matrix.one_mulVec]`. Establish `hq' : (g - 1) ^ q *ᵥ (g *ᵥ v - v) = 0`.

Rewrite using `[← hgv, Matrix.mulVec_mulVec, ← pow_succ]`. Conclude with `hq`. Establish `hx` using `ih (g *ᵥ v - v) hv' hq'`. Use `set v' := g *ᵥ v - v with hv'def`. Use `set x := g *ᵥ v' - v' with hxdef`.

Establish `hgv' : g *ᵥ v' = v' + x` using `by rw [hxdef]; abel`. Establish `hgv2 : g *ᵥ v = v + v'` using `by rw [hv'def]; abel`. Establish `e1` using `herm_inv hgU v' v`. Rewrite `e1` using `[hgv', hgv2, herm_add_left, herm_add_right, herm_add_right, herm_inX_perp hv hx, herm_inX_perp hv' hx]`. Establish `h1 : herm (Hpk k r) v' v' = 0` using `by linear_combination e1`.

Establish `e2` using `herm_inv hgU v z`. Establish `hgz' : g *ᵥ z = z + (g *ᵥ z - z)` using `by abel`. Rewrite `e2` using `[hgv2, hgz', herm_add_left, herm_add_right, herm_add_right, herm_perp_inX hv hgz, herm_perp_inX hv' hgz]`. Establish `h2 : herm (Hpk k r) v' z = 0` using `by linear_combination e2`. Conclude with `definite hv' hz hT h1 h2`.
-/
lemma key {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hgU : gᴴ * Hpk k r * g = Hpk k r)
    (hperp : ∀ v, perpX k r v → perpX k r (g *ᵥ v)) (hgz : inX k r (g *ᵥ z - z)) :
    ∀ q : ℕ, ∀ v, perpX k r v → (g - 1) ^ q *ᵥ v = 0 → inX k r (g *ᵥ v - v) := by
  intro q
  induction q with
  | zero =>
    intro v _ hv0
    rw [pow_zero, Matrix.one_mulVec] at hv0
    subst hv0
    intro i _
    simp
  | succ q ih =>
    intro v hv hq
    have hv' : perpX k r (g *ᵥ v - v) := fun i hi => by
      simp only [Pi.sub_apply]
      rw [hperp v hv i hi, hv i hi, sub_zero]
    have hgv : (g - 1) *ᵥ v = g *ᵥ v - v := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    have hq' : (g - 1) ^ q *ᵥ (g *ᵥ v - v) = 0 := by
      rw [← hgv, Matrix.mulVec_mulVec, ← pow_succ]
      exact hq
    have hx := ih (g *ᵥ v - v) hv' hq'
    set v' := g *ᵥ v - v with hv'def
    set x := g *ᵥ v' - v' with hxdef
    have hgv' : g *ᵥ v' = v' + x := by rw [hxdef]; abel
    have hgv2 : g *ᵥ v = v + v' := by rw [hv'def]; abel
    have e1 := herm_inv hgU v' v
    rw [hgv', hgv2, herm_add_left, herm_add_right, herm_add_right, herm_inX_perp hv hx,
      herm_inX_perp hv' hx] at e1
    have h1 : herm (Hpk k r) v' v' = 0 := by linear_combination e1
    have e2 := herm_inv hgU v z
    have hgz' : g *ᵥ z = z + (g *ᵥ z - z) := by abel
    rw [hgv2, hgz', herm_add_left, herm_add_right, herm_add_right, herm_perp_inX hv hgz,
      herm_perp_inX hv' hgz] at e2
    have h2 : herm (Hpk k r) v' z = 0 := by linear_combination e2
    exact definite hv' hz hT h1 h2

/- English proof (translation)
Introduce `i hi`. Simplify using `only [Pi.sub_apply, Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h), sub_eq_zero]`. Distinguish the cases in `hik : i.val ≤ r + k`. Rewrite using `[hm i i hik (Or.inr hi), if_pos rfl, one_mul]`.

Rewrite using `[hv i (by omega), mul_zero]`. Distinguish the cases in `hjk : j.val ≤ r + k`. Rewrite using `[hm i j hjk (Or.inr hi), if_neg (Ne.symm hji), zero_mul]`. Rewrite using `[hv j (by omega), mul_zero]`.
-/
lemma m_perp {k r : ℕ} {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hm : Formalism.QuantumDeterminants.WeylGroupFacts.col k r m) {v : Fin (2 * r + k + 1) → ℂ} (hv : perpX k r v) :
    inX k r (m *ᵥ v - v) := by
  intro i hi
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h), sub_eq_zero]
  · by_cases hik : i.val ≤ r + k
    · rw [hm i i hik (Or.inr hi), if_pos rfl, one_mul]
    · rw [hv i (by omega), mul_zero]
  · by_cases hjk : j.val ≤ r + k
    · rw [hm i j hjk (Or.inr hi), if_neg (Ne.symm hji), zero_mul]
    · rw [hv j (by omega), mul_zero]

/- English proof (translation)
Establish `hx' : x = ∑ a : Fin r, x (eI k r a) • bvec (eI k r a)`. Use function extensionality and compare the values at `i`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Distinguish the cases in `hi : i.val < r`.

Rewrite using `[Finset.sum_eq_single ⟨i.val, hi⟩]`. Establish `e : i = eI k r ⟨i.val, hi⟩` using `Fin.ext rfl`. Rewrite using `[if_pos e, ← e]`. Introduce `a _ ha`. Rewrite using `[if_neg]`.

Introduce `h`. Apply `ha` to reduce the goal to its premises. Use `ext`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [eI] at this`.

Simplify using `only`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[hx i (by omega)]`.

Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `a _`. Rewrite using `[if_neg]`. Introduce `h`.

Apply `hi` to reduce the goal to its premises. Rewrite using `[h]`. Conclude with `a.2`. Rewrite using `[hx']`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`.
-/
lemma inX_mem {k r : ℕ} {x : Fin (2 * r + k + 1) → ℂ} (hx : inX k r x) : x ∈ Xsp k r := by
  have hx' : x = ∑ a : Fin r, x (eI k r a) • bvec (eI k r a) := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hi : i.val < r
    · rw [Finset.sum_eq_single ⟨i.val, hi⟩]
      · have e : i = eI k r ⟨i.val, hi⟩ := Fin.ext rfl
        rw [if_pos e, ← e]
      · intro a _ ha
        rw [if_neg]
        intro h
        apply ha
        ext
        have := congrArg Fin.val h
        simp only [eI] at this
        simp only
        omega
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [hx i (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro a _
      rw [if_neg]
      intro h
      apply hi
      rw [h]
      exact a.2
  rw [hx']
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end PI.StabSplit.UnipW

namespace PI.StabSplit

open UnipW in
/- English proof (translation)
Introduce `k r g hg v hv`. Take `⟨_, h1, h2⟩` from `hg`. Establish `hcol : Formalism.QuantumDeterminants.WeylGroupFacts.col k r g`. Introduce `i j hj hji`. Distinguish the cases in `hjr : j.val < r`.

Establish `h3` using `h1 ⟨j.val, hjr⟩ i (by show j.val ≤ i.val; omega)`. Establish `e : eI k r ⟨j.val, hjr⟩ = j` using `Fin.ext rfl`. Rewrite `h3` using `[e]`. Conclude with `h3`. Conclude with `h2 i j (by omega) hj (by omega)`.

Establish `hperp : UnipW.perpX k r v`. Introduce `i hi`. Establish `hir : 2 * r + k - i.val < r` using `by omega`. Establish `h4` using `hv ⟨2 * r + k - i.val, hir⟩`. Rewrite `h4` using `[herm_coord, Finset.sum_eq_single (eI k r ⟨2 * r + k - i.val, hir⟩)]`.

Establish `hs : sig k r (eI k r ⟨2 * r + k - i.val, hir⟩) = i`. Establish `hc : (eI k r ⟨2 * r + k - i.val, hir⟩).val < r ∨ r + k < (eI k r ⟨2 * r + k - i.val, hir⟩).val` using `Or.inl hir`. Unfold `sig`. Rewrite using `[if_pos hc]`. Apply `Fin.ext` to reduce the goal to its premises.

Use `show 2 * r + k - (2 * r + k - i.val) = i.val`. Use linear arithmetic over natural numbers and integers. Establish `hsg : sgn k r (eI k r ⟨2 * r + k - i.val, hir⟩) = 1`. Establish `hc : ¬ (eI k r ⟨2 * r + k - i.val, hir⟩).val = r + k` using `by show ¬ 2 * r + k - i.val = r + k`. Use linear arithmetic over natural numbers and integers.

Unfold `sgn`. Rewrite using `[if_neg hc]`. Rewrite `h4` using `[hs, hsg]`. Simplify `h4` using `[bvec]`. Introduce `j _ hj`.

Simplify using `[bvec, Pi.single_apply, hj]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `h5` using `m_perp hcol hperp`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`.

Conclude with `inX_mem h5`.
-/
theorem nilpotent_orthogonal_complement : NPerp := by
  intro k r g hg v hv
  obtain ⟨_, h1, h2⟩ := hg
  have hcol : Formalism.QuantumDeterminants.WeylGroupFacts.col k r g := by
    intro i j hj hji
    by_cases hjr : j.val < r
    · have h3 := h1 ⟨j.val, hjr⟩ i (by show j.val ≤ i.val; omega)
      have e : eI k r ⟨j.val, hjr⟩ = j := Fin.ext rfl
      rw [e] at h3
      exact h3
    · exact h2 i j (by omega) hj (by omega)
  have hperp : UnipW.perpX k r v := by
    intro i hi
    have hir : 2 * r + k - i.val < r := by omega
    have h4 := hv ⟨2 * r + k - i.val, hir⟩
    rw [herm_coord, Finset.sum_eq_single (eI k r ⟨2 * r + k - i.val, hir⟩)] at h4
    · have hs : sig k r (eI k r ⟨2 * r + k - i.val, hir⟩) = i := by
        have hc : (eI k r ⟨2 * r + k - i.val, hir⟩).val < r ∨
            r + k < (eI k r ⟨2 * r + k - i.val, hir⟩).val := Or.inl hir
        unfold sig
        rw [if_pos hc]
        apply Fin.ext
        show 2 * r + k - (2 * r + k - i.val) = i.val
        omega
      have hsg : sgn k r (eI k r ⟨2 * r + k - i.val, hir⟩) = 1 := by
        have hc : ¬ (eI k r ⟨2 * r + k - i.val, hir⟩).val = r + k := by
          show ¬ 2 * r + k - i.val = r + k
          omega
        unfold sgn
        rw [if_neg hc]
      rw [hs, hsg] at h4
      simpa [bvec] using h4
    · intro j _ hj
      simp [bvec, Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have h5 := m_perp hcol hperp
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact inX_mem h5

open UnipW in
/- English proof (translation)
Introduce `k r z hzs g hg p hp`. Establish `hz` using `hzs.1`. Establish `hT` using `hzs.2`. Establish `hgU : gᴴ * Hpk k r * g = Hpk k r` using `Sset_UH hg`. Take `⟨u, hu, m, hm, rfl⟩` from `hg`.

Establish `hb` using `Formalism.QuantumDeterminants.WeylGroupFacts.uw_block hu`. Establish `hmc` using `((Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff m).1 hm).2`. Establish `hzp : perpX k r z` using `fun i hi => hz i (Or.inr hi)`. Establish `row_out : ∀ i j, (i.val < r ∨ r + k < i.val) → (u * m) i j = m i j`. Introduce `i j hi`.

Rewrite using `[mul_apply, Finset.sum_eq_single i]`. Rewrite using `[hb.2 i i hi, if_pos rfl, one_mul]`. Introduce `l _ hl`. Rewrite using `[hb.2 i l hi, if_neg (Ne.symm hl), zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Establish `xcol : ∀ i j : Fin (2 * r + k + 1), j.val < r → j.val ≤ i.val → (u * m) i j = if i = j then 1 else 0`. Introduce `i j hj hij`. Distinguish the cases in `hi : i.val < r ∨ r + k < i.val`. Rewrite using `[row_out i j hi]; exact hmc i j (by omega) (Or.inl hij)`.

Establish `hne : i ≠ j` using `by intro h; subst h; omega`. Rewrite using `[if_neg hne, mul_apply]`. Use `Finset.sum_eq_zero (fun l _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hl : l.val < r ∨ r + k < l.val`. Rewrite using `[hb.1 i l hl, if_neg (by intro h; subst h; omega), zero_mul]`.

Rewrite using `[hmc l j (by omega) (Or.inr (by omega)), if_neg (by intro h; subst h; omega), mul_zero]`. Establish `u_fix : ∀ x, inX k r x → u *ᵥ x = x`. Introduce `x hx`. Use extensionality with `i`. Simplify using `only [mulVec, dotProduct]`.

Rewrite using `[Finset.sum_eq_single i]`. Distinguish the cases in `hi : i.val < r`. Rewrite using `[hb.1 i i (Or.inl hi), if_pos rfl, one_mul]`. Rewrite using `[hx i (by omega), mul_zero]`. Introduce `l _ hl`.

Distinguish the cases in `hlr : l.val < r`. Rewrite using `[hb.1 i l (Or.inl hlr), if_neg (Ne.symm hl), zero_mul]`. Rewrite using `[hx l (by omega), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Establish `hperp : ∀ v, perpX k r v → perpX k r ((u * m) *ᵥ v)`. Introduce `v hv i hi`. Establish `h1 : ((u * m) *ᵥ v) i = (m *ᵥ v) i`. Simplify using `only [mulVec, dotProduct]`. Conclude with `Finset.sum_congr rfl (fun j _ => by rw [row_out i j (Or.inr hi)])`.

Establish `h2` using `m_perp hmc hv i (by omega)`. Rewrite `h2` using `[Pi.sub_apply, sub_eq_zero]`. Rewrite using `[h1, h2, hv i hi]`. Establish `hgz : inX k r ((u * m) *ᵥ z - z)`. Establish `hx` using `m_perp hmc hzp`.

Establish `e : (u * m) *ᵥ z - z = m *ᵥ z - z`. Rewrite using `[← mulVec_mulVec]`. Establish `e2 : m *ᵥ z = z + (m *ᵥ z - z)` using `by abel`. Rewrite using `[e2, mulVec_add, hu.2.2, u_fix _ hx]`. Rewrite using `[e]`.

Conclude with `hx`. Establish `hkey` using `key hz hT hgU hperp hgz p`. Use `(Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff _).2 ⟨hgU, ?_⟩` and prove the remaining obligations. Introduce `i j hj hij`. Distinguish the cases in `hjr : j.val < r`.

Conclude with `xcol i j hjr (by omega)`. Establish `hir : r ≤ i.val` using `by omega`. Establish `hbp : perpX k r (bvec j)`. Introduce `l hl`. Simplify using `only [bvec, Pi.single_apply]`.

Rewrite using `[if_neg]`. Introduce `h`. Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers. Establish `h` using `hkey (bvec j) hbp (by rw [hp, zero_mulVec]) i hir`.

Rewrite `h` using `[Pi.sub_apply, sub_eq_zero, mulVec_bvec]`. Establish `h' : (u * m) i j = bvec j i` using `h`. Rewrite using `[h']`. Simplify using `[bvec, Pi.single_apply]`.
-/
theorem unipotent_nilpotent_radical : UnipN := by
  intro k r z hzs g hg p hp
  have hz := hzs.1
  have hT := hzs.2
  have hgU : gᴴ * Hpk k r * g = Hpk k r := Sset_UH hg
  obtain ⟨u, hu, m, hm, rfl⟩ := hg
  have hb := Formalism.QuantumDeterminants.WeylGroupFacts.uw_block hu
  have hmc := ((Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff m).1 hm).2
  have hzp : perpX k r z := fun i hi => hz i (Or.inr hi)
  have row_out : ∀ i j, (i.val < r ∨ r + k < i.val) → (u * m) i j = m i j := by
    intro i j hi
    rw [mul_apply, Finset.sum_eq_single i]
    · rw [hb.2 i i hi, if_pos rfl, one_mul]
    · intro l _ hl; rw [hb.2 i l hi, if_neg (Ne.symm hl), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have xcol : ∀ i j : Fin (2 * r + k + 1), j.val < r → j.val ≤ i.val →
      (u * m) i j = if i = j then 1 else 0 := by
    intro i j hj hij
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [row_out i j hi]; exact hmc i j (by omega) (Or.inl hij)
    · have hne : i ≠ j := by intro h; subst h; omega
      rw [if_neg hne, mul_apply]
      refine Finset.sum_eq_zero (fun l _ => ?_)
      by_cases hl : l.val < r ∨ r + k < l.val
      · rw [hb.1 i l hl, if_neg (by intro h; subst h; omega), zero_mul]
      · rw [hmc l j (by omega) (Or.inr (by omega)), if_neg (by intro h; subst h; omega), mul_zero]
  have u_fix : ∀ x, inX k r x → u *ᵥ x = x := by
    intro x hx
    ext i
    simp only [mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · by_cases hi : i.val < r
      · rw [hb.1 i i (Or.inl hi), if_pos rfl, one_mul]
      · rw [hx i (by omega), mul_zero]
    · intro l _ hl
      by_cases hlr : l.val < r
      · rw [hb.1 i l (Or.inl hlr), if_neg (Ne.symm hl), zero_mul]
      · rw [hx l (by omega), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hperp : ∀ v, perpX k r v → perpX k r ((u * m) *ᵥ v) := by
    intro v hv i hi
    have h1 : ((u * m) *ᵥ v) i = (m *ᵥ v) i := by
      simp only [mulVec, dotProduct]
      exact Finset.sum_congr rfl (fun j _ => by rw [row_out i j (Or.inr hi)])
    have h2 := m_perp hmc hv i (by omega)
    rw [Pi.sub_apply, sub_eq_zero] at h2
    rw [h1, h2, hv i hi]
  have hgz : inX k r ((u * m) *ᵥ z - z) := by
    have hx := m_perp hmc hzp
    have e : (u * m) *ᵥ z - z = m *ᵥ z - z := by
      rw [← mulVec_mulVec]
      have e2 : m *ᵥ z = z + (m *ᵥ z - z) := by abel
      rw [e2, mulVec_add, hu.2.2, u_fix _ hx]
    rw [e]; exact hx
  have hkey := key hz hT hgU hperp hgz p
  refine (Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff _).2 ⟨hgU, ?_⟩
  intro i j hj hij
  by_cases hjr : j.val < r
  · exact xcol i j hjr (by omega)
  · have hir : r ≤ i.val := by omega
    have hbp : perpX k r (bvec j) := by
      intro l hl
      simp only [bvec, Pi.single_apply]
      rw [if_neg]; intro h; subst h; omega
    have h := hkey (bvec j) hbp (by rw [hp, zero_mulVec]) i hir
    rw [Pi.sub_apply, sub_eq_zero, mulVec_bvec] at h
    have h' : (u * m) i j = bvec j i := h
    rw [h']; simp [bvec, Pi.single_apply]

end PI.StabSplit
