import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrimeB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFock
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARUnit

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

abbrev tco (s : Finset (Fin (n * n))) (y : TensorProduct ℂ M (Fock n)) : M :=
  tcoef ((fockBasis n).coord s) y

def tform (y y' : TensorProduct ℂ M (Fock n)) : ℂ :=
  ∑ s, inner ℂ (tco s y) (tco s y')

/- English proof (translation)
Unfold `tform`. Rewrite using `[star_sum]`. Conclude with `sum_congr rfl fun s _ => inner_conj_symm _ _`.
-/
theorem tform_conj (y y' : TensorProduct ℂ M (Fock n)) : star (tform y y') = tform y' y := by
  unfold tform
  rw [star_sum]
  exact sum_congr rfl fun s _ => inner_conj_symm _ _

/- English proof (translation)
Unfold `tform`. Simplify using `only [map_sum, sum_inner]`. Conclude with `sum_comm`.
-/
theorem tform_sum_left {ι : Type*} (t : Finset ι) (f : ι → TensorProduct ℂ M (Fock n))
    (y' : TensorProduct ℂ M (Fock n)) : tform (∑ i ∈ t, f i) y' = ∑ i ∈ t, tform (f i) y' := by
  unfold tform
  simp only [map_sum, sum_inner]
  exact sum_comm

/- English proof (translation)
Unfold `tform`. Simplify using `only [map_sum, inner_sum]`. Conclude with `sum_comm`.
-/
theorem tform_sum_right {ι : Type*} (t : Finset ι) (f : ι → TensorProduct ℂ M (Fock n))
    (y : TensorProduct ℂ M (Fock n)) : tform y (∑ i ∈ t, f i) = ∑ i ∈ t, tform y (f i) := by
  unfold tform
  simp only [map_sum, inner_sum]
  exact sum_comm

/- English proof (translation)
Unfold `tform`. Simplify using `[inner_neg_left]`.
-/
theorem tform_neg_left (y y' : TensorProduct ℂ M (Fock n)) : tform (-y) y' = -tform y y' := by
  unfold tform
  simp [inner_neg_left]

/- English proof (translation)
Unfold `tform`. Simplify using `[inner_neg_right]`.
-/
theorem tform_neg_right (y y' : TensorProduct ℂ M (Fock n)) : tform y (-y') = -tform y y' := by
  unfold tform
  simp [inner_neg_right]

/- English proof (translation)
Unfold `tform`. Simplify using `[sum_add_distrib]`.
-/
theorem tform_add_left (y z y' : TensorProduct ℂ M (Fock n)) :
    tform (y + z) y' = tform y y' + tform z y' := by
  unfold tform
  simp [sum_add_distrib]

/- English proof (translation)
Unfold `tform`. Simplify using `[sum_add_distrib]`.
-/
theorem tform_add_right (y y' z : TensorProduct ℂ M (Fock n)) :
    tform y (y' + z) = tform y y' + tform y z := by
  unfold tform
  simp [sum_add_distrib]

/- English proof (translation)
Unfold `tform`. Simplify using `[mul_sum]`.
-/
theorem tform_smul_right (c : ℂ) (y y' : TensorProduct ℂ M (Fock n)) :
    tform y (c • y') = c * tform y y' := by
  unfold tform
  simp [mul_sum]

/- English proof (translation)
Unfold `tform`. Rewrite using `[Complex.re_sum]`. Use `sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[inner_self_eq_norm_sq_to_K]`. Use `norm_cast`.
-/
theorem tform_self_re (y : TensorProduct ℂ M (Fock n)) : (tform y y).re = ∑ s, ‖tco s y‖ ^ 2 := by
  unfold tform
  rw [Complex.re_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/- English proof (translation)
Rewrite using `[tform_self_re]`. Conclude with `sum_nonneg fun s _ => sq_nonneg _`.
-/
theorem tform_self_re_nonneg (y : TensorProduct ℂ M (Fock n)) : 0 ≤ (tform y y).re := by
  rw [tform_self_re]
  exact sum_nonneg fun s _ => sq_nonneg _

/- English proof (translation)
Break down `(tform_self_re_nonneg y).lt_or_eq with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Rewrite `h` using `[tform_self_re]`. Establish `h0 : ∀ s, tcoef ((fockBasis n).coord s) y = 0`.

Introduce `s`. Establish `hs` using `(sum_eq_zero_iff_of_nonneg (fun t _ => sq_nonneg ‖tco t y‖)).mp h.symm s (mem_univ s)`. Conclude with `norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hs)`. Apply `hy` to reduce the goal to its premises. Rewrite using `[tcoef_expand y]`.

Conclude with `sum_eq_zero fun s _ => by rw [h0 s, TensorProduct.zero_tmul]`.
-/
theorem tform_self_re_pos {y : TensorProduct ℂ M (Fock n)} (hy : y ≠ 0) : 0 < (tform y y).re := by
  rcases (tform_self_re_nonneg y).lt_or_eq with h | h
  · exact h
  exfalso
  rw [tform_self_re] at h
  have h0 : ∀ s, tcoef ((fockBasis n).coord s) y = 0 := by
    intro s
    have hs := (sum_eq_zero_iff_of_nonneg (fun t _ => sq_nonneg ‖tco t y‖)).mp h.symm s (mem_univ s)
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hs)
  apply hy
  rw [tcoef_expand y]
  exact sum_eq_zero fun s _ => by rw [h0 s, TensorProduct.zero_tmul]

/- English proof (translation)
The claim follows from `tcoef_map_left _ T y`.
-/
theorem tco_map_left (T : Module.End ℂ M) (s : Finset (Fin (n * n))) (y : TensorProduct ℂ M (Fock n)) :
    tco s (TensorProduct.map T LinearMap.id y) = T (tco s y) :=
  tcoef_map_left _ T y

/- English proof (translation)
Use `conv_lhs => rw [tcoef_expand y]`. Simplify using `only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply, tcoef_tmul, Module.Basis.coord_apply]`.
-/
theorem tco_lTensor (g : Module.End ℂ (Fock n)) (s : Finset (Fin (n * n))) (y : TensorProduct ℂ M (Fock n)) :
    tco s (TensorProduct.map LinearMap.id g y) =
      ∑ t, (fockBasis n).repr (g (fockBasis n t)) s • tco t y := by
  conv_lhs => rw [tcoef_expand y]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply, tcoef_tmul, Module.Basis.coord_apply]

/- English proof (translation)
Unfold `tform eT`. Simplify using `only [tco_map_left, mul_sum]`. Conclude with `sum_congr rfl fun s _ => hU a b _ _`.
-/
theorem tform_eT {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E) (a b : Fin n)
    (y y' : TensorProduct ℂ M (Fock n)) :
    tform (eT E a b y) y' = adjSign ε a b * tform y (eT E b a y') := by
  unfold tform eT
  simp only [tco_map_left, mul_sum]
  exact sum_congr rfl fun s _ => hU a b _ _

/- English proof (translation)
Unfold `tform cpT cmT`. Simplify using `only [tco_lTensor, sum_inner, inner_sum, inner_smul_left, inner_smul_right]`. Rewrite using `[sum_comm]`. Use `sum_congr rfl fun t _ => sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Use `congr 1`.

Establish `h1` using `lf_repr_cp_star (i, a) t s`. Establish `h2` using `lf_repr_cm_eq (i, a) s t`. Rewrite using `[h2, starRingEnd_apply]`. Conclude with `h1`.
-/
theorem tform_cpT (i a : Fin n) (y y' : TensorProduct ℂ M (Fock n)) :
    tform (cpT i a y) y' = tform y (cmT i a y') := by
  unfold tform cpT cmT
  simp only [tco_lTensor, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => sum_congr rfl fun s _ => ?_
  congr 1
  have h1 := lf_repr_cp_star (i, a) t s
  have h2 := lf_repr_cm_eq (i, a) s t
  rw [h2, starRingEnd_apply]
  exact h1

/- English proof (translation)
Rewrite using `[← tform_conj y' (cmT i a y), ← tform_cpT, tform_conj]`.
-/
theorem tform_cmT (i a : Fin n) (y y' : TensorProduct ℂ M (Fock n)) :
    tform (cmT i a y) y' = tform y (cpT i a y') := by
  rw [← tform_conj y' (cmT i a y), ← tform_cpT, tform_conj]

/- English proof (translation)
Unfold `dOp dOp'`. Simplify using `only [LinearMap.sum_apply, LinearMap.neg_apply, tform_sum_left, tform_neg_right, tform_sum_right, Module.End.mul_apply, ← sum_neg_distrib]`. Use `sum_congr rfl fun i hi => sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Simplify using `only [plusIdx, minusIdx, mem_filter, mem_univ, true_and] at hi ha`. Rewrite using `[tform_eT hU, tform_cpT]`.

Establish `hc : cmT i a (eT E i a y') = eT E i a (cmT i a y')`. Use `LinearMap.congr_fun ((eT_commutesCAR (n := n) E) i a i a).2 y'` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Conclude with `this.symm`. Rewrite using `[hc]`.

Simplify using `[adjSign, hi, ha]`.
-/
theorem tform_dOp {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E)
    (y y' : TensorProduct ℂ M (Fock n)) :
    tform (dOp ε (eT E) cpT y) y' = tform y (dOp' ε (eT E) cmT y') := by
  unfold dOp dOp'
  simp only [LinearMap.sum_apply, LinearMap.neg_apply, tform_sum_left, tform_neg_right, tform_sum_right,
    Module.End.mul_apply, ← sum_neg_distrib]
  refine sum_congr rfl fun i hi => sum_congr rfl fun a ha => ?_
  simp only [plusIdx, minusIdx, mem_filter, mem_univ, true_and] at hi ha
  rw [tform_eT hU, tform_cpT]
  have hc : cmT i a (eT E i a y') = eT E i a (cmT i a y') := by
    have := LinearMap.congr_fun ((eT_commutesCAR (n := n) E) i a i a).2 y'
    simp only [Module.End.mul_apply] at this
    exact this.symm
  rw [hc]
  simp [adjSign, hi, ha]

/- English proof (translation)
Establish `h' : tform (dOp' ε (eT E) cmT y) y' = tform y (dOp ε (eT E) cpT y')`. Rewrite using `[← tform_conj y' (dOp' ε (eT E) cmT y), ← tform_dOp hU, tform_conj]`. Rewrite using `[LinearMap.add_apply, LinearMap.add_apply, tform_add_left, tform_add_right, tform_dOp hU, h', add_comm]`.
-/
theorem tform_D {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E)
    (y y' : TensorProduct ℂ M (Fock n)) :
    tform ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y) y' =
      tform y ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y') := by
  have h' : tform (dOp' ε (eT E) cmT y) y' = tform y (dOp ε (eT E) cpT y') := by
    rw [← tform_conj y' (dOp' ε (eT E) cmT y), ← tform_dOp hU, tform_conj]
  rw [LinearMap.add_apply, LinearMap.add_apply, tform_add_left, tform_add_right, tform_dOp hU, h', add_comm]

section Shift

/- English proof (translation)
Unfold `root`. Simplify using `only [Pi.sub_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem ssh_root_le (a b c : Fin n) : root a b c ≤ 1 := by
  unfold root
  simp only [Pi.sub_apply, Pi.single_apply]
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `root`. Simplify using `only [Pi.sub_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem ssh_root_ge (a b c : Fin n) : -1 ≤ root a b c := by
  unfold root
  simp only [Pi.sub_apply, Pi.single_apply]
  split_ifs <;> norm_num

/- English proof (translation)
Establish `h` using `lfD_cnt (fun c => ε c ≠ ε x) hxy`. Establish `h1 : (univ.filter fun c => c = x ∧ ε c ≠ ε x).card = 0`. Rewrite using `[lfD_single]`. Simplify using the standard rewrite rules. Establish `h2 : (univ.filter fun c => c = y ∧ ε c ≠ ε x).card = 0`.

Rewrite using `[lfD_single]`. Simplify using `[he]`. Establish `h3 : (univ.filter fun c => x < c ∧ c < y ∧ ε c ≠ ε x).card = 0`. Rewrite using `[card_eq_zero, filter_eq_empty_iff]`. Introduce `c _ hc'`.

Conclude with `hc c hc'.1 hc'.2.1`. Simplify using `only [rhoN, ← he]`. Rewrite `h` using `[h1, h2, h3]`. Establish `h'` using `congrArg (Nat.cast : ℕ → ℝ) h`. Move the coercions through the operations in `at h'`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ssh_rhoN_consec (ε : Fin n → Bool) {x y : Fin n} (hxy : x < y) (he : ε x = ε y)
    (hc : ∀ c, x < c → c < y → False) : rhoN ε x = rhoN ε y := by
  have h := lfD_cnt (fun c => ε c ≠ ε x) hxy
  have h1 : (univ.filter fun c => c = x ∧ ε c ≠ ε x).card = 0 := by
    rw [lfD_single]; simp
  have h2 : (univ.filter fun c => c = y ∧ ε c ≠ ε x).card = 0 := by
    rw [lfD_single]; simp [he]
  have h3 : (univ.filter fun c => x < c ∧ c < y ∧ ε c ≠ ε x).card = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro c _ hc'
    exact hc c hc'.1 hc'.2.1
  simp only [rhoN, ← he]
  rw [h1, h2, h3] at h
  have h' := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h'
  linarith

/- English proof (translation)
Establish `hF : Formalism.REAL.KRel ε E` using `fun a b c d _ _ => hE a b c d`. Consider the cases of `n with`. Consider the case `zero => exact fun x => x.elim0`. Consider the case `succ m`. Rewrite using `[Fin.strictAnti_iff_succ_lt]`.

Introduce `i`. Establish `hxy : i.castSucc < i.succ` using `Fin.castSucc_lt_succ`. Establish `hl` using `hmono hxy`. Simplify using `only [Pi.sub_apply]`. Distinguish the cases in `he : ε i.castSucc = ε i.succ`.

Take `⟨N, hN⟩` from `HW.kIrrHW_int ε hF hW _ _ hxy he`. Establish `hbet : ∀ c, i.castSucc < c → c < i.succ → False`. Introduce `c h1 h2`. Rewrite `h1`, `h2` using `[Fin.lt_def]`. Simplify using `only [Fin.val_castSucc, Fin.val_succ] at h1 h2`.

Use linear arithmetic over natural numbers and integers. Establish `hC` using `HW.rhoC_consec ε hxy he (fun c h1 h2 => (hbet c h1 h2).elim)`. Establish `hN'` using `ssh_rhoN_consec ε hxy he hbet`. Simplify using `only [lowK, Pi.add_apply, Pi.sub_apply] at hN`. Establish `: (0 : ℝ) ≤ N` using `Nat.cast_nonneg _`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hg` using `hh _ _ he`. Rewrite `hg` using `[abs_of_pos (sub_pos.mpr hl)]`. Use `ssh_root_le a b i.castSucc` as an intermediate fact. Use `ssh_root_ge a b i.succ` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ssh_strictAnti {ε : Fin n → Bool} {lam : Fin n → ℝ} (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) (h2 : 2 < h) {N : Type*} [AddCommGroup N] [Module ℂ N]
    {E : Fin n → Fin n → Module.End ℂ N} (hE : IsGlRep E) (a b : Fin n) {W : Submodule ℂ N}
    (hW : IsKIrrHW ε E (lowK ε (lam - root a b)) W) : StrictAnti (lam - root a b) := by
  have hF : Formalism.REAL.KRel ε E := fun a b c d _ _ => hE a b c d
  cases n with
  | zero => exact fun x => x.elim0
  | succ m =>
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    have hxy : i.castSucc < i.succ := Fin.castSucc_lt_succ
    have hl := hmono hxy
    simp only [Pi.sub_apply]
    by_cases he : ε i.castSucc = ε i.succ
    · obtain ⟨N, hN⟩ := HW.kIrrHW_int ε hF hW _ _ hxy he
      have hbet : ∀ c, i.castSucc < c → c < i.succ → False := by
        intro c h1 h2
        rw [Fin.lt_def] at h1 h2
        simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
        omega
      have hC := HW.rhoC_consec ε hxy he (fun c h1 h2 => (hbet c h1 h2).elim)
      have hN' := ssh_rhoN_consec ε hxy he hbet
      simp only [lowK, Pi.add_apply, Pi.sub_apply] at hN
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      linarith
    · have hg := hh _ _ he
      rw [abs_of_pos (sub_pos.mpr hl)] at hg
      have := ssh_root_le a b i.castSucc
      have := ssh_root_ge a b i.succ
      linarith

/- English proof (translation)
Apply `TensorProduct.ext'` to reduce the goal to its premises. Introduce `m f`. Simplify using `[casimir, eT, LinearMap.sum_apply, TensorProduct.sum_tmul]`.
-/
theorem ssh_casimir_eT {N : Type*} [AddCommGroup N] [Module ℂ N] (E : Fin n → Fin n → Module.End ℂ N) :
    casimir (eT (n := n) E) = TensorProduct.map (casimir E) LinearMap.id := by
  apply TensorProduct.ext'
  intro m f
  simp [casimir, eT, LinearMap.sum_apply, TensorProduct.sum_tmul]

/- English proof (translation)
Establish `e : nsq (lam - root a b) = nsq lam - 2 * dot (root a b) lam + dot (root a b) (root a b)`. Unfold `nsq dot`. Rewrite using `[mul_sum, ← sum_sub_distrib, ← sum_add_distrib]`. Use `sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.sub_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, dot_root_left, dot_root_left]`. Establish `ha : root a b a = 1` using `by simp [root, hab]`. Establish `hb : root a b b = -1` using `by simp [root, Ne.symm hab]`. Rewrite using `[ha, hb]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ssh_nsq_sub_root (lam : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b) :
    nsq (lam - root a b) = nsq lam - 2 * (lam a - lam b) + 2 := by
  have e : nsq (lam - root a b) = nsq lam - 2 * dot (root a b) lam + dot (root a b) (root a b) := by
    unfold nsq dot
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun c _ => ?_
    simp only [Pi.sub_apply]
    ring
  rw [e, dot_root_left, dot_root_left]
  have ha : root a b a = 1 := by simp [root, hab]
  have hb : root a b b = -1 := by simp [root, Ne.symm hab]
  rw [ha, hb]
  ring

end Shift

end ReciprocityTheory.ChartRestriction.DS
