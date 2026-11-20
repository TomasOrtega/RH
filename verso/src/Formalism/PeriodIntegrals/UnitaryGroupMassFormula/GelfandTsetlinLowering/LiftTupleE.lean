import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleD

noncomputable section

namespace PI.WGL.LTE

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD

/- English proof (translation)
Unfold `dualWeyl at hf hg ⊢`. Rewrite `hf`, `hg`, the goal using `[Submodule.mem_inf]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite `hf`, `hg`, the goal using `[mem_weightedHomogeneousSubmodule]`. Conclude with `hf.1.mul hg.1`.

Establish `h1` using `hf.2`. Establish `h2` using `hg.2`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero] at h1 h2 ⊢`. Introduce `l j hlj`. Rewrite using `[map_mul, map_mul, h1 l j hlj, h2 l j hlj]`.
-/
private theorem mul_mem_dualWeyl_int {N : ℕ} {ν ν' : Fin N → ℕ} {f g : MvPolynomial (Fin N × Fin N) ℤ}
    (hf : f ∈ dualWeyl ℤ N N ν) (hg : g ∈ dualWeyl ℤ N N ν') : f * g ∈ dualWeyl ℤ N N (ν + ν') := by
  unfold dualWeyl at hf hg ⊢
  rw [Submodule.mem_inf] at hf hg ⊢
  refine ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule] at hf hg ⊢
    exact hf.1.mul hg.1
  · have h1 := hf.2
    have h2 := hg.2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
      sub_eq_zero] at h1 h2 ⊢
    intro l j hlj
    rw [map_mul, map_mul, h1 l j hlj, h2 l j hlj]

/- English proof (translation)
Unfold `dualWeyl`. Rewrite using `[Submodule.mem_inf]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_weightedHomogeneousSubmodule]`. Conclude with `isWeightedHomogeneous_one ℤ _`.

Simplify using `[Submodule.mem_iInf, LinearMap.mem_ker]`.
-/
private theorem one_mem_dualWeyl_int {N : ℕ} : (1 : MvPolynomial (Fin N × Fin N) ℤ) ∈ dualWeyl ℤ N N 0 := by
  unfold dualWeyl
  rw [Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_one ℤ _
  · simp [Submodule.mem_iInf, LinearMap.mem_ker]

/- English proof (translation)
Establish `h` using `bidetMem ℤ N N 1 (fun _ => s) (fun _ => hs) (fun _ => I)`. Establish `e1 : bideterminant ℤ (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) = initMinor ℤ (n` using `N) I hs := by`. Unfold `bideterminant`. Simplify using the standard rewrite rules. Establish `e2 : shapeDeg (n` using `N) (fun _ : Fin 1 => s) = initW N s := by`.

Use function extensionality and compare the values at `t`. Unfold `shapeDeg initW`. Apply the tactic sequence `split_ifs with ht <;> simp [ht]`. Rewrite `h` using `[e1, e2]`. Conclude with `h`.
-/
private theorem initMinor_mem_dualWeyl_int_initW {N s : ℕ} (I : Fin s → Fin N) (hs : s ≤ N) :
    initMinor ℤ I hs ∈ dualWeyl ℤ N N (initW N s) := by
  have h := bidetMem ℤ N N 1 (fun _ => s) (fun _ => hs) (fun _ => I)
  have e1 : bideterminant ℤ (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) = initMinor ℤ (n := N) I hs := by
    unfold bideterminant
    simp
  have e2 : shapeDeg (n := N) (fun _ : Fin 1 => s) = initW N s := by
    funext t
    unfold shapeDeg initW
    split_ifs with ht <;> simp [ht]
  rw [e1, e2] at h
  exact h

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, zero_smul]`. Conclude with `one_mem_dualWeyl_int`. Consider the case `succ k ih => rw [pow_succ, succ_nsmul]`. Conclude with `mul_mem_dualWeyl_int ih hf`.
-/
theorem pow_memZ {N : ℕ} (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) ℤ)
    (hf : f ∈ dualWeyl ℤ N N ν) (k : ℕ) : f ^ k ∈ dualWeyl ℤ N N (k • ν) := by
  induction k with
  | zero => rw [pow_zero, zero_smul]; exact one_mem_dualWeyl_int
  | succ k ih => rw [pow_succ, succ_nsmul]; exact mul_mem_dualWeyl_int ih hf

/- English proof (translation)
Use `revert hf`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Simplify using `using (one_mem_dualWeyl_int (N := N))`. Introduce `a s ha ih hf`.

Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `mul_mem_dualWeyl_int (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))`.
-/
theorem prod_memZ {N : ℕ} {ι : Type*} (s : Finset ι) (ν : ι → Fin N → ℕ) (f : ι → MvPolynomial (Fin N × Fin N) ℤ)
    (hf : ∀ i ∈ s, f i ∈ dualWeyl ℤ N N (ν i)) :
    ∏ i ∈ s, f i ∈ dualWeyl ℤ N N (∑ i ∈ s, ν i) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using (one_mem_dualWeyl_int (N := N))
  · intro a s ha ih hf
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul_mem_dualWeyl_int (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Use `split_ifs`. Conclude with `pow_memZ _ f hf e`. Simplify using `using (one_mem_dualWeyl_int (N := N))`.
-/
theorem ite_pow_memZ {N s : ℕ} (c : Prop) [Decidable c] (f : MvPolynomial (Fin N × Fin N) ℤ)
    (hf : f ∈ dualWeyl ℤ N N (initW N s)) (e : ℕ) :
    (if c then f ^ e else 1) ∈ dualWeyl ℤ N N ((if c then e else 0) • initW N s) := by
  split_ifs
  · exact pow_memZ _ f hf e
  · simpa using (one_mem_dualWeyl_int (N := N))

def colWt {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (L : Finset (Fin K)) : Fin N → ℕ :=
  (∑ i : Fin n, ((if i.1 + 1 = n then (aa h lam sg i).toNat else 0) • initW N (i.1 + 1) +
    (if i.1 = 0 then (bb h lam sg i).toNat else 0) • initW N (i.1 + 1))) +
  ∑ k : Fin K, (if k ∈ L then initW N (sz k + 1) else initW N (sz k))

/- English proof (translation)
Establish `hlp : ∀ (s : ℕ) (hr : s ≤ N) (hc : s ≤ N), lpMinor ℤ s hr hc ∈ dualWeyl ℤ N N (initW N s)` using `fun s hr hc => initMinor_mem_dualWeyl_int_initW (Fin.castLE hr) hc`. Unfold `Mlift colWt`. Apply `mul_mem_dualWeyl_int` to reduce the goal to its premises. Unfold `C0`. Use `prod_memZ Finset.univ _ _ fun i _ => ?_` and prove the remaining obligations.

Conclude with `mul_mem_dualWeyl_int (ite_pow_memZ _ _ (hlp _ _ _) _) (ite_pow_memZ _ _ (initMinor_mem_dualWeyl_int_initW _ _) _)`. Use `prod_memZ Finset.univ _ _ fun k _ => ?_ split_ifs` and prove the remaining obligations. Unfold `lif`. Conclude with `initMinor_mem_dualWeyl_int_initW _ _`. Unfold `unl`.

Conclude with `initMinor_mem_dualWeyl_int_initW _ _`.
-/
theorem Mlift_mem_colWt {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ}
    (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K)) (I : ∀ k, Fin (sz k) → Fin n) :
    Mlift h lam sg sz hsz L I ∈ dualWeyl ℤ N N (colWt h lam sg sz L) := by
  have hlp : ∀ (s : ℕ) (hr : s ≤ N) (hc : s ≤ N), lpMinor ℤ s hr hc ∈ dualWeyl ℤ N N (initW N s) :=
    fun s hr hc => initMinor_mem_dualWeyl_int_initW (Fin.castLE hr) hc
  unfold Mlift colWt
  apply mul_mem_dualWeyl_int
  · unfold C0
    refine prod_memZ Finset.univ _ _ fun i _ => ?_
    exact mul_mem_dualWeyl_int (ite_pow_memZ _ _ (hlp _ _ _) _) (ite_pow_memZ _ _ (initMinor_mem_dualWeyl_int_initW _ _) _)
  · refine prod_memZ Finset.univ _ _ fun k _ => ?_
    split_ifs
    · unfold lif
      exact initMinor_mem_dualWeyl_int_initW _ _
    · unfold unl
      exact initMinor_mem_dualWeyl_int_initW _ _

/- English proof (translation)
Substitute `h` using the available equality. Establish `hds : lam.detShift = lam.w ⟨n, by omega⟩`. Unfold `DomWeight.detShift`. Rewrite using `[dif_pos (by omega)]`. Conclude with `congrArg lam.w (Fin.ext (by simp))`.

Establish `hle : lam.w ⟨n, by omega⟩ ≤ lam.w ⟨t, ht⟩` using `lam.anti (Fin.le_iff_val_le_val.mpr (by show t ≤ n; omega))`. Unfold `DomWeight.natW`. Rewrite using `[hds]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lam_natW_val {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (t : ℕ) (ht : t < N) :
    ((lam.natW ⟨t, ht⟩ : ℕ) : ℤ) = lam.w ⟨t, ht⟩ - lam.w ⟨n, by omega⟩ := by
  subst h
  have hds : lam.detShift = lam.w ⟨n, by omega⟩ := by
    unfold DomWeight.detShift
    rw [dif_pos (by omega)]
    exact congrArg lam.w (Fin.ext (by simp))
  have hle : lam.w ⟨n, by omega⟩ ≤ lam.w ⟨t, ht⟩ :=
    lam.anti (Fin.le_iff_val_le_val.mpr (by show t ≤ n; omega))
  unfold DomWeight.natW
  rw [hds]
  omega

/- English proof (translation)
Substitute `h` using the available equality. Unfold `DomWeight.detShift`. Rewrite using `[dif_pos (by omega)]`. Conclude with `congrArg lam.w (Fin.ext (by simp))`.
-/
theorem lam_detShift {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) :
    lam.detShift = lam.w ⟨n, by omega⟩ := by
  subst h
  unfold DomWeight.detShift
  rw [dif_pos (by omega)]
  exact congrArg lam.w (Fin.ext (by simp))

/- English proof (translation)
Unfold `DomWeight.detShift`. Rewrite using `[dif_pos hn]`.
-/
theorem sg_detShift {n : ℕ} (sg : DomWeight n) (hn : 0 < n) :
    sg.detShift = sg.w ⟨n - 1, by omega⟩ := by
  unfold DomWeight.detShift
  rw [dif_pos hn]

/- English proof (translation)
Establish `h2` using `(hI ⟨n - 1, by omega⟩).2`. Establish `e : lam.w ⟨(⟨n - 1, by omega⟩ : Fin n).1 + 1, by omega⟩ = lam.w ⟨n, by omega⟩` using `congrArg lam.w (Fin.ext (by simp only; omega))`. Unfold `aa`. Use linear arithmetic over natural numbers and integers.
-/
theorem aLast_val {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (hn : 0 < n) :
    (((aa h lam sg ⟨n - 1, by omega⟩).toNat : ℕ) : ℤ) = sg.w ⟨n - 1, by omega⟩ - lam.w ⟨n, by omega⟩ := by
  have h2 := (hI ⟨n - 1, by omega⟩).2
  have e : lam.w ⟨(⟨n - 1, by omega⟩ : Fin n).1 + 1, by omega⟩ = lam.w ⟨n, by omega⟩ :=
    congrArg lam.w (Fin.ext (by simp only; omega))
  unfold aa
  omega

/- English proof (translation)
Establish `h1` using `(hI ⟨t, ht⟩).1`. Establish `e : lam.w ⟨(⟨t, ht⟩ : Fin n).1, by omega⟩ = lam.w ⟨t, by omega⟩` using `rfl`. Unfold `bb`. Use linear arithmetic over natural numbers and integers.
-/
theorem b_val {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (t : ℕ) (ht : t < n) :
    (((bb h lam sg ⟨t, ht⟩).toNat : ℕ) : ℤ) = lam.w ⟨t, by omega⟩ - sg.w ⟨t, ht⟩ := by
  have h1 := (hI ⟨t, ht⟩).1
  have e : lam.w ⟨(⟨t, ht⟩ : Fin n).1, by omega⟩ = lam.w ⟨t, by omega⟩ := rfl
  unfold bb
  omega

/- English proof (translation)
Use function extensionality and compare the values at `t`. Take `⟨tv, htv⟩` from `t`. Unfold `colWt`. Simplify using `only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]`. Establish `hP : (∑ i : Fin n, (if i.1 + 1 = n then (aa h lam sg i).toNat else 0) * initW N (i.1 + 1) ⟨tv, htv⟩) = if hn : n - 1 < n then (aa h lam sg ⟨n - 1, hn⟩).toNat * initW N (n - 1 + 1) ⟨tv, htv⟩ else 0`.

Rewrite using `[← sum_ite_val (fun i : Fin n => (aa h lam sg i).toNat * initW N (i.1 + 1) ⟨tv, htv⟩) (n - 1)]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Use `i.2` as an intermediate fact. Distinguish the cases in `hi : i.1 + 1 = n`.

Rewrite using `[if_pos hi, if_pos (by omega)]`. Rewrite using `[if_neg hi, if_neg (by omega), zero_mul]`. Establish `hQ : (∑ i : Fin n, (if i.1 = 0 then (bb h lam sg i).toNat else 0) * initW N (i.1 + 1) ⟨tv, htv⟩) = if hn : 0 < n then (bb h lam sg ⟨0, hn⟩).toNat * initW N (0 + 1) ⟨tv, htv⟩ else 0`. Rewrite using `[← sum_ite_val (fun i : Fin n => (bb h lam sg i).toNat * initW N (i.1 + 1) ⟨tv, htv⟩) 0]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `i _`. Distinguish the cases in `hi : i.1 = 0`. Rewrite using `[if_pos hi, if_pos hi]`. Rewrite using `[if_neg hi, if_neg hi, zero_mul]`. Establish `hK : (∑ k : Fin K, (if k ∈ L then initW N (sz k + 1) else initW N (sz k)) ⟨tv, htv⟩) = (Finset.univ.filter fun k => tv < sz k).card + (Finset.univ.filter fun k => k ∈ L ∧ sz k = tv).card`.

Rewrite using `[Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k _`. Distinguish the cases in `hk : k ∈ L`. Apply the tactic sequence `simp only [hk, if_true, true_and, initW] split_ifs <;> omega`.

Apply the tactic sequence `simp only [hk, if_false, false_and, initW] split_ifs <;> omega`. Rewrite using `[hP, hQ, hK]`. Distinguish the cases in `htn : tv < n`. Establish `hn : 0 < n` using `by omega`. Establish `h1` using `card_lt_sz sg sz hshape ⟨tv, htn⟩`.

Establish `h2` using `hL.2 ⟨tv, htn⟩`. Simplify using `only at h1 h2`. Rewrite using `[h1, h2, dif_pos (by omega), dif_pos hn]`. Establish `e1` using `natW_sg_val sg ⟨tv, htn⟩`. Establish `e2` using `lam_natW_val h lam tv htv`.

Establish `e3` using `aLast_val h lam sg hI hn`. Establish `e4` using `b_val h lam sg hI tv htn`. Establish `hw1 : initW N (n - 1 + 1) ⟨tv, htv⟩ = 1` using `by simp only [initW]; rw [if_pos (by simp; omega)]`. Rewrite using `[hw1, mul_one]`. Distinguish the cases in `ht0 : tv = 0`.

Substitute `ht0` using the available equality. Establish `hw2 : initW N (0 + 1) ⟨0, htv⟩ = 1` using `by simp [initW]`. Rewrite using `[hw2, mul_one, if_pos rfl]`. Simplify using `only at e1 e2 e3 e4 ⊢`. Use `sg.anti (show (⟨0, htn⟩ : Fin n) ≤ ⟨n - 1, by omega⟩ by rw [Fin.le_def]; simp)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hw2 : initW N (0 + 1) ⟨tv, htv⟩ = 0` using `by simp only [initW]; rw [if_neg (by simp; omega)]`. Rewrite using `[hw2, mul_zero, if_neg ht0]`. Simplify using `only at e1 e2 e3 e4 ⊢`. Use linear arithmetic over natural numbers and integers.

Establish `htn' : tv = n` using `by omega`. Substitute `htn'` using the available equality. Establish `h1 : (Finset.univ.filter fun k => tv < sz k).card = 0`. Rewrite using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Introduce `k _`.

Use `hsz k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h2 : (Finset.univ.filter fun k => k ∈ L ∧ sz k = tv).card = 0`. Rewrite using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Introduce `k _ hk`.

Use `hL.1 k hk.1` as an intermediate fact. Apply the tactic sequence `rcases sz_lt sg sz hsz hshape k with h3 | h3 <;> omega`. Rewrite using `[h1, h2]`. Establish `e2` using `lam_natW_val h lam tv htv`. Establish `hz : lam.natW ⟨tv, htv⟩ = 0`.

Establish `: (⟨tv, htv⟩ : Fin N) = ⟨tv, by omega⟩` using `rfl`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hz]`. Establish `hw1 : ∀ j, j ≤ tv → initW N j ⟨tv, htv⟩ = 0`. Introduce `j hj; simp only [initW]; rw [if_neg (by simp; omega)]`.

Use `split_ifs with ha hb`. Rewrite using `[hw1 _ (by omega), hw1 _ (by omega)]; simp`. Rewrite using `[hw1 _ (by omega)]; simp`. Rewrite using `[hw1 _ (by omega)]; simp`. Simplify using the standard rewrite rules.
-/
theorem colWt_eq {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (hshape : shapeDeg sz = sg.natW) (L : Finset (Fin K))
    (hL : GoodL h lam sg sz L) : colWt h lam sg sz L = lam.natW := by
  classical
  funext t
  obtain ⟨tv, htv⟩ := t
  unfold colWt
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]

  have hP : (∑ i : Fin n, (if i.1 + 1 = n then (aa h lam sg i).toNat else 0) * initW N (i.1 + 1) ⟨tv, htv⟩) =
      if hn : n - 1 < n then (aa h lam sg ⟨n - 1, hn⟩).toNat * initW N (n - 1 + 1) ⟨tv, htv⟩ else 0 := by
    rw [← sum_ite_val (fun i : Fin n => (aa h lam sg i).toNat * initW N (i.1 + 1) ⟨tv, htv⟩) (n - 1)]
    apply Finset.sum_congr rfl
    intro i _
    have := i.2
    by_cases hi : i.1 + 1 = n
    · rw [if_pos hi, if_pos (by omega)]
    · rw [if_neg hi, if_neg (by omega), zero_mul]
  have hQ : (∑ i : Fin n, (if i.1 = 0 then (bb h lam sg i).toNat else 0) * initW N (i.1 + 1) ⟨tv, htv⟩) =
      if hn : 0 < n then (bb h lam sg ⟨0, hn⟩).toNat * initW N (0 + 1) ⟨tv, htv⟩ else 0 := by
    rw [← sum_ite_val (fun i : Fin n => (bb h lam sg i).toNat * initW N (i.1 + 1) ⟨tv, htv⟩) 0]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.1 = 0
    · rw [if_pos hi, if_pos hi]
    · rw [if_neg hi, if_neg hi, zero_mul]

  have hK : (∑ k : Fin K, (if k ∈ L then initW N (sz k + 1) else initW N (sz k)) ⟨tv, htv⟩) =
      (Finset.univ.filter fun k => tv < sz k).card +
        (Finset.univ.filter fun k => k ∈ L ∧ sz k = tv).card := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k ∈ L
    · simp only [hk, if_true, true_and, initW]
      split_ifs <;> omega
    · simp only [hk, if_false, false_and, initW]
      split_ifs <;> omega
  rw [hP, hQ, hK]
  by_cases htn : tv < n
  · have hn : 0 < n := by omega
    have h1 := card_lt_sz sg sz hshape ⟨tv, htn⟩
    have h2 := hL.2 ⟨tv, htn⟩
    simp only at h1 h2
    rw [h1, h2, dif_pos (by omega), dif_pos hn]
    have e1 := natW_sg_val sg ⟨tv, htn⟩
    have e2 := lam_natW_val h lam tv htv
    have e3 := aLast_val h lam sg hI hn
    have e4 := b_val h lam sg hI tv htn
    have hw1 : initW N (n - 1 + 1) ⟨tv, htv⟩ = 1 := by simp only [initW]; rw [if_pos (by simp; omega)]
    rw [hw1, mul_one]
    by_cases ht0 : tv = 0
    · subst ht0
      have hw2 : initW N (0 + 1) ⟨0, htv⟩ = 1 := by simp [initW]
      rw [hw2, mul_one, if_pos rfl]
      simp only at e1 e2 e3 e4 ⊢
      have := sg.anti (show (⟨0, htn⟩ : Fin n) ≤ ⟨n - 1, by omega⟩ by rw [Fin.le_def]; simp)
      omega
    · have hw2 : initW N (0 + 1) ⟨tv, htv⟩ = 0 := by simp only [initW]; rw [if_neg (by simp; omega)]
      rw [hw2, mul_zero, if_neg ht0]
      simp only at e1 e2 e3 e4 ⊢
      omega
  · have htn' : tv = n := by omega
    subst htn'
    have h1 : (Finset.univ.filter fun k => tv < sz k).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro k _; have := hsz k; omega
    have h2 : (Finset.univ.filter fun k => k ∈ L ∧ sz k = tv).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _ hk
      have := hL.1 k hk.1
      rcases sz_lt sg sz hsz hshape k with h3 | h3 <;> omega
    rw [h1, h2]
    have e2 := lam_natW_val h lam tv htv
    have hz : lam.natW ⟨tv, htv⟩ = 0 := by
      have : (⟨tv, htv⟩ : Fin N) = ⟨tv, by omega⟩ := rfl
      omega
    rw [hz]
    have hw1 : ∀ j, j ≤ tv → initW N j ⟨tv, htv⟩ = 0 := by
      intro j hj; simp only [initW]; rw [if_neg (by simp; omega)]
    split_ifs with ha hb
    · rw [hw1 _ (by omega), hw1 _ (by omega)]; simp
    · rw [hw1 _ (by omega)]; simp
    · rw [hw1 _ (by omega)]; simp
    · simp

end PI.WGL.LTE
