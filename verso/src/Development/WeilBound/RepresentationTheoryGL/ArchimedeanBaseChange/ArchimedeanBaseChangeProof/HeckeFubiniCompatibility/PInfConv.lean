import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.NatDegreeDefectGelf

noncomputable section

open Polynomial Finset Filter Topology
open PositivityTheory.RgBcC.Bridge

namespace PositivityTheory.Rg.BcB.CG

namespace InfiniteConvergence

def CoefTo (p : ℕ → ℂ[X]) (q : ℂ[X]) : Prop := ∀ i, Tendsto (fun k => (p k).coeff i) atTop (𝓝 (q.coeff i))

/- English proof (translation)
Introduce `_` and use `tendsto_const_nhds`.
-/
theorem CoefTo.const (q : ℂ[X]) : CoefTo (fun _ => q) q := fun _ => tendsto_const_nhds

/- English proof (translation)
Introduce `i`. Simplify using `only [coeff_C]`. Use `split_ifs`. Conclude with `h`. Conclude with `tendsto_const_nhds`.
-/
theorem CoefTo.C {c : ℕ → ℂ} {c₀ : ℂ} (h : Tendsto c atTop (𝓝 c₀)) :
    CoefTo (fun k => Polynomial.C (c k)) (Polynomial.C c₀) := by
  intro i
  simp only [coeff_C]
  split_ifs
  · exact h
  · exact tendsto_const_nhds

/- English proof (translation)
Introduce `i` and use `by simpa only [coeff_add] using (h i).add (h' i)`.
-/
theorem CoefTo.add {p p' : ℕ → ℂ[X]} {q q' : ℂ[X]} (h : CoefTo p q) (h' : CoefTo p' q') :
    CoefTo (fun k => p k + p' k) (q + q') := fun i => by
  simpa only [coeff_add] using (h i).add (h' i)

/- English proof (translation)
Introduce `i` and use `by simpa only [coeff_sub] using (h i).sub (h' i)`.
-/
theorem CoefTo.sub {p p' : ℕ → ℂ[X]} {q q' : ℂ[X]} (h : CoefTo p q) (h' : CoefTo p' q') :
    CoefTo (fun k => p k - p' k) (q - q') := fun i => by
  simpa only [coeff_sub] using (h i).sub (h' i)

/- English proof (translation)
Introduce `i` and use `by simp only [coeff_mul] exact tendsto_finsetSum _ fun x _ => (h x.1).mul (h' x.2)`.
-/
theorem CoefTo.mul {p p' : ℕ → ℂ[X]} {q q' : ℂ[X]} (h : CoefTo p q) (h' : CoefTo p' q') :
    CoefTo (fun k => p k * p' k) (q * q') := fun i => by
  simp only [coeff_mul]
  exact tendsto_finsetSum _ fun x _ => (h x.1).mul (h' x.2)

/- English proof (translation)
Introduce `i` and use `by simp only [finsetSum_coeff] exact tendsto_finsetSum _ fun j hj => h j hj i`.
-/
theorem CoefTo.sum {ι : Type} (s : Finset ι) {p : ι → ℕ → ℂ[X]} {q : ι → ℂ[X]} (h : ∀ j ∈ s, CoefTo (p j) (q j)) :
    CoefTo (fun k => ∑ j ∈ s, p j k) (∑ j ∈ s, q j) := fun i => by
  simp only [finsetSum_coeff]
  exact tendsto_finsetSum _ fun j hj => h j hj i

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using CoefTo.const (1 : ℂ[X])`. Consider the case `insert a s ha ih`. Simplify using `only [prod_insert ha]`. Conclude with `(h a (mem_insert_self _ _)).mul (ih fun j hj => h j (mem_insert_of_mem hj))`.
-/
theorem CoefTo.prod {ι : Type} [DecidableEq ι] (s : Finset ι) {p : ι → ℕ → ℂ[X]} {q : ι → ℂ[X]}
    (h : ∀ j ∈ s, CoefTo (p j) (q j)) : CoefTo (fun k => ∏ j ∈ s, p j k) (∏ j ∈ s, q j) := by
  induction s using Finset.induction_on with
  | empty => simpa using CoefTo.const (1 : ℂ[X])
  | insert a s ha ih =>
    simp only [prod_insert ha]
    exact (h a (mem_insert_self _ _)).mul (ih fun j hj => h j (mem_insert_of_mem hj))

def sS (t : ℕ → ℂ) (m N : ℕ) : ℂ[X] := ∑ k ∈ range (N + 1), Polynomial.C ((-1) ^ k * t k) * (X - Polynomial.C (m : ℂ)) ^ (N - k)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem defect_eq (t : ℕ → ℂ) (m N : ℕ) (D : ℂ[X]) :
    defect t m N D = (X - Polynomial.C (m : ℂ)) ^ (N + 1) * (D.comp (X + 1) - D) - D * sS t m N := rfl

/- English proof (translation)
Simplify using `only [defect_eq, add_comp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem defect_add' (t : ℕ → ℂ) (m N : ℕ) (P Q : ℂ[X]) :
    defect t m N (P + Q) = defect t m N P + defect t m N Q := by
  simp only [defect_eq, add_comp]; ring

/- English proof (translation)
Simplify using `only [defect_eq, mul_comp, C_comp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem defect_Cmul (t : ℕ → ℂ) (m N : ℕ) (c : ℂ) (P : ℂ[X]) :
    defect t m N (Polynomial.C c * P) = Polynomial.C c * defect t m N P := by
  simp only [defect_eq, mul_comp, C_comp]; ring

/- English proof (translation)
Simplify using `[defect_eq]`.
-/
theorem defect_zero' (t : ℕ → ℂ) (m N : ℕ) : defect t m N 0 = 0 := by
  simp [defect_eq]

/- English proof (translation)
Rewrite using `[(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]`.
-/
theorem natDegree_Xm_pow (m j : ℕ) : ((X - Polynomial.C (m : ℂ)) ^ j).natDegree = j := by
  rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]

/- English proof (translation)
Use `((monic_X_sub_C (m : ℂ)).pow j).coeff_natDegree` as an intermediate fact. Rewrite `this` using `[natDegree_Xm_pow]`. Then use the resulting hypothesis.
-/
theorem coeff_Xm_pow (m j : ℕ) : ((X - Polynomial.C (m : ℂ)) ^ j).coeff j = 1 := by
  have := ((monic_X_sub_C (m : ℂ)).pow j).coeff_natDegree
  rwa [natDegree_Xm_pow] at this

/- English proof (translation)
Use `natDegree_sum_le_of_forall_le _ _ fun k _ => ?_` and prove the remaining obligations. Use `(natDegree_C_mul_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[natDegree_Xm_pow]`. Use linear arithmetic over natural numbers and integers.
-/
theorem natDegree_sS (t : ℕ → ℂ) (m N : ℕ) : (sS t m N).natDegree ≤ N := by
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_Xm_pow]; omega

/- English proof (translation)
Rewrite using `[sS, sum_range_succ', coeff_add, finsetSum_coeff, sum_eq_zero]`. Rewrite using `[zero_add, coeff_C_mul, Nat.sub_zero, coeff_Xm_pow, pow_zero, one_mul, mul_one]`. Introduce `k hk`. Use `mem_range.mp hk` as an intermediate fact. Apply `coeff_eq_zero_of_natDegree_lt` to reduce the goal to its premises.

Use `lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_` and prove the remaining obligations. Rewrite using `[natDegree_Xm_pow]`. Use linear arithmetic over natural numbers and integers.
-/
theorem coeff_sS (t : ℕ → ℂ) (m N : ℕ) : (sS t m N).coeff N = t 0 := by
  rw [sS, sum_range_succ', coeff_add, finsetSum_coeff, sum_eq_zero]
  · rw [zero_add, coeff_C_mul, Nat.sub_zero, coeff_Xm_pow, pow_zero, one_mul, mul_one]
  · intro k hk
    have := mem_range.mp hk
    apply coeff_eq_zero_of_natDegree_lt
    refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
    rw [natDegree_Xm_pow]; omega

/- English proof (translation)
Rewrite using `[defect_eq]`. Use `(natDegree_sub_le _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Distinguish the cases in `h0 : R.natDegree = 0`. Rewrite using `[eq_C_of_natDegree_eq_zero h0, C_comp, sub_self, mul_zero, natDegree_zero]`. Conclude with `Nat.zero_le _`.

Use `natDegree_mul_le.trans ?_` and prove the remaining obligations. Rewrite using `[natDegree_Xm_pow]`. Use `natDegree_comp_sub_le R (R.natDegree - 1) (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `natDegree_mul_le.trans (Nat.add_le_add_left (natDegree_sS t m N) _)`.
-/
theorem natDegree_defect_le (t : ℕ → ℂ) (m N : ℕ) (R : ℂ[X]) :
    (defect t m N R).natDegree ≤ R.natDegree + N := by
  rw [defect_eq]
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · by_cases h0 : R.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero h0, C_comp, sub_self, mul_zero, natDegree_zero]; exact Nat.zero_le _
    · refine natDegree_mul_le.trans ?_
      rw [natDegree_Xm_pow]
      have := natDegree_comp_sub_le R (R.natDegree - 1) (by omega)
      omega
  · exact natDegree_mul_le.trans (Nat.add_le_add_left (natDegree_sS t m N) _)

/- English proof (translation)
Establish `h2 : (X ^ r * sS t m N).coeff (r + N) = t 0` using `by rw [add_comm, coeff_X_pow_mul, coeff_sS]`. Rewrite using `[defect_eq, coeff_sub, h2]`. Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases. Substitute `hr` using the available equality. Simplify using the standard rewrite rules.

Take `⟨d, rfl⟩ : ∃ d, r = d + 1` from `⟨r - 1, by omega⟩`. Establish `hd : (X ^ (d + 1) : ℂ[X]).natDegree = d + 1` using `natDegree_X_pow _`. Establish `hΔd` using `natDegree_comp_sub_le (X ^ (d + 1) : ℂ[X]) d hd`. Establish `hΔc` using `coeff_comp_sub (X ^ (d + 1) : ℂ[X]) d hd`. Rewrite using `[show d + 1 + N = (N + 1) + d by omega, coeff_mul_add_eq_of_natDegree_le (natDegree_Xm_pow m (N + 1)).le hΔd, coeff_Xm_pow, hΔc, leadingCoeff_X_pow]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_defect_X_pow (t : ℕ → ℂ) (m N r : ℕ) :
    (defect t m N (X ^ r)).coeff (r + N) = (r : ℂ) - t 0 := by
  have h2 : (X ^ r * sS t m N).coeff (r + N) = t 0 := by rw [add_comm, coeff_X_pow_mul, coeff_sS]
  rw [defect_eq, coeff_sub, h2]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  · obtain ⟨d, rfl⟩ : ∃ d, r = d + 1 := ⟨r - 1, by omega⟩
    have hd : (X ^ (d + 1) : ℂ[X]).natDegree = d + 1 := natDegree_X_pow _
    have hΔd := natDegree_comp_sub_le (X ^ (d + 1) : ℂ[X]) d hd
    have hΔc := coeff_comp_sub (X ^ (d + 1) : ℂ[X]) d hd
    rw [show d + 1 + N = (N + 1) + d by omega, coeff_mul_add_eq_of_natDegree_le (natDegree_Xm_pow m (N + 1)).le hΔd,
      coeff_Xm_pow, hΔc, leadingCoeff_X_pow]
    push_cast; ring

/- English proof (translation)
Use `set R' := R - Polynomial.C (R.coeff r) * X ^ r with hR'`. Establish `hsplit : R = Polynomial.C (R.coeff r) * X ^ r + R'` using `by rw [hR']; ring`. Establish `hR'c : ∀ i, r ≤ i → R'.coeff i = 0`. Introduce `i hi`. Rewrite using `[hR', coeff_sub, coeff_C_mul_X_pow]`.

Break down `eq_or_lt_of_le hi with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg (by omega), hR i h, sub_zero]`. Establish `h0 : (defect t m N R').coeff (r + N) = 0`.

Distinguish the cases in `hz : R' = 0`. Rewrite using `[hz, defect_zero', coeff_zero]`. Apply `coeff_eq_zero_of_natDegree_lt` to reduce the goal to its premises. Establish `: R'.natDegree < r`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Conclude with `hz (leadingCoeff_eq_zero.mp (hR'c _ hc))`. Use `natDegree_defect_le t m N R'` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `conv_lhs => rw [hsplit]`.

Rewrite using `[defect_add', defect_Cmul, coeff_add, coeff_C_mul, coeff_defect_X_pow, h0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_defect_top (t : ℕ → ℂ) (m N r : ℕ) (R : ℂ[X]) (hR : ∀ i, r < i → R.coeff i = 0) :
    (defect t m N R).coeff (r + N) = ((r : ℂ) - t 0) * R.coeff r := by
  set R' := R - Polynomial.C (R.coeff r) * X ^ r with hR'
  have hsplit : R = Polynomial.C (R.coeff r) * X ^ r + R' := by rw [hR']; ring
  have hR'c : ∀ i, r ≤ i → R'.coeff i = 0 := by
    intro i hi
    rw [hR', coeff_sub, coeff_C_mul_X_pow]
    rcases eq_or_lt_of_le hi with h | h
    · subst h; simp
    · rw [if_neg (by omega), hR i h, sub_zero]
  have h0 : (defect t m N R').coeff (r + N) = 0 := by
    by_cases hz : R' = 0
    · rw [hz, defect_zero', coeff_zero]
    · apply coeff_eq_zero_of_natDegree_lt
      have : R'.natDegree < r := by
        by_contra hc
        push Not at hc
        exact hz (leadingCoeff_eq_zero.mp (hR'c _ hc))
      have := natDegree_defect_le t m N R'
      omega
  conv_lhs => rw [hsplit]
  rw [defect_add', defect_Cmul, coeff_add, coeff_C_mul, coeff_defect_X_pow, h0]
  ring

def Hi (r n : ℕ) (Q : ℂ[X]) : ℂ[X] := ∑ i ∈ Ioc r n, Polynomial.C (Q.coeff i) * X ^ i

/- English proof (translation)
Simplify using `only [Hi, finsetSum_coeff, coeff_C_mul_X_pow]`. Rewrite using `[Finset.sum_ite_eq]`.
-/
theorem coeff_Hi (r n : ℕ) (Q : ℂ[X]) (i : ℕ) : (Hi r n Q).coeff i = if i ∈ Ioc r n then Q.coeff i else 0 := by
  simp only [Hi, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]

/- English proof (translation)
Rewrite using `[Hi, ← coe_compRingHom_apply, map_sum]`. Simplify using `only [coe_compRingHom_apply, mul_comp, C_comp, X_pow_comp]`.
-/
theorem Hi_comp (r n : ℕ) (Q : ℂ[X]) :
    (Hi r n Q).comp (X + 1) = ∑ i ∈ Ioc r n, Polynomial.C (Q.coeff i) * (X + 1) ^ i := by
  rw [Hi, ← coe_compRingHom_apply, map_sum]
  simp only [coe_compRingHom_apply, mul_comp, C_comp, X_pow_comp]

/- English proof (translation)
Simplify using `only [defect_eq, sS]`. Use `CoefTo.sub (CoefTo.mul (CoefTo.const _) (CoefTo.sub hDc hD)) (CoefTo.mul hD (CoefTo.sum _ fun l _ => CoefTo.mul (CoefTo.C (tendsto_const_nhds.mul (ht l))) (CoefTo.const _)))` and prove the remaining obligations.
-/
theorem CoefTo.defect {t : ℕ → ℕ → ℂ} {t₀ : ℕ → ℂ} (ht : ∀ l, Tendsto (fun k => t k l) atTop (𝓝 (t₀ l)))
    (m N : ℕ) {D : ℕ → ℂ[X]} {D₀ : ℂ[X]} (hD : CoefTo D D₀)
    (hDc : CoefTo (fun k => (D k).comp (X + 1)) (D₀.comp (X + 1))) :
    CoefTo (fun k => defect (t k) m N (D k)) (defect t₀ m N D₀) := by
  simp only [defect_eq, sS]
  refine CoefTo.sub (CoefTo.mul (CoefTo.const _) (CoefTo.sub hDc hD))
    (CoefTo.mul hD (CoefTo.sum _ fun l _ => CoefTo.mul (CoefTo.C (tendsto_const_nhds.mul (ht l))) (CoefTo.const _)))

/- English proof (translation)
Use `set n := p.natDegree with hn`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Establish `h1 : 1 < ‖z‖` using `lt_of_le_of_lt (le_max_left _ _) hlt`. Establish `h2 : ∑ i ∈ range n, ‖p.coeff i‖ < ‖z‖` using `lt_of_le_of_lt (le_max_right _ _) hlt`.

Establish `hev : p.eval z = z ^ n + ∑ i ∈ range n, p.coeff i * z ^ i`. Rewrite using `[eval_eq_sum_range, sum_range_succ, ← hn, hp.coeff_natDegree, one_mul, add_comm]`. Rewrite `hev` using `[hz]`. Establish `hpos : 0 < n`. Break down `Nat.eq_zero_or_pos n with h | h` into its components or cases.

It suffices to derive a contradiction. Rewrite `hz` using `[eq_one_of_monic_natDegree_zero hp h]`. Simplify using `at hz`. Conclude with `h`. Establish `h3 : ‖z‖ ^ n ≤ ∑ i ∈ range n, ‖p.coeff i‖ * ‖z‖ ^ i`.

Establish `e : z ^ n = -∑ i ∈ range n, p.coeff i * z ^ i` using `by linear_combination -hev`. Combine the equalities or inequalities in the displayed calculation. Establish `h4 : ∑ i ∈ range n, ‖p.coeff i‖ * ‖z‖ ^ i ≤ (∑ i ∈ range n, ‖p.coeff i‖) * ‖z‖ ^ (n - 1)`. Rewrite using `[sum_mul]`. Use `sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1.le ?_) (norm_nonneg _)` and prove the remaining obligations.

Use `mem_range.mp hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h5 : (∑ i ∈ range n, ‖p.coeff i‖) * ‖z‖ ^ (n - 1) < ‖z‖ * ‖z‖ ^ (n - 1)` using `mul_lt_mul_of_pos_right h2 (pow_pos (by linarith) _)`. Establish `h6 : ‖z‖ * ‖z‖ ^ (n - 1) = ‖z‖ ^ n`. Rewrite using `[← pow_succ']`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_root_le (p : ℂ[X]) (hp : p.Monic) (z : ℂ) (hz : p.eval z = 0) :
    ‖z‖ ≤ max 1 (∑ i ∈ range p.natDegree, ‖p.coeff i‖) := by
  set n := p.natDegree with hn
  by_contra hlt
  push Not at hlt
  have h1 : 1 < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hlt
  have h2 : ∑ i ∈ range n, ‖p.coeff i‖ < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hlt
  have hev : p.eval z = z ^ n + ∑ i ∈ range n, p.coeff i * z ^ i := by
    rw [eval_eq_sum_range, sum_range_succ, ← hn, hp.coeff_natDegree, one_mul, add_comm]
  rw [hz] at hev
  have hpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [eq_one_of_monic_natDegree_zero hp h] at hz
      simp at hz
    · exact h
  have h3 : ‖z‖ ^ n ≤ ∑ i ∈ range n, ‖p.coeff i‖ * ‖z‖ ^ i := by
    have e : z ^ n = -∑ i ∈ range n, p.coeff i * z ^ i := by linear_combination -hev
    calc ‖z‖ ^ n = ‖z ^ n‖ := (norm_pow _ _).symm
      _ = ‖∑ i ∈ range n, p.coeff i * z ^ i‖ := by rw [e, norm_neg]
      _ ≤ ∑ i ∈ range n, ‖p.coeff i * z ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ range n, ‖p.coeff i‖ * ‖z‖ ^ i := by simp only [norm_mul, norm_pow]
  have h4 : ∑ i ∈ range n, ‖p.coeff i‖ * ‖z‖ ^ i ≤ (∑ i ∈ range n, ‖p.coeff i‖) * ‖z‖ ^ (n - 1) := by
    rw [sum_mul]
    refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1.le ?_) (norm_nonneg _)
    have := mem_range.mp hi; omega
  have h5 : (∑ i ∈ range n, ‖p.coeff i‖) * ‖z‖ ^ (n - 1) < ‖z‖ * ‖z‖ ^ (n - 1) :=
    mul_lt_mul_of_pos_right h2 (pow_pos (by linarith) _)
  have h6 : ‖z‖ * ‖z‖ ^ (n - 1) = ‖z‖ ^ n := by
    rw [← pow_succ']; congr 1; omega
  linarith

def cq (m : ℕ) (χ : Fin (m + 1) → ℂ) : ℂ[X] := ∏ s, (X + Polynomial.C (χ s - (m : ℂ) / 2))

/- English proof (translation)
The claim follows from `natDegree_capQ m χ`.
-/
theorem cq_natDegree (m : ℕ) (χ : Fin (m + 1) → ℂ) : (cq m χ).natDegree = m + 1 := natDegree_capQ m χ

/- English proof (translation)
The claim follows from `monic_capQ m χ`.
-/
theorem cq_monic (m : ℕ) (χ : Fin (m + 1) → ℂ) : (cq m χ).Monic := monic_capQ m χ

/- English proof (translation)
Establish `e : cq m χ = (Multiset.map (fun a => X - Polynomial.C a) (Multiset.map (fun s => (m : ℂ) / 2 - χ s) univ.val)).prod`. Rewrite using `[Multiset.map_map, cq, Finset.prod_eq_multiset_prod]`. Use `congr 1`. Use `Multiset.map_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, map_sub]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, roots_multiset_prod_X_sub_C]`.
-/
theorem cq_roots (m : ℕ) (χ : Fin (m + 1) → ℂ) :
    (cq m χ).roots = Multiset.map (fun s => (m : ℂ) / 2 - χ s) univ.val := by
  have e : cq m χ = (Multiset.map (fun a => X - Polynomial.C a) (Multiset.map (fun s => (m : ℂ) / 2 - χ s) univ.val)).prod := by
    rw [Multiset.map_map, cq, Finset.prod_eq_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun s _ => ?_
    simp only [Function.comp_apply, map_sub]
    ring
  rw [e, roots_multiset_prod_X_sub_C]

/- English proof (translation)
Simplify using `only [cq, eval_prod, eval_add, eval_X, eval_C]`. Conclude with `prod_eq_zero (mem_univ s) (by ring)`.
-/
theorem cq_eval (m : ℕ) (χ : Fin (m + 1) → ℂ) (s : Fin (m + 1)) : (cq m χ).eval ((m : ℂ) / 2 - χ s) = 0 := by
  simp only [cq, eval_prod, eval_add, eval_X, eval_C]
  exact prod_eq_zero (mem_univ s) (by ring)

/- English proof (translation)
Establish `hz : (defect (GlobalTheory.Dec.gelfVal χ) m (m + 1) (cq m χ)).coeff (r + (m + 1)) = 0` using `coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_defect_gelf m χ (m + 1)) (by omega))`. Establish `e : defect (GlobalTheory.Dec.gelfVal χ) m (m + 1) (cq m χ) = defect (GlobalTheory.Dec.gelfVal χ) m (m + 1) (Hi r (m + 1) (cq m χ)) + defect (GlobalTheory.Dec.gelfVal χ) m (m + 1) (cq m χ - Hi r (m + 1) (cq m χ))`. Rewrite using `[← defect_add']`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hvan : ∀ i, r < i → (cq m χ - Hi r (m + 1) (cq m χ)).coeff i = 0`. Introduce `i hi`. Rewrite using `[coeff_sub, coeff_Hi]`. Distinguish the cases in `hin : i ∈ Ioc r (m + 1)`. Rewrite using `[if_pos hin, sub_self]`.

Rewrite using `[if_neg hin, sub_zero]`. Apply `coeff_eq_zero_of_natDegree_lt` to reduce the goal to its premises. Rewrite using `[cq_natDegree]`. Simplify using `only [mem_Ioc, not_and, not_le] at hin`. Conclude with `hin hi`.

Establish `hr' : (cq m χ - Hi r (m + 1) (cq m χ)).coeff r = (cq m χ).coeff r`. Rewrite using `[coeff_sub, coeff_Hi, if_neg (by simp), sub_zero]`. Rewrite `hz` using `[e, coeff_add, coeff_defect_top _ _ _ r _ hvan, hr', gelfVal_zero']`. Move the coercions through the operations in `at hz`. Conclude with `hz`.
-/
theorem key (m : ℕ) (χ : Fin (m + 1) → ℂ) (r : ℕ) (_hr : r ≤ m) :
    (defect (GlobalTheory.Dec.gelfVal χ) m (m + 1) (Hi r (m + 1) (cq m χ))).coeff (r + (m + 1)) +
      ((r : ℂ) - ((m : ℂ) + 1)) * (cq m χ).coeff r = 0 := by
  have hz : (defect (GlobalTheory.Dec.gelfVal χ) m (m + 1) (cq m χ)).coeff (r + (m + 1)) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_defect_gelf m χ (m + 1)) (by omega))
  have e : defect (GlobalTheory.Dec.gelfVal χ) m (m + 1) (cq m χ) =
      defect (GlobalTheory.Dec.gelfVal χ) m (m + 1) (Hi r (m + 1) (cq m χ)) +
        defect (GlobalTheory.Dec.gelfVal χ) m (m + 1) (cq m χ - Hi r (m + 1) (cq m χ)) := by
    rw [← defect_add']; congr 1; ring
  have hvan : ∀ i, r < i → (cq m χ - Hi r (m + 1) (cq m χ)).coeff i = 0 := by
    intro i hi
    rw [coeff_sub, coeff_Hi]
    by_cases hin : i ∈ Ioc r (m + 1)
    · rw [if_pos hin, sub_self]
    · rw [if_neg hin, sub_zero]
      apply coeff_eq_zero_of_natDegree_lt
      rw [cq_natDegree]
      simp only [mem_Ioc, not_and, not_le] at hin
      exact hin hi
  have hr' : (cq m χ - Hi r (m + 1) (cq m χ)).coeff r = (cq m χ).coeff r := by
    rw [coeff_sub, coeff_Hi, if_neg (by simp), sub_zero]
  rw [e, coeff_add, coeff_defect_top _ _ _ r _ hvan, hr', gelfVal_zero'] at hz
  push_cast at hz
  exact hz

/- English proof (translation)
Establish `hind : ∀ j i, m + 1 - j ≤ i → Tendsto (fun k => (cq m (x k)).coeff i) atTop (𝓝 ((cq m y).coeff i))`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `i hi`.

Break down `eq_or_lt_of_le (show m + 1 ≤ i by omega) with h | h` into its components or cases. Substitute `h` using the available equality. Establish `e : ∀ χ, (cq m χ).coeff (m + 1) = 1` using `fun χ => by`. Use `(cq_monic m χ).coeff_natDegree` as an intermediate fact. Rewrite `this` using `[cq_natDegree]`. Then use the resulting hypothesis.

Simplify using `only [e]`. Conclude with `tendsto_const_nhds`. Establish `e : ∀ χ, (cq m χ).coeff i = 0` using `fun χ => coeff_eq_zero_of_natDegree_lt (by rw [cq_natDegree]; exact h)`. Simplify using `only [e]`. Conclude with `tendsto_const_nhds`.

Consider the case `succ j ih`. Introduce `i hi`. Distinguish the cases in `hij : m + 1 - j ≤ i`. Conclude with `ih i hij`. Establish `hr : i ≤ m` using `by omega`.

Establish `hij' : i + j = m` using `by omega`. Establish `hne : ((j : ℂ) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero j`. Establish `hform : ∀ χ : Fin (m + 1) → ℂ, (cq m χ).coeff i = (defect (GlobalTheory.Dec.gelfVal χ) m (m + 1) (Hi i (m + 1) (cq m χ))).coeff (i + (m + 1)) / ((j : ℂ) + 1)`. Introduce `χ`. Establish `hk` using `key m χ i hr`.

Establish `hc : (i : ℂ) = (m : ℂ) - j` using `by rw [← hij']; push_cast; ring`. Rewrite using `[eq_div_iff hne]`. Take the linear combination `(-1 : ℂ) * hk + (cq m χ).coeff i * hc`. Use `Tendsto.congr (fun k => (hform (x k)).symm) ?_` and prove the remaining obligations. Rewrite using `[hform y]`.

Apply `Tendsto.div_const` to reduce the goal to its premises. Establish `hHi : ∀ l ∈ Ioc i (m + 1), Tendsto (fun k => (cq m (x k)).coeff l) atTop (𝓝 ((cq m y).coeff l))` using `fun l hl => ih l (by simp only [mem_Ioc] at hl; omega)`. Establish `h1 : CoefTo (fun k => Hi i (m + 1) (cq m (x k))) (Hi i (m + 1) (cq m y))`. Simplify using `only [Hi]`. Conclude with `CoefTo.sum _ fun l hl => CoefTo.mul (CoefTo.C (hHi l hl)) (CoefTo.const _)`.

Establish `h2 : CoefTo (fun k => (Hi i (m + 1) (cq m (x k))).comp (X + 1)) ((Hi i (m + 1) (cq m y)).comp (X + 1))`. Simplify using `only [Hi_comp]`. Conclude with `CoefTo.sum _ fun l hl => CoefTo.mul (CoefTo.C (hHi l hl)) (CoefTo.const _)`. Conclude with `CoefTo.defect (t := fun k => GlobalTheory.Dec.gelfVal (x k)) hconv m (m + 1) h1 h2 (i + (m + 1))`. Conclude with `fun i => hind (m + 1) i (by omega)`.
-/
theorem coef_tendsto (m : ℕ) (x : ℕ → Fin (m + 1) → ℂ) (y : Fin (m + 1) → ℂ)
    (hconv : ∀ l, Tendsto (fun k => GlobalTheory.Dec.gelfVal (x k) l) atTop (𝓝 (GlobalTheory.Dec.gelfVal y l))) :
    CoefTo (fun k => cq m (x k)) (cq m y) := by
  have hind : ∀ j i, m + 1 - j ≤ i → Tendsto (fun k => (cq m (x k)).coeff i) atTop (𝓝 ((cq m y).coeff i)) := by
    intro j
    induction j with
    | zero =>
      intro i hi
      rcases eq_or_lt_of_le (show m + 1 ≤ i by omega) with h | h
      · subst h
        have e : ∀ χ, (cq m χ).coeff (m + 1) = 1 := fun χ => by
          have := (cq_monic m χ).coeff_natDegree
          rwa [cq_natDegree] at this
        simp only [e]
        exact tendsto_const_nhds
      · have e : ∀ χ, (cq m χ).coeff i = 0 := fun χ =>
          coeff_eq_zero_of_natDegree_lt (by rw [cq_natDegree]; exact h)
        simp only [e]
        exact tendsto_const_nhds
    | succ j ih =>
      intro i hi
      by_cases hij : m + 1 - j ≤ i
      · exact ih i hij
      · have hr : i ≤ m := by omega
        have hij' : i + j = m := by omega
        have hne : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
        have hform : ∀ χ : Fin (m + 1) → ℂ, (cq m χ).coeff i =
            (defect (GlobalTheory.Dec.gelfVal χ) m (m + 1) (Hi i (m + 1) (cq m χ))).coeff (i + (m + 1)) / ((j : ℂ) + 1) := by
          intro χ
          have hk := key m χ i hr
          have hc : (i : ℂ) = (m : ℂ) - j := by rw [← hij']; push_cast; ring
          rw [eq_div_iff hne]
          linear_combination (-1 : ℂ) * hk + (cq m χ).coeff i * hc
        refine Tendsto.congr (fun k => (hform (x k)).symm) ?_
        rw [hform y]
        apply Tendsto.div_const
        have hHi : ∀ l ∈ Ioc i (m + 1), Tendsto (fun k => (cq m (x k)).coeff l) atTop (𝓝 ((cq m y).coeff l)) :=
          fun l hl => ih l (by simp only [mem_Ioc] at hl; omega)
        have h1 : CoefTo (fun k => Hi i (m + 1) (cq m (x k))) (Hi i (m + 1) (cq m y)) := by
          simp only [Hi]
          exact CoefTo.sum _ fun l hl => CoefTo.mul (CoefTo.C (hHi l hl)) (CoefTo.const _)
        have h2 : CoefTo (fun k => (Hi i (m + 1) (cq m (x k))).comp (X + 1)) ((Hi i (m + 1) (cq m y)).comp (X + 1)) := by
          simp only [Hi_comp]
          exact CoefTo.sum _ fun l hl => CoefTo.mul (CoefTo.C (hHi l hl)) (CoefTo.const _)
        exact CoefTo.defect (t := fun k => GlobalTheory.Dec.gelfVal (x k)) hconv m (m + 1) h1 h2 (i + (m + 1))
  exact fun i => hind (m + 1) i (by omega)

end InfiniteConvergence

open InfiniteConvergence in
/- English proof (translation)
Introduce `n x y hconv ε hε`. Break down `n with _ | m` into its components or cases. Use `Filter.Eventually.of_forall fun k => ?_` and prove the remaining obligations. Establish `: (Finset.univ : Finset (Fin 0)) = ∅` using `Finset.univ_eq_empty`. Simplify using the standard rewrite rules.

Establish `hcoef` using `coef_tendsto m x y hconv`. Establish `hbd : ∀ i, ∃ B, ∀ k, ‖(cq m (x k)).coeff i‖ ≤ B` using `fun i => by`. Take `⟨B, hB⟩` from `(Metric.isBounded_range_of_tendsto _ (hcoef i)).exists_norm_le`. Conclude with `⟨B, fun k => hB _ ⟨k, rfl⟩⟩`. Use `choose Cb hCb using hbd`.

Use `set B := max 1 (∑ i ∈ range (m + 1), Cb i) + ‖(m : ℂ) / 2‖ with hBdef`. Establish `hB0 : 0 ≤ B`. Use `le_max_left (1 : ℝ) (∑ i ∈ range (m + 1), Cb i)` as an intermediate fact. Use `norm_nonneg ((m : ℂ) / 2)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hxb : ∀ k s, ‖x k s‖ ≤ B`. Introduce `k s`. Establish `h1` using `norm_root_le _ (cq_monic m (x k)) _ (cq_eval m (x k) s)`. Rewrite `h1` using `[cq_natDegree]`. Establish `h2 : ∑ i ∈ range (m + 1), ‖(cq m (x k)).coeff i‖ ≤ ∑ i ∈ range (m + 1), Cb i` using `sum_le_sum fun i _ => hCb i k`.

Establish `h3 : ‖x k s‖ ≤ ‖(m : ℂ) / 2‖ + ‖(m : ℂ) / 2 - x k s‖`. Use `norm_sub_le ((m : ℂ) / 2) ((m : ℂ) / 2 - x k s)` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Establish `h4` using `max_le_max (le_refl (1 : ℝ)) h2`. Combine the linear equalities and inequalities to obtain the conclusion.

Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[Filter.not_eventually]`. Take `⟨φ, hφm, hφ⟩` from `Filter.extraction_of_frequently_atTop hne`. Establish `hmem : ∀ k, x (φ k) ∈ Metric.closedBall (0 : Fin (m + 1) → ℂ) B` using `fun k => mem_closedBall_zero_iff.2 ((pi_norm_le_iff_of_nonneg hB0).2 fun s => hxb _ s)`. Take `⟨z, -, ψ, hψm, hψ⟩` from `tendsto_subseq_of_bounded Metric.isBounded_closedBall hmem`.

Establish `hw : CoefTo (fun k => cq m (x (φ (ψ k)))) (cq m z)`. Simplify using `only [cq]`. Conclude with `CoefTo.prod univ fun s _ => (CoefTo.const X).add (CoefTo.C ((tendsto_pi_nhds.1 hψ s).sub_const _))`. Establish `hw' : CoefTo (fun k => cq m (x (φ (ψ k)))) (cq m y)` using `fun i => (hcoef i).comp (hφm.comp hψm).tendsto_atTop`. Establish `hPz : cq m z = cq m y` using `Polynomial.ext fun i => tendsto_nhds_unique (hw i) (hw' i)`.

Establish `hms : Multiset.map z univ.val = Multiset.map y univ.val`. Establish `h` using `congrArg Polynomial.roots hPz`. Rewrite `h` using `[cq_roots, cq_roots]`. Establish `h'` using `congrArg (Multiset.map fun a => (m : ℂ) / 2 - a) h`. Simplify `h'` using `only [Multiset.map_map, Function.comp_def, sub_sub_cancel, Multiset.map_id']`.

Establish `hclose : ∀ᶠ k in atTop, ∀ s, ‖x (φ (ψ k)) s - z s‖ ≤ ε`. Use `Filter.eventually_all.2 fun s => ?_` and prove the remaining obligations. Use `((Metric.tendsto_nhds.1 (tendsto_pi_nhds.1 hψ s)) ε hε).mono fun k hk => ?_` and prove the remaining obligations. Rewrite `hk` using `[dist_eq_norm]`. Conclude with `hk.le`.

Take `⟨k, hk⟩` from `hclose.exists`. Apply `hφ (ψ k)` to reduce the goal to its premises. Rewrite using `[← hms, Multiset.rel_map]`. Conclude with `Multiset.rel_refl_of_refl_on fun s _ => hk s`.
-/
theorem infConv : InfConv := by
  intro n x y hconv ε hε
  rcases n with _ | m
  · refine Filter.Eventually.of_forall fun k => ?_
    have : (Finset.univ : Finset (Fin 0)) = ∅ := Finset.univ_eq_empty
    simp
  have hcoef := coef_tendsto m x y hconv
  have hbd : ∀ i, ∃ B, ∀ k, ‖(cq m (x k)).coeff i‖ ≤ B := fun i => by
    obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ (hcoef i)).exists_norm_le
    exact ⟨B, fun k => hB _ ⟨k, rfl⟩⟩
  choose Cb hCb using hbd
  set B := max 1 (∑ i ∈ range (m + 1), Cb i) + ‖(m : ℂ) / 2‖ with hBdef
  have hB0 : 0 ≤ B := by
    have := le_max_left (1 : ℝ) (∑ i ∈ range (m + 1), Cb i)
    have := norm_nonneg ((m : ℂ) / 2)
    linarith
  have hxb : ∀ k s, ‖x k s‖ ≤ B := by
    intro k s
    have h1 := norm_root_le _ (cq_monic m (x k)) _ (cq_eval m (x k) s)
    rw [cq_natDegree] at h1
    have h2 : ∑ i ∈ range (m + 1), ‖(cq m (x k)).coeff i‖ ≤ ∑ i ∈ range (m + 1), Cb i :=
      sum_le_sum fun i _ => hCb i k
    have h3 : ‖x k s‖ ≤ ‖(m : ℂ) / 2‖ + ‖(m : ℂ) / 2 - x k s‖ := by
      have := norm_sub_le ((m : ℂ) / 2) ((m : ℂ) / 2 - x k s)
      rwa [sub_sub_cancel] at this
    have h4 := max_le_max (le_refl (1 : ℝ)) h2
    linarith
  by_contra hne
  rw [Filter.not_eventually] at hne
  obtain ⟨φ, hφm, hφ⟩ := Filter.extraction_of_frequently_atTop hne
  have hmem : ∀ k, x (φ k) ∈ Metric.closedBall (0 : Fin (m + 1) → ℂ) B := fun k =>
    mem_closedBall_zero_iff.2 ((pi_norm_le_iff_of_nonneg hB0).2 fun s => hxb _ s)
  obtain ⟨z, -, ψ, hψm, hψ⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hmem
  have hw : CoefTo (fun k => cq m (x (φ (ψ k)))) (cq m z) := by
    simp only [cq]
    exact CoefTo.prod univ fun s _ =>
      (CoefTo.const X).add (CoefTo.C ((tendsto_pi_nhds.1 hψ s).sub_const _))
  have hw' : CoefTo (fun k => cq m (x (φ (ψ k)))) (cq m y) := fun i =>
    (hcoef i).comp (hφm.comp hψm).tendsto_atTop
  have hPz : cq m z = cq m y := Polynomial.ext fun i => tendsto_nhds_unique (hw i) (hw' i)
  have hms : Multiset.map z univ.val = Multiset.map y univ.val := by
    have h := congrArg Polynomial.roots hPz
    rw [cq_roots, cq_roots] at h
    have h' := congrArg (Multiset.map fun a => (m : ℂ) / 2 - a) h
    simpa only [Multiset.map_map, Function.comp_def, sub_sub_cancel, Multiset.map_id'] using h'
  have hclose : ∀ᶠ k in atTop, ∀ s, ‖x (φ (ψ k)) s - z s‖ ≤ ε := by
    refine Filter.eventually_all.2 fun s => ?_
    refine ((Metric.tendsto_nhds.1 (tendsto_pi_nhds.1 hψ s)) ε hε).mono fun k hk => ?_
    rw [dist_eq_norm] at hk
    exact hk.le
  obtain ⟨k, hk⟩ := hclose.exists
  apply hφ (ψ k)
  rw [← hms, Multiset.rel_map]
  exact Multiset.rel_refl_of_refl_on fun s _ => hk s

end PositivityTheory.Rg.BcB.CG

end
