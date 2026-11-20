import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdDefs

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Simplify using `only [sCoef, dif_pos hi, lamT, Dvec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.val_mk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sCoef_lamT (lam : Fin n → ℝ) (t : ℕ) {i : ℕ} (hi : i + 1 < n) :
    sCoef (lamT lam t) i = sCoef lam i + t := by
  simp only [sCoef, dif_pos hi, lamT, Dvec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.val_mk]
  push_cast
  ring

/- English proof (translation)
Simplify using `[sCoef, hi]`.
-/
theorem sCoef_zero_of (i : ℕ) (hi : i + 1 < n) : sCoef (0 : Fin n → ℝ) i = 1 := by
  simp [sCoef, hi]

/- English proof (translation)
Unfold `Ph`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun i hi => ?_)` and prove the remaining obligations. Establish `hi' : i + 1 < n`. Use `Finset.mem_range.mp hi` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[sCoef_lamT lam t hi', sCoef_zero_of i hi']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ph_lamT (lam : Fin n → ℝ) (t : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Ph (lamT lam t) X = Ph lam X + (t : ℝ) * Ph (0 : Fin n → ℝ) X := by
  unfold Ph
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i + 1 < n := by
    have := Finset.mem_range.mp hi
    omega
  rw [sCoef_lamT lam t hi', sCoef_zero_of i hi']
  ring

/- English proof (translation)
Introduce `a b hab`. Simplify using `only [Dvec]`. Establish `h1 : (a : ℕ) ≤ (b : ℕ)` using `hab`. Establish `h2 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ)` using `by exact_mod_cast h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dvec_antitone : Antitone (Dvec n) := by
  intro a b hab
  simp only [Dvec]
  have h1 : (a : ℕ) ≤ (b : ℕ) := hab
  have h2 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast h1
  linarith

/- English proof (translation)
Apply the tactic sequence `simp only [lamT, Dvec, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring`.
-/
theorem lamT_apply (lam : Fin n → ℝ) (t : ℕ) (a : Fin n) :
    lamT lam t a = lam a + (t : ℝ) * ((n : ℝ) - 1 - ((a : ℕ) : ℝ)) := by
  simp only [lamT, Dvec, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

/- English proof (translation)
Rewrite using `[lamT_apply, lamT_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lamT_sub (lam : Fin n → ℝ) (t : ℕ) (a b : Fin n) :
    lamT lam t a - lamT lam t b = (lam a - lam b) + (t : ℝ) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  rw [lamT_apply, lamT_apply]
  ring

/- English proof (translation)
Introduce `a b hab`. Rewrite using `[lamT_apply, lamT_apply]`. Establish `h1` using `hlam hab`. Establish `h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast (show (a : ℕ) < b from hab)`. Establish `ht : (0 : ℝ) ≤ t` using `Nat.cast_nonneg t`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem strictAnti_lamT {lam : Fin n → ℝ} (hlam : StrictAnti lam) (t : ℕ) : StrictAnti (lamT lam t) := by
  intro a b hab
  rw [lamT_apply, lamT_apply]
  have h1 := hlam hab
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast (show (a : ℕ) < b from hab)
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  nlinarith

/- English proof (translation)
Use `⟨strictAnti_lamT hlam.1 t, fun a => ?_⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `hlam.2 a`. Use `⟨m + (t : ℤ) * ((n : ℤ) - 1 - ((a : ℕ) : ℤ)), ?_⟩` and prove the remaining obligations. Rewrite using `[lamT_apply]`. Use `push_cast`.

Take the linear combination `hm`.
-/
theorem isHCParam_lamT {lam : Fin n → ℝ} (hlam : IsHCParam lam) (t : ℕ) : IsHCParam (lamT lam t) := by
  refine ⟨strictAnti_lamT hlam.1 t, fun a => ?_⟩
  obtain ⟨m, hm⟩ := hlam.2 a
  refine ⟨m + (t : ℤ) * ((n : ℤ) - 1 - ((a : ℕ) : ℤ)), ?_⟩
  rw [lamT_apply]
  push_cast
  linear_combination hm

/- English proof (translation)
Introduce `a b hab`. Establish `hne : a ≠ b` using `fun e => hab (by rw [e])`. Establish `hg` using `hgap a b hab`. Establish `ht : (0 : ℝ) ≤ t` using `Nat.cast_nonneg t`. Rewrite using `[lamT_sub]`.

Break down `lt_or_gt_of_ne hne with h1 | h1` into its components or cases. Establish `hl` using `hlam h1`. Establish `hab' : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ)` using `by exact_mod_cast (show (a : ℕ) + 1 ≤ b from h1)`. Rewrite `hg` using `[abs_of_pos (sub_pos.mpr hl)]`. Conclude with `le_abs.mpr (Or.inl (by nlinarith))`.

Establish `hl` using `hlam h1`. Establish `hab' : ((b : ℕ) : ℝ) + 1 ≤ ((a : ℕ) : ℝ)` using `by exact_mod_cast (show (b : ℕ) + 1 ≤ a from h1)`. Rewrite `hg` using `[abs_of_neg (sub_neg.mpr hl)]`. Conclude with `le_abs.mpr (Or.inr (by nlinarith))`.
-/
theorem gap_lamT {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hlam : StrictAnti lam)
    (hgap : GapAtLeast ε lam h) (t : ℕ) : GapAtLeast ε (lamT lam t) (h + t) := by
  intro a b hab
  have hne : a ≠ b := fun e => hab (by rw [e])
  have hg := hgap a b hab
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  rw [lamT_sub]
  rcases lt_or_gt_of_ne hne with h1 | h1
  · have hl := hlam h1
    have hab' : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast (show (a : ℕ) + 1 ≤ b from h1)
    rw [abs_of_pos (sub_pos.mpr hl)] at hg
    exact le_abs.mpr (Or.inl (by nlinarith))
  · have hl := hlam h1
    have hab' : ((b : ℕ) : ℝ) + 1 ≤ ((a : ℕ) : ℝ) := by exact_mod_cast (show (b : ℕ) + 1 ≤ a from h1)
    rw [abs_of_neg (sub_neg.mpr hl)] at hg
    exact le_abs.mpr (Or.inr (by nlinarith))

/- English proof (translation)
Unfold `lowK lamT`. Normalize the expressions using the abelian group laws.
-/
theorem lowK_lamT (ε : Fin n → Bool) (lam : Fin n → ℝ) (t : ℕ) :
    lowK ε (lamT lam t) = lowK ε lam + (t : ℝ) • Dvec n := by
  unfold lowK lamT
  abel

/- English proof (translation)
Unfold `Vand`. Use `Finset.prod_pos (fun a _ => Finset.prod_pos (fun b hb => ?_))` and prove the remaining obligations. Establish `hab : a < b` using `(Finset.mem_filter.mp hb).2`. Conclude with `sub_pos.mpr (hlam hab)`.
-/
theorem vand_pos {lam : Fin n → ℝ} (hlam : StrictAnti lam) : 0 < Vand lam := by
  unfold Vand
  refine Finset.prod_pos (fun a _ => Finset.prod_pos (fun b hb => ?_))
  have hab : a < b := (Finset.mem_filter.mp hb).2
  exact sub_pos.mpr (hlam hab)

/- English proof (translation)
Establish `hne : ∀ a b : Fin n, a ≠ b → μ a - μ b ≠ 0` using `fun a b h => sub_ne_zero.mpr (hμ.injective.ne h)`. Establish `hV : Vand μ ≠ 0` using `(vand_pos hμ).ne'`. Establish `hfac : ∀ a ∈ (univ : Finset (Fin n)), ∀ b ∈ univ.filter (fun b : Fin n => a < b), (μ + Pi.single s (1 : ℝ) : Fin n → ℝ) a - (μ + Pi.single s (1 : ℝ) : Fin n → ℝ) b = (μ a - μ b) * ((if a = s then (μ s + 1 - μ b) / (μ s - μ b) else 1) * (if b = s then (μ s + 1 - μ a) / (μ s - μ a) …`. Introduce `a _ b hb`. Establish `hab : a < b` using `(Finset.mem_filter.mp hb).2`.

Establish `hab' : a ≠ b` using `ne_of_lt hab`. Distinguish the cases in `ha : a = s`. Substitute `ha` using the available equality. Establish `h1 : μ a - μ b ≠ 0` using `hne a b hab'`. Rewrite using `[if_pos rfl, if_neg hab'.symm, mul_one]`.

Simplify using `only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab'.symm, add_zero]`. Apply the tactic sequence `field_simp <;> ring`. Distinguish the cases in `hb' : b = s`. Substitute `hb'` using the available equality. Establish `h2 : μ b - μ a ≠ 0` using `hne b a hab'.symm`.

Rewrite using `[if_neg ha, if_pos rfl, one_mul]`. Simplify using `only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne ha, add_zero]`. Apply the tactic sequence `field_simp <;> ring`. Rewrite using `[if_neg ha, if_neg hb', mul_one, mul_one]`. Simplify using `only [Pi.add_apply, Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb', add_zero]`.

Rewrite using `[eq_div_iff hV]`. Establish `hsplit : Vand (μ + Pi.single s 1) = Vand μ * ((∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (if a = s then (μ s + 1 - μ b) / (μ s - μ b) else 1)) * ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (if b = s then (μ s + 1 - μ a) / (μ s - μ a) else 1))`. Unfold `Vand`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl (fun a ha => ?_)` and prove the remaining obligations.

Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl (fun b hb => hfac a ha b hb)`. Establish `hA : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (if a = s then (μ s + 1 - μ b) / (μ s - μ b) else 1)) = ∏ b ∈ univ.filter (fun b : Fin n => s < b), (μ s + 1 - μ b) / (μ s - μ b)`. Rewrite using `[Finset.prod_eq_single s]`. Conclude with `Finset.prod_congr rfl (fun b _ => if_pos rfl)`.

Introduce `a _ ha`. Conclude with `Finset.prod_eq_one (fun b _ => if_neg ha)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ s) h`. Establish `hB : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (if b = s then (μ s + 1 - μ a) / (μ s - μ a) else 1)) = ∏ a ∈ univ.filter (fun a : Fin n => a < s), (μ s + 1 - μ a) / (μ s - μ a)`.

Rewrite using `[Finset.prod_filter]`. Use `Finset.prod_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.prod_ite_eq']`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[hsplit, hA, hB]`.

Unfold `ratioV`. Rewrite using `[← Finset.prod_filter_mul_prod_filter_not (univ.erase s) (fun x => x < s)]`. Establish `e1 : (univ.erase s).filter (fun x => x < s) = univ.filter (fun x : Fin n => x < s)`. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]`.

Conclude with `⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩`. Establish `e2 : (univ.erase s).filter (fun x => ¬ x < s) = univ.filter (fun x : Fin n => s < x)`. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and, not_lt]`. Conclude with `⟨fun h => lt_of_le_of_ne h.2 (Ne.symm h.1), fun h => ⟨ne_of_gt h, le_of_lt h⟩⟩`.

Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ratioV_eq_vand {μ : Fin n → ℝ} (hμ : StrictAnti μ) (s : Fin n) :
    ratioV μ s = Vand (μ + Pi.single s 1) / Vand μ := by
  have hne : ∀ a b : Fin n, a ≠ b → μ a - μ b ≠ 0 := fun a b h => sub_ne_zero.mpr (hμ.injective.ne h)
  have hV : Vand μ ≠ 0 := (vand_pos hμ).ne'
  have hfac : ∀ a ∈ (univ : Finset (Fin n)), ∀ b ∈ univ.filter (fun b : Fin n => a < b),
      (μ + Pi.single s (1 : ℝ) : Fin n → ℝ) a - (μ + Pi.single s (1 : ℝ) : Fin n → ℝ) b =
        (μ a - μ b) * ((if a = s then (μ s + 1 - μ b) / (μ s - μ b) else 1) *
          (if b = s then (μ s + 1 - μ a) / (μ s - μ a) else 1)) := by
    intro a _ b hb
    have hab : a < b := (Finset.mem_filter.mp hb).2
    have hab' : a ≠ b := ne_of_lt hab
    by_cases ha : a = s
    · subst ha
      have h1 : μ a - μ b ≠ 0 := hne a b hab'
      rw [if_pos rfl, if_neg hab'.symm, mul_one]
      simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab'.symm, add_zero]
      field_simp <;> ring
    · by_cases hb' : b = s
      · subst hb'
        have h2 : μ b - μ a ≠ 0 := hne b a hab'.symm
        rw [if_neg ha, if_pos rfl, one_mul]
        simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne ha, add_zero]
        field_simp <;> ring
      · rw [if_neg ha, if_neg hb', mul_one, mul_one]
        simp only [Pi.add_apply, Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb', add_zero]
  rw [eq_div_iff hV]
  have hsplit : Vand (μ + Pi.single s 1) = Vand μ *
      ((∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
          (if a = s then (μ s + 1 - μ b) / (μ s - μ b) else 1)) *
        ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
          (if b = s then (μ s + 1 - μ a) / (μ s - μ a) else 1)) := by
    unfold Vand
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun a ha => ?_)
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun b hb => hfac a ha b hb)
  have hA : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
          (if a = s then (μ s + 1 - μ b) / (μ s - μ b) else 1)) =
        ∏ b ∈ univ.filter (fun b : Fin n => s < b), (μ s + 1 - μ b) / (μ s - μ b) := by
    rw [Finset.prod_eq_single s]
    · exact Finset.prod_congr rfl (fun b _ => if_pos rfl)
    · intro a _ ha
      exact Finset.prod_eq_one (fun b _ => if_neg ha)
    · intro h
      exact absurd (Finset.mem_univ s) h
  have hB : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
          (if b = s then (μ s + 1 - μ a) / (μ s - μ a) else 1)) =
        ∏ a ∈ univ.filter (fun a : Fin n => a < s), (μ s + 1 - μ a) / (μ s - μ a) := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    rw [Finset.prod_ite_eq']
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hsplit, hA, hB]
  unfold ratioV
  rw [← Finset.prod_filter_mul_prod_filter_not (univ.erase s) (fun x => x < s)]
  have e1 : (univ.erase s).filter (fun x => x < s) = univ.filter (fun x : Fin n => x < s) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
    exact ⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩
  have e2 : (univ.erase s).filter (fun x => ¬ x < s) = univ.filter (fun x : Fin n => s < x) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h.2 (Ne.symm h.1), fun h => ⟨ne_of_gt h, le_of_lt h⟩⟩
  rw [e1, e2]
  ring

/- English proof (translation)
Establish `gen : ∀ m : ℕ, ∏ k ∈ range m, ((m : ℝ) - (k : ℝ)) = (m.factorial : ℝ)`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`.

Rewrite using `[Finset.prod_range_succ', Nat.factorial_succ, Nat.cast_mul, ← ih]`. Establish `e : ∀ k ∈ range m, (((m + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) = (m : ℝ) - (k : ℝ)`. Introduce `k _`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.prod_congr rfl e]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ∏ a ∈ univ.filter (fun a : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) = ∏ k ∈ range (b : ℕ), (((b : ℕ) : ℝ) - (k : ℝ))`. Apply `Finset.prod_nbij (fun a : Fin n => (a : ℕ))` to reduce the goal to its premises.

Introduce `a ha`. Conclude with `Finset.mem_range.mpr (Finset.mem_filter.mp ha).2`. Introduce `a _ a' _ h`. Conclude with `Fin.ext h`. Introduce `k hk`.

Establish `hk' : k < (b : ℕ)` using `Finset.mem_range.mp hk`. Use `⟨⟨k, lt_trans hk' b.isLt⟩, ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]`. Conclude with `hk'`. Introduce `a _`.

Both sides reduce to the same expression. Rewrite using `[h1, gen]`.
-/
theorem prod_sub_lt_eq_factorial (b : Fin n) :
    ∏ a ∈ univ.filter (fun a : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) = ((b : ℕ).factorial : ℝ) := by
  have gen : ∀ m : ℕ, ∏ k ∈ range m, ((m : ℝ) - (k : ℝ)) = (m.factorial : ℝ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_range_succ', Nat.factorial_succ, Nat.cast_mul, ← ih]
      have e : ∀ k ∈ range m, (((m + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) = (m : ℝ) - (k : ℝ) := by
        intro k _
        push_cast
        ring
      rw [Finset.prod_congr rfl e]
      push_cast
      ring
  have h1 : ∏ a ∈ univ.filter (fun a : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ k ∈ range (b : ℕ), (((b : ℕ) : ℝ) - (k : ℝ)) := by
    apply Finset.prod_nbij (fun a : Fin n => (a : ℕ))
    · intro a ha
      exact Finset.mem_range.mpr (Finset.mem_filter.mp ha).2
    · intro a _ a' _ h
      exact Fin.ext h
    · intro k hk
      have hk' : k < (b : ℕ) := Finset.mem_range.mp hk
      refine ⟨⟨k, lt_trans hk' b.isLt⟩, ?_, rfl⟩
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact hk'
    · intro a _
      rfl
  rw [h1, gen]

/- English proof (translation)
Rewrite using `[Finset.prod_comm' (t' := univ) (s' := fun b => univ.filter (fun a : Fin n => a < b)) (by intro a b; simp)]`. Rewrite using `[Finset.prod_congr rfl (fun b _ => prod_sub_lt_eq_factorial b)]`. Conclude with `Fin.prod_univ_eq_prod_range (fun i => (i.factorial : ℝ)) n`.
-/
theorem prod_pairs_eq_factorial (n : ℕ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ i ∈ range n, (i.factorial : ℝ) := by
  rw [Finset.prod_comm' (t' := univ) (s' := fun b => univ.filter (fun a : Fin n => a < b))
    (by intro a b; simp)]
  rw [Finset.prod_congr rfl (fun b _ => prod_sub_lt_eq_factorial b)]
  exact Fin.prod_univ_eq_prod_range (fun i => (i.factorial : ℝ)) n

/- English proof (translation)
Unfold `dimVlam Vand`. Rewrite using `[prod_pairs_eq_factorial]`. Use `congr 1`. Use `Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun b hb => ?_))` and prove the remaining obligations. Conclude with `abs_of_pos (sub_pos.mpr (hlam (Finset.mem_filter.mp hb).2))`.
-/
theorem dimVlam_eq_vand {lam : Fin n → ℝ} (hlam : StrictAnti lam) :
    dimVlam lam = Vand lam / ∏ i ∈ range n, (i.factorial : ℝ) := by
  unfold dimVlam Vand
  rw [prod_pairs_eq_factorial]
  congr 1
  refine Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun b hb => ?_))
  exact abs_of_pos (sub_pos.mpr (hlam (Finset.mem_filter.mp hb).2))

end ReciprocityTheory.ChartRestriction.DS
