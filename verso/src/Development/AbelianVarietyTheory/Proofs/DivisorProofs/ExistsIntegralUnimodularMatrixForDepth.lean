import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory

noncomputable section

variable {C : Type} [Field C]

/- English proof (translation)
Consider the cases of `a with`. Consider the case `top => exact le_top`. Consider the case `coe r`. Establish `e : ((N • r : ℝ) : WithTop ℝ) = N • (r : WithTop ℝ)` using `WithTop.coe_nsmul _ _`. Rewrite `h` using `[← e]`.

Establish `h' : (0 : ℝ) ≤ N • r` using `by exact_mod_cast h`. Rewrite `h'` using `[nsmul_eq_mul]`. Establish `hN' : (0 : ℝ) < N` using `by exact_mod_cast Nat.pos_of_ne_zero hN`. Establish `: 0 ≤ r`. Assume the negation of the conclusion as `hr`.

Use `push Not at hr`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `this` after adjusting the coercions.
-/
theorem powRow_nonneg_of_nsmul {a : WithTop ℝ} {N : ℕ} (hN : N ≠ 0) (h : 0 ≤ N • a) : 0 ≤ a := by
  cases a with
  | top => exact le_top
  | coe r =>
    have e : ((N • r : ℝ) : WithTop ℝ) = N • (r : WithTop ℝ) := WithTop.coe_nsmul _ _
    rw [← e] at h
    have h' : (0 : ℝ) ≤ N • r := by exact_mod_cast h
    rw [nsmul_eq_mul] at h'
    have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have : 0 ≤ r := by
      by_contra hr
      push Not at hr
      nlinarith
    exact_mod_cast this

/- English proof (translation)
Take `⟨x, hx⟩` from `IsAlgClosed.exists_pow_nat_eq y hN`. Use `⟨x, hx, powRow_nonneg_of_nsmul hN.ne' ?_⟩` and prove the remaining obligations. Rewrite using `[← AddValuation.map_pow, hx]`. Conclude with `hy`.
-/
theorem powRow_int_root [IsAlgClosed C] (v : AddValuation C (WithTop ℝ)) {N : ℕ} (hN : 0 < N)
    (y : C) (hy : IsIntV v y) : ∃ x, x ^ N = y ∧ IsIntV v x := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hN
  refine ⟨x, hx, powRow_nonneg_of_nsmul hN.ne' ?_⟩
  rw [← AddValuation.map_pow, hx]
  exact hy

/- English proof (translation)
Unfold `IsIntV`. Rewrite `h` using `[AddValuation.map_mul]`. Establish `hb' : v b ≠ ⊤` using `(v.ne_top_iff).2 hb`. Consider the cases of `hvb : v b with`. Consider the case `top => exact absurd hvb hb'`.

Consider the case `coe r`. Rewrite `h` using `[hvb]`. Consider the cases of `hva : v a with`. Consider the case `top => exact le_top`. Consider the case `coe s`.

Rewrite `h` using `[hva]`. Establish `h2 : r ≤ s + r` using `by exact_mod_cast h`. Conclude with `(by linarith : (0 : ℝ) ≤ s)` after adjusting the coercions.
-/
theorem powRow_int_of_le (v : AddValuation C (WithTop ℝ)) {a b : C} (hb : b ≠ 0)
    (h : v b ≤ v (a * b)) : IsIntV v a := by
  unfold IsIntV
  rw [AddValuation.map_mul] at h
  have hb' : v b ≠ ⊤ := (v.ne_top_iff).2 hb
  cases hvb : v b with
  | top => exact absurd hvb hb'
  | coe r =>
    rw [hvb] at h
    cases hva : v a with
    | top => exact le_top
    | coe s =>
      rw [hva] at h
      have h2 : r ≤ s + r := by exact_mod_cast h
      exact_mod_cast (by linarith : (0 : ℝ) ≤ s)

/- English proof (translation)
Rewrite using `[AddValuation.map_pow, AddValuation.map_neg, AddValuation.map_one, smul_zero]`.
-/
theorem powRow_v_neg_one_pow (v : AddValuation C (WithTop ℝ)) (k : ℕ) : v ((-1 : C) ^ k) = 0 := by
  rw [AddValuation.map_pow, AddValuation.map_neg, AddValuation.map_one, smul_zero]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `z _`. Conclude with `⟨1, fun w => w.elim0, by simp, fun w => w.elim0⟩`.

Consider the case `succ m ih`. Introduce `z hz`. Distinguish the cases in `hli : LinearIndependent C z`. Establish `hmj : m + 1 ≤ j`. Use `finrank_span_eq_card hli` as an intermediate fact.

Simplify using `only [Fintype.card_fin] at this`. Use linear arithmetic over natural numbers and integers. Use `⟨1, ?_, by simp [AddValuation.map_one], fun w hw => absurd hw (by omega)⟩` and prove the remaining obligations. Introduce `w u`. Unfold `IsIntV`.

Rewrite using `[Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Take `⟨g, hg, i, hi⟩` from `Fintype.not_linearIndependent_iff.1 hli`. Take `⟨u0, -, hu0⟩` from `Finset.exists_min_image Finset.univ (fun u => v (g u)) ⟨i, Finset.mem_univ _⟩`. Establish `hg0 : g u0 ≠ 0`.

Introduce `h0`. Apply `hi` to reduce the goal to its premises. Use `hu0 i (Finset.mem_univ _)` as an intermediate fact. Rewrite `this` using `[h0, AddValuation.map_zero]`. Conclude with `(v.top_iff).1 (top_le_iff.1 this)`.

Use `set c : Fin (m + 1) → C := fun u => g u / g u0 with hc`. Establish `hc0 : c u0 = 1` using `div_self hg0`. Establish `hcint : ∀ u, IsIntV v (c u)`. Introduce `u`. Apply `powRow_int_of_le v hg0` to reduce the goal to its premises.

Establish `: c u * g u0 = g u` using `div_mul_cancel₀ _ hg0`. Rewrite using `[this]`. Conclude with `hu0 u (Finset.mem_univ _)`. Establish `hcz : ∑ u, c u • z u = 0`. Establish `: ∑ u, c u • z u = (g u0)⁻¹ • ∑ u, g u • z u`.

Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, hc]`. Simplify using `only [div_eq_mul_inv, mul_comm]`. Rewrite using `[this, hg, smul_zero]`.

Use `choose r hr hrint using fun u => powRow_int_root v hN (c u) (hcint u)`. Use `set r' : Fin (m + 1) → C := Function.update r u0 1 with hr'`. Establish `hr'N : ∀ u, r' u ^ N = c u`. Introduce `u`. Distinguish the cases in `hu : u = u0`.

Substitute `hu` using the available equality. Rewrite using `[hr', Function.update_self, one_pow, hc0]`. Rewrite using `[hr', Function.update_of_ne hu, hr]`. Establish `hr'int : ∀ u, IsIntV v (r' u)`. Introduce `u`.

Distinguish the cases in `hu : u = u0`. Substitute `hu` using the available equality. Rewrite using `[hr', Function.update_self]`. Unfold `IsIntV`. Rewrite using `[AddValuation.map_one]`.

Rewrite using `[hr', Function.update_of_ne hu]`. Conclude with `hrint u`. Establish `hz' : Module.finrank C (Submodule.span C (Set.range (z ∘ u0.succAbove))) ≤ j`. Establish `: Module.Finite C (Submodule.span C (Set.range z))` using `Module.Finite.span_of_finite C (Set.finite_range z)`. Use `le_trans (Submodule.finrank_mono (Submodule.span_mono ?_)) hz` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨_, rfl⟩`. Take `⟨x', hx'int, hx'det, hx'k⟩` from `ih (z ∘ u0.succAbove) hz'`. Set `A : Matrix (Fin (m + 1)) (Fin (m + 1)) C` to `Matrix.of (Fin.snoc (fun w' => Fin.insertNth (α := fun _ => C) u0 0 (x' w')) r')`. Establish `hAlast : ∀ u, A (Fin.last m) u = r' u`.

Introduce `u`. Simplify using `[A, Fin.snoc_last]`. Establish `hAcs : ∀ w' u, A w'.castSucc u = Fin.insertNth (α` using `fun _ => C) u0 0 (x' w') u := by`. Introduce `w' u`. Simplify using `[A, Fin.snoc_castSucc]`.

Use `⟨A, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w u`. Proceed by induction on `w using Fin.lastCases with`. Consider the case `last => rw [hAlast]`. Conclude with `hr'int u`.

Consider the case `cast w'`. Rewrite using `[hAcs]`. Proceed by induction on `u using Fin.succAboveCases u0 with`. Consider the case `x`. Rewrite using `[Fin.insertNth_apply_same]`.

Unfold `IsIntV`. Rewrite using `[AddValuation.map_zero]`. Conclude with `le_top`. Consider the case `p k => rw [Fin.insertNth_apply_succAbove]`. Conclude with `hx'int w' k`.

Rewrite using `[Matrix.det_succ_column A u0]`. Rewrite using `[Fintype.sum_eq_single (Fin.last m)]`. Establish `hsub : A.submatrix (Fin.last m).succAbove u0.succAbove = x'`. Use extensionality with `w' k`. Simplify using `only [Matrix.submatrix_apply, Fin.succAbove_last]`.

Rewrite using `[hAcs, Fin.insertNth_apply_succAbove]`. Rewrite using `[hsub, hAlast]`. Rewrite using `[AddValuation.map_mul, AddValuation.map_mul, powRow_v_neg_one_pow, hx'det]`. Establish `: r' u0 = 1` using `by rw [hr', Function.update_self]`. Rewrite using `[this, AddValuation.map_one]`.

Simplify using the standard rewrite rules. Introduce `w hw`. Proceed by induction on `w using Fin.lastCases with`. Consider the case `last => exact absurd rfl hw`. Consider the case `cast w' => rw [hAcs, Fin.insertNth_apply_same]`.

Simplify using the standard rewrite rules. Introduce `w hw`. Proceed by induction on `w using Fin.lastCases with`. Consider the case `last`. Simplify using `only [hAlast, hr'N]`.

Conclude with `hcz`. Consider the case `cast w'`. Simplify using `only [hAcs]`. Rewrite using `[Fin.sum_univ_succAbove _ u0, Fin.insertNth_apply_same, zero_pow hN.ne', zero_smul, zero_add]`. Simplify using `only [Fin.insertNth_apply_succAbove]`.

Conclude with `hx'k w' (by simpa using hw)`.
-/
theorem powRow_exists [IsAlgClosed C] (v : AddValuation C (WithTop ℝ)) {V : Type} [AddCommGroup V]
    [Module C V] (N : ℕ) (hN : 0 < N) (j : ℕ) : ∀ (m : ℕ) (z : Fin m → V),
    Module.finrank C (Submodule.span C (Set.range z)) ≤ j →
    ∃ x : Matrix (Fin m) (Fin m) C, (∀ w u, IsIntV v (x w u)) ∧ v x.det = 0 ∧
      ∀ w : Fin m, j ≤ w.val → ∑ u, (x w u) ^ N • z u = 0 := by
  intro m
  induction m with
  | zero =>
    intro z _
    exact ⟨1, fun w => w.elim0, by simp, fun w => w.elim0⟩
  | succ m ih =>
    intro z hz
    by_cases hli : LinearIndependent C z
    · have hmj : m + 1 ≤ j := by
        have := finrank_span_eq_card hli
        simp only [Fintype.card_fin] at this
        omega
      refine ⟨1, ?_, by simp [AddValuation.map_one], fun w hw => absurd hw (by omega)⟩
      intro w u
      unfold IsIntV
      rw [Matrix.one_apply]
      split_ifs <;> simp
    · obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
      obtain ⟨u0, -, hu0⟩ := Finset.exists_min_image Finset.univ (fun u => v (g u))
        ⟨i, Finset.mem_univ _⟩
      have hg0 : g u0 ≠ 0 := by
        intro h0
        apply hi
        have := hu0 i (Finset.mem_univ _)
        rw [h0, AddValuation.map_zero] at this
        exact (v.top_iff).1 (top_le_iff.1 this)
      set c : Fin (m + 1) → C := fun u => g u / g u0 with hc
      have hc0 : c u0 = 1 := div_self hg0
      have hcint : ∀ u, IsIntV v (c u) := by
        intro u
        apply powRow_int_of_le v hg0
        have : c u * g u0 = g u := div_mul_cancel₀ _ hg0
        rw [this]
        exact hu0 u (Finset.mem_univ _)
      have hcz : ∑ u, c u • z u = 0 := by
        have : ∑ u, c u • z u = (g u0)⁻¹ • ∑ u, g u • z u := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [smul_smul, hc]
          simp only [div_eq_mul_inv, mul_comm]
        rw [this, hg, smul_zero]
      choose r hr hrint using fun u => powRow_int_root v hN (c u) (hcint u)
      set r' : Fin (m + 1) → C := Function.update r u0 1 with hr'
      have hr'N : ∀ u, r' u ^ N = c u := by
        intro u
        by_cases hu : u = u0
        · subst hu; rw [hr', Function.update_self, one_pow, hc0]
        · rw [hr', Function.update_of_ne hu, hr]
      have hr'int : ∀ u, IsIntV v (r' u) := by
        intro u
        by_cases hu : u = u0
        · subst hu; rw [hr', Function.update_self]; unfold IsIntV; rw [AddValuation.map_one]
        · rw [hr', Function.update_of_ne hu]; exact hrint u
      have hz' : Module.finrank C (Submodule.span C (Set.range (z ∘ u0.succAbove))) ≤ j := by
        have : Module.Finite C (Submodule.span C (Set.range z)) :=
          Module.Finite.span_of_finite C (Set.finite_range z)
        refine le_trans (Submodule.finrank_mono (Submodule.span_mono ?_)) hz
        rintro _ ⟨k, rfl⟩
        exact ⟨_, rfl⟩
      obtain ⟨x', hx'int, hx'det, hx'k⟩ := ih (z ∘ u0.succAbove) hz'
      let A : Matrix (Fin (m + 1)) (Fin (m + 1)) C :=
        Matrix.of (Fin.snoc (fun w' => Fin.insertNth (α := fun _ => C) u0 0 (x' w')) r')
      have hAlast : ∀ u, A (Fin.last m) u = r' u := by
        intro u; simp [A, Fin.snoc_last]
      have hAcs : ∀ w' u, A w'.castSucc u = Fin.insertNth (α := fun _ => C) u0 0 (x' w') u := by
        intro w' u; simp [A, Fin.snoc_castSucc]
      refine ⟨A, ?_, ?_, ?_⟩
      · intro w u
        induction w using Fin.lastCases with
        | last => rw [hAlast]; exact hr'int u
        | cast w' =>
          rw [hAcs]
          induction u using Fin.succAboveCases u0 with
          | x =>
            rw [Fin.insertNth_apply_same]; unfold IsIntV; rw [AddValuation.map_zero]; exact le_top
          | p k => rw [Fin.insertNth_apply_succAbove]; exact hx'int w' k
      · rw [Matrix.det_succ_column A u0]
        rw [Fintype.sum_eq_single (Fin.last m)]
        · have hsub : A.submatrix (Fin.last m).succAbove u0.succAbove = x' := by
            ext w' k
            simp only [Matrix.submatrix_apply, Fin.succAbove_last]
            rw [hAcs, Fin.insertNth_apply_succAbove]
          rw [hsub, hAlast]
          rw [AddValuation.map_mul, AddValuation.map_mul, powRow_v_neg_one_pow, hx'det]
          have : r' u0 = 1 := by rw [hr', Function.update_self]
          rw [this, AddValuation.map_one]
          simp
        · intro w hw
          induction w using Fin.lastCases with
          | last => exact absurd rfl hw
          | cast w' => rw [hAcs, Fin.insertNth_apply_same]; simp
      · intro w hw
        induction w using Fin.lastCases with
        | last =>
          simp only [hAlast, hr'N]
          exact hcz
        | cast w' =>
          simp only [hAcs]
          rw [Fin.sum_univ_succAbove _ u0, Fin.insertNth_apply_same, zero_pow hN.ne', zero_smul,
            zero_add]
          simp only [Fin.insertNth_apply_succAbove]
          exact hx'k w' (by simpa using hw)

/- English proof (translation)
Introduce `C _ _ v V _ _ N hN j m z hz`. Conclude with `powRow_exists v N hN j m z hz`.
-/
theorem powRow_matrix : ∀ (C : Type) [Field C] [IsAlgClosed C] (v : AddValuation C (WithTop ℝ)) (V : Type) [AddCommGroup V] [Module C V] (N : ℕ), 0 < N → ∀ (j m : ℕ) (z : Fin m → V), Module.finrank C (Submodule.span C (Set.range z)) ≤ j → ∃ x : Matrix (Fin m) (Fin m) C, (∀ w u, IsIntV v (x w u)) ∧ v x.det = 0 ∧ ∀ w : Fin m, j ≤ w.val → ∑ u, (x w u) ^ N • z u = 0 := by
  intro C _ _ v V _ _ N hN j m z hz
  exact powRow_exists v N hN j m z hz

end

end GlobalTheory
