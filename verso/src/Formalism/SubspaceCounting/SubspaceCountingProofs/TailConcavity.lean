import Formalism.SubspaceCounting.StatementB

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.G0

namespace TailConcavityP

def g (k : ℕ) (b : ℝ) : ℝ := ∑ i ∈ range k, 1 / (b + i + 1)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[prod_range_succ, ← ih]`. Establish `h` using `Nat.add_one_mul_choose_eq (y + k) k`.

Establish `h2 : y + (k + 1) = y + k + 1` using `by omega`. Rewrite using `[h2]`. Establish `h3 : (((y + k + 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = ((y : ℝ) + k + 1) * (((y + k).choose k : ℕ) : ℝ)`. Use `congrArg (fun n : ℕ => (n : ℝ)) h.symm` as an intermediate fact. Move the coercions through the operations in `at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk : (k : ℝ) + 1 ≠ 0` using `by positivity`. Rewrite using `[mul_div_assoc', eq_div_iff hk]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma choose_cast (y k : ℕ) :
    ((y + k).choose k : ℝ) = ∏ i ∈ range k, (((y : ℝ) + i + 1) / (i + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ← ih]
    have h := Nat.add_one_mul_choose_eq (y + k) k
    have h2 : y + (k + 1) = y + k + 1 := by omega
    rw [h2]
    have h3 : (((y + k + 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) =
        ((y : ℝ) + k + 1) * (((y + k).choose k : ℕ) : ℝ) := by
      have := congrArg (fun n : ℕ => (n : ℝ)) h.symm
      push_cast at this
      linarith
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    rw [mul_div_assoc', eq_div_iff hk]
    linarith

/- English proof (translation)
Unfold `fTail`. Rewrite using `[choose_cast, Real.log_prod]`. Apply `sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Apply the tactic sequence `rw [Real.log_div] <;> positivity`.

Introduce `i _`. Check the signs of the components of the expression.
-/
lemma fTail_eq (k y : ℕ) :
    fTail k y = ∑ i ∈ range k, (Real.log ((y : ℝ) + i + 1) - Real.log ((i : ℝ) + 1)) := by
  unfold fTail
  rw [choose_cast, Real.log_prod]
  · apply sum_congr rfl
    intro i _
    rw [Real.log_div] <;> positivity
  · intro i _
    positivity

/- English proof (translation)
Establish `hb : (0 : ℝ) < b + i + 1` using `by positivity`. Establish `ha : (0 : ℝ) < a + i + 1` using `by positivity`. Rewrite using `[← Real.log_div ha.ne' hb.ne']`. Establish `h1` using `Real.log_le_sub_one_of_pos (div_pos ha hb)`. Establish `e : ((a : ℝ) + i + 1) / (b + i + 1) - 1 = 1 / ((b : ℝ) + i + 1) * ((a : ℝ) - b)`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma term_le (a b i : ℕ) :
    Real.log ((a : ℝ) + i + 1) - Real.log ((b : ℝ) + i + 1) ≤
      1 / ((b : ℝ) + i + 1) * ((a : ℝ) - b) := by
  have hb : (0 : ℝ) < b + i + 1 := by positivity
  have ha : (0 : ℝ) < a + i + 1 := by positivity
  rw [← Real.log_div ha.ne' hb.ne']
  have h1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
  have e : ((a : ℝ) + i + 1) / (b + i + 1) - 1 = 1 / ((b : ℝ) + i + 1) * ((a : ℝ) - b) := by
    field_simp
    ring
  linarith

/- English proof (translation)
Rewrite using `[fTail_eq, fTail_eq, ← sum_sub_distrib, g, sum_mul]`. Apply `sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Use `term_le a b i` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma fTail_sub_le (k a b : ℕ) : fTail k a - fTail k b ≤ g k b * ((a : ℝ) - b) := by
  rw [fTail_eq, fTail_eq, ← sum_sub_distrib, g, sum_mul]
  apply sum_le_sum
  intro i _
  have := term_le a b i
  linarith

/- English proof (translation)
Unfold `g`. Apply `sum_nonneg` to reduce the goal to its premises. Introduce `i _`. Check the signs of the components of the expression.
-/
lemma g_nonneg (k : ℕ) {b : ℝ} (hb : 0 ≤ b) : 0 ≤ g k b := by
  unfold g
  apply sum_nonneg
  intro i _
  positivity

/- English proof (translation)
Unfold `g`. Apply `sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Apply `one_div_le_one_div_of_le (by positivity) (by linarith)` to reduce the goal to its premises.
-/
lemma g_anti (k : ℕ) {b b' : ℝ} (hb : 0 ≤ b) (h : b ≤ b') : g k b' ≤ g k b := by
  unfold g
  apply sum_le_sum
  intro i _
  apply one_div_le_one_div_of_le (by positivity) (by linarith)

/- English proof (translation)
Unfold `g`. Rewrite using `[sum_div]`. Apply `sum_le_sum` to reduce the goal to its premises. Introduce `i hi`. Establish `hi' : (i : ℝ) + 1 ≤ k`.

Establish `: i + 1 ≤ k` using `mem_range.mp hi`. Conclude with `this` after adjusting the coercions. Establish `hi0 : (0 : ℝ) ≤ i` using `i.cast_nonneg`. Establish `h0 : (0 : ℝ) < b + i + 1` using `by linarith`. Rewrite using `[div_div]`.

Apply `one_div_le_one_div_of_le (by positivity) (by linarith)` to reduce the goal to its premises.
-/
lemma g_four {k : ℕ} {b : ℝ} (hb : (k : ℝ) ≤ b) : g k (4 * b) ≤ g k b / 2 := by
  unfold g
  rw [sum_div]
  apply sum_le_sum
  intro i hi
  have hi' : (i : ℝ) + 1 ≤ k := by
    have : i + 1 ≤ k := mem_range.mp hi
    exact_mod_cast this
  have hi0 : (0 : ℝ) ≤ i := i.cast_nonneg
  have h0 : (0 : ℝ) < b + i + 1 := by linarith
  rw [div_div]
  apply one_div_le_one_div_of_le (by positivity) (by linarith)

/- English proof (translation)
Establish `h : ∑ i ∈ range k, (1 : ℝ) / (2 * b) ≤ g k b`. Unfold `g`. Apply `sum_le_sum` to reduce the goal to its premises. Introduce `i hi`. Establish `hi' : (i : ℝ) + 1 ≤ k`.

Establish `: i + 1 ≤ k` using `mem_range.mp hi`. Conclude with `this` after adjusting the coercions. Apply `one_div_le_one_div_of_le (by positivity) (by linarith)` to reduce the goal to its premises. Rewrite `h` using `[sum_const, card_range, nsmul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma g_lower {k : ℕ} {b : ℝ} (hk : (k : ℝ) ≤ b) (hb : 0 < b) : (k : ℝ) / (2 * b) ≤ g k b := by
  have h : ∑ i ∈ range k, (1 : ℝ) / (2 * b) ≤ g k b := by
    unfold g
    apply sum_le_sum
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ k := by
      have : i + 1 ≤ k := mem_range.mp hi
      exact_mod_cast this
    apply one_div_le_one_div_of_le (by positivity) (by linarith)
  rw [sum_const, card_range, nsmul_eq_mul] at h
  calc (k : ℝ) / (2 * b) = k * (1 / (2 * b)) := by ring
    _ ≤ g k b := h

def cn (k N : ℕ) (B : Fin N → ℕ) (l : ℕ) : ℝ :=
  if h : l < N then g k (B ⟨l, h⟩) else 0

def en (k N : ℕ) (B : Fin N → ℕ) (u : ℕ) : ℝ :=
  cn k N B u - (if u = 0 then 0 else cn k N B (u - 1))

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simp [en]`. Consider the case `succ l ih`. Rewrite using `[sum_range_succ, ih]`. Simplify using `[en]`.
-/
lemma tele (k N : ℕ) (B : Fin N → ℕ) (l : ℕ) :
    ∑ u ∈ range (l + 1), en k N B u = cn k N B l := by
  induction l with
  | zero => simp [en]
  | succ l ih =>
    rw [sum_range_succ, ih]
    simp [en]

end TailConcavityP

end Formalism.G0

open Formalism.G0.TailConcavityP in
/- English proof (translation)
Introduce `N k' X u₀ α B hu hkB hB4 hT hX`. Break down `Nat.eq_zero_or_pos k' with hk0 | hkpos` into its components or cases. Substitute `hk0` using the available equality. Simplify using `[fTail]`. Use `set U : Fin N := ⟨u₀, hu⟩ with hU`.

Establish `hbk : (k' : ℝ) ≤ B U` using `by exact_mod_cast hkB U`. Establish `hkpos' : (0 : ℝ) < k'` using `by exact_mod_cast hkpos`. Establish `hbpos : (0 : ℝ) < B U` using `lt_of_lt_of_le hkpos' hbk`. Establish `hcn : ∀ l : Fin N, cn k' N B l.val = g k' (B l)`. Introduce `l`.

Simplify using `[cn, l.isLt]`. Establish `hprev : ∀ u : Fin N, u.val ≠ 0 → ∃ hp : u.val - 1 < N, 4 * B u ≤ B ⟨u.val - 1, hp⟩`. Introduce `u hu0`. Use `⟨by omega, ?_⟩` and prove the remaining obligations. Establish `h : (u.val - 1) + 1 < N` using `by omega`.

Establish `h4` using `hB4 ⟨u.val - 1, by omega⟩ h`. Establish `e : (⟨u.val - 1 + 1, h⟩ : Fin N) = u` using `Fin.ext (by dsimp; omega)`. Rewrite `h4` using `[e]`. Conclude with `h4`. Establish `hen_eq : ∀ u : Fin N, u.val ≠ 0 → ∃ hp : u.val - 1 < N, en k' N B u.val = g k' (B u) - g k' (B ⟨u.val - 1, hp⟩) ∧ 4 * B u ≤ B ⟨u.val - 1, hp⟩`.

Introduce `u hu0`. Take `⟨hp, h4⟩` from `hprev u hu0`. Use `⟨hp, ?_, h4⟩` and prove the remaining obligations. Simplify using `only [en, if_neg hu0, hcn u]`. Simplify using `[cn, hp]`.

Establish `hen0 : ∀ u : Fin N, u.val = 0 → en k' N B u.val = g k' (B u)`. Introduce `u hu0`. Simplify using `only [en, hu0, if_true, sub_zero]`. Rewrite using `[← hu0, hcn u]`. Establish `en_nonneg : ∀ u : Fin N, 0 ≤ en k' N B u.val`.

Introduce `u`. Distinguish the cases in `hu0 : u.val = 0`. Rewrite using `[hen0 u hu0]`. Conclude with `g_nonneg k' (by positivity)`. Take `⟨hp, he, h4⟩` from `hen_eq u hu0`.

Rewrite using `[he]`. Establish `: ((B u : ℕ) : ℝ) ≤ (B ⟨u.val - 1, hp⟩ : ℝ)` using `by exact_mod_cast (by omega : B u ≤ B ⟨u.val - 1, hp⟩)`. Use `g_anti k' (by positivity) this` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Set `d : Fin N → ℝ` to `fun l => (α l : ℝ) - B l`.

Set `D : Fin N → ℝ` to `fun u => ∑ l : Fin N, if u.val ≤ l.val then d l else 0`. Establish `hD : ∀ u : Fin N, D u = (tailSum α u.val : ℝ) - tailSum B u.val`. Introduce `u`. Simplify using `only [D, d, tailSum]`. Use `push_cast`.

Rewrite using `[← sum_sub_distrib]`. Apply `sum_congr rfl` to reduce the goal to its premises. Introduce `l _`. Apply the tactic sequence `split_ifs <;> ring`. Establish `D_nonpos : ∀ u : Fin N, D u ≤ 0`.

Introduce `u`. Rewrite using `[hD u]`. Establish `: (tailSum α u.val : ℝ) ≤ tailSum B u.val` using `by exact_mod_cast hT u.val`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `DU : D U ≤ -(X : ℝ)`.

Rewrite using `[hD U]`. Establish `: (tailSum α u₀ : ℝ) + X ≤ tailSum B u₀` using `by exact_mod_cast hX`. Simplify using `only [hU]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `step1 : ∑ l, fTail k' (α l) - ∑ l, fTail k' (B l) ≤ ∑ l, cn k' N B l.val * d l`.

Rewrite using `[← sum_sub_distrib]`. Apply `sum_le_sum` to reduce the goal to its premises. Introduce `l _`. Rewrite using `[hcn l]`. Conclude with `fTail_sub_le k' (α l) (B l)`.

Establish `step2 : ∑ l, cn k' N B l.val * d l = ∑ u : Fin N, en k' N B u.val * D u`. Establish `hc : ∀ l : Fin N, cn k' N B l.val = ∑ u : Fin N, if u.val ≤ l.val then en k' N B u.val else 0`. Introduce `l`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun u => if u ≤ l.val then en k' N B u else 0), ← sum_filter, ← tele]`. Apply `sum_congr _ (fun _ _ => rfl)` to reduce the goal to its premises.

Use extensionality with `u`. Simplify using `only [mem_filter, mem_range]`. Use `l.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `only [D, mul_sum]`.

Repeatedly rewrite using `[hc, sum_mul]`. Rewrite using `[sum_comm]`. Apply `sum_congr rfl` to reduce the goal to its premises. Introduce `u _`. Apply `sum_congr rfl` to reduce the goal to its premises.

Introduce `l _`. Apply the tactic sequence `split_ifs <;> simp`. Establish `step3 : ∑ u : Fin N, en k' N B u.val * D u ≤ en k' N B U.val * D U`. Rewrite using `[← Finset.add_sum_erase univ _ (mem_univ U)]`. Establish `: ∑ x ∈ univ.erase U, en k' N B x.val * D x ≤ 0` using `sum_nonpos (fun x _ => mul_nonpos_of_nonneg_of_nonpos (en_nonneg x) (D_nonpos x))`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hgb` using `g_lower hbk hbpos`. Establish `hen : (k' : ℝ) / (4 * B U) ≤ en k' N B U.val`. Establish `e2 : (k' : ℝ) / (4 * B U) = (k' : ℝ) / (2 * B U) / 2`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hu0 : U.val = 0`. Rewrite using `[hen0 U hu0, e2]`. Establish `: (0 : ℝ) ≤ (k' : ℝ) / (2 * B U)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨hp, he, h4⟩` from `hen_eq U hu0`. Rewrite using `[he, e2]`. Establish `h4' : 4 * ((B U : ℕ) : ℝ) ≤ (B ⟨U.val - 1, hp⟩ : ℝ)` using `by exact_mod_cast h4`. Establish `h5` using `g_anti k' (by positivity) h4'`. Establish `h6` using `g_four hbk`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `step4 : en k' N B U.val * D U ≤ -((k' : ℝ) / (4 * B U) * X)`. Establish `h1 : en k' N B U.val * D U ≤ en k' N B U.val * (-(X : ℝ))` using `mul_le_mul_of_nonneg_left DU (en_nonneg U)`. Establish `h2 : (k' : ℝ) / (4 * B U) * X ≤ en k' N B U.val * X` using `mul_le_mul_of_nonneg_right hen (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hfin : (X : ℝ) * k' / (4 * B U) = (k' : ℝ) / (4 * B U) * X` using `by ring`. Use `show ∑ l, fTail k' (α l) ≤ ∑ l, fTail k' (B l) - (X : ℝ) * k' / (4 * B U)`. Rewrite using `[hfin]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Formalism.G0.tail_concavity : TailConcavity := by
  intro N k' X u₀ α B hu hkB hB4 hT hX
  rcases Nat.eq_zero_or_pos k' with hk0 | hkpos
  · subst hk0
    simp [fTail]
  set U : Fin N := ⟨u₀, hu⟩ with hU
  have hbk : (k' : ℝ) ≤ B U := by exact_mod_cast hkB U
  have hkpos' : (0 : ℝ) < k' := by exact_mod_cast hkpos
  have hbpos : (0 : ℝ) < B U := lt_of_lt_of_le hkpos' hbk
  have hcn : ∀ l : Fin N, cn k' N B l.val = g k' (B l) := by
    intro l
    simp [cn, l.isLt]

  have hprev : ∀ u : Fin N, u.val ≠ 0 →
      ∃ hp : u.val - 1 < N, 4 * B u ≤ B ⟨u.val - 1, hp⟩ := by
    intro u hu0
    refine ⟨by omega, ?_⟩
    have h : (u.val - 1) + 1 < N := by omega
    have h4 := hB4 ⟨u.val - 1, by omega⟩ h
    have e : (⟨u.val - 1 + 1, h⟩ : Fin N) = u := Fin.ext (by dsimp; omega)
    rw [e] at h4
    exact h4
  have hen_eq : ∀ u : Fin N, u.val ≠ 0 → ∃ hp : u.val - 1 < N,
      en k' N B u.val = g k' (B u) - g k' (B ⟨u.val - 1, hp⟩) ∧ 4 * B u ≤ B ⟨u.val - 1, hp⟩ := by
    intro u hu0
    obtain ⟨hp, h4⟩ := hprev u hu0
    refine ⟨hp, ?_, h4⟩
    simp only [en, if_neg hu0, hcn u]
    simp [cn, hp]
  have hen0 : ∀ u : Fin N, u.val = 0 → en k' N B u.val = g k' (B u) := by
    intro u hu0
    simp only [en, hu0, if_true, sub_zero]
    rw [← hu0, hcn u]
  have en_nonneg : ∀ u : Fin N, 0 ≤ en k' N B u.val := by
    intro u
    by_cases hu0 : u.val = 0
    · rw [hen0 u hu0]
      exact g_nonneg k' (by positivity)
    · obtain ⟨hp, he, h4⟩ := hen_eq u hu0
      rw [he]
      have : ((B u : ℕ) : ℝ) ≤ (B ⟨u.val - 1, hp⟩ : ℝ) := by exact_mod_cast (by omega : B u ≤ B ⟨u.val - 1, hp⟩)
      have := g_anti k' (by positivity) this
      linarith

  let d : Fin N → ℝ := fun l => (α l : ℝ) - B l
  let D : Fin N → ℝ := fun u => ∑ l : Fin N, if u.val ≤ l.val then d l else 0
  have hD : ∀ u : Fin N, D u = (tailSum α u.val : ℝ) - tailSum B u.val := by
    intro u
    simp only [D, d, tailSum]
    push_cast
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro l _
    split_ifs <;> ring
  have D_nonpos : ∀ u : Fin N, D u ≤ 0 := by
    intro u
    rw [hD u]
    have : (tailSum α u.val : ℝ) ≤ tailSum B u.val := by exact_mod_cast hT u.val
    linarith
  have DU : D U ≤ -(X : ℝ) := by
    rw [hD U]
    have : (tailSum α u₀ : ℝ) + X ≤ tailSum B u₀ := by exact_mod_cast hX
    simp only [hU]
    linarith

  have step1 : ∑ l, fTail k' (α l) - ∑ l, fTail k' (B l) ≤ ∑ l, cn k' N B l.val * d l := by
    rw [← sum_sub_distrib]
    apply sum_le_sum
    intro l _
    rw [hcn l]
    exact fTail_sub_le k' (α l) (B l)

  have step2 : ∑ l, cn k' N B l.val * d l = ∑ u : Fin N, en k' N B u.val * D u := by
    have hc : ∀ l : Fin N, cn k' N B l.val =
        ∑ u : Fin N, if u.val ≤ l.val then en k' N B u.val else 0 := by
      intro l
      rw [Fin.sum_univ_eq_sum_range (fun u => if u ≤ l.val then en k' N B u else 0),
        ← sum_filter, ← tele]
      apply sum_congr _ (fun _ _ => rfl)
      ext u
      simp only [mem_filter, mem_range]
      have := l.isLt
      omega
    simp only [D, mul_sum]
    simp_rw [hc, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro l _
    split_ifs <;> simp

  have step3 : ∑ u : Fin N, en k' N B u.val * D u ≤ en k' N B U.val * D U := by
    rw [← Finset.add_sum_erase univ _ (mem_univ U)]
    have : ∑ x ∈ univ.erase U, en k' N B x.val * D x ≤ 0 :=
      sum_nonpos (fun x _ => mul_nonpos_of_nonneg_of_nonpos (en_nonneg x) (D_nonpos x))
    linarith

  have hgb := g_lower hbk hbpos
  have hen : (k' : ℝ) / (4 * B U) ≤ en k' N B U.val := by
    have e2 : (k' : ℝ) / (4 * B U) = (k' : ℝ) / (2 * B U) / 2 := by
      field_simp
      ring
    by_cases hu0 : U.val = 0
    · rw [hen0 U hu0, e2]
      have : (0 : ℝ) ≤ (k' : ℝ) / (2 * B U) := by positivity
      linarith
    · obtain ⟨hp, he, h4⟩ := hen_eq U hu0
      rw [he, e2]
      have h4' : 4 * ((B U : ℕ) : ℝ) ≤ (B ⟨U.val - 1, hp⟩ : ℝ) := by exact_mod_cast h4
      have h5 := g_anti k' (by positivity) h4'
      have h6 := g_four hbk
      linarith
  have step4 : en k' N B U.val * D U ≤ -((k' : ℝ) / (4 * B U) * X) := by
    have h1 : en k' N B U.val * D U ≤ en k' N B U.val * (-(X : ℝ)) :=
      mul_le_mul_of_nonneg_left DU (en_nonneg U)
    have h2 : (k' : ℝ) / (4 * B U) * X ≤ en k' N B U.val * X :=
      mul_le_mul_of_nonneg_right hen (by positivity)
    linarith
  have hfin : (X : ℝ) * k' / (4 * B U) = (k' : ℝ) / (4 * B U) * X := by ring
  show ∑ l, fTail k' (α l) ≤ ∑ l, fTail k' (B l) - (X : ℝ) * k' / (4 * B U)
  rw [hfin]
  linarith
