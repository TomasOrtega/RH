import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.Imports

open Finset

noncomputable section

namespace GlobalTheory.WigSh.LowerBound

/- English proof (translation)
Rewrite using `[← Finset.compl_singleton, ← Fin.image_succAbove_univ]`. Rewrite using `[Finset.prod_image]`. Introduce `a _ b _ hab`. Conclude with `Fin.succAbove_right_injective hab`.
-/
private theorem prod_erase_succAbove {n : ℕ} (f : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    ∏ j ∈ univ.erase l, f j = ∏ j : Fin n, f (l.succAbove j) := by
  rw [← Finset.compl_singleton, ← Fin.image_succAbove_univ]
  · rw [Finset.prod_image]
    intro a _ b _ hab
    exact Fin.succAbove_right_injective hab

/- English proof (translation)
Establish `: c * b / b ^ 2 = c / b` using `by field_simp`. Rewrite using `[this]`. Conclude with `div_le_div_of_nonneg_right h hb.le`.
-/
private theorem ratio_pos_case {a b c : ℝ} (hb : 0 < b) (h : c ≤ a) :
    c * b / b ^ 2 ≤ a / b := by
  have : c * b / b ^ 2 = c / b := by field_simp
  rw [this]
  exact div_le_div_of_nonneg_right h hb.le

/- English proof (translation)
Establish `g1` using `hG j.succ`. Establish `g2` using `hG j.castSucc`. Break down `lt_or_ge j.castSucc l with hl | hl` into its components or cases. Rewrite using `[Fin.succAbove_of_castSucc_lt _ _ hl]`. Establish `a1 : L l < L j.castSucc` using `hs hl`.

Establish `a2 : L l ≤ L j.succ` using `hs.antitone (Fin.castSucc_lt_iff_succ_le.1 hl)`. Establish `e : G j.castSucc = L j.castSucc - L l` using `by omega`. Establish `e' : (L j.castSucc : ℝ) - L l = G j.castSucc` using `by rw [e]; push_cast; ring`. Rewrite using `[e']`. Apply `ratio_pos_case` to reduce the goal to its premises.

Establish `: (0 : ℤ) < G j.castSucc` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `: G j.succ ≤ M j - L l` using `by omega`. Conclude with `this` after adjusting the coercions. Rewrite using `[Fin.succAbove_of_le_castSucc _ _ hl]`.

Establish `a2 : L j.castSucc ≤ L l` using `hs.antitone hl`. Establish `e : G j.succ = L l - L j.succ` using `by omega`. Establish `e' : (L j.succ : ℝ) - L l = -G j.succ` using `by rw [e]; push_cast; ring`. Rewrite using `[e', div_neg, ← neg_div, mul_comm]`. Apply `ratio_pos_case` to reduce the goal to its premises.

Establish `: (0 : ℤ) < G j.succ` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `: G j.castSucc ≤ -(M j - L l)` using `by omega`. Conclude with `this` after adjusting the coercions.
-/
private theorem factor_lower {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (l : Fin (n + 1))
    (hs : StrictAnti L) (j : Fin n) (h1 : L j.succ < M j) (h2 : M j ≤ L j.castSucc)
    (h3 : M j ≠ L l) (G : Fin (n + 1) → ℤ)
    (hG : ∀ i, G i = max 1 (max (L i - L l) (L l - L i))) :
    (G j.succ : ℝ) * G j.castSucc / (G (l.succAbove j) : ℝ) ^ 2 ≤
      ((M j : ℝ) - L l) / ((L (l.succAbove j) : ℝ) - L l) := by
  have g1 := hG j.succ
  have g2 := hG j.castSucc
  rcases lt_or_ge j.castSucc l with hl | hl
  · rw [Fin.succAbove_of_castSucc_lt _ _ hl]
    have a1 : L l < L j.castSucc := hs hl
    have a2 : L l ≤ L j.succ := hs.antitone (Fin.castSucc_lt_iff_succ_le.1 hl)
    have e : G j.castSucc = L j.castSucc - L l := by omega
    have e' : (L j.castSucc : ℝ) - L l = G j.castSucc := by rw [e]; push_cast; ring
    rw [e']
    apply ratio_pos_case
    · have : (0 : ℤ) < G j.castSucc := by omega
      exact_mod_cast this
    · have : G j.succ ≤ M j - L l := by omega
      exact_mod_cast this
  · rw [Fin.succAbove_of_le_castSucc _ _ hl]
    have a2 : L j.castSucc ≤ L l := hs.antitone hl
    have e : G j.succ = L l - L j.succ := by omega
    have e' : (L j.succ : ℝ) - L l = -G j.succ := by rw [e]; push_cast; ring
    rw [e', div_neg, ← neg_div, mul_comm]
    apply ratio_pos_case
    · have : (0 : ℤ) < G j.succ := by omega
      exact_mod_cast this
    · have : G j.castSucc ≤ -(M j - L l) := by omega
      exact_mod_cast this

end GlobalTheory.WigSh.LowerBound

namespace GlobalTheory.WigSh

open LowerBound

/- English proof (translation)
Use `set G : Fin (n + 1) → ℤ := fun i => max 1 (max (L i - L l) (L l - L i)) with hGdef`. Establish `hG : ∀ i, G i = max 1 (max (L i - L l) (L l - L i))` using `fun i => rfl`. Establish `hpos : ∀ i, (0 : ℝ) < G i` using `fun i => by`. Establish `: (0 : ℤ) < G i` using `by rw [hG]; omega`. Conclude with `this` after adjusting the coercions.

Establish `hl : G l = 1` using `by rw [hG]; omega`. Establish `hG0 : (G 0 : ℝ) ≤ D`. Establish `a : L l ≤ L 0` using `hs.antitone (Fin.zero_le l)`. Establish `: G 0 = 1 ∨ G 0 = L 0 - L l` using `by rw [hG]; omega`. Apply the tactic sequence `rcases this with e | e <;> rw [e] <;> push_cast <;> assumption`.

Establish `hGl : (G (Fin.last n) : ℝ) ≤ D`. Establish `a : L (Fin.last n) ≤ L l` using `hs.antitone (Fin.le_last l)`. Establish `: G (Fin.last n) = 1 ∨ G (Fin.last n) = L l - L (Fin.last n)` using `by rw [hG]; omega`. Apply the tactic sequence `rcases this with e | e <;> rw [e] <;> push_cast <;> assumption`. Use `set P : ℝ := ∏ i, (G i : ℝ) with hP`.

Establish `hPpos : 0 < P` using `Finset.prod_pos fun i _ => hpos i`. Establish `p1 : ∏ j : Fin n, (G j.succ : ℝ) = P / G 0`. Rewrite using `[eq_div_iff (hpos 0).ne', hP, Fin.prod_univ_succ, mul_comm]`. Establish `p2 : ∏ j : Fin n, (G j.castSucc : ℝ) = P / G (Fin.last n)`. Rewrite using `[eq_div_iff (hpos _).ne', hP, Fin.prod_univ_castSucc]`.

Establish `p3 : ∏ j : Fin n, (G (l.succAbove j) : ℝ) = P`. Rewrite using `[hP, Fin.prod_univ_succAbove _ l, hl]`. Simplify using the standard rewrite rules. Unfold `wM`. Rewrite using `[prod_erase_succAbove, ← Finset.prod_div_distrib]`.

Use `le_trans ?_ (Finset.prod_le_prod (f := fun j : Fin n => (G j.succ : ℝ) * G j.castSucc / (G (l.succAbove j) : ℝ) ^ 2) (fun j _ => ?_) (fun j _ => factor_lower l hs j (hbox j).1 (hbox j).2 (hne j) G hG))` and prove the remaining obligations. Rewrite using `[Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_pow, p1, p2, p3]`. Establish `q0` using `hpos 0`. Establish `ql` using `hpos (Fin.last n)`. Establish `: P / G 0 * (P / G (Fin.last n)) / P ^ 2 = ((G 0 : ℝ) * G (Fin.last n))⁻¹`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Apply `inv_anti₀ (mul_pos q0 ql)` to reduce the goal to its premises. Rewrite using `[sq]`. Conclude with `mul_le_mul hG0 hGl ql.le (by linarith)`.

Use `hpos j.succ` as an intermediate fact. Use `hpos j.castSucc` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem inv_sq_le_wM (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ)
    (hs : StrictAnti L) (hbox : ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc)
    (hne : ∀ j, M j ≠ L l) (hD : 1 ≤ D) (h0 : (L 0 : ℝ) - L l ≤ D)
    (hlast : (L l : ℝ) - L (Fin.last n) ≤ D) : (D ^ 2)⁻¹ ≤ GlobalTheory.WigSh.wM L M l := by
  set G : Fin (n + 1) → ℤ := fun i => max 1 (max (L i - L l) (L l - L i)) with hGdef
  have hG : ∀ i, G i = max 1 (max (L i - L l) (L l - L i)) := fun i => rfl
  have hpos : ∀ i, (0 : ℝ) < G i := fun i => by
    have : (0 : ℤ) < G i := by rw [hG]; omega
    exact_mod_cast this
  have hl : G l = 1 := by rw [hG]; omega
  have hG0 : (G 0 : ℝ) ≤ D := by
    have a : L l ≤ L 0 := hs.antitone (Fin.zero_le l)
    have : G 0 = 1 ∨ G 0 = L 0 - L l := by rw [hG]; omega
    rcases this with e | e <;> rw [e] <;> push_cast <;> assumption
  have hGl : (G (Fin.last n) : ℝ) ≤ D := by
    have a : L (Fin.last n) ≤ L l := hs.antitone (Fin.le_last l)
    have : G (Fin.last n) = 1 ∨ G (Fin.last n) = L l - L (Fin.last n) := by rw [hG]; omega
    rcases this with e | e <;> rw [e] <;> push_cast <;> assumption
  set P : ℝ := ∏ i, (G i : ℝ) with hP
  have hPpos : 0 < P := Finset.prod_pos fun i _ => hpos i
  have p1 : ∏ j : Fin n, (G j.succ : ℝ) = P / G 0 := by
    rw [eq_div_iff (hpos 0).ne', hP, Fin.prod_univ_succ, mul_comm]
  have p2 : ∏ j : Fin n, (G j.castSucc : ℝ) = P / G (Fin.last n) := by
    rw [eq_div_iff (hpos _).ne', hP, Fin.prod_univ_castSucc]
  have p3 : ∏ j : Fin n, (G (l.succAbove j) : ℝ) = P := by
    rw [hP, Fin.prod_univ_succAbove _ l, hl]; simp
  unfold wM
  rw [prod_erase_succAbove, ← Finset.prod_div_distrib]
  refine le_trans ?_ (Finset.prod_le_prod
    (f := fun j : Fin n => (G j.succ : ℝ) * G j.castSucc / (G (l.succAbove j) : ℝ) ^ 2)
    (fun j _ => ?_) (fun j _ => factor_lower l hs j (hbox j).1 (hbox j).2 (hne j) G hG))
  · rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_pow, p1, p2, p3]
    have q0 := hpos 0
    have ql := hpos (Fin.last n)
    have : P / G 0 * (P / G (Fin.last n)) / P ^ 2 = ((G 0 : ℝ) * G (Fin.last n))⁻¹ := by
      field_simp
    rw [this]
    apply inv_anti₀ (mul_pos q0 ql)
    rw [sq]
    exact mul_le_mul hG0 hGl ql.le (by linarith)
  · have := hpos j.succ
    have := hpos j.castSucc
    positivity

end GlobalTheory.WigSh
