import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorUniformizerExponent
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.OriginBox

section Entries
variable {k : Type} [Field k] {n n' : Type} {c : ℕ}

/- English proof (translation)
Simplify using `only [stepPt, Matrix.add_apply, Matrix.of_apply, hb, zero_add, dif_pos h]`.
-/
theorem stepPt_var (x₀ : Matrix n n' k) (e : StepVar n c n' → k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) (hb : basePt c x₀ r s = 0) : stepPt x₀ e r s = e ⟨(r, s), h⟩ := by
  simp only [stepPt, Matrix.add_apply, Matrix.of_apply, hb, zero_add, dif_pos h]

/- English proof (translation)
Simplify using `[basePt]`.
-/
theorem basePt_inr_succ (x₀ : Matrix n n' k) (i : Fin c) : basePt c x₀ (.inr i) (.inr i.succ) = 0 := by
  simp [basePt]

/- English proof (translation)
Simplify using `[basePt]`.
-/
theorem basePt_inl_inr (x₀ : Matrix n n' k) (r : n) (i : Fin (c + 1)) : basePt c x₀ (.inl r) (.inr i) = 0 := by
  simp [basePt]

/- English proof (translation)
Simplify using `[basePt]`.
-/
theorem basePt_inr_inl (x₀ : Matrix n n' k) (l : Fin c) (s : n') : basePt c x₀ (.inr l) (.inl s) = 0 := by
  simp [basePt]

end Entries

section Main
variable {k : Type} [Field k] [ValuativeRel k]

/- English proof (translation)
Establish `hbox : ∀ j v {A : ℤ}, boxExp G a a' j v = A → valuation k (e j v) ≤ valuation k ((ϖ ^ A : kˣ) : k)` using `fun j v A hA => hA ▸ he j (Set.mem_univ j) v (Set.mem_univ v)`. Establish `hmul : ∀ {x y : k} {A B : ℤ}, valuation k x ≤ valuation k ((ϖ ^ A : kˣ) : k) → valuation k y ≤ valuation k ((ϖ ^ B : kˣ) : k) → A + B = a + a' → valuation k (x * y) ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k)`. Introduce `x y A B hx hy hAB`. Rewrite using `[← hAB, _root_.zpow_add, Units.val_mul, map_mul, map_mul]`. Conclude with `mul_le_mul' hx hy`.

Unfold `phase`. Use `Valuation.map_sum_le _ fun j _ => Valuation.map_add_le _ ?_ ?_` and prove the remaining obligations. Unfold `ch`. Use `Valuation.map_sum_le _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[stepPt_var _ _ (Or.inl (by simp [Free])) (basePt_inr_succ _ i)]`.

Use `hbox _ _ ?_` and prove the remaining obligations. Simplify using `only [boxExp, auxiliaryVectorUniformizerExponent, Fin.val_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `split_ifs with hc`.

Use `Valuation.map_sum_le _ fun r _ => ?_` and prove the remaining obligations. Unfold `rowVar`. Use `split_ifs with h`. Rewrite using `[Finset.sum_mul]`. Use `Valuation.map_sum_le _ fun l _ => ?_` and prove the remaining obligations.

Use `split_ifs with hl`. Establish `hc' : Odd (G.m - 2 - (j + 1))`. Take `⟨q, hq⟩` from `hc`. Conclude with `⟨q - 1, by omega⟩`. Unfold `colVar`.

Rewrite using `[stepPt_var (c := G.m - 2 - (j + 1)) (r := .inr l) (s := .inl r) _ _ (Or.inr ⟨hc', hl⟩) (basePt_inr_inl _ l r), stepPt_var (c := G.m - 2 - j) (r := .inl r) (s := .inr ⟨(G.m - 2 - j) / 2, by omega⟩) _ _ (Or.inr ⟨hc, rfl⟩) (basePt_inl_inr _ r _)]`. Use `hmul (hbox _ _ rfl) (hbox _ _ rfl) ?_` and prove the remaining obligations. Take `⟨q, hq⟩` from `hc`. Establish `h1 : (G.m - 2 - (j + 1) : ℕ) = q + q - 1` using `by omega`. Establish `h2 : (l : ℕ) + 1 = q` using `by omega`.

Establish `h3 : (G.m - 2 - j) / 2 = q` using `by omega`. Establish `h4 : (((q + q - 1 : ℕ)) : ℤ) = 2 * (q : ℤ) - 1` using `by omega`. Establish `h5 : ((l : ℕ) : ℤ) = (q : ℤ) - 1` using `by omega`. Simplify using `only [boxExp, auxiliaryVectorUniformizerExponent]`. Rewrite using `[h5, h3, hq, h1, h4]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem phase_origin_le (G : Grid k) (ϖ : kˣ) (a a' : ℤ) (e : Vars G) (he : e ∈ box G ϖ a a') :
    valuation k (phase (0 : ColArgs G) e) ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) := by
  have hbox : ∀ j v {A : ℤ}, boxExp G a a' j v = A → valuation k (e j v) ≤ valuation k ((ϖ ^ A : kˣ) : k) :=
    fun j v A hA => hA ▸ he j (Set.mem_univ j) v (Set.mem_univ v)
  have hmul : ∀ {x y : k} {A B : ℤ}, valuation k x ≤ valuation k ((ϖ ^ A : kˣ) : k) →
      valuation k y ≤ valuation k ((ϖ ^ B : kˣ) : k) → A + B = a + a' →
      valuation k (x * y) ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) := by
    intro x y A B hx hy hAB
    rw [← hAB, _root_.zpow_add, Units.val_mul, map_mul, map_mul]
    exact mul_le_mul' hx hy
  unfold phase
  refine Valuation.map_sum_le _ fun j _ => Valuation.map_add_le _ ?_ ?_
  · unfold ch
    refine Valuation.map_sum_le _ fun i _ => ?_
    rw [stepPt_var _ _ (Or.inl (by simp [Free])) (basePt_inr_succ _ i)]
    refine hbox _ _ ?_
    simp only [boxExp, auxiliaryVectorUniformizerExponent, Fin.val_succ]
    push_cast
    ring
  · split_ifs with hc
    · refine Valuation.map_sum_le _ fun r _ => ?_
      unfold rowVar
      split_ifs with h
      · rw [Finset.sum_mul]
        refine Valuation.map_sum_le _ fun l _ => ?_
        split_ifs with hl
        · have hc' : Odd (G.m - 2 - (j + 1)) := by
            obtain ⟨q, hq⟩ := hc
            exact ⟨q - 1, by omega⟩
          unfold colVar
          rw [stepPt_var (c := G.m - 2 - (j + 1)) (r := .inr l) (s := .inl r) _ _ (Or.inr ⟨hc', hl⟩) (basePt_inr_inl _ l r),
            stepPt_var (c := G.m - 2 - j) (r := .inl r) (s := .inr ⟨(G.m - 2 - j) / 2, by omega⟩) _ _ (Or.inr ⟨hc, rfl⟩) (basePt_inl_inr _ r _)]
          refine hmul (hbox _ _ rfl) (hbox _ _ rfl) ?_
          obtain ⟨q, hq⟩ := hc
          have h1 : (G.m - 2 - (j + 1) : ℕ) = q + q - 1 := by omega
          have h2 : (l : ℕ) + 1 = q := by omega
          have h3 : (G.m - 2 - j) / 2 = q := by omega
          have h4 : (((q + q - 1 : ℕ)) : ℤ) = 2 * (q : ℤ) - 1 := by omega
          have h5 : ((l : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
          simp only [boxExp, auxiliaryVectorUniformizerExponent]
          rw [h5, h3, hq, h1, h4]
          push_cast
          ring
        · simp
      · simp
    · simp

end Main
end GlobalTheory.OriginBox
