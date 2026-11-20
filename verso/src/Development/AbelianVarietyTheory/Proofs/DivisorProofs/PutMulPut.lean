import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem put_apply' {R : Type} [CommRing R] (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R)
    (i j : Fin n) : put n o₁ o₂ X i j =
      if h : (o₁ ≤ i.val ∧ i.val < o₁ + p) ∧ (o₂ ≤ j.val ∧ j.val < o₂ + q) then
        X ⟨i.val - o₁, by omega⟩ ⟨j.val - o₂, by omega⟩ else 0 := rfl

/- English proof (translation)
Introduce `R _ n o₁ o₂ o₃ o₄ p q s t X Y Z`. Use `⟨fun hn => ?_, fun hd => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, put_apply']`. Set `e : Fin q ↪ Fin n` to `⟨fun c => ⟨o₂ + c.val, by omega⟩, fun a b h => by`.

Simplify using `only [Fin.mk.injEq] at h; exact Fin.ext (by omega)⟩`. Establish `he : ∀ c : Fin q, (e c).val = o₂ + c.val` using `fun c => rfl`. Rewrite using `[← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) ?_, Finset.sum_map]`. Distinguish the cases in `hi : o₁ ≤ i.val ∧ i.val < o₁ + p`. Distinguish the cases in `hj : o₃ ≤ j.val ∧ j.val < o₃ + s`.

Rewrite using `[dif_pos ⟨hi, hj⟩, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Establish `hc : (o₂ ≤ (e c).val ∧ (e c).val < o₂ + q)` using `by rw [he]; omega`. Rewrite using `[put_apply', put_apply', dif_pos ⟨hi, hc⟩, dif_pos ⟨hc, hj⟩]`. Establish `h1 : (⟨(e c).val - o₂, by omega⟩ : Fin q) = c` using `Fin.ext (by show (e c).val - o₂ = c.val; rw [he]; omega)`.

Rewrite using `[h1]`. Rewrite using `[dif_neg (fun h => hj h.2)]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Rewrite using `[put_apply' n o₂ o₃ Y, dif_neg (fun h => hj h.2), mul_zero]`. Rewrite using `[dif_neg (fun h => hi h.1)]`.

Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Rewrite using `[put_apply' n o₁ o₂ X, dif_neg (fun h => hi h.1), zero_mul]`. Introduce `l _ hl`. Establish `: ¬ (o₂ ≤ l.val ∧ l.val < o₂ + q)`. Introduce and unpack `⟨h1, h2⟩`.

Apply `hl` to reduce the goal to its premises. Use `Finset.mem_map.2 ⟨⟨l.val - o₂, by omega⟩, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Conclude with `Fin.ext (by show o₂ + (l.val - o₂) = l.val; omega)`. Rewrite using `[put_apply' n o₁ o₂ X, dif_neg (fun h => this h.2), zero_mul]`. Use extensionality with `i j`.

Rewrite using `[Matrix.mul_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : o₂ ≤ l.val ∧ l.val < o₂ + q`. Rewrite using `[put_apply' n o₃ o₄ Z, dif_neg (fun h => by omega), mul_zero]`. Rewrite using `[put_apply' n o₁ o₂ X, dif_neg (fun h => h1 h.2), zero_mul]`.
-/
theorem put_mul_put :
    ∀ (R : Type) [CommRing R] (n o₁ o₂ o₃ o₄ p q s t : ℕ) (X : Matrix (Fin p) (Fin q) R)
      (Y : Matrix (Fin q) (Fin s) R) (Z : Matrix (Fin t) (Fin s) R),
      (o₂ + q ≤ n → put n o₁ o₂ X * put n o₂ o₃ Y = put n o₁ o₃ (X * Y)) ∧
      ((o₂ + q ≤ o₃ ∨ o₃ + t ≤ o₂) → put n o₁ o₂ X * put n o₃ o₄ Z = 0) := by
  intro R _ n o₁ o₂ o₃ o₄ p q s t X Y Z
  refine ⟨fun hn => ?_, fun hd => ?_⟩
  · ext i j
    rw [Matrix.mul_apply, put_apply']
    let e : Fin q ↪ Fin n := ⟨fun c => ⟨o₂ + c.val, by omega⟩, fun a b h => by
      simp only [Fin.mk.injEq] at h; exact Fin.ext (by omega)⟩
    have he : ∀ c : Fin q, (e c).val = o₂ + c.val := fun c => rfl
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) ?_, Finset.sum_map]
    · by_cases hi : o₁ ≤ i.val ∧ i.val < o₁ + p
      · by_cases hj : o₃ ≤ j.val ∧ j.val < o₃ + s
        · rw [dif_pos ⟨hi, hj⟩, Matrix.mul_apply]
          refine Finset.sum_congr rfl fun c _ => ?_
          have hc : (o₂ ≤ (e c).val ∧ (e c).val < o₂ + q) := by rw [he]; omega
          rw [put_apply', put_apply', dif_pos ⟨hi, hc⟩, dif_pos ⟨hc, hj⟩]
          have h1 : (⟨(e c).val - o₂, by omega⟩ : Fin q) = c := Fin.ext (by show (e c).val - o₂ = c.val; rw [he]; omega)
          rw [h1]
        · rw [dif_neg (fun h => hj h.2)]
          refine Finset.sum_eq_zero fun c _ => ?_
          rw [put_apply' n o₂ o₃ Y, dif_neg (fun h => hj h.2), mul_zero]
      · rw [dif_neg (fun h => hi h.1)]
        refine Finset.sum_eq_zero fun c _ => ?_
        rw [put_apply' n o₁ o₂ X, dif_neg (fun h => hi h.1), zero_mul]
    · intro l _ hl
      have : ¬ (o₂ ≤ l.val ∧ l.val < o₂ + q) := by
        rintro ⟨h1, h2⟩
        apply hl
        refine Finset.mem_map.2 ⟨⟨l.val - o₂, by omega⟩, Finset.mem_univ _, ?_⟩
        exact Fin.ext (by show o₂ + (l.val - o₂) = l.val; omega)
      rw [put_apply' n o₁ o₂ X, dif_neg (fun h => this h.2), zero_mul]
  · ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h1 : o₂ ≤ l.val ∧ l.val < o₂ + q
    · rw [put_apply' n o₃ o₄ Z, dif_neg (fun h => by omega), mul_zero]
    · rw [put_apply' n o₁ o₂ X, dif_neg (fun h => h1 h.2), zero_mul]

end GlobalTheory.GamMul
