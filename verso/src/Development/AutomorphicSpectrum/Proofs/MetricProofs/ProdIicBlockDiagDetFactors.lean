import Mathlib

open Matrix

namespace GlobalTheory.CompanionTheory.Metric.GradedLines

/- English proof (translation)
Use `symm`. Use `Finset.prod_bij (fun l _ => Fin.castLE hn l) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `l _`. Use `l.2` as an intermediate fact. Simplify using `only [Finset.mem_Iic, Fin.le_def, Fin.val_castLE]`.

Use linear arithmetic over natural numbers and integers. Introduce `a _ b _ hab`. Conclude with `Fin.castLE_injective hn hab`. Introduce `b hb`. Establish `hb' : (b : ℕ) ≤ (i : ℕ)` using `Fin.le_def.mp (Finset.mem_Iic.mp hb)`.

Use `⟨⟨(b : ℕ), by omega⟩, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using the standard rewrite rules. Introduce `_ _`. Both sides reduce to the same expression.
-/
theorem prod_Iic_eq_prod_castLE {Φ : Type} [CommMonoid Φ] {N : ℕ} (G : Fin N → Φ)
    (i : Fin N) (n : ℕ) (hn : n ≤ N) (hin : n = (i : ℕ) + 1) :
    ∏ k ∈ Finset.Iic i, G k = ∏ l : Fin n, G (Fin.castLE hn l) := by
  symm
  refine Finset.prod_bij (fun l _ => Fin.castLE hn l) ?_ ?_ ?_ ?_
  · intro l _
    have := l.2
    simp only [Finset.mem_Iic, Fin.le_def, Fin.val_castLE]
    omega
  · intro a _ b _ hab
    exact Fin.castLE_injective hn hab
  · intro b hb
    have hb' : (b : ℕ) ≤ (i : ℕ) := Fin.le_def.mp (Finset.mem_Iic.mp hb)
    refine ⟨⟨(b : ℕ), by omega⟩, Finset.mem_univ _, ?_⟩
    ext
    simp
  · intro _ _
    rfl

/- English proof (translation)
Introduce `Φ _ p q tW tO G h1 h2 i`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[prod_Iic_eq_prod_castLE G i ((i : ℕ) + 1) (by have := i.2; omega) rfl]`. Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations.

Establish `hl : ((Fin.castLE (by have` using `i.2; omega) l : Fin (p + q)) : ℕ) < p := by`. Use `l.2` as an intermediate fact. Simplify using `only [Fin.val_castLE]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h1 _ hl]`.

Both sides reduce to the same expression. Introduce `h`. Establish `hi` using `i.2`. Rewrite using `[prod_Iic_eq_prod_castLE G i (p + ((i : ℕ) - p + 1)) (by omega) (by omega), Fin.prod_univ_add]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `hl : ((Fin.castLE (by omega) (Fin.castAdd ((i : ℕ) - p + 1) l) : Fin (p + q)) : ℕ) < p`. Use `l.2` as an intermediate fact. Simplify using `only [Fin.val_castLE, Fin.val_castAdd]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[h1 _ hl]`. Both sides reduce to the same expression. Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `hl : p ≤ ((Fin.castLE (by omega) (Fin.natAdd p l) : Fin (p + q)) : ℕ)`. Simplify using `only [Fin.val_castLE, Fin.val_natAdd]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[h2 _ hl]`. Use `congr 1`. Use `ext`. Simplify using the standard rewrite rules.
-/
theorem prod_first_graded_lines :
    ∀ (Φ : Type) [CommMonoid Φ] (p q : ℕ) (tW : Fin p → Φ) (tO : Fin q → Φ) (G : Fin (p + q) → Φ), (∀ (i : Fin (p + q)) (h : (i : ℕ) < p), G i = tW ⟨i, h⟩) → (∀ (i : Fin (p + q)) (h : p ≤ (i : ℕ)), G i = tO ⟨(i : ℕ) - p, by have := i.2; omega⟩) → ∀ i : Fin (p + q), (∀ h : (i : ℕ) < p, ∏ k ∈ Finset.Iic i, G k = ∏ l : Fin ((i : ℕ) + 1), tW (Fin.castLE h l)) ∧ (∀ h : p ≤ (i : ℕ), ∏ k ∈ Finset.Iic i, G k = (∏ l, tW l) * ∏ l : Fin ((i : ℕ) - p + 1), tO (Fin.castLE (by have := i.2; omega) l)) := by
  intro Φ _ p q tW tO G h1 h2 i
  constructor
  · intro h
    rw [prod_Iic_eq_prod_castLE G i ((i : ℕ) + 1) (by have := i.2; omega) rfl]
    refine Finset.prod_congr rfl fun l _ => ?_
    have hl : ((Fin.castLE (by have := i.2; omega) l : Fin (p + q)) : ℕ) < p := by
      have := l.2
      simp only [Fin.val_castLE]
      omega
    rw [h1 _ hl]
    rfl
  · intro h
    have hi := i.2
    rw [prod_Iic_eq_prod_castLE G i (p + ((i : ℕ) - p + 1)) (by omega) (by omega),
      Fin.prod_univ_add]
    congr 1
    · refine Finset.prod_congr rfl fun l _ => ?_
      have hl : ((Fin.castLE (by omega) (Fin.castAdd ((i : ℕ) - p + 1) l) : Fin (p + q)) : ℕ) < p := by
        have := l.2
        simp only [Fin.val_castLE, Fin.val_castAdd]
        omega
      rw [h1 _ hl]
      rfl
    · refine Finset.prod_congr rfl fun l _ => ?_
      have hl : p ≤ ((Fin.castLE (by omega) (Fin.natAdd p l) : Fin (p + q)) : ℕ) := by
        simp only [Fin.val_castLE, Fin.val_natAdd]
        omega
      rw [h2 _ hl]
      congr 1
      ext
      simp

end GlobalTheory.CompanionTheory.Metric.GradedLines
