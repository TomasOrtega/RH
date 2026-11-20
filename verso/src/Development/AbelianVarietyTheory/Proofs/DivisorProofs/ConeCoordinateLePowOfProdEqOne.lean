import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `i j hij`. Establish `hji : j = i` using `Fin.ext (by simpa using hij)`.

Substitute `hji` using the available equality. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `i j hij`. Establish `hja` using `j.isLt`.

Establish `hk : (i : ℕ) + k < a` using `by omega`. Establish `h1` using `ih i ⟨(i : ℕ) + k, hk⟩ rfl`. Establish `hmj : (j : ℕ) = ((⟨(i : ℕ) + k, hk⟩ : Fin a) : ℕ) + 1` using `by simp; omega`. Establish `hu` using `hup _ j hmj`. Establish `hd` using `hdown _ j hmj`.

Use `set m : Fin a := ⟨(i : ℕ) + k, hk⟩`. Establish `hrj : r j ≤ t⁻¹ * r m`. Rewrite using `[inv_mul_eq_div, le_div_iff₀ ht]`. Combine the linear equalities and inequalities to obtain the conclusion. Prove the components needed by the constructor for the conclusion.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem coneChain_step_bounds {a : ℕ} {t ρ K : ℝ} (ht : 0 < t) (hKt : t⁻¹ ≤ K) (hK0 : 0 ≤ K)
    (hρ0 : 0 ≤ ρ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i)
    (hup : ∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i)
    (hdown : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) :
    ∀ k : ℕ, ∀ i j : Fin a, (j : ℕ) = i + k → r j ≤ K ^ k * r i ∧ r i ≤ ρ ^ k * r j := by
  intro k
  induction k with
  | zero =>
    intro i j hij
    have hji : j = i := Fin.ext (by simpa using hij)
    subst hji
    simp
  | succ k ih =>
    intro i j hij
    have hja := j.isLt
    have hk : (i : ℕ) + k < a := by omega
    have h1 := ih i ⟨(i : ℕ) + k, hk⟩ rfl
    have hmj : (j : ℕ) = ((⟨(i : ℕ) + k, hk⟩ : Fin a) : ℕ) + 1 := by simp; omega
    have hu := hup _ j hmj
    have hd := hdown _ j hmj
    set m : Fin a := ⟨(i : ℕ) + k, hk⟩
    have hrj : r j ≤ t⁻¹ * r m := by
      rw [inv_mul_eq_div, le_div_iff₀ ht]; linarith
    constructor
    · calc r j ≤ t⁻¹ * r m := hrj
        _ ≤ K * r m := mul_le_mul_of_nonneg_right hKt (hr m).le
        _ ≤ K * (K ^ k * r i) := mul_le_mul_of_nonneg_left h1.1 hK0
        _ = K ^ (k + 1) * r i := by ring
    · calc r i ≤ ρ ^ k * r m := h1.2
        _ ≤ ρ ^ k * (ρ * r j) := mul_le_mul_of_nonneg_left hd (pow_nonneg hρ0 _)
        _ = ρ ^ (k + 1) * r j := by ring

/- English proof (translation)
Introduce `a t ht`. Take `⟨K, hK1, hKt⟩ : ∃ K : ℝ, 1 ≤ K ∧ t⁻¹ ≤ K` from `⟨max 1 t⁻¹, le_max_left _ _, le_max_right _ _⟩`. Use `⟨K ^ a, one_le_pow₀ hK1, ?_⟩` and prove the remaining obligations. Introduce `r ρ hr hup hprod hρ hdown i`. Establish `hK0 : (0 : ℝ) ≤ K` using `by linarith`.

Establish `hρ0 : (0 : ℝ) ≤ ρ` using `by linarith`. Establish `hC0 : 0 ≤ K ^ a * ρ ^ a` using `mul_nonneg (pow_nonneg hK0 _) (pow_nonneg hρ0 _)`. Establish `step` using `coneChain_step_bounds ht hKt hK0 hρ0 r hr hup hdown`. Establish `pair : ∀ p q : Fin a, r p ≤ K ^ a * ρ ^ a * r q`. Introduce `p q`.

Break down `le_total (q : ℕ) p with h | h` into its components or cases. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le h`. Establish `hka : k ≤ a` using `by have := p.isLt; omega`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ (hr q).le` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le h`. Establish `hka : k ≤ a` using `by have := q.isLt; omega`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ (hr q).le` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Establish `hne : (Finset.univ : Finset (Fin a)).Nonempty` using `⟨i, Finset.mem_univ _⟩`. Establish `ex_le : ∃ j, r j ≤ 1`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Use `Finset.prod_lt_prod_of_nonempty (s := Finset.univ) (f := fun _ => (1 : ℝ)) (g := r) (fun _ _ => one_pos) (fun j _ => hcon j) hne` as an intermediate fact. Simplify using `[hprod] at this`. Establish `ex_ge : ∃ j, 1 ≤ r j`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Use `Finset.prod_lt_prod_of_nonempty (s := Finset.univ) (f := r) (g := fun _ => (1 : ℝ)) (fun j _ => hr j) (fun j _ => hcon j) hne` as an intermediate fact. Simplify using `[hprod] at this`. Take `⟨j, hj⟩` from `ex_le`. Take `⟨l, hl⟩` from `ex_ge`. Prove the components needed by the constructor for the conclusion.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_eq_one_div, div_le_iff₀ (hr i)]`. Use `pair l i` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem coneCoord_le_pow_of_prod_eq_one : ∀ (a : ℕ) (t : ℝ), 0 < t → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (r : Fin a → ℝ) (ρ : ℝ), (∀ i, 0 < r i) →
      (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∏ i, r i = 1 → 1 ≤ ρ →
      (∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) →
      ∀ i, r i ≤ C * ρ ^ a ∧ (r i)⁻¹ ≤ C * ρ ^ a := by
  intro a t ht
  obtain ⟨K, hK1, hKt⟩ : ∃ K : ℝ, 1 ≤ K ∧ t⁻¹ ≤ K := ⟨max 1 t⁻¹, le_max_left _ _, le_max_right _ _⟩
  refine ⟨K ^ a, one_le_pow₀ hK1, ?_⟩
  intro r ρ hr hup hprod hρ hdown i
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hρ0 : (0 : ℝ) ≤ ρ := by linarith
  have hC0 : 0 ≤ K ^ a * ρ ^ a := mul_nonneg (pow_nonneg hK0 _) (pow_nonneg hρ0 _)
  have step := coneChain_step_bounds ht hKt hK0 hρ0 r hr hup hdown
  have pair : ∀ p q : Fin a, r p ≤ K ^ a * ρ ^ a * r q := by
    intro p q
    rcases le_total (q : ℕ) p with h | h
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      have hka : k ≤ a := by have := p.isLt; omega
      calc r p ≤ K ^ k * r q := (step k q p hk).1
        _ ≤ K ^ a * ρ ^ a * r q := by
          apply mul_le_mul_of_nonneg_right _ (hr q).le
          calc K ^ k ≤ K ^ a := pow_le_pow_right₀ hK1 hka
            _ = K ^ a * 1 := by ring
            _ ≤ K ^ a * ρ ^ a := mul_le_mul_of_nonneg_left (one_le_pow₀ hρ) (pow_nonneg hK0 _)
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      have hka : k ≤ a := by have := q.isLt; omega
      calc r p ≤ ρ ^ k * r q := (step k p q hk).2
        _ ≤ K ^ a * ρ ^ a * r q := by
          apply mul_le_mul_of_nonneg_right _ (hr q).le
          calc ρ ^ k ≤ ρ ^ a := pow_le_pow_right₀ hρ hka
            _ = 1 * ρ ^ a := by ring
            _ ≤ K ^ a * ρ ^ a := mul_le_mul_of_nonneg_right (one_le_pow₀ hK1) (pow_nonneg hρ0 _)
  have hne : (Finset.univ : Finset (Fin a)).Nonempty := ⟨i, Finset.mem_univ _⟩
  have ex_le : ∃ j, r j ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have := Finset.prod_lt_prod_of_nonempty (s := Finset.univ) (f := fun _ => (1 : ℝ)) (g := r)
      (fun _ _ => one_pos) (fun j _ => hcon j) hne
    simp [hprod] at this
  have ex_ge : ∃ j, 1 ≤ r j := by
    by_contra hcon
    push_neg at hcon
    have := Finset.prod_lt_prod_of_nonempty (s := Finset.univ) (f := r) (g := fun _ => (1 : ℝ))
      (fun j _ => hr j) (fun j _ => hcon j) hne
    simp [hprod] at this
  obtain ⟨j, hj⟩ := ex_le
  obtain ⟨l, hl⟩ := ex_ge
  constructor
  · calc r i ≤ K ^ a * ρ ^ a * r j := pair i j
      _ ≤ K ^ a * ρ ^ a * 1 := mul_le_mul_of_nonneg_left hj hC0
      _ = K ^ a * ρ ^ a := by ring
  · rw [inv_eq_one_div, div_le_iff₀ (hr i)]
    have := pair l i
    linarith

end GlobalTheory
