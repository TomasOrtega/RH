import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing

open Matrix GlobalTheory.SUCong

namespace GlobalTheory.SUCong

/- English proof (translation)
Introduce `hR hk g h hg hh`. Take `⟨-, -, hϖS, -, hnz, -⟩` from `hR`. Establish `canc : ∀ m : ℕ, ∀ x : A, ϖ ^ m * x = 0 → x = 0`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => intro x hx`. Simplify using `using hx`. Consider the case `succ m ih`. Introduce `x hx`. Apply `ih` to reduce the goal to its premises.

Apply `hnz` to reduce the goal to its premises. Rewrite using `[← mul_assoc, ← pow_succ']`. Conclude with `hx`. Establish `redAdd : ∀ a b, a ∈ S → b ∈ S → red S ϖ (a + b) = red S ϖ a + red S ϖ b`. Introduce `a b ha hb`.

Simplify using `only [red, dif_pos ha, dif_pos hb, dif_pos (add_mem ha hb)]`. Rewrite using `[← map_add]`. Both sides reduce to the same expression. Establish `redPi : ∀ t ∈ S, red S ϖ (ϖ * t) = 0`. Introduce `t ht`.

Rewrite using `[red, dif_pos (mul_mem hϖS ht), Ideal.Quotient.eq_zero_iff_mem]`. Establish `e : (⟨ϖ * t, mul_mem hϖS ht⟩ : S) = ⟨ϖ, hϖS⟩ * ⟨t, ht⟩` using `rfl`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)`. Establish `hgh` using `(congSU S σ H ϖ k).mul_mem hg hh`.

Set `X : n → n → A` to `fun i j => Classical.choose (hg.2.2.2.2 i j)`. Set `Y : n → n → A` to `fun i j => Classical.choose (hh.2.2.2.2 i j)`. Set `Z : n → n → A` to `fun i j => Classical.choose (hgh.2.2.2.2 i j)`. Establish `hX : ∀ i j, X i j ∈ S ∧ ((g : Matrix n n A) - 1) i j = ϖ ^ k * X i j` using `fun i j => Classical.choose_spec (hg.2.2.2.2 i j)`. Establish `hY : ∀ i j, Y i j ∈ S ∧ ((h : Matrix n n A) - 1) i j = ϖ ^ k * Y i j` using `fun i j => Classical.choose_spec (hh.2.2.2.2 i j)`.

Establish `hZ : ∀ i j, Z i j ∈ S ∧ (((g * h : GL n A) : Matrix n n A) - 1) i j = ϖ ^ k * Z i j` using `fun i j => Classical.choose_spec (hgh.2.2.2.2 i j)`. Establish `hX2 : ∀ i j, ((g : Matrix n n A) - 1) i j = ϖ ^ k * X i j` using `fun i j => (hX i j).2`. Establish `hY2 : ∀ i j, ((h : Matrix n n A) - 1) i j = ϖ ^ k * Y i j` using `fun i j => (hY i j).2`. Establish `hZ2 : ∀ i j, (((g * h : GL n A) : Matrix n n A) - 1) i j = ϖ ^ k * Z i j` using `fun i j => (hZ i j).2`. Establish `e : ((g * h : GL n A) : Matrix n n A) - 1 = ((g : Matrix n n A) - 1) + ((h : Matrix n n A) - 1) + ((g : Matrix n n A) - 1) * ((h : Matrix n n A) - 1)`.

Rewrite using `[Units.val_mul]`. Use `noncomm_ring`. Establish `key : ∀ i j, Z i j = X i j + Y i j + ϖ ^ k * ∑ l, X i l * Y l j`. Introduce `i j`. Establish `e1` using `congrArg (fun M : Matrix n n A => M i j) e`.

Simplify using `only [Matrix.add_apply, Matrix.mul_apply, hX2, hY2, hZ2] at e1`. Establish `e2 : ∑ l, ϖ ^ k * X i l * (ϖ ^ k * Y l j) = ϖ ^ k * (ϖ ^ k * ∑ l, X i l * Y l j)`. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`. Apply `eq_of_sub_eq_zero` to reduce the goal to its premises.

Apply `canc k` to reduce the goal to its premises. Take the linear combination `e1 + e2`. Take `⟨m, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Use extensionality with `i j`. Simplify using `only [levMap, Matrix.add_apply]`.

Rewrite using `[dif_pos (hgh.2.2.2.2 i j), dif_pos (hg.2.2.2.2 i j), dif_pos (hh.2.2.2.2 i j)]`. Express the relevant statement in the definitionally equal form `red S ϖ (Z i j) = red S ϖ (X i j) + red S ϖ (Y i j)`. Establish `hT : (∑ l, X i l * Y l j) ∈ S` using `Subring.sum_mem _ fun l _ => mul_mem (hX i l).1 (hY l j).1`. Establish `hPm : ϖ ^ m * ∑ l, X i l * Y l j ∈ S` using `mul_mem (pow_mem hϖS m) hT`. Establish `e3 : ϖ ^ (m + 1) * ∑ l, X i l * Y l j = ϖ * (ϖ ^ m * ∑ l, X i l * Y l j)` using `by ring`.

Rewrite using `[key, redAdd _ _ (add_mem (hX i j).1 (hY i j).1) (by rw [e3]; exact mul_mem hϖS hPm), redAdd _ _ (hX i j).1 (hY i j).1, e3, redPi _ hPm, add_zero]`.
-/
theorem levMap_mul_of_goodRing {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (S : Subring A) (σ : A →+* A) (H : Matrix n n A) (ϖ : A) (q k : ℕ) :
    GoodRing S σ ϖ q → 1 ≤ k → ∀ (g h : GL n A), g ∈ congSU S σ H ϖ k → h ∈ congSU S σ H ϖ k →
    levMap S ϖ k ((g * h : GL n A) : Matrix n n A) =
      levMap S ϖ k (g : Matrix n n A) + levMap S ϖ k (h : Matrix n n A) := by
  intro hR hk g h hg hh
  obtain ⟨-, -, hϖS, -, hnz, -⟩ := hR
  have canc : ∀ m : ℕ, ∀ x : A, ϖ ^ m * x = 0 → x = 0 := by
    intro m
    induction m with
    | zero => intro x hx; simpa using hx
    | succ m ih =>
      intro x hx; apply ih; apply hnz; rw [← mul_assoc, ← pow_succ']; exact hx
  have redAdd : ∀ a b, a ∈ S → b ∈ S → red S ϖ (a + b) = red S ϖ a + red S ϖ b := by
    intro a b ha hb
    simp only [red, dif_pos ha, dif_pos hb, dif_pos (add_mem ha hb)]
    rw [← map_add]; rfl
  have redPi : ∀ t ∈ S, red S ϖ (ϖ * t) = 0 := by
    intro t ht
    rw [red, dif_pos (mul_mem hϖS ht), Ideal.Quotient.eq_zero_iff_mem]
    have e : (⟨ϖ * t, mul_mem hϖS ht⟩ : S) = ⟨ϖ, hϖS⟩ * ⟨t, ht⟩ := rfl
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hgh := (congSU S σ H ϖ k).mul_mem hg hh
  let X : n → n → A := fun i j => Classical.choose (hg.2.2.2.2 i j)
  let Y : n → n → A := fun i j => Classical.choose (hh.2.2.2.2 i j)
  let Z : n → n → A := fun i j => Classical.choose (hgh.2.2.2.2 i j)
  have hX : ∀ i j, X i j ∈ S ∧ ((g : Matrix n n A) - 1) i j = ϖ ^ k * X i j :=
    fun i j => Classical.choose_spec (hg.2.2.2.2 i j)
  have hY : ∀ i j, Y i j ∈ S ∧ ((h : Matrix n n A) - 1) i j = ϖ ^ k * Y i j :=
    fun i j => Classical.choose_spec (hh.2.2.2.2 i j)
  have hZ : ∀ i j, Z i j ∈ S ∧ (((g * h : GL n A) : Matrix n n A) - 1) i j = ϖ ^ k * Z i j :=
    fun i j => Classical.choose_spec (hgh.2.2.2.2 i j)
  have hX2 : ∀ i j, ((g : Matrix n n A) - 1) i j = ϖ ^ k * X i j := fun i j => (hX i j).2
  have hY2 : ∀ i j, ((h : Matrix n n A) - 1) i j = ϖ ^ k * Y i j := fun i j => (hY i j).2
  have hZ2 : ∀ i j, (((g * h : GL n A) : Matrix n n A) - 1) i j = ϖ ^ k * Z i j :=
    fun i j => (hZ i j).2
  have e : ((g * h : GL n A) : Matrix n n A) - 1 = ((g : Matrix n n A) - 1) + ((h : Matrix n n A) - 1)
      + ((g : Matrix n n A) - 1) * ((h : Matrix n n A) - 1) := by
    rw [Units.val_mul]; noncomm_ring
  have key : ∀ i j, Z i j = X i j + Y i j + ϖ ^ k * ∑ l, X i l * Y l j := by
    intro i j
    have e1 := congrArg (fun M : Matrix n n A => M i j) e
    simp only [Matrix.add_apply, Matrix.mul_apply, hX2, hY2, hZ2] at e1
    have e2 : ∑ l, ϖ ^ k * X i l * (ϖ ^ k * Y l j) = ϖ ^ k * (ϖ ^ k * ∑ l, X i l * Y l j) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    apply eq_of_sub_eq_zero
    apply canc k
    linear_combination e1 + e2
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  ext i j
  simp only [levMap, Matrix.add_apply]
  rw [dif_pos (hgh.2.2.2.2 i j), dif_pos (hg.2.2.2.2 i j), dif_pos (hh.2.2.2.2 i j)]
  change red S ϖ (Z i j) = red S ϖ (X i j) + red S ϖ (Y i j)
  have hT : (∑ l, X i l * Y l j) ∈ S := Subring.sum_mem _ fun l _ => mul_mem (hX i l).1 (hY l j).1
  have hPm : ϖ ^ m * ∑ l, X i l * Y l j ∈ S := mul_mem (pow_mem hϖS m) hT
  have e3 : ϖ ^ (m + 1) * ∑ l, X i l * Y l j = ϖ * (ϖ ^ m * ∑ l, X i l * Y l j) := by ring
  rw [key, redAdd _ _ (add_mem (hX i j).1 (hY i j).1) (by rw [e3]; exact mul_mem hϖS hPm),
    redAdd _ _ (hX i j).1 (hY i j).1, e3, redPi _ hPm, add_zero]

end GlobalTheory.SUCong
