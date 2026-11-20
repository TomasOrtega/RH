import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Fin.sum_univ_add, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem pluck_cb {F : Type} [Field F] (A B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F)
    (i i' p q : Fin (2 + 2)) :
    (A * B) i p * (A * B) i' q - (A * B) i q * (A * B) i' p =
      ∑ k, ∑ l, (A i k * A i' l - A i l * A i' k) * (B k p * B l q) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_add, Fin.sum_univ_two]
  ring

/- English proof (translation)
Rewrite using `[Matrix.det_fin_two]`. Simplify using `only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one]`.
-/
private theorem pluck_det {F : Type} [Field F] (A : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F)
    (k l : Fin (2 + 2)) :
    (A.submatrix (Fin.natAdd 2) ![k, l]).det =
      A (Fin.natAdd 2 0) k * A (Fin.natAdd 2 1) l - A (Fin.natAdd 2 0) l * A (Fin.natAdd 2 1) k := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `hz : ∀ k l : Fin (2 + 2), (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) (Fin.natAdd 2 0) k * (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) (Fin.natAdd 2 1) l - (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) (Fin.natAdd 2 0) l * (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) (Fin.natAdd 2 1) k …`. Introduce `k l`. Distinguish the cases in `hkl : k = l`.

Substitute `hkl` using the available equality. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← pluck_det]`. Apply `h` to reduce the goal to its premises. Introduce `x y hxy`.

Apply the tactic sequence `fin_cases x <;> fin_cases y <;> simp_all [eq_comm]`. Use `pluck_cb (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) ((γ⁻¹ : GL (Fin (2 + 2)) F) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) (Fin.natAdd 2 0) (Fin.natAdd 2 1) (Fin.natAdd 2 0) (Fin.natAdd 2 1)` as an intermediate fact. Rewrite `this` using `[Units.mul_inv]`. Simplify using `only [hz, zero_mul, Finset.sum_const_zero] at this`. Establish `hne : (Fin.natAdd 2 (0 : Fin 2) : Fin (2 + 2)) ≠ Fin.natAdd 2 1` using `by decide`.

Rewrite `this` using `[Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_ne hne]`. Simplify using `at this`.
-/
private theorem pluck_one {F : Type} [Field F] (γ : GL (Fin (2 + 2)) F) :
    ∃ c : Fin 2 → Fin (2 + 2), Function.Injective c ∧ ((γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) c).det ≠ 0 := by
  by_contra h
  push Not at h
  have hz : ∀ k l : Fin (2 + 2), (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) (Fin.natAdd 2 0) k * (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) (Fin.natAdd 2 1) l -
      (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) (Fin.natAdd 2 0) l * (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) (Fin.natAdd 2 1) k = 0 := by
    intro k l
    by_cases hkl : k = l
    · subst hkl; ring
    · rw [← pluck_det]
      apply h
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [eq_comm]
  have := pluck_cb (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) ((γ⁻¹ : GL (Fin (2 + 2)) F) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F)
    (Fin.natAdd 2 0) (Fin.natAdd 2 1) (Fin.natAdd 2 0) (Fin.natAdd 2 1)
  rw [Units.mul_inv] at this
  simp only [hz, zero_mul, Finset.sum_const_zero] at this
  have hne : (Fin.natAdd 2 (0 : Fin 2) : Fin (2 + 2)) ≠ Fin.natAdd 2 1 := by decide
  rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_ne hne] at this
  simp at this

/- English proof (translation)
Introduce `F _ γ γ'`. Use `⟨pluck_one γ, ?_⟩` and prove the remaining obligations. Introduce `a ha i j hi hj`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`.

Take `⟨c, -, hc⟩` from `pluck_one γ`. Conclude with `hc (by rw [ha, zero_mul])`. Rewrite using `[Units.val_mul]`. Use `set A : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F := ↑γ with hA`. Use `set A' : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F := ↑γ' with hA'`.

Use `set B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F := ↑(γ'⁻¹) with hB`. Establish `h1 : A' * B = 1` using `Units.mul_inv γ'`. Use `set r : Fin (2 + 2) := Fin.natAdd 2 (0 : Fin 2) with hr`. Use `set s : Fin (2 + 2) := Fin.natAdd 2 (1 : Fin 2) with hs`. Establish `key : ∀ p q, (A * B) r p * (A * B) s q - (A * B) r q * (A * B) s p = a * ((1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) r p * (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) s q - (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) r q * (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) s p)`.

Introduce `p q`. Rewrite using `[← h1, pluck_cb, pluck_cb, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Use `ha ![k, l]` as an intermediate fact. Rewrite `this` using `[pluck_det, pluck_det]`. Rewrite using `[hr, hs, this, mul_assoc]`. Establish `hrs : r ≠ s` using `by rw [hr, hs]; decide`. Establish `hrv : (r : ℕ) = 2` using `rfl`.

Establish `hsv : (s : ℕ) = 3` using `rfl`. Establish `hrj : r ≠ j` using `by intro h; rw [h] at hrv; omega`. Establish `hsj : s ≠ j` using `by intro h; rw [h] at hsv; omega`. Establish `k1` using `key j r`. Establish `k2` using `key j s`.

Establish `k3` using `key r s`. Rewrite `k1`, `k2` using `[Matrix.one_apply_ne hrj, Matrix.one_apply_ne hsj]`. Rewrite `k3` using `[Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_ne hrs]`. Establish `hi' : i = r ∨ i = s`. Use `i.isLt` as an intermediate fact.

Break down `(by omega : (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h | h` into its components or cases. Use the proof step `left; exact Fin.ext (by omega)`. Use the proof step `right; exact Fin.ext (by omega)`. Apply `mul_left_cancel₀ ha0` to reduce the goal to its premises. Break down `hi' with h | h` into its components or cases.

Rewrite using `[h]`. Take the linear combination `(-(A * B) r j) * k3 + (A * B) r r * k2 - (A * B) r s * k1`. Rewrite using `[h]`. Take the linear combination `(-(A * B) s j) * k3 + (A * B) s r * k2 - (A * B) s s * k1`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.pluck :
    ∀ {F : Type} [Field F] (γ γ' : GL (Fin (2 + 2)) F),
      (∃ c : Fin 2 → Fin (2 + 2), Function.Injective c ∧ ((γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) c).det ≠ 0) ∧
      ∀ a : F, (∀ c : Fin 2 → Fin (2 + 2), ((γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) c).det =
          a * ((γ' : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) c).det) →
        ∀ i j : Fin (2 + 2), 2 ≤ (i : ℕ) → (j : ℕ) < 2 → ((γ * γ'⁻¹ : GL (Fin (2 + 2)) F) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) i j = 0 := by
  intro F _ γ γ'
  refine ⟨pluck_one γ, ?_⟩
  intro a ha i j hi hj
  have ha0 : a ≠ 0 := by
    rintro rfl
    obtain ⟨c, -, hc⟩ := pluck_one γ
    exact hc (by rw [ha, zero_mul])
  rw [Units.val_mul]
  set A : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F := ↑γ with hA
  set A' : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F := ↑γ' with hA'
  set B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F := ↑(γ'⁻¹) with hB
  have h1 : A' * B = 1 := Units.mul_inv γ'
  set r : Fin (2 + 2) := Fin.natAdd 2 (0 : Fin 2) with hr
  set s : Fin (2 + 2) := Fin.natAdd 2 (1 : Fin 2) with hs
  have key : ∀ p q, (A * B) r p * (A * B) s q - (A * B) r q * (A * B) s p =
      a * ((1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) r p * (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) s q -
        (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) r q * (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) s p) := by
    intro p q
    rw [← h1, pluck_cb, pluck_cb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have := ha ![k, l]
    rw [pluck_det, pluck_det] at this
    rw [hr, hs, this, mul_assoc]
  have hrs : r ≠ s := by rw [hr, hs]; decide
  have hrv : (r : ℕ) = 2 := rfl
  have hsv : (s : ℕ) = 3 := rfl
  have hrj : r ≠ j := by intro h; rw [h] at hrv; omega
  have hsj : s ≠ j := by intro h; rw [h] at hsv; omega
  have k1 := key j r
  have k2 := key j s
  have k3 := key r s
  rw [Matrix.one_apply_ne hrj, Matrix.one_apply_ne hsj] at k1 k2
  rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_ne hrs] at k3
  have hi' : i = r ∨ i = s := by
    have := i.isLt
    rcases (by omega : (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h | h
    · left; exact Fin.ext (by omega)
    · right; exact Fin.ext (by omega)
  apply mul_left_cancel₀ ha0
  rcases hi' with h | h
  · rw [h]
    linear_combination (-(A * B) r j) * k3 + (A * B) r r * k2 - (A * B) r s * k1
  · rw [h]
    linear_combination (-(A * B) s j) * k3 + (A * B) s r * k2 - (A * B) s s * k1
