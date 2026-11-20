import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFielStatement

noncomputable section

namespace GlobalTheory.GLm.Recip

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

/- English proof (translation)
Unfold `toG`. Rewrite using `[dif_pos h.isUnit]`. Conclude with `Units.ext (IsUnit.unit_spec _)`.
-/
theorem toG_coe {g : ℕ} [Fact g.Prime] {n : ℕ} (h : Gn g n) : toG (h : Mt g n) = h := by
  unfold toG
  rw [dif_pos h.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

/- English proof (translation)
Unfold `toG`. Rewrite using `[dif_pos h]`. Conclude with `IsUnit.unit_spec _`.
-/
theorem coe_toG {g : ℕ} [Fact g.Prime] {n : ℕ} {M : Mt g n} (h : IsUnit M) : ((toG M : Gn g n) : Mt g n) = M := by
  unfold toG
  rw [dif_pos h]
  exact IsUnit.unit_spec _

/- English proof (translation)
Unfold `mean`. Establish `h1 : ∀ y : G, ∑ x, χ x * F (y⁻¹ * x * y) = ∑ x, F x * χ x`. Introduce `y`. Use `symm`. Use `Fintype.sum_equiv (MulAut.conj y).toEquiv _ _ ?_` and prove the remaining obligations.

Introduce `x`. Establish `: y⁻¹ * (y * x * y⁻¹) * y = x` using `by group`. Simplify using `only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]`. Rewrite using `[hχ, this, mul_comm]`. Establish `h2 : ∑ x, χ x * (c * ∑ y, F (y⁻¹ * x * y)) = c * ∑ y : G, ∑ x, χ x * F (y⁻¹ * x * y)`.

Rewrite using `[Finset.sum_comm, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : (Fintype.card G : ℂ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`.

Rewrite using `[h2]`. Simplify using `only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem mean_conj {G : Type} [Group G] [Fintype G] (χ F : G → ℂ) (hχ : IsClass χ) (c : ℂ) :
    mean (fun x => χ x * (c * ∑ y, F (y⁻¹ * x * y))) = c * ∑ x, F x * χ x := by
  unfold mean
  have h1 : ∀ y : G, ∑ x, χ x * F (y⁻¹ * x * y) = ∑ x, F x * χ x := by
    intro y
    symm
    refine Fintype.sum_equiv (MulAut.conj y).toEquiv _ _ ?_
    intro x
    have : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    rw [hχ, this, mul_comm]
  have h2 : ∑ x, χ x * (c * ∑ y, F (y⁻¹ * x * y)) = c * ∑ y : G, ∑ x, χ x * F (y⁻¹ * x * y) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum]; ring
  have h3 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [h2]
  simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/- English proof (translation)
Take `⟨-, -, hu, -, -, hcard⟩` from `GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g c d n hn`. Establish `key : ∀ x : Gn g n, (∑ p : Gn g c × Gn g d, Λ p.1 p.2 * (if InPar c (x : Mt g n) ∧ tl c (x : Mt g n) = (p.1 : Mt g c) ∧ br c d (x : Mt g n) = (p.2 : Mt g d) then χ x else 0)) = if InPar c (x : Mt g n) then Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))) * χ x else 0`. Introduce `x`. Distinguish the cases in `hx : InPar c (x : Mt g n)`. Take `⟨h1, h2⟩` from `hu x hx`.

Rewrite using `[if_pos hx, Finset.sum_eq_single (toG (tl c (x : Mt g n)), toG (br c d (x : Mt g n)))]`. Rewrite using `[if_pos ⟨hx, (coe_toG h1).symm, (coe_toG h2).symm⟩]`. Introduce `p _ hp`. Rewrite using `[if_neg, mul_zero]`. Introduce and unpack `⟨-, e1, e2⟩`.

Apply `hp` to reduce the goal to its premises. Rewrite using `[e1, e2, toG_coe, toG_coe]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Simplify using `[hx]`.

Unfold `mean res`. Rewrite using `[hcard]`. Simplify using `only [← key]`. Rewrite using `[Finset.sum_comm (γ := Gn g n), Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.mul_sum, Fintype.card_prod]`. Use `push_cast`. Rewrite using `[mul_inv (_ * _)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mean_res (g : ℕ) [Fact g.Prime] (c d n : ℕ) (hn : n = c + d) (χ : Gn g n → ℂ)
    (Λ : Gn g c → Gn g d → ℂ) :
    mean (fun p : Gn g c × Gn g d => Λ p.1 p.2 * res c d χ p.1 p.2) =
      ((Finset.univ.filter fun x : Gn g n => InPar c (x : Mt g n)).card : ℂ)⁻¹ * ∑ x : Gn g n,
        if InPar c (x : Mt g n) then Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))) * χ x else 0 := by
  obtain ⟨-, -, hu, -, -, hcard⟩ := GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g c d n hn
  have key : ∀ x : Gn g n, (∑ p : Gn g c × Gn g d, Λ p.1 p.2 *
      (if InPar c (x : Mt g n) ∧ tl c (x : Mt g n) = (p.1 : Mt g c) ∧ br c d (x : Mt g n) = (p.2 : Mt g d)
        then χ x else 0)) =
      if InPar c (x : Mt g n) then Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))) * χ x else 0 := by
    intro x
    by_cases hx : InPar c (x : Mt g n)
    · obtain ⟨h1, h2⟩ := hu x hx
      rw [if_pos hx, Finset.sum_eq_single (toG (tl c (x : Mt g n)), toG (br c d (x : Mt g n)))]
      · rw [if_pos ⟨hx, (coe_toG h1).symm, (coe_toG h2).symm⟩]
      · intro p _ hp
        rw [if_neg, mul_zero]
        rintro ⟨-, e1, e2⟩
        apply hp
        rw [e1, e2, toG_coe, toG_coe]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp [hx]
  unfold mean res
  rw [hcard]
  simp only [← key]
  rw [Finset.sum_comm (γ := Gn g n), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.mul_sum, Fintype.card_prod]
  push_cast
  rw [mul_inv (_ * _)]
  ring

/- English proof (translation)
Establish `h0` using `h (fun x y => (starRingEnd ℂ) (A x y - B x y)) (fun y x z => by`. Establish `e1` using `hA1 y x z`. Establish `e2` using `hB1 y x z`. Simplify using `only at e1 e2 ⊢`. Rewrite using `[e1, e2])`.

Use the proof step `(fun x y z => by`. Simplify using `only`. Rewrite using `[hA2 x y z, hB2 x y z])`. Unfold `mean at h0`. Establish `h3 : (Fintype.card (G₁ × G₂) : ℂ)⁻¹ ≠ 0` using `inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)`.

Establish `h1` using `sub_eq_zero.mpr (mul_left_cancel₀ h3 h0)`. Rewrite `h1` using `[← Finset.sum_sub_distrib]`. Establish `h2 : ∑ p : G₁ × G₂, Complex.normSq (A p.1 p.2 - B p.1 p.2) = 0`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[Complex.ofReal_sum, Complex.ofReal_zero, ← h1]`.

Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)]`. Use function extensionality and compare the values at `x y`.

Conclude with `sub_eq_zero.mp (Complex.normSq_eq_zero.mp (h2 (x, y) (Finset.mem_univ _)))`.
-/
theorem eq_of_mean (G₁ G₂ : Type) [Group G₁] [Group G₂] [Fintype G₁] [Fintype G₂] (A B : G₁ → G₂ → ℂ)
    (hA1 : ∀ y, IsClass fun x => A x y) (hA2 : ∀ x, IsClass (A x)) (hB1 : ∀ y, IsClass fun x => B x y)
    (hB2 : ∀ x, IsClass (B x))
    (h : ∀ Λ : G₁ → G₂ → ℂ, (∀ y, IsClass fun x => Λ x y) → (∀ x, IsClass (Λ x)) →
      mean (fun p : G₁ × G₂ => Λ p.1 p.2 * A p.1 p.2) = mean (fun p : G₁ × G₂ => Λ p.1 p.2 * B p.1 p.2)) :
    A = B := by
  have h0 := h (fun x y => (starRingEnd ℂ) (A x y - B x y))
    (fun y x z => by
      have e1 := hA1 y x z
      have e2 := hB1 y x z
      simp only at e1 e2 ⊢
      rw [e1, e2])
    (fun x y z => by
      simp only
      rw [hA2 x y z, hB2 x y z])
  unfold mean at h0
  have h3 : (Fintype.card (G₁ × G₂) : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
  have h1 := sub_eq_zero.mpr (mul_left_cancel₀ h3 h0)
  rw [← Finset.sum_sub_distrib] at h1
  have h2 : ∑ p : G₁ × G₂, Complex.normSq (A p.1 p.2 - B p.1 p.2) = 0 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_zero, ← h1]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]; ring
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)] at h2
  funext x y
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp (h2 (x, y) (Finset.mem_univ _)))

/- English proof (translation)
Introduce `g _`. Use `⟨?_, mean_res g, eq_of_mean⟩` and prove the remaining obligations. Introduce `a b n hn χ Φ hχ`. Establish `h1` using `mean_res g a b n hn χ Φ`. Establish `h2` using `mean_conj χ (fun x : Gn g n => if InPar a (x : Mt g n) then Φ (toG (tl a (x : Mt g n))) (toG (br a b (x : Mt g n))) else 0) hχ ((Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n)).card : ℂ)⁻¹`.

Simplify using `only [ite_mul, zero_mul] at h2`. Rewrite `h2` using `[← h1]`. Simplify using `only [mul_comm (res a b χ _ _)]`. Conclude with `h2`.
-/
theorem reciprocity : ∀ (g : ℕ) [Fact g.Prime] , (∀ (a b n : ℕ), n = a + b → ∀ (χ : Gn g n → ℂ) (Φ : Gn g a → Gn g b → ℂ), IsClass χ → mean (fun x => χ x * hcT a b Φ n x) = mean (fun p : Gn g a × Gn g b => res a b χ p.1 p.2 * Φ p.1 p.2)) ∧ (∀ (c d n : ℕ), n = c + d → ∀ (χ : Gn g n → ℂ) (Λ : Gn g c → Gn g d → ℂ), mean (fun p : Gn g c × Gn g d => Λ p.1 p.2 * res c d χ p.1 p.2) = ((Finset.univ.filter fun x : Gn g n => InPar c (x : Mt g n)).card : ℂ)⁻¹ * ∑ x : Gn g n, if InPar c (x : Mt g n) then Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))) * χ x else 0) ∧ ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] [Fintype G₁] [Fintype G₂] (A B : G₁ → G₂ → ℂ), (∀ y, IsClass fun x => A x y) → (∀ x, IsClass (A x)) → (∀ y, IsClass fun x => B x y) → (∀ x, IsClass (B x)) → (∀ Λ : G₁ → G₂ → ℂ, (∀ y, IsClass fun x => Λ x y) → (∀ x, IsClass (Λ x)) → mean (fun p : G₁ × G₂ => Λ p.1 p.2 * A p.1 p.2) = mean (fun p : G₁ × G₂ => Λ p.1 p.2 * B p.1 p.2)) → A = B := by
  intro g _
  refine ⟨?_, mean_res g, eq_of_mean⟩
  intro a b n hn χ Φ hχ
  have h1 := mean_res g a b n hn χ Φ
  have h2 := mean_conj χ (fun x : Gn g n => if InPar a (x : Mt g n) then
    Φ (toG (tl a (x : Mt g n))) (toG (br a b (x : Mt g n))) else 0) hχ
    ((Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n)).card : ℂ)⁻¹
  simp only [ite_mul, zero_mul] at h2
  rw [← h1] at h2
  simp only [mul_comm (res a b χ _ _)]
  exact h2

end GlobalTheory.GLm.Recip
