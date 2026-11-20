import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped Matrix
open Matrix

namespace GlobalTheory

/- English proof (translation)
Establish `hψne : ∀ v, ψ v ≠ 0` using `fun v hv => by`. Establish `h1` using `AddChar.map_add_eq_mul ψ v (-v)`. Rewrite `h1` using `[add_neg_cancel, AddChar.map_zero_eq_one, hv, zero_mul]`. Conclude with `one_ne_zero h1`. Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Establish `hne' : b.1 + c.1 ≠ a.1` using `fun e => hne e.symm`. Establish `h0` using `congrFun (h fun v => if v = a.1 then 1 else 0) 0`. Simplify using `only [GlobalTheory.WeilM.schr, zero_add, if_pos rfl, if_true, if_neg hne', mul_zero, mul_one] at h0`. Conclude with `hψne _ h0`.

Establish `h1` using `congrFun (h fun _ => 1) x`. Simplify using `only [GlobalTheory.WeilM.schr, mul_one] at h1`. Conclude with `h1`.
-/
theorem schr_factor_data {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    {a b c : (κ → R) × (κ → R)}
    (h : ∀ φ : (κ → R) → ℂ, GlobalTheory.WeilM.schr ψ a φ = GlobalTheory.WeilM.schr ψ b (GlobalTheory.WeilM.schr ψ c φ)) :
    a.1 = b.1 + c.1 ∧ ∀ x : κ → R, ψ (x ⬝ᵥ a.2 + ⅟(2 : R) * (a.1 ⬝ᵥ a.2)) =
      ψ (x ⬝ᵥ b.2 + ⅟(2 : R) * (b.1 ⬝ᵥ b.2)) * ψ ((x + b.1) ⬝ᵥ c.2 + ⅟(2 : R) * (c.1 ⬝ᵥ c.2)) := by
  classical
  have hψne : ∀ v, ψ v ≠ 0 := fun v hv => by
    have h1 := AddChar.map_add_eq_mul ψ v (-v)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, hv, zero_mul] at h1
    exact one_ne_zero h1
  refine ⟨?_, fun x => ?_⟩
  · by_contra hne
    have hne' : b.1 + c.1 ≠ a.1 := fun e => hne e.symm
    have h0 := congrFun (h fun v => if v = a.1 then 1 else 0) 0
    simp only [GlobalTheory.WeilM.schr, zero_add, if_pos rfl, if_true, if_neg hne', mul_zero, mul_one] at h0
    exact hψne _ h0
  · have h1 := congrFun (h fun _ => 1) x
    simp only [GlobalTheory.WeilM.schr, mul_one] at h1
    exact h1

/- English proof (translation)
Introduce `R _ _ ψ κ _ a b c a' b' c' h h' Φ`. Take `⟨ha1, hE⟩` from `schr_factor_data ψ h`. Take `⟨ha1', hE'⟩` from `schr_factor_data ψ h'`. Use function extensionality and compare the values at `X`. Take `⟨x, x', rfl⟩ : ∃ x x' : κ → R, X = Sum.elim x x'` from `⟨_, _, (Sum.elim_comp_inl_inr X).symm⟩`.

Simplify using `only [GlobalTheory.WeilM.schr, ← Sum.elim_add_add, sumElim_dotProduct_sumElim, dotProduct_neg, neg_dotProduct, dotProduct_zero, zero_dotProduct, add_zero, zero_add]`. Establish `hP : Sum.elim (x + a.1) (x' + a'.1) = Sum.elim (x + b.1 + c.1) (x' + b'.1 + c'.1)`. Rewrite using `[ha1, ha1', add_assoc, add_assoc]`. Rewrite using `[hP]`. Simplify using `only [← mul_assoc]`.

Use `congr 1`. Establish `hN : ∀ u v w : R, ψ u = ψ v * ψ w → ψ (-u) = ψ (-v) * ψ (-w)` using `fun u v w e => by`. Rewrite using `[AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv, e, mul_inv]`. Establish `e1` using `hE x`. Establish `e2` using `hN _ _ _ (hE' x')`.

Rewrite using `[show x ⬝ᵥ a.2 + -(x' ⬝ᵥ a'.2) + ⅟(2 : R) * (a.1 ⬝ᵥ a.2 + -(a'.1 ⬝ᵥ a'.2)) = (x ⬝ᵥ a.2 + ⅟(2 : R) * (a.1 ⬝ᵥ a.2)) + -(x' ⬝ᵥ a'.2 + ⅟(2 : R) * (a'.1 ⬝ᵥ a'.2)) by ring, AddChar.map_add_eq_mul, e1, e2]`. Simplify using `only [← AddChar.map_add_eq_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem schr_block_factor : ∀ {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a b c a' b' c' : (κ → R) × (κ → R)),
    (∀ φ : (κ → R) → ℂ, GlobalTheory.WeilM.schr ψ a φ = GlobalTheory.WeilM.schr ψ b (GlobalTheory.WeilM.schr ψ c φ)) →
    (∀ φ : (κ → R) → ℂ, GlobalTheory.WeilM.schr ψ a' φ = GlobalTheory.WeilM.schr ψ b' (GlobalTheory.WeilM.schr ψ c' φ)) →
    ∀ Φ : (κ ⊕ κ → R) → ℂ,
      GlobalTheory.WeilM.schr ψ (Sum.elim a.1 a'.1, Sum.elim a.2 (-a'.2)) Φ =
        GlobalTheory.WeilM.schr ψ (Sum.elim b.1 0, Sum.elim b.2 0)
          (GlobalTheory.WeilM.schr ψ (Sum.elim 0 b'.1, Sum.elim 0 (-b'.2))
            (GlobalTheory.WeilM.schr ψ (Sum.elim c.1 c'.1, Sum.elim c.2 (-c'.2)) Φ)) := by
  intro R _ _ ψ κ _ a b c a' b' c' h h' Φ
  obtain ⟨ha1, hE⟩ := schr_factor_data ψ h
  obtain ⟨ha1', hE'⟩ := schr_factor_data ψ h'
  funext X
  obtain ⟨x, x', rfl⟩ : ∃ x x' : κ → R, X = Sum.elim x x' := ⟨_, _, (Sum.elim_comp_inl_inr X).symm⟩
  simp only [GlobalTheory.WeilM.schr, ← Sum.elim_add_add, sumElim_dotProduct_sumElim, dotProduct_neg, neg_dotProduct,
    dotProduct_zero, zero_dotProduct, add_zero, zero_add]
  have hP : Sum.elim (x + a.1) (x' + a'.1) = Sum.elim (x + b.1 + c.1) (x' + b'.1 + c'.1) := by
    rw [ha1, ha1', add_assoc, add_assoc]
  rw [hP]
  simp only [← mul_assoc]
  congr 1
  have hN : ∀ u v w : R, ψ u = ψ v * ψ w → ψ (-u) = ψ (-v) * ψ (-w) := fun u v w e => by
    rw [AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv, e, mul_inv]
  have e1 := hE x
  have e2 := hN _ _ _ (hE' x')
  rw [show x ⬝ᵥ a.2 + -(x' ⬝ᵥ a'.2) + ⅟(2 : R) * (a.1 ⬝ᵥ a.2 + -(a'.1 ⬝ᵥ a'.2))
      = (x ⬝ᵥ a.2 + ⅟(2 : R) * (a.1 ⬝ᵥ a.2)) + -(x' ⬝ᵥ a'.2 + ⅟(2 : R) * (a'.1 ⬝ᵥ a'.2)) by ring,
    AddChar.map_add_eq_mul, e1, e2]
  simp only [← AddChar.map_add_eq_mul]
  congr 1
  ring

end GlobalTheory
