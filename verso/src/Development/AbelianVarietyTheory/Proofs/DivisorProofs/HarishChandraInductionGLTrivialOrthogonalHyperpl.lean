import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterCosetSumEqZeroOfSubgroupSum
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

/- English proof (translation)
Introduce `F _ _ a b n hn hb α Y hY hF`. Use `haveI : Fintype (GL (Fin n) F) := Fintype.ofFinite _`. Establish `hn0 : 0 < n` using `by omega`. Establish `hcl : ∀ g x : GL (Fin n) F, Y (x⁻¹ * g * x) = Y g` using `(virt_mul_comap_conj_ind_linear (GL (Fin n) F)).2.2.1 Y (isChar_mem_virt_complex hY)`. Set `Pm : GL (Fin n) F → Prop` to `fun x => ∀ i j : Fin n, (j : ℕ) + 1 < n → (x : Matrix (Fin n) (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j`.

Establish `hR : ∀ (M : Matrix (Fin n) (Fin n) F) (x : GL (Fin n) F), Pm x → ∀ i j : Fin n, (j : ℕ) + 1 < n → (M * (x : Matrix (Fin n) (Fin n) F)) i j = M i j`. Introduce `M x hx i j hj`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [hx _ j hj]`. Rewrite using `[← Matrix.mul_apply, Matrix.mul_one]`.

Set `H : Subgroup (GL (Fin n) F)` to `{ carrier := {x | Pm x} one_mem' := fun i j _ => by simp mul_mem' := fun {x y : GL (Fin n) F} hx hy i j hj => by show ((x * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = _`. Rewrite using `[Units.val_mul, hR _ y hy i j hj]`. Conclude with `hx i j hj`. Use the proof step `inv_mem' := fun {x : GL (Fin n) F} hx i j hj => by`. Establish `h1 : ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (x : Matrix (Fin n) (Fin n) F) = 1`.

Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Use `hR ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) x hx i j hj` as an intermediate fact. Rewrite `this` using `[h1]`. Conclude with `this.symm }`. Establish `hH : ∑ᶠ u : H, Y u = 0`.

Use `hF hn0` as an intermediate fact. Rewrite `this` using `[← finsum_set_coe_eq_finsum_mem]`. Conclude with `this`. Establish `hcos` using `char_coset_sum_eq_zero (GL (Fin n) F) Y hY H hH`. Use `haveI : Fintype H := Fintype.ofFinite _`.

Set `f : GL (Fin n) F → ℂ` to `fun x => if InPar a x then α (tlG a x) else 0`. Establish `hent : ∀ x : GL (Fin n) F, ∀ h ∈ H, ∀ i j : Fin n, (j : ℕ) < a → ((x * h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = (x : Matrix (Fin n) (Fin n) F) i j`. Introduce `x h hh i j hj`. Rewrite using `[Units.val_mul]`. Conclude with `hR _ h hh i j (by omega)`.

Establish `hinv : ∀ x : GL (Fin n) F, ∀ h ∈ H, f (x * h) = f x`. Introduce `x h hh`. Establish `h1 : InPar a (x * h) ↔ InPar a x`. Unfold `InPar`. Prove the components needed by the constructor for the conclusion.

Introduce `H' i j hj hi`. Rewrite using `[← hent x h hh i j hj]`. Conclude with `H' i j hj hi`. Introduce `H' i j hj hi`. Rewrite using `[hent x h hh i j hj]`.

Conclude with `H' i j hj hi`. Establish `h2 : tlG a (x * h) = tlG a x`. Unfold `tlG`. Use `congr 1`. Use function extensionality and compare the values at `i j`.

Unfold `tl ent`. Use `split_ifs with hij`. Conclude with `hent x h hh _ _ j.2`. Both sides reduce to the same expression. Simplify using `only [f, h1, h2]`.

Establish `hS : ∑ x, f x * star (Y x) = 0`. Establish `hh : ∀ h : H, ∑ x, f x * star (Y x) = ∑ x, f x * star (Y (x * h))`. Introduce `h`. Use `Fintype.sum_equiv (Equiv.mulRight (h : GL (Fin n) F)).symm _ _ ?_` and prove the remaining obligations. Introduce `x`.

Simplify using `only [Equiv.coe_mulRight, Equiv.mulRight_symm]`. Rewrite using `[inv_mul_cancel_right, hinv x _ (H.inv_mem h.2)]`. Establish `hsum : (Fintype.card H : ℂ) * ∑ x, f x * star (Y x) = 0`. Rewrite using `[← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]`. Rewrite using `[Finset.sum_congr rfl fun h _ => hh h, Finset.sum_comm]`.

Use `Finset.sum_eq_zero fun x _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, ← star_sum]`. Use `hcos x` as an intermediate fact. Rewrite `this` using `[finsum_eq_sum_of_fintype]`. Rewrite using `[this, star_zero, mul_zero]`.

Establish `hc0 : (Fintype.card H : ℂ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Conclude with `(mul_eq_zero.mp hsum).resolve_left hc0`. Establish `hmain : ∀ y : GL (Fin n) F, ∑ x, f (y⁻¹ * x * y) * star (Y x) = 0`. Introduce `y`. Rewrite using `[← hS]`.

Use `Fintype.sum_equiv (MulAut.conj y⁻¹).toEquiv _ _ ?_` and prove the remaining obligations. Introduce `x`. Simplify using `only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv, hcl]`. Establish `hg : ∀ y : GL (Fin n) F, gal (RingHom.id F) n y = y` using `fun y => by`. Use extensionality with `i j`.

Simplify using `[gal]`. Rewrite using `[finsum_eq_sum_of_fintype]`. Unfold `hc hcTw`. Simplify using `only [hg, mul_one, finsum_eq_sum_of_fintype]`. Simplify using `only [Finset.sum_mul, Finset.mul_sum, mul_assoc]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun y _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum]`. Use `hmain y` as an intermediate fact. Simplify using `only [f, mul_assoc] at this`.

Rewrite using `[this, mul_zero]`.
-/
theorem hc_one_orth_hfree : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → 0 < b →
    ∀ (α : GL (Fin a) F → ℂ) (Y : GL (Fin n) F → ℂ), IsChar ℂ ℂ Y → HFree Y →
    ∑ᶠ x, hc a b α (fun _ => 1) n x * star (Y x) = 0 := by
  intro F _ _ a b n hn hb α Y hY hF
  haveI : Fintype (GL (Fin n) F) := Fintype.ofFinite _
  have hn0 : 0 < n := by omega
  have hcl : ∀ g x : GL (Fin n) F, Y (x⁻¹ * g * x) = Y g :=
    (virt_mul_comap_conj_ind_linear (GL (Fin n) F)).2.2.1 Y (isChar_mem_virt_complex hY)
  let Pm : GL (Fin n) F → Prop := fun x => ∀ i j : Fin n, (j : ℕ) + 1 < n →
    (x : Matrix (Fin n) (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j
  have hR : ∀ (M : Matrix (Fin n) (Fin n) F) (x : GL (Fin n) F), Pm x → ∀ i j : Fin n, (j : ℕ) + 1 < n →
      (M * (x : Matrix (Fin n) (Fin n) F)) i j = M i j := by
    intro M x hx i j hj
    rw [Matrix.mul_apply]
    simp only [hx _ j hj]
    rw [← Matrix.mul_apply, Matrix.mul_one]
  let H : Subgroup (GL (Fin n) F) :=
    { carrier := {x | Pm x}
      one_mem' := fun i j _ => by simp
      mul_mem' := fun {x y : GL (Fin n) F} hx hy i j hj => by
        show ((x * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = _
        rw [Units.val_mul, hR _ y hy i j hj]; exact hx i j hj
      inv_mem' := fun {x : GL (Fin n) F} hx i j hj => by
        have h1 : ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (x : Matrix (Fin n) (Fin n) F) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        have := hR ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) x hx i j hj
        rw [h1] at this
        exact this.symm }
  have hH : ∑ᶠ u : H, Y u = 0 := by
    have := hF hn0
    rw [← finsum_set_coe_eq_finsum_mem] at this
    exact this
  have hcos := char_coset_sum_eq_zero (GL (Fin n) F) Y hY H hH
  haveI : Fintype H := Fintype.ofFinite _
  let f : GL (Fin n) F → ℂ := fun x => if InPar a x then α (tlG a x) else 0
  have hent : ∀ x : GL (Fin n) F, ∀ h ∈ H, ∀ i j : Fin n, (j : ℕ) < a →
      ((x * h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = (x : Matrix (Fin n) (Fin n) F) i j := by
    intro x h hh i j hj
    rw [Units.val_mul]
    exact hR _ h hh i j (by omega)
  have hinv : ∀ x : GL (Fin n) F, ∀ h ∈ H, f (x * h) = f x := by
    intro x h hh
    have h1 : InPar a (x * h) ↔ InPar a x := by
      unfold InPar
      constructor
      · intro H' i j hj hi; rw [← hent x h hh i j hj]; exact H' i j hj hi
      · intro H' i j hj hi; rw [hent x h hh i j hj]; exact H' i j hj hi
    have h2 : tlG a (x * h) = tlG a x := by
      unfold tlG
      congr 1
      funext i j
      unfold tl ent
      split_ifs with hij
      · exact hent x h hh _ _ j.2
      · rfl
    simp only [f, h1, h2]
  have hS : ∑ x, f x * star (Y x) = 0 := by
    have hh : ∀ h : H, ∑ x, f x * star (Y x) = ∑ x, f x * star (Y (x * h)) := by
      intro h
      refine Fintype.sum_equiv (Equiv.mulRight (h : GL (Fin n) F)).symm _ _ ?_
      intro x
      simp only [Equiv.coe_mulRight, Equiv.mulRight_symm]
      rw [inv_mul_cancel_right, hinv x _ (H.inv_mem h.2)]
    have hsum : (Fintype.card H : ℂ) * ∑ x, f x * star (Y x) = 0 := by
      rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
      rw [Finset.sum_congr rfl fun h _ => hh h, Finset.sum_comm]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [← Finset.mul_sum, ← star_sum]
      have := hcos x
      rw [finsum_eq_sum_of_fintype] at this
      rw [this, star_zero, mul_zero]
    have hc0 : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact (mul_eq_zero.mp hsum).resolve_left hc0
  have hmain : ∀ y : GL (Fin n) F, ∑ x, f (y⁻¹ * x * y) * star (Y x) = 0 := by
    intro y
    rw [← hS]
    refine Fintype.sum_equiv (MulAut.conj y⁻¹).toEquiv _ _ ?_
    intro x
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv, hcl]
  have hg : ∀ y : GL (Fin n) F, gal (RingHom.id F) n y = y := fun y => by
    ext i j; simp [gal]
  rw [finsum_eq_sum_of_fintype]
  unfold hc hcTw
  simp only [hg, mul_one, finsum_eq_sum_of_fintype]
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [← Finset.mul_sum]
  have := hmain y
  simp only [f, mul_assoc] at this
  rw [this, mul_zero]

end GlobalTheory.Shin
