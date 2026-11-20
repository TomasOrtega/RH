import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat

noncomputable section

open GlobalTheory.Shin
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[gal]`.
-/
private theorem gal_id {F : Type} [Field F] (n : ℕ) (y : GL (Fin n) F) :
    gal (RingHom.id F) n y = y := by
  ext i j
  simp [gal]

/- English proof (translation)
Introduce `i j hj hi`. Establish `hij : i ≠ j`. Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers. Simplify using `[Matrix.one_apply_ne hij]`.
-/
private theorem inPar_one {F : Type} [Field F] (a n : ℕ) : InPar a (1 : GL (Fin n) F) := by
  intro i j hj hi
  have hij : i ≠ j := by
    rintro rfl
    omega
  simp [Matrix.one_apply_ne hij]

/- English proof (translation)
Introduce `F _ _ a b n _`. Use `haveI : Fintype (GL (Fin n) F) := Fintype.ofFinite _`. Use `haveI : Fintype (GL (Fin a) F) := Fintype.ofFinite _`. Use `haveI : Fintype (GL (Fin b) F) := Fintype.ofFinite _`. Establish `hN : (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ) ≠ 0` using `by haveI : Nonempty {p : GL (Fin n) F // InPar a p} := ⟨⟨1, inPar_one a n⟩⟩`.

Conclude with `(Nat.card_pos (α := {p : GL (Fin n) F // InPar a p})).ne'` after adjusting the coercions. Establish `hG : (Fintype.card (GL (Fin n) F) : ℂ) ≠ 0`. Conclude with `Fintype.card_ne_zero` after adjusting the coercions. Use `⟨star ((Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹) * (Fintype.card (GL (Fin n) F) : ℂ), mul_ne_zero (star_ne_zero.2 (inv_ne_zero hN)) hG, ?_⟩` and prove the remaining obligations. Introduce `α β T hT`.

Use `set w : GL (Fin n) F → ℂ := fun p => if InPar a p then star (α (tlG a p) * β (brG a b p)) * T p else 0 with hw`. Establish `hleft : ∑ᶠ g, star (hc a b α β n g) * T g = star ((Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹) * ((Fintype.card (GL (Fin n) F) : ℂ) * ∑ p, w p)`. Establish `hy : ∀ y : GL (Fin n) F, ∑ g : GL (Fin n) F, star (if InPar a (y⁻¹ * (g * y)) then α (tlG a (y⁻¹ * (g * y))) * β (brG a b (y⁻¹ * (g * y))) else 0) * T g = ∑ p, w p`. Introduce `y`. Use `Fintype.sum_equiv ((Equiv.mulRight y).trans (Equiv.mulLeft y⁻¹)) _ _ fun g => ?_` and prove the remaining obligations.

Establish `hTg : T (y⁻¹ * (g * y)) = T g`. Rewrite using `[← mul_assoc]`. Conclude with `hT g y`. Simplify using `only [Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight, hw, hTg]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[finsum_eq_sum_of_fintype]`. Simplify using `only [hc, hcTw, gal_id, finsum_eq_sum_of_fintype, star_mul', star_sum, mul_assoc, ← Finset.mul_sum]`. Use `congr 1`. Simplify using `only [Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Simplify using `only [hy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Establish `hright : ∑ᶠ x, star (α x) * ∑ᶠ y, star (β y) * resT a b T x y = ∑ p, w p`. Establish `key : ∀ p : GL (Fin n) F, ∑ x : GL (Fin a) F, ∑ y : GL (Fin b) F, star (α x) * (star (β y) * if InPar a p ∧ tlG a p = x ∧ brG a b p = y then T p else 0) = w p`. Introduce `p`. Rewrite using `[Finset.sum_eq_single (tlG a p), Finset.sum_eq_single (brG a b p)]`.

Apply the tactic sequence `by_cases h : InPar a p <;> simp [hw, h, star_mul', mul_assoc]`. Introduce `y _ hy`. Simplify using `[Ne.symm hy]`. Simplify using the standard rewrite rules. Introduce `x _ hx`.

Simplify using `[Ne.symm hx]`. Simplify using the standard rewrite rules. Simplify using `only [resT, finsum_eq_sum_of_fintype, Finset.mul_sum]`. Rewrite using `[← Finset.sum_congr rfl fun p _ => key p]`. Use `(Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans ?_` and prove the remaining obligations.

Conclude with `Finset.sum_comm`. Rewrite using `[hleft, hright, mul_assoc]`.
-/
theorem frobTwo : FrobTwo := by
  intro F _ _ a b n _
  haveI : Fintype (GL (Fin n) F) := Fintype.ofFinite _
  haveI : Fintype (GL (Fin a) F) := Fintype.ofFinite _
  haveI : Fintype (GL (Fin b) F) := Fintype.ofFinite _
  have hN : (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ) ≠ 0 := by
    haveI : Nonempty {p : GL (Fin n) F // InPar a p} := ⟨⟨1, inPar_one a n⟩⟩
    exact_mod_cast (Nat.card_pos (α := {p : GL (Fin n) F // InPar a p})).ne'
  have hG : (Fintype.card (GL (Fin n) F) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  refine ⟨star ((Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹) * (Fintype.card (GL (Fin n) F) : ℂ),
    mul_ne_zero (star_ne_zero.2 (inv_ne_zero hN)) hG, ?_⟩
  intro α β T hT
  set w : GL (Fin n) F → ℂ := fun p =>
    if InPar a p then star (α (tlG a p) * β (brG a b p)) * T p else 0 with hw
  have hleft : ∑ᶠ g, star (hc a b α β n g) * T g =
      star ((Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹) *
        ((Fintype.card (GL (Fin n) F) : ℂ) * ∑ p, w p) := by
    have hy : ∀ y : GL (Fin n) F,
        ∑ g : GL (Fin n) F, star (if InPar a (y⁻¹ * (g * y)) then
          α (tlG a (y⁻¹ * (g * y))) * β (brG a b (y⁻¹ * (g * y))) else 0) * T g = ∑ p, w p := by
      intro y
      refine Fintype.sum_equiv ((Equiv.mulRight y).trans (Equiv.mulLeft y⁻¹)) _ _ fun g => ?_
      have hTg : T (y⁻¹ * (g * y)) = T g := by
        rw [← mul_assoc]
        exact hT g y
      simp only [Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight, hw, hTg]
      split_ifs <;> simp
    rw [finsum_eq_sum_of_fintype]
    simp only [hc, hcTw, gal_id, finsum_eq_sum_of_fintype, star_mul', star_sum, mul_assoc,
      ← Finset.mul_sum]
    congr 1
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [hy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hright : ∑ᶠ x, star (α x) * ∑ᶠ y, star (β y) * resT a b T x y = ∑ p, w p := by
    have key : ∀ p : GL (Fin n) F, ∑ x : GL (Fin a) F, ∑ y : GL (Fin b) F,
        star (α x) * (star (β y) *
          if InPar a p ∧ tlG a p = x ∧ brG a b p = y then T p else 0) = w p := by
      intro p
      rw [Finset.sum_eq_single (tlG a p), Finset.sum_eq_single (brG a b p)]
      · by_cases h : InPar a p <;> simp [hw, h, star_mul', mul_assoc]
      · intro y _ hy
        simp [Ne.symm hy]
      · simp
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    simp only [resT, finsum_eq_sum_of_fintype, Finset.mul_sum]
    rw [← Finset.sum_congr rfl fun p _ => key p]
    refine (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans ?_
    exact Finset.sum_comm
  rw [hleft, hright, mul_assoc]

end UpperTheory.Gal.InertialTypesAlt
