import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

set_option autoImplicit false

namespace GlobalTheory.InertSquareNorm

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S.Lat
open scoped Classical

/- English proof (translation)
Establish `hs2 : s ^ 2 = 1`. Use extensionality with `x`. Simplify using `[pow_two, hs]`. Establish `hs1 : s ≠ 1`. Take `⟨x, hx⟩` from `h1`.

Introduce `h`. Conclude with `hx (by rw [h]; rfl)`. Establish `hord : orderOf s = 2` using `orderOf_eq_prime hs2 hs1`. Use `haveI : Finite (k ≃+* k) := Finite.of_injective (fun f : k ≃+* k => (f : k → k)) (fun a b h => RingEquiv.ext (congrFun h))`. Use `haveI : Fintype (Subgroup.zpowers s) := Fintype.ofFinite _`.

Use `haveI : FaithfulSMul (Subgroup.zpowers s) k := ⟨fun {g₁ g₂} h => Subtype.ext (RingEquiv.ext h)⟩`. Establish `hcardG : Fintype.card (Subgroup.zpowers s) = 2`. Rewrite using `[Fintype.card_eq_nat_card]`. Conclude with `(Nat.card_zpowers s).trans hord`. Establish `hfin : Module.finrank (FixedPoints.subfield (Subgroup.zpowers s) k) k = 2` using `(FixedPoints.finrank_eq_card (Subgroup.zpowers s) k).trans hcardG`.

Use `haveI : Fintype k := Fintype.ofFinite k`. Use `haveI : Fintype (FixedPoints.subfield (Subgroup.zpowers s) k) := Fintype.ofFinite _`. Establish `hk : Fintype.card k = Fintype.card (FixedPoints.subfield (Subgroup.zpowers s) k) ^ Module.finrank (FixedPoints.subfield (Subgroup.zpowers s) k) k` using `Module.card_eq_pow_finrank`. Use `⟨Fintype.card (FixedPoints.subfield (Subgroup.zpowers s) k), ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.card_eq_fintype_card, hk, hfin, pow_two]`.
-/
theorem isSquare_card_of_involution {k : Type} [Field k] [Finite k] (s : k ≃+* k)
    (hs : ∀ x, s (s x) = x) (h1 : ∃ x, s x ≠ x) : IsSquare (Nat.card k) := by
  classical
  have hs2 : s ^ 2 = 1 := by
    ext x
    simp [pow_two, hs]
  have hs1 : s ≠ 1 := by
    obtain ⟨x, hx⟩ := h1
    intro h
    exact hx (by rw [h]; rfl)
  have hord : orderOf s = 2 := orderOf_eq_prime hs2 hs1

  haveI : Finite (k ≃+* k) := Finite.of_injective (fun f : k ≃+* k => (f : k → k))
    (fun a b h => RingEquiv.ext (congrFun h))
  haveI : Fintype (Subgroup.zpowers s) := Fintype.ofFinite _
  haveI : FaithfulSMul (Subgroup.zpowers s) k :=
    ⟨fun {g₁ g₂} h => Subtype.ext (RingEquiv.ext h)⟩
  have hcardG : Fintype.card (Subgroup.zpowers s) = 2 := by
    rw [Fintype.card_eq_nat_card]
    exact (Nat.card_zpowers s).trans hord
  have hfin : Module.finrank (FixedPoints.subfield (Subgroup.zpowers s) k) k = 2 :=
    (FixedPoints.finrank_eq_card (Subgroup.zpowers s) k).trans hcardG
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Fintype (FixedPoints.subfield (Subgroup.zpowers s) k) := Fintype.ofFinite _
  have hk : Fintype.card k = Fintype.card (FixedPoints.subfield (Subgroup.zpowers s) k) ^
      Module.finrank (FixedPoints.subfield (Subgroup.zpowers s) k) k :=
    Module.card_eq_pow_finrank
  refine ⟨Fintype.card (FixedPoints.subfield (Subgroup.zpowers s) k), ?_⟩
  rw [Nat.card_eq_fintype_card, hk, hfin, pow_two]

/- English proof (translation)
Introduce `E _ _ _ hE P hP`. Set `c : 𝓞 E →+* 𝓞 E` to `RingOfIntegers.mapRingHom (starRingEnd E)`. Establish `hc : ∀ x : 𝓞 E, algebraMap (𝓞 E) E (c x) = star (algebraMap (𝓞 E) E x)` using `fun x => rfl`. Establish `hcc : ∀ x : 𝓞 E, c (c x) = x` using `fun x => RingOfIntegers.ext (by simp [c])`. Establish `hle : P.asIdeal ≤ P.asIdeal.comap c`.

Introduce `x hx`. Rewrite using `[Ideal.mem_comap, ← hP]`. Conclude with `Ideal.subset_span ⟨x, hx, hc x⟩`. Use `haveI hmax : P.asIdeal.IsMaximal := P.isMaximal`. Use `letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal`.

Set `sb : (𝓞 E ⧸ P.asIdeal) →+* (𝓞 E ⧸ P.asIdeal)` to `Ideal.quotientMap P.asIdeal c hle`. Establish `hsb_mk : ∀ x : 𝓞 E, sb (Ideal.Quotient.mk P.asIdeal x) = Ideal.Quotient.mk P.asIdeal (c x)` using `fun x => Ideal.quotientMap_mk`. Establish `hsb : ∀ y, sb (sb y) = y`. Introduce `y`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Rewrite using `[hsb_mk, hsb_mk, hcc]`. Set `s : (𝓞 E ⧸ P.asIdeal) ≃+* (𝓞 E ⧸ P.asIdeal)` to `{ sb with invFun := sb, left_inv := hsb, right_inv := hsb }`. Establish `hN : Ideal.absNorm P.asIdeal = Nat.card (𝓞 E ⧸ P.asIdeal)`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Use `haveI : Finite (𝓞 E ⧸ P.asIdeal) := by`.

Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises. Rewrite using `[← hN]`. Conclude with `fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)`. Take `⟨θ, t, ht, hθ⟩` from `hE.2.2 P.asIdeal P.isMaximal`. Establish `htc : t = c θ` using `FaithfulSMul.algebraMap_injective (𝓞 E) E (ht.trans (hc θ).symm)`.

Rewrite using `[hN]`. Use `isSquare_card_of_involution s hsb ⟨Ideal.Quotient.mk P.asIdeal θ, fun h => hθ ?_⟩` and prove the remaining obligations. Establish `h2 : Ideal.Quotient.mk P.asIdeal θ = Ideal.Quotient.mk P.asIdeal t`. Rewrite using `[htc, ← hsb_mk]`. Conclude with `h.symm`.

Conclude with `Ideal.Quotient.eq.mp h2`.
-/
theorem isSquare_absNorm : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ P : HeightOneSpectrum (𝓞 E), Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal = P.asIdeal → IsSquare (Ideal.absNorm P.asIdeal) := by
  intro E _ _ _ hE P hP
  classical

  let c : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)
  have hc : ∀ x : 𝓞 E, algebraMap (𝓞 E) E (c x) = star (algebraMap (𝓞 E) E x) := fun x => rfl
  have hcc : ∀ x : 𝓞 E, c (c x) = x := fun x => RingOfIntegers.ext (by simp [c])

  have hle : P.asIdeal ≤ P.asIdeal.comap c := by
    intro x hx
    rw [Ideal.mem_comap, ← hP]
    exact Ideal.subset_span ⟨x, hx, hc x⟩
  haveI hmax : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  let sb : (𝓞 E ⧸ P.asIdeal) →+* (𝓞 E ⧸ P.asIdeal) := Ideal.quotientMap P.asIdeal c hle
  have hsb_mk : ∀ x : 𝓞 E, sb (Ideal.Quotient.mk P.asIdeal x) = Ideal.Quotient.mk P.asIdeal (c x) :=
    fun x => Ideal.quotientMap_mk
  have hsb : ∀ y, sb (sb y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hsb_mk, hsb_mk, hcc]
  let s : (𝓞 E ⧸ P.asIdeal) ≃+* (𝓞 E ⧸ P.asIdeal) :=
    { sb with invFun := sb, left_inv := hsb, right_inv := hsb }
  have hN : Ideal.absNorm P.asIdeal = Nat.card (𝓞 E ⧸ P.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := by
    apply Nat.finite_of_card_ne_zero
    rw [← hN]
    exact fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)

  obtain ⟨θ, t, ht, hθ⟩ := hE.2.2 P.asIdeal P.isMaximal
  have htc : t = c θ := FaithfulSMul.algebraMap_injective (𝓞 E) E (ht.trans (hc θ).symm)
  rw [hN]
  refine isSquare_card_of_involution s hsb ⟨Ideal.Quotient.mk P.asIdeal θ, fun h => hθ ?_⟩
  have h2 : Ideal.Quotient.mk P.asIdeal θ = Ideal.Quotient.mk P.asIdeal t := by
    rw [htc, ← hsb_mk]
    exact h.symm
  exact Ideal.Quotient.eq.mp h2

end GlobalTheory.InertSquareNorm
