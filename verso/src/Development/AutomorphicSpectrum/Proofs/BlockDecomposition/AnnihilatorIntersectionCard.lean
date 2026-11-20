import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard

namespace GlobalTheory.CompanionTheory.PairCount

/- English proof (translation)
The claim follows from `Nat.card_congr { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩ invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }`.
-/
theorem card_comap_subtype {R X : Type} [Ring R] [AddCommGroup X] [Module R X]
    (p q : Submodule R X) :
    Nat.card ↥(q.comap p.subtype) = Nat.card ↥(p ⊓ q) :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/- English proof (translation)
Establish `e` using `Nat.card_congr (LinearMap.quotientInfEquivSupQuotient I L).toEquiv`. Establish `hq : I.comap I.subtype ⊓ L.comap I.subtype = L.comap I.subtype`. Rewrite using `[Submodule.comap_subtype_self, top_inf_eq]`. Rewrite `e` using `[hq]`. Establish `h1` using `Submodule.card_eq_card_quotient_mul_card (L.comap I.subtype)`.

Establish `h2` using `Submodule.card_eq_card_quotient_mul_card (L.comap (I ⊔ L).subtype)`. Rewrite `h1`, `h2` using `[card_comap_subtype]`. Rewrite `h2` using `[inf_eq_right.2 (le_sup_right : L ≤ I ⊔ L)]`. Rewrite using `[h1, h2, e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_sup_mul_card_inf {R X : Type} [Ring R] [AddCommGroup X] [Module R X] [Finite X]
    (I L : Submodule R X) :
    Nat.card ↥(I ⊔ L) * Nat.card ↥(I ⊓ L) = Nat.card ↥I * Nat.card ↥L := by
  have e := Nat.card_congr (LinearMap.quotientInfEquivSupQuotient I L).toEquiv
  have hq : I.comap I.subtype ⊓ L.comap I.subtype = L.comap I.subtype := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
  rw [hq] at e
  have h1 := Submodule.card_eq_card_quotient_mul_card (L.comap I.subtype)
  have h2 := Submodule.card_eq_card_quotient_mul_card (L.comap (I ⊔ L).subtype)
  rw [card_comap_subtype] at h1 h2
  rw [inf_eq_right.2 (le_sup_right : L ≤ I ⊔ L)] at h2
  rw [h1, h2, e]
  ring

/- English proof (translation)
Establish `: Finite (X →ₗ[ZMod n] ZMod n)` using `Finite.of_injective _ DFunLike.coe_injective`. Establish `hd : Nat.card (X →ₗ[ZMod n] ZMod n) = Nat.card X` using `GlobalTheory.ZModDual.card_dual_eq n X`. Establish `hd' : Nat.card (Y →ₗ[ZMod n] ZMod n) = Nat.card Y` using `GlobalTheory.ZModDual.card_dual_eq n Y`. Establish `: Finite (Y →ₗ[ZMod n] ZMod n)` using `Finite.of_injective _ DFunLike.coe_injective`. Establish `h1 : Nat.card X ≤ Nat.card Y` using `hd' ▸ Nat.card_le_card_of_injective _ hB'`.

Conclude with `hB.bijective_of_nat_card_le (hd ▸ h1)`.
-/
theorem bijective_of_injective (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X]
    [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y]
    (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n) (hB : Function.Injective B)
    (hB' : Function.Injective B.flip) : Function.Bijective B := by
  have : Finite (X →ₗ[ZMod n] ZMod n) := Finite.of_injective _ DFunLike.coe_injective
  have hd : Nat.card (X →ₗ[ZMod n] ZMod n) = Nat.card X := GlobalTheory.ZModDual.card_dual_eq n X
  have hd' : Nat.card (Y →ₗ[ZMod n] ZMod n) = Nat.card Y := GlobalTheory.ZModDual.card_dual_eq n Y
  have : Finite (Y →ₗ[ZMod n] ZMod n) := Finite.of_injective _ DFunLike.coe_injective
  have h1 : Nat.card X ≤ Nat.card Y := hd' ▸ Nat.card_le_card_of_injective _ hB'
  exact hB.bijective_of_nat_card_le (hd ▸ h1)

/- English proof (translation)
Set `e : Y ≃ (X →ₗ[ZMod n] ZMod n)` to `Equiv.ofBijective B (bijective_of_injective n X Y B hB hB')`. Establish `h1 : Nat.card ↥(⨅ x ∈ U, LinearMap.ker (B.flip x)) = Nat.card ↥U.dualAnnihilator`. Use `Nat.card_congr (Equiv.subtypeEquiv e fun y => ?_)` and prove the remaining obligations. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply, Submodule.mem_dualAnnihilator]`. Both sides reduce to the same expression.

Establish `: Finite (X ⧸ U)` using `Finite.of_surjective _ (Submodule.mkQ_surjective U)`. Establish `h2 : Nat.card ↥U.dualAnnihilator = Nat.card (X ⧸ U)`. Rewrite using `[← Nat.card_congr (Submodule.dualQuotEquivDualAnnihilator U).toEquiv]`. Conclude with `GlobalTheory.ZModDual.card_dual_eq n (X ⧸ U)`. Rewrite using `[h1, h2]`.

Rewrite using `[mul_comm]`. Conclude with `(Submodule.card_eq_card_quotient_mul_card U).symm`.
-/
theorem card_annihilator_mul_card (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X]
    [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y]
    (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n) (hB : Function.Injective B)
    (hB' : Function.Injective B.flip) (U : Submodule (ZMod n) X) :
    Nat.card ↥(⨅ x ∈ U, LinearMap.ker (B.flip x)) * Nat.card ↥U = Nat.card X := by
  let e : Y ≃ (X →ₗ[ZMod n] ZMod n) :=
    Equiv.ofBijective B (bijective_of_injective n X Y B hB hB')
  have h1 : Nat.card ↥(⨅ x ∈ U, LinearMap.ker (B.flip x)) = Nat.card ↥U.dualAnnihilator := by
    refine Nat.card_congr (Equiv.subtypeEquiv e fun y => ?_)
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      Submodule.mem_dualAnnihilator]
    rfl
  have : Finite (X ⧸ U) := Finite.of_surjective _ (Submodule.mkQ_surjective U)
  have h2 : Nat.card ↥U.dualAnnihilator = Nat.card (X ⧸ U) := by
    rw [← Nat.card_congr (Submodule.dualQuotEquivDualAnnihilator U).toEquiv]
    exact GlobalTheory.ZModDual.card_dual_eq n (X ⧸ U)
  rw [h1, h2]
  rw [mul_comm]
  exact (Submodule.card_eq_card_quotient_mul_card U).symm

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]`. Use `⟨fun h x hx => ?_, fun h => ⟨fun x hx => h x (Submodule.mem_sup_left hx), fun x hx => h x (Submodule.mem_sup_right hx)⟩⟩` and prove the remaining obligations. Take `⟨i, hi, l, hl, rfl⟩` from `Submodule.mem_sup.1 hx`. Rewrite using `[map_add, h.1 i hi, h.2 l hl, add_zero]`.
-/
theorem annihilator_inf (n : ℕ) (X Y : Type) [AddCommGroup X] [Module (ZMod n) X]
    [AddCommGroup Y] [Module (ZMod n) Y] (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n)
    (I L : Submodule (ZMod n) X) :
    (⨅ x ∈ I, LinearMap.ker (B.flip x)) ⊓ (⨅ x ∈ L, LinearMap.ker (B.flip x)) =
      ⨅ x ∈ I ⊔ L, LinearMap.ker (B.flip x) := by
  ext y
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
  refine ⟨fun h x hx => ?_, fun h => ⟨fun x hx => h x (Submodule.mem_sup_left hx),
    fun x hx => h x (Submodule.mem_sup_right hx)⟩⟩
  obtain ⟨i, hi, l, hl, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add, h.1 i hi, h.2 l hl, add_zero]

/- English proof (translation)
Rewrite using `[annihilator_inf, mul_assoc, ← card_sup_mul_card_inf, ← mul_assoc, card_annihilator_mul_card n X Y B hB hB']`.
-/
theorem card_annihilator_inf (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X]
    [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y]
    (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n) (hB : Function.Injective B)
    (hB' : Function.Injective B.flip) (I L : Submodule (ZMod n) X) :
    Nat.card ↥((⨅ x ∈ I, LinearMap.ker (B.flip x)) ⊓ (⨅ x ∈ L, LinearMap.ker (B.flip x))) *
        Nat.card ↥I * Nat.card ↥L = Nat.card X * Nat.card ↥(I ⊓ L) := by
  rw [annihilator_inf, mul_assoc, ← card_sup_mul_card_inf, ← mul_assoc,
    card_annihilator_mul_card n X Y B hB hB']

end GlobalTheory.CompanionTheory.PairCount
