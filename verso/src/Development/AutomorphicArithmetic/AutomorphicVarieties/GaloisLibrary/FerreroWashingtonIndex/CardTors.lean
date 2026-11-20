import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

/- English proof (translation)
Conclude with `Nat.card_congr (LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq).toEquiv`.
-/
private theorem card_dual (K A : Type) [Field K] [AddCommGroup A] [Module K A] [Finite A] :
    Nat.card (Module.Dual K A) = Nat.card A := by
  exact Nat.card_congr (LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq).toEquiv

/- English proof (translation)
Rewrite using `[← card_dual (ZMod l) A]`. Conclude with `Nat.card_congr { toFun := fun f => f.toZModLinearMap l invFun := fun g => g.toAddMonoidHom left_inv := fun f => by ext; rfl right_inv := fun g => by ext; rfl }`.
-/
private theorem card_addHom_mod (l : ℕ) [Fact l.Prime] (A : Type) [AddCommGroup A] [Finite A]
    [Module (ZMod l) A] : Nat.card (A →+ ZMod l) = Nat.card A := by
  rw [← card_dual (ZMod l) A]
  exact Nat.card_congr
    { toFun := fun f => f.toZModLinearMap l
      invFun := fun g => g.toAddMonoidHom
      left_inv := fun f => by ext; rfl
      right_inv := fun g => by ext; rfl }

/- English proof (translation)
The claim follows from `@card_addHom_mod l _ A _ _ (AddCommGroup.zmodModule h)`.
-/
private theorem card_addHom_zmod (l : ℕ) [Fact l.Prime] (A : Type) [AddCommGroup A] [Finite A]
    (h : ∀ x : A, l • x = 0) : Nat.card (A →+ ZMod l) = Nat.card A :=
  @card_addHom_mod l _ A _ _ (AddCommGroup.zmodModule h)

/- English proof (translation)
Introduce `C _ _`. Use `⟨fun n => ?_, fun l _ => ?_⟩` and prove the remaining obligations. Establish `h1` using `Subgroup.card_mul_index (powR C n)`. Establish `h2` using `Subgroup.card_mul_index (torK C n)`. Establish `h3 : (torK C n).index = Nat.card (powR C n)` using `Subgroup.index_ker _`.

Rewrite `h2` using `[h3]`. Establish `hpos : 0 < Nat.card (powR C n)` using `Nat.card_pos`. Establish `h4 : Nat.card (powR C n) * (powR C n).index = Nat.card (powR C n) * Nat.card (torK C n)`. Rewrite using `[h1, ← h2, mul_comm]`. Conclude with `Nat.eq_of_mul_eq_mul_left hpos h4`.

Use `set N := powR C l`. Establish `hle : ∀ f : C →* Multiplicative (ZMod l), N ≤ f.ker`. Introduce and unpack `f _ ⟨c, rfl⟩`. Rewrite using `[MonoidHom.mem_ker, powMonoidHom_apply, map_pow]`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises.

Simplify using `[toAdd_pow]`. Establish `e : (C ⧸ N →* Multiplicative (ZMod l)) ≃ (C →* Multiplicative (ZMod l))` using `{ toFun := fun g => g.comp (QuotientGroup.mk' N) invFun := fun f => QuotientGroup.lift N f (hle f) left_inv := fun g => by`. Apply `QuotientGroup.monoidHom_ext` to reduce the goal to its premises. Use `ext`. Both sides reduce to the same expression.

Use `right_inv := fun f => by`. Use `ext`. Use `rfl }`. Rewrite using `[← Nat.card_congr e, Nat.card_congr MonoidHom.toAdditiveLeft]`. Establish `ht : ∀ x : Additive (C ⧸ N), l • x = 0`.

Introduce `x`. Take `⟨c, hc⟩` from `QuotientGroup.mk'_surjective N (Additive.toMul x)`. Apply `Additive.toMul.injective` to reduce the goal to its premises. Rewrite using `[toMul_nsmul, ← hc, toMul_zero, QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]`. Conclude with `⟨c, rfl⟩`.

Rewrite using `[card_addHom_zmod l (Additive (C ⧸ N)) ht]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.FW.cardTors :
    ∀ (C : Type) [CommGroup C] [Finite C], (∀ n : ℕ, (powR C n).index = Nat.card (torK C n)) ∧ ∀ (l : ℕ) [Fact l.Prime], Nat.card (C →* Multiplicative (ZMod l)) = (powR C l).index := by
  intro C _ _
  refine ⟨fun n => ?_, fun l _ => ?_⟩
  · have h1 := Subgroup.card_mul_index (powR C n)
    have h2 := Subgroup.card_mul_index (torK C n)
    have h3 : (torK C n).index = Nat.card (powR C n) := Subgroup.index_ker _
    rw [h3] at h2
    have hpos : 0 < Nat.card (powR C n) := Nat.card_pos
    have h4 : Nat.card (powR C n) * (powR C n).index
        = Nat.card (powR C n) * Nat.card (torK C n) := by
      rw [h1, ← h2, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos h4
  · set N := powR C l
    have hle : ∀ f : C →* Multiplicative (ZMod l), N ≤ f.ker := by
      rintro f _ ⟨c, rfl⟩
      rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow]
      apply Multiplicative.toAdd.injective
      simp [toAdd_pow]
    have e : (C ⧸ N →* Multiplicative (ZMod l)) ≃ (C →* Multiplicative (ZMod l)) :=
      { toFun := fun g => g.comp (QuotientGroup.mk' N)
        invFun := fun f => QuotientGroup.lift N f (hle f)
        left_inv := fun g => by
          apply QuotientGroup.monoidHom_ext
          ext
          rfl
        right_inv := fun f => by
          ext
          rfl }
    rw [← Nat.card_congr e, Nat.card_congr MonoidHom.toAdditiveLeft]
    have ht : ∀ x : Additive (C ⧸ N), l • x = 0 := by
      intro x
      obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective N (Additive.toMul x)
      apply Additive.toMul.injective
      rw [toMul_nsmul, ← hc, toMul_zero, QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow,
        QuotientGroup.eq_one_iff]
      exact ⟨c, rfl⟩
    rw [card_addHom_zmod l (Additive (C ⧸ N)) ht]
    rfl
