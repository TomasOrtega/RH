import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qf15.CardLe :
    Type → ℕ → Prop :=
    fun (M : Type) (B : ℕ) ↦ Finite M ∧ Nat.card M ≤ B

noncomputable def UpperTheory.Reformulated.B.Qf15.TorsLe :
    (M : Type) → [AddCommGroup M] → ℕ → Prop :=
    fun (M : Type) [AddCommGroup M] (B : ℕ) ↦ Finite ↥(AddCommGroup.torsion M) ∧ Nat.card ↥(AddCommGroup.torsion M) ≤ B

/- English proof (translation)
Introduce `A B C _ _ _ f g a c hfg hA hC`. Take `⟨hAf, hAc⟩` from `hA`. Take `⟨hCf, hCc⟩` from `hC`. Set `φ : AddCommGroup.torsion B →+ AddCommGroup.torsion C` to `(g.comp (AddCommGroup.torsion B).subtype).codRestrict _ (fun x => g.isOfFinAddOrder x.2)`. Establish `hk : ∀ x : φ.ker, ∃ y : A, f y = ((x : AddCommGroup.torsion B) : B)`.

Introduce `x`. Establish `hx : φ x = 0` using `x.2`. Conclude with `(hfg _).1 (congrArg Subtype.val hx)`. Use `choose s hs using hk`. Establish `hsi : Function.Injective s`.

Introduce `x y h`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hs x, ← hs y, h]`. Use `haveI : Finite φ.ker := Finite.of_injective s hsi`.

Establish `e` using `(QuotientAddGroup.quotientKerEquivRange φ).toEquiv`. Use `haveI : Finite (AddCommGroup.torsion B ⧸ φ.ker) := Finite.of_equiv _ e.symm`. Establish `h1 : Nat.card φ.ker ≤ a` using `(Nat.card_le_card_of_injective s hsi).trans hAc`. Establish `h2 : Nat.card (AddCommGroup.torsion B ⧸ φ.ker) ≤ c`. Rewrite using `[Nat.card_congr e]`.

Conclude with `(Nat.card_le_card_of_injective _ Subtype.val_injective).trans hCc`. Use `⟨Finite.of_equiv _ (AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := φ.ker)).symm, ?_⟩` and prove the remaining obligations. Rewrite using `[AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker, mul_comm]`. Conclude with `Nat.mul_le_mul h1 h2`.
-/
theorem UpperTheory.Reformulated.B.Qf15.torsStep :
    ∀ (A B C : Type) [inst : AddCommGroup A] [inst_1 : AddCommGroup B] [inst_2 : AddCommGroup C] (f : A →+ B) (g : B →+ C)
      (a c : ℕ),
      Function.Exact (⇑f : A → B) (⇑g : B → C) →
        UpperTheory.Reformulated.B.Qf15.CardLe A a → UpperTheory.Reformulated.B.Qf15.TorsLe C c → UpperTheory.Reformulated.B.Qf15.TorsLe B (a * c) := by
  intro A B C _ _ _ f g a c hfg hA hC
  obtain ⟨hAf, hAc⟩ := hA
  obtain ⟨hCf, hCc⟩ := hC
  let φ : AddCommGroup.torsion B →+ AddCommGroup.torsion C :=
    (g.comp (AddCommGroup.torsion B).subtype).codRestrict _
      (fun x => g.isOfFinAddOrder x.2)
  have hk : ∀ x : φ.ker, ∃ y : A, f y = ((x : AddCommGroup.torsion B) : B) := by
    intro x
    have hx : φ x = 0 := x.2
    exact (hfg _).1 (congrArg Subtype.val hx)
  choose s hs using hk
  have hsi : Function.Injective s := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    rw [← hs x, ← hs y, h]
  haveI : Finite φ.ker := Finite.of_injective s hsi
  have e := (QuotientAddGroup.quotientKerEquivRange φ).toEquiv
  haveI : Finite (AddCommGroup.torsion B ⧸ φ.ker) := Finite.of_equiv _ e.symm
  have h1 : Nat.card φ.ker ≤ a := (Nat.card_le_card_of_injective s hsi).trans hAc
  have h2 : Nat.card (AddCommGroup.torsion B ⧸ φ.ker) ≤ c := by
    rw [Nat.card_congr e]
    exact (Nat.card_le_card_of_injective _ Subtype.val_injective).trans hCc
  refine ⟨Finite.of_equiv _ (AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := φ.ker)).symm, ?_⟩
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker, mul_comm]
  exact Nat.mul_le_mul h1 h2
