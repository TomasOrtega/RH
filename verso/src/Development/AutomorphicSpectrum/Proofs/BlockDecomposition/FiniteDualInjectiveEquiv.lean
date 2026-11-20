import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.ZModDual

/- English proof (translation)
Establish `hfin : Finite (Module.Dual (ZMod n) X)` using `Finite.of_injective (fun φ : Module.Dual (ZMod n) X => (φ : X → ZMod n)) DFunLike.coe_injective`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Use `letI := Fintype.ofFinite X`. Set `e : Module.Dual (ZMod n) X → AddChar X ℂ` to `fun φ => (ZMod.stdAddChar (N := n)).compAddMonoidHom φ.toAddMonoidHom`. Establish `he : Function.Injective e`.

Introduce `φ ψ h`. Use extensionality with `x`. Establish `hx` using `DFunLike.congr_fun h x`. Conclude with `ZMod.injective_stdAddChar hx`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]`.
-/
private theorem finite_dual_zmod_and_card_le (n : ℕ) [NeZero n] (X : Type) [AddCommGroup X]
    [Module (ZMod n) X] [Finite X] :
    Finite (Module.Dual (ZMod n) X) ∧ Nat.card (Module.Dual (ZMod n) X) ≤ Nat.card X := by
  have hfin : Finite (Module.Dual (ZMod n) X) :=
    Finite.of_injective (fun φ : Module.Dual (ZMod n) X => (φ : X → ZMod n)) DFunLike.coe_injective
  refine ⟨hfin, ?_⟩
  letI := Fintype.ofFinite X
  let e : Module.Dual (ZMod n) X → AddChar X ℂ :=
    fun φ => (ZMod.stdAddChar (N := n)).compAddMonoidHom φ.toAddMonoidHom
  have he : Function.Injective e := by
    intro φ ψ h
    ext x
    have hx := DFunLike.congr_fun h x
    exact ZMod.injective_stdAddChar hx
  calc Nat.card (Module.Dual (ZMod n) X) ≤ Nat.card (AddChar X ℂ) :=
        Nat.card_le_card_of_injective e he
    _ = Nat.card X := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]

/- English proof (translation)
Introduce `n _ X Y _ _ _ _ _ _ hf hg`. Take `⟨f, hf⟩` from `hf`. Take `⟨g, hg⟩` from `hg`. Take `⟨hXf, hXc⟩` from `finite_dual_zmod_and_card_le n X`. Take `⟨hYf, hYc⟩` from `finite_dual_zmod_and_card_le n Y`.

Establish `h1` using `Nat.card_le_card_of_injective f hf`. Establish `h2` using `Nat.card_le_card_of_injective g hg`. Establish `hXY : Nat.card X = Nat.card Y` using `by omega`. Use `⟨⟨LinearEquiv.ofBijective f ⟨hf, ?_⟩⟩, hXY⟩` and prove the remaining obligations. Conclude with `(hf.bijective_of_nat_card_le (by omega)).2`.
-/
theorem equiv_dual_of_injective_pair :
    ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X]
      [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y],
      (∃ f : Y →ₗ[ZMod n] Module.Dual (ZMod n) X, Function.Injective f) →
      (∃ g : X →ₗ[ZMod n] Module.Dual (ZMod n) Y, Function.Injective g) →
      Nonempty (Y ≃ₗ[ZMod n] Module.Dual (ZMod n) X) ∧ Nat.card X = Nat.card Y := by
  intro n _ X Y _ _ _ _ _ _ hf hg
  obtain ⟨f, hf⟩ := hf
  obtain ⟨g, hg⟩ := hg
  obtain ⟨hXf, hXc⟩ := finite_dual_zmod_and_card_le n X
  obtain ⟨hYf, hYc⟩ := finite_dual_zmod_and_card_le n Y
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 := Nat.card_le_card_of_injective g hg
  have hXY : Nat.card X = Nat.card Y := by omega
  refine ⟨⟨LinearEquiv.ofBijective f ⟨hf, ?_⟩⟩, hXY⟩
  exact (hf.bijective_of_nat_card_le (by omega)).2

end GlobalTheory.CompanionTheory.ZModDual
