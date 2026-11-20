import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

/- English proof (translation)
Introduce `l _ k N _ _ h`. Establish `hne : NeZero (l ^ k)` using `⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Use `letI : Module (ZMod (l ^ k)) N := AddCommGroup.zmodModule h`. Establish `hfin : Finite (N →+ ZMod (l ^ k))` using `Finite.of_injective (fun f : N →+ ZMod (l ^ k) => (f : N → ZMod (l ^ k))) DFunLike.coe_injective`. Use `⟨hfin, ?_⟩` and prove the remaining obligations.

Rewrite using `[← GlobalTheory.ZModDual.card_dual_eq (l ^ k) N]`. Use `Nat.card_congr { toFun := fun f => f.toZModLinearMap (l ^ k) invFun := fun f => f.toAddMonoidHom left_inv := fun f => rfl right_inv := fun f => rfl }` and prove the remaining obligations.
-/
theorem UpperTheory.V.Z.J.dualCard :
    ∀ (l : ℕ) [Fact l.Prime] (k : ℕ) (N : Type) [AddCommGroup N] [Finite N], (∀ x : N, l ^ k • x = 0) → Finite (N →+ ZMod (l ^ k)) ∧ Nat.card (N →+ ZMod (l ^ k)) = Nat.card N := by
  intro l _ k N _ _ h
  have hne : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  letI : Module (ZMod (l ^ k)) N := AddCommGroup.zmodModule h
  have hfin : Finite (N →+ ZMod (l ^ k)) :=
    Finite.of_injective (fun f : N →+ ZMod (l ^ k) => (f : N → ZMod (l ^ k))) DFunLike.coe_injective
  refine ⟨hfin, ?_⟩
  rw [← GlobalTheory.ZModDual.card_dual_eq (l ^ k) N]
  refine Nat.card_congr
    { toFun := fun f => f.toZModLinearMap (l ^ k)
      invFun := fun f => f.toAddMonoidHom
      left_inv := fun f => rfl
      right_inv := fun f => rfl }
