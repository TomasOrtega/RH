import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderValueEval
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerRingInjective
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.BT.ValEmb.val_emb` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FBtOrderValueEval.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.bt_order_value_eval : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → ∀ (f : Γ.btOrder ⊤) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (f : T → R) → ∀ (B : Type) [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (ρ : (Γ.btOrder ⊤) →+* B), y ≫ j = Spec.map (CommRingCat.ofHom ρ) → valAt y ⊤ le_top s = ρ f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.ValEmb.val_emb | exact GlobalTheory.CompanionTheory.Ar.BT.ValEmb.val_emb | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.ValEmb.val_emb <;> assumption)
