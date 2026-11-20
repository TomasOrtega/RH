import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardFiberDoubleCosetMapEqCardInfConj
import Mathlib
open scoped Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCardFiberDoubleCosetMapEqCardInfConj.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.card_fiber_doubleCoset_map_eq_card_inf_conj : ∀ {G : Type} [Group G] (T Γ K' : Subgroup G) (x : G), Nat.card ((fun q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G) => DoubleCoset.mk T K' (Quotient.out q)) ⁻¹' {DoubleCoset.mk T K' x}) = Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T) (((T ⊓ K'.map (MulAut.conj x).toMonoidHom).subgroupOf T : Subgroup T) : Set T)) := by
  first | exact @GlobalTheory.doubleCoset_fibre_card | exact GlobalTheory.doubleCoset_fibre_card | (intros; apply GlobalTheory.doubleCoset_fibre_card <;> assumption)
