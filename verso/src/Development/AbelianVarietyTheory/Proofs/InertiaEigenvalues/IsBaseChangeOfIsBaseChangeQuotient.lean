import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfBijectiveBaseChangeQuotientJacobsonStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `R S _ _ _ 𝔞 h𝔞 P _ _ _ V _ _ _ _ _ _ W _ _ _ _ _ _ _ u g hg hgu`. Establish `hF : IsBaseChange S (TensorProduct.mk R S P 1)` using `TensorProduct.isBaseChange R P S`. Set `w : S ⊗[R] P →ₗ[S] V` to `hF.lift u`. Establish `hw : ∀ x : P, w (1 ⊗ₜ[R] x) = u x` using `fun x => hF.lift_eq u x`. Establish `hcomp : (g ∘ₗ w).restrictScalars R ∘ₗ TensorProduct.mk R S P 1 = g.restrictScalars R ∘ₗ u`.

Use extensionality with `x`. Simplify using `[hw]`. Establish `hgw : IsBaseChange (S ⧸ 𝔞) (g ∘ₗ w)` using `hF.of_comp (hcomp ▸ hgu)`. Establish `heq : ∀ z, hg.equiv (w.baseChange (S ⧸ 𝔞) z) = hgw.equiv z`. Introduce `z`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a m`. Rewrite using `[LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul]`. Both sides reduce to the same expression.

Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add]`. Establish `hfun : ⇑(w.baseChange (S ⧸ 𝔞)) = hg.equiv.symm ∘ hgw.equiv`. Use function extensionality and compare the values at `z`. Simplify using `[← heq z]`. Establish `hbij : Function.Bijective (w.baseChange (S ⧸ 𝔞))`.

Rewrite using `[hfun]`. Conclude with `hg.equiv.symm.bijective.comp hgw.equiv.bijective`. Establish `hwb : Function.Bijective w` using `GlobalTheory.BSP.bijective_of_bijective_baseChange_quotient S 𝔞 h𝔞 (S ⊗[R] P) V w hbij`. Conclude with `IsBaseChange.of_equiv (LinearEquiv.ofBijective w hwb) (fun x => hw x)`.
-/
theorem isBaseChange_of_isBaseChange_quotient :
    ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (𝔞 : Ideal S), 𝔞 ≤ Ideal.jacobson ⊥ → ∀ (P : Type) [AddCommGroup P] [Module R P] [Module.Finite R P] (V : Type) [AddCommGroup V] [Module S V] [Module R V] [IsScalarTower R S V] [Module.Finite S V] [Module.Projective S V] (W : Type) [AddCommGroup W] [Module (S ⧸ 𝔞) W] [Module S W] [Module R W] [IsScalarTower S (S ⧸ 𝔞) W] [IsScalarTower R (S ⧸ 𝔞) W] [IsScalarTower R S W] (u : P →ₗ[R] V) (g : V →ₗ[S] W), IsBaseChange (S ⧸ 𝔞) g → IsBaseChange (S ⧸ 𝔞) (g.restrictScalars R ∘ₗ u) → IsBaseChange S u := by
  intro R S _ _ _ 𝔞 h𝔞 P _ _ _ V _ _ _ _ _ _ W _ _ _ _ _ _ _ u g hg hgu
  have hF : IsBaseChange S (TensorProduct.mk R S P 1) := TensorProduct.isBaseChange R P S
  let w : S ⊗[R] P →ₗ[S] V := hF.lift u
  have hw : ∀ x : P, w (1 ⊗ₜ[R] x) = u x := fun x => hF.lift_eq u x
  have hcomp : (g ∘ₗ w).restrictScalars R ∘ₗ TensorProduct.mk R S P 1 = g.restrictScalars R ∘ₗ u := by
    ext x
    simp [hw]
  have hgw : IsBaseChange (S ⧸ 𝔞) (g ∘ₗ w) := hF.of_comp (hcomp ▸ hgu)
  have heq : ∀ z, hg.equiv (w.baseChange (S ⧸ 𝔞) z) = hgw.equiv z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have hfun : ⇑(w.baseChange (S ⧸ 𝔞)) = hg.equiv.symm ∘ hgw.equiv := by
    funext z
    simp [← heq z]
  have hbij : Function.Bijective (w.baseChange (S ⧸ 𝔞)) := by
    rw [hfun]
    exact hg.equiv.symm.bijective.comp hgw.equiv.bijective
  have hwb : Function.Bijective w := GlobalTheory.BSP.bijective_of_bijective_baseChange_quotient S 𝔞 h𝔞 (S ⊗[R] P) V w hbij
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective w hwb) (fun x => hw x)

end GlobalTheory.BSP
