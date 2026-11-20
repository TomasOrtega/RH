import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

/- English proof (translation)
Introduce `q B C I h hinj hC hI`. Establish `hcoch : ∀ (U : B.Etale) (n : ℤ), n < 0 → ∀ α : Cochain (C.obj U) I n, α = 0`. Introduce `U n hn α`. Use `Cochain.ext _ _ fun p r hpr => ?_` and prove the remaining obligations. Break down `lt_or_ge 0 p with hp | hp` into its components or cases.

Conclude with `(hC U p hp).eq_of_src _ _`. Conclude with `(hI r (by omega)).eq_of_tgt _ _`. Use `haveI : (TC C I h).IsStrictlyGE 0 := by`. Rewrite using `[CochainComplex.isStrictlyGE_iff]`. Introduce `n hn`.

Rewrite using `[IsZero.iff_id_eq_zero]`. Use `Sheaf.hom_ext (NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun α => ?_)))` and prove the remaining obligations. Conclude with `(hcoch U.unop n hn α).trans (hcoch U.unop n hn _).symm`. Use `haveI : ∀ n, Injective ((TC C I h).X n) := hinj`. Conclude with `CochainComplex.isKInjective_of_injective _ 0`.
-/
theorem UpperTheory.totalHomComplex_isKInjective_of_bounded_injective :
    ∀ (q : ℕ) {B : Scheme.{0}} (C : B.Etale ⥤ Cx (ZMod q)) (I : Cx (ZMod q)) (h : ∀ n, Presheaf.IsSheaf (EtTop B) (TP C I n)), (∀ n, Injective (⟨TP C I n, h n⟩ : SShv B q)) → (∀ (U : B.Etale) (n : ℤ), 0 < n → IsZero ((C.obj U).X n)) → (∀ n : ℤ, n < 0 → IsZero (I.X n)) → (TC C I h).IsKInjective := by
  intro q B C I h hinj hC hI
  have hcoch : ∀ (U : B.Etale) (n : ℤ), n < 0 → ∀ α : Cochain (C.obj U) I n, α = 0 := by
    intro U n hn α
    refine Cochain.ext _ _ fun p r hpr => ?_
    rcases lt_or_ge 0 p with hp | hp
    · exact (hC U p hp).eq_of_src _ _
    · exact (hI r (by omega)).eq_of_tgt _ _
  haveI : (TC C I h).IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    rw [IsZero.iff_id_eq_zero]
    refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun α => ?_)))
    exact (hcoch U.unop n hn α).trans (hcoch U.unop n hn _).symm
  haveI : ∀ n, Injective ((TC C I h).X n) := hinj
  exact CochainComplex.isKInjective_of_injective _ 0
