import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
import Development.AutomorphicArithmetic.CommutativeAlgebra.RepresentedByUnits
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

/- English proof (translation)
Introduce `D _ d U hU`. Use `UpperTheory.represented_by_units (varIdeal (RingHom.id (MvPolynomial (Fin d) D))) U hU (Vec D d).psh (fun T x => ringOf ((Vec.toAff d).app Γ(T, ⊤) x)) ?_ ?_ ?_` and prove the remaining obligations. Introduce `T T' f x`. Conclude with `ringOf_map D f.appTop.hom ((Vec.toAff d).app Γ(T, ⊤) x)`. Introduce `T x`.

Rewrite using `[map_varIdeal, ← x.2]`. Use `congr 2`. Use function extensionality and compare the values at `j`. Simplify using `[ringOf, Vec.toAff]`. Introduce `T ξ hξ`.

Rewrite `hξ` using `[map_varIdeal]`. Use `⟨⟨(ξ.comp MvPolynomial.C, fun j => ξ (MvPolynomial.X j)), hξ⟩, ?_, ?_⟩` and prove the remaining obligations. Use `MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)` and prove the remaining obligations. Simplify using `[ringOf, Vec.toAff]`. Simplify using `[ringOf, Vec.toAff]`.

Introduce `y hy`. Substitute `hy` using the available equality. Use `Subtype.ext (Prod.ext ?_ ?_)` and prove the remaining obligations. Use extensionality with `c`. Simplify using `[ringOf, Vec.toAff]`.

Use function extensionality and compare the values at `j`. Simplify using `[ringOf, Vec.toAff]`.
-/
theorem UpperTheory.vector_bundle_affine_rep :
    ∀ (D : Type) [CommRing D] (d : ℕ) (U : (Spec (CommRingCat.of (MvPolynomial (Fin d) D))).Opens), IsCompl' (varIdeal (RingHom.id (MvPolynomial (Fin d) D))) U → ∃ φ : (Vec D d).psh ⟶ yoneda.obj (U : Scheme.{0}), (∀ (T : Scheme.{0}) (x : (Vec D d).obj Γ(T, ⊤)), φ.app (op T) x ≫ U.ι = specOf (ringOf ((Vec.toAff d).app _ x))) ∧ ∀ T : Scheme.{0}, IsAffine T → Function.Bijective (φ.app (op T)) := by
  intro D _ d U hU
  refine UpperTheory.represented_by_units (varIdeal (RingHom.id (MvPolynomial (Fin d) D))) U hU (Vec D d).psh
    (fun T x => ringOf ((Vec.toAff d).app Γ(T, ⊤) x)) ?_ ?_ ?_
  · intro T T' f x
    exact ringOf_map D f.appTop.hom ((Vec.toAff d).app Γ(T, ⊤) x)
  · intro T x
    rw [map_varIdeal, ← x.2]
    congr 2
    funext j
    simp [ringOf, Vec.toAff]
  · intro T ξ hξ
    rw [map_varIdeal] at hξ
    refine ⟨⟨(ξ.comp MvPolynomial.C, fun j => ξ (MvPolynomial.X j)), hξ⟩, ?_, ?_⟩
    · refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
      · simp [ringOf, Vec.toAff]
      · simp [ringOf, Vec.toAff]
    · intro y hy
      subst hy
      refine Subtype.ext (Prod.ext ?_ ?_)
      · ext c
        simp [ringOf, Vec.toAff]
      · funext j
        simp [ringOf, Vec.toAff]
