import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormFrameCoordinatesConstantStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

/- English proof (translation)
Take `⟨n, ⟨Φ⟩⟩` from `hF`. Take `⟨l, hl, hsum⟩` from `GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 n Φ`. Set `S` to `F.obj T`. Set `fwd : S ⊗[R] Glob1 F →ₗ[S] Ω[F.obj T⁄R]` to `e.liftBaseChange S`. Set `inv : Ω[F.obj T⁄R] →ₗ[S] S ⊗[R] Glob1 F` to `∑ i, (Φ.δ i T).smulRight ((1 : S) ⊗ₜ[R] Φ.w i)`.

Establish `hinv : ∀ ω, inv ω = ∑ i, Φ.δ i T ω ⊗ₜ[R] Φ.w i`. Introduce `ω`. Simplify using `only [inv, LinearMap.sum_apply, LinearMap.smulRight_apply]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`.

Establish `h1 : ∀ ω, fwd (inv ω) = ω`. Introduce `ω`. Rewrite using `[hinv, map_sum]`. Simplify using `only [fwd, LinearMap.liftBaseChange_tmul, he]`. Conclude with `(Φ.sum T ω).symm`.

Establish `h2 : ∀ x, inv (fwd x) = x`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.

Consider the case `tmul b w`. Establish `: ∑ i, Φ.δ i T (w.1 T) ⊗ₜ[R] Φ.w i = (1 : S) ⊗ₜ[R] w` using `by conv_rhs => rw [hsum w]`. Rewrite using `[TensorProduct.tmul_sum]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[hl, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`.

Use `show inv (e.liftBaseChange S (b ⊗ₜ[R] w)) = _`. Rewrite using `[LinearMap.liftBaseChange_tmul, map_smul, he, hinv, this, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`. Conclude with `IsBaseChange.of_equiv (LinearEquiv.ofLinear fwd inv (LinearMap.ext h1) (LinearMap.ext h2)) (fun w ↦ by simp [fwd])`.
-/
theorem isBaseChange_glob1 (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (hF : HasFrame F) (h0 : CohomZeroIsConstants F) (T : C) (e : Glob1 F →ₗ[R] Ω[F.obj T⁄R]) (he : ∀ w, e w = w.1 T) :
    IsBaseChange (F.obj T) e := by
  obtain ⟨n, ⟨Φ⟩⟩ := hF
  obtain ⟨l, hl, hsum⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 n Φ
  let S := F.obj T
  let fwd : S ⊗[R] Glob1 F →ₗ[S] Ω[F.obj T⁄R] := e.liftBaseChange S
  let inv : Ω[F.obj T⁄R] →ₗ[S] S ⊗[R] Glob1 F :=
    ∑ i, (Φ.δ i T).smulRight ((1 : S) ⊗ₜ[R] Φ.w i)
  have hinv : ∀ ω, inv ω = ∑ i, Φ.δ i T ω ⊗ₜ[R] Φ.w i := by
    intro ω
    simp only [inv, LinearMap.sum_apply, LinearMap.smulRight_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have h1 : ∀ ω, fwd (inv ω) = ω := by
    intro ω
    rw [hinv, map_sum]
    simp only [fwd, LinearMap.liftBaseChange_tmul, he]
    exact (Φ.sum T ω).symm
  have h2 : ∀ x, inv (fwd x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul b w =>
      have : ∑ i, Φ.δ i T (w.1 T) ⊗ₜ[R] Φ.w i = (1 : S) ⊗ₜ[R] w := by
        conv_rhs => rw [hsum w]
        rw [TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hl, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      show inv (e.liftBaseChange S (b ⊗ₜ[R] w)) = _
      rw [LinearMap.liftBaseChange_tmul, map_smul, he, hinv, this, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  exact IsBaseChange.of_equiv (LinearEquiv.ofLinear fwd inv (LinearMap.ext h1) (LinearMap.ext h2))
    (fun w ↦ by simp [fwd])

end GlobalTheory.AbCoh
