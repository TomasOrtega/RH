import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleTensorProductLeft
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOfIsLocalization

open scoped TensorProduct

namespace GlobalTheory.IndEtaleCancel

/- English proof (translation)
Introduce `A W O _ _ _ _ _ _ _ _ h`. Establish `hT : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W (W ⊗[A] O))` using `GlobalTheory.isIndEtale_tensorProduct_left A O W h`. Take `⟨t, ht1, ht2⟩` from `(Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := W)).1 inferInstance`. Set `g : W →ₐ[A] O` to `IsScalarTower.toAlgHom A W O`. Set `μ : W ⊗[A] O →ₐ[W] O` to `Algebra.TensorProduct.lift (Algebra.ofId W O) (AlgHom.id A O) (fun _ _ => Commute.all _ _)`.

Establish `hμ : ∀ w o, μ (w ⊗ₜ o) = algebraMap W O w * o` using `fun w o => by simp [μ]`. Set `e : W ⊗[A] O` to `Algebra.TensorProduct.map (AlgHom.id A W) g t`. Establish `he1 : ∀ s : W, ((1 : W) ⊗ₜ[A] (algebraMap W O s) - s ⊗ₜ[A] (1 : O)) * e = 0`. Introduce `s`. Use `congrArg (Algebra.TensorProduct.map (AlgHom.id A W) g) (ht1 s)` as an intermediate fact.

Simplify `this` using `[map_mul, map_sub, e, g]`. Establish `hμe : μ e = 1`. Establish `H : (μ.restrictScalars A).comp (Algebra.TensorProduct.map (AlgHom.id A W) g) = g.comp (Algebra.TensorProduct.lmul' A)`. Apply `Algebra.TensorProduct.ext'` to reduce the goal to its premises. Introduce `a b`.

Simplify using `[μ, g, Algebra.TensorProduct.lmul'_apply_tmul, IsScalarTower.algebraMap_apply A W O]`. Use `DFunLike.congr_fun H t` as an intermediate fact. Simplify using `only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at this`. Rewrite using `[show μ e = _ from this, ht2, map_one]`. Establish `hkey : ∀ x : W ⊗[A] O, e * x = e * ((1 : W) ⊗ₜ[A] μ x)`.

Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul w o`. Rewrite using `[hμ]`.

Establish `h1 : (w ⊗ₜ[A] o : W ⊗[A] O) = (w ⊗ₜ[A] (1 : O)) * ((1 : W) ⊗ₜ[A] o)` using `by simp`. Establish `h2 : ((1 : W) ⊗ₜ[A] (algebraMap W O w * o) : W ⊗[A] O) = ((1 : W) ⊗ₜ[A] algebraMap W O w) * ((1 : W) ⊗ₜ[A] o)` using `by simp`. Take the linear combination `e * h1 - e * h2 - ((1 : W) ⊗ₜ[A] o) * he1 w`. Consider the case `add x y hx hy => rw [mul_add, hx, hy, map_add, TensorProduct.tmul_add, mul_add]`. Establish `hidem : IsIdempotentElem e` using `by show e * e = e`.

Rewrite using `[hkey e, hμe, Algebra.TensorProduct.one_def.symm, mul_one]`. Use `letI : Algebra (W ⊗[A] O) O := μ.toRingHom.toAlgebra`. Establish `hmap : ∀ x, algebraMap (W ⊗[A] O) O x = μ x` using `fun _ => rfl`. Use `haveI : IsScalarTower W (W ⊗[A] O) O := IsScalarTower.of_algebraMap_eq (fun w => by rw [hmap, μ.commutes])`. Use `haveI : IsLocalization.Away e O := by`.

Use `IsLocalization.away_of_isIdempotentElem_of_mul hidem (fun x y => ?_) ?_` and prove the remaining obligations. Rewrite using `[hmap, hmap]`. Prove the components needed by the constructor for the conclusion. Introduce `hxy`. Rewrite using `[hkey x, hkey y, hxy]`.

Introduce `hxy`. Establish `hx : μ (e * x) = μ x` using `by rw [map_mul, hμe, one_mul]`. Establish `hy : μ (e * y) = μ y` using `by rw [map_mul, hμe, one_mul]`. Rewrite using `[← hx, ← hy, hxy]`. Introduce `o`.

Conclude with `⟨(1 : W) ⊗ₜ o, by rw [hmap, hμ, map_one, one_mul]⟩`. Conclude with `GlobalTheory.IndEtaleLoc.isIndEtale_of_isLocalization W (W ⊗[A] O) O (Submonoid.powers e) hT`.
-/
theorem isIndEtale_of_etale_of_isIndEtale : ∀ (A W O : Type) [CommRing A] [CommRing W]
    [CommRing O] [Algebra A W] [Algebra A O] [Algebra W O] [IsScalarTower A W O]
    [Algebra.Etale A W], GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A O) →
      GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W O) := by
  intro A W O _ _ _ _ _ _ _ _ h
  have hT : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W (W ⊗[A] O)) :=
    GlobalTheory.isIndEtale_tensorProduct_left A O W h
  obtain ⟨t, ht1, ht2⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := W)).1 inferInstance
  let g : W →ₐ[A] O := IsScalarTower.toAlgHom A W O
  let μ : W ⊗[A] O →ₐ[W] O := Algebra.TensorProduct.lift (Algebra.ofId W O) (AlgHom.id A O)
    (fun _ _ => Commute.all _ _)
  have hμ : ∀ w o, μ (w ⊗ₜ o) = algebraMap W O w * o := fun w o => by simp [μ]
  let e : W ⊗[A] O := Algebra.TensorProduct.map (AlgHom.id A W) g t
  have he1 : ∀ s : W, ((1 : W) ⊗ₜ[A] (algebraMap W O s) - s ⊗ₜ[A] (1 : O)) * e = 0 := by
    intro s
    have := congrArg (Algebra.TensorProduct.map (AlgHom.id A W) g) (ht1 s)
    simpa [map_mul, map_sub, e, g] using this
  have hμe : μ e = 1 := by
    have H : (μ.restrictScalars A).comp (Algebra.TensorProduct.map (AlgHom.id A W) g) =
        g.comp (Algebra.TensorProduct.lmul' A) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp [μ, g, Algebra.TensorProduct.lmul'_apply_tmul, IsScalarTower.algebraMap_apply A W O]
    have := DFunLike.congr_fun H t
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at this
    rw [show μ e = _ from this, ht2, map_one]
  have hkey : ∀ x : W ⊗[A] O, e * x = e * ((1 : W) ⊗ₜ[A] μ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul w o =>
      rw [hμ]
      have h1 : (w ⊗ₜ[A] o : W ⊗[A] O) = (w ⊗ₜ[A] (1 : O)) * ((1 : W) ⊗ₜ[A] o) := by simp
      have h2 : ((1 : W) ⊗ₜ[A] (algebraMap W O w * o) : W ⊗[A] O) =
          ((1 : W) ⊗ₜ[A] algebraMap W O w) * ((1 : W) ⊗ₜ[A] o) := by simp
      linear_combination e * h1 - e * h2 - ((1 : W) ⊗ₜ[A] o) * he1 w
    | add x y hx hy => rw [mul_add, hx, hy, map_add, TensorProduct.tmul_add, mul_add]
  have hidem : IsIdempotentElem e := by
    show e * e = e
    rw [hkey e, hμe, Algebra.TensorProduct.one_def.symm, mul_one]
  letI : Algebra (W ⊗[A] O) O := μ.toRingHom.toAlgebra
  have hmap : ∀ x, algebraMap (W ⊗[A] O) O x = μ x := fun _ => rfl
  haveI : IsScalarTower W (W ⊗[A] O) O :=
    IsScalarTower.of_algebraMap_eq (fun w => by rw [hmap, μ.commutes])
  haveI : IsLocalization.Away e O := by
    refine IsLocalization.away_of_isIdempotentElem_of_mul hidem (fun x y => ?_) ?_
    · rw [hmap, hmap]
      constructor
      · intro hxy; rw [hkey x, hkey y, hxy]
      · intro hxy
        have hx : μ (e * x) = μ x := by rw [map_mul, hμe, one_mul]
        have hy : μ (e * y) = μ y := by rw [map_mul, hμe, one_mul]
        rw [← hx, ← hy, hxy]
    · intro o
      exact ⟨(1 : W) ⊗ₜ o, by rw [hmap, hμ, map_one, one_mul]⟩
  exact GlobalTheory.IndEtaleLoc.isIndEtale_of_isLocalization W (W ⊗[A] O) O (Submonoid.powers e) hT

/- English proof (translation)
The claim follows from `isIndEtale_of_etale_of_isIndEtale`.
-/
example : ∀ (A W O : Type) [CommRing A] [CommRing W] [CommRing O] [Algebra A W] [Algebra A O] [Algebra W O] [IsScalarTower A W O] [Algebra.Etale A W], GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A O) → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W O) :=
  isIndEtale_of_etale_of_isIndEtale

end GlobalTheory.IndEtaleCancel
