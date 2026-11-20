import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtCover

/- English proof (translation)
Introduce `R _ A _ hA n hn D _ _ x`. Take `⟨hf, hfl⟩` from `AbTorsionAnyBase.isFinite_and_flat_mulA _ A hA n hn`. Establish `hs` using `AbelianLimit.surjective_pow A hA n hn`. Set `m : A.left ⟶ A.left` to `((𝟙 A) ^ n : A ⟶ A).left`. Establish `: IsFinite m` using `hf`.

Establish `: Flat m` using `hfl`. Establish `: Surjective m` using `hs`. Set `x₀ : Spec (CommRingCat.of D) ⟶ A.left` to `x.left`. Set `Y` to `Limits.pullback x₀ m`. Establish `: IsAffine Y` using `isAffine_of_isAffineHom (Limits.pullback.fst x₀ m)`.

Set `q : Spec Γ(Y, ⊤) ⟶ Spec (CommRingCat.of D)` to `Y.isoSpec.inv ≫ Limits.pullback.fst x₀ m`. Set `φ : CommRingCat.of D ⟶ Γ(Y, ⊤)` to `Spec.preimage q`. Establish `hφ : Spec.map φ = q` using `Spec.map_preimage q`. Establish `hff : φ.hom.FaithfullyFlat` using `(flat_and_surjective_SpecMap_iff φ).1 (by`. Rewrite using `[hφ]`.

Conclude with `⟨inferInstance, inferInstance⟩)`. Use `letI : Algebra R Γ(Y, ⊤) := (φ.hom.comp (algebraMap R D)).toAlgebra`. Set `ψ : D →ₐ[R] Γ(Y, ⊤)` to `{ φ.hom with commutes' := fun _ ↦ rfl }`. Establish `hψ : (spOver ψ).left = q` using `hφ`. Establish `hc : (Y.isoSpec.inv ≫ Limits.pullback.snd x₀ m) ≫ m = (spOver ψ ≫ x).left`.

Rewrite using `[Category.assoc, ← Limits.pullback.condition, ← Category.assoc, Over.comp_left, hψ]`. Set `z : Pt A Γ(Y, ⊤)` to `Over.homMk (Y.isoSpec.inv ≫ Limits.pullback.snd x₀ m) (by`. Rewrite using `[← Over.w (spOver ψ ≫ x), ← hc]`. Simplify using `only [Category.assoc]`. Rewrite using `[Over.w ((𝟙 A) ^ n : A ⟶ A)])`.

Use `⟨Γ(Y, ⊤), inferInstance, inferInstance, ψ, z, hff, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.comp_id z, ← MonObj.comp_pow]`. Conclude with `Over.OverMorphism.ext hc`.
-/
theorem exists_faithfullyFlat_pow_eq : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, 0 < n → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), ∃ (D' : Type) (_ : CommRing D') (_ : Algebra R D') (ψ : D →ₐ[R] D') (z : Pt A D'), (ψ : D →+* D').FaithfullyFlat ∧ z ^ n = spOver ψ ≫ x := by
  intro R _ A _ hA n hn D _ _ x
  obtain ⟨hf, hfl⟩ := AbTorsionAnyBase.isFinite_and_flat_mulA _ A hA n hn
  have hs := AbelianLimit.surjective_pow A hA n hn
  let m : A.left ⟶ A.left := ((𝟙 A) ^ n : A ⟶ A).left
  have : IsFinite m := hf
  have : Flat m := hfl
  have : Surjective m := hs
  let x₀ : Spec (CommRingCat.of D) ⟶ A.left := x.left
  let Y := Limits.pullback x₀ m
  have : IsAffine Y := isAffine_of_isAffineHom (Limits.pullback.fst x₀ m)
  let q : Spec Γ(Y, ⊤) ⟶ Spec (CommRingCat.of D) := Y.isoSpec.inv ≫ Limits.pullback.fst x₀ m
  let φ : CommRingCat.of D ⟶ Γ(Y, ⊤) := Spec.preimage q
  have hφ : Spec.map φ = q := Spec.map_preimage q
  have hff : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).1 (by
    rw [hφ]; exact ⟨inferInstance, inferInstance⟩)
  letI : Algebra R Γ(Y, ⊤) := (φ.hom.comp (algebraMap R D)).toAlgebra
  let ψ : D →ₐ[R] Γ(Y, ⊤) := { φ.hom with commutes' := fun _ ↦ rfl }
  have hψ : (spOver ψ).left = q := hφ
  have hc : (Y.isoSpec.inv ≫ Limits.pullback.snd x₀ m) ≫ m = (spOver ψ ≫ x).left := by
    rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc, Over.comp_left, hψ]
  let z : Pt A Γ(Y, ⊤) := Over.homMk (Y.isoSpec.inv ≫ Limits.pullback.snd x₀ m) (by
    rw [← Over.w (spOver ψ ≫ x), ← hc]
    simp only [Category.assoc]
    rw [Over.w ((𝟙 A) ^ n : A ⟶ A)])
  refine ⟨Γ(Y, ⊤), inferInstance, inferInstance, ψ, z, hff, ?_⟩
  rw [← Category.comp_id z, ← MonObj.comp_pow]
  exact Over.OverMorphism.ext hc

end GlobalTheory.PtCover
