import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

/- English proof (translation)
Establish `hη : genericPoint W ∈ genericPoints W`. Rewrite using `[genericPoints_eq_singleton]`. Both sides reduce to the same expression. Take `⟨z, hz⟩` from `genericPoints_subset_range_of_isDominant a hη`. Set `k` to `AlgebraicClosure (Z.residueField z)`.

Set `t : Sp k ⟶ Z` to `spMap (algebraMap (Z.residueField z) k) ≫ Z.fromSpecResidueField z`. Use `⟨k, inferInstance, inferInstance, t, ⟨fun z' => ?_⟩⟩` and prove the remaining obligations. Establish `h₁ : z ⤳ z'`. Rewrite using `[← a.isEmbedding.isInducing.specializes_iff, hz]`. Conclude with `genericPoint_specializes _`.

Establish `h₂ : z ∈ Set.range t` using `⟨IsLocalRing.closedPoint k, Scheme.fromSpecResidueField_apply z _⟩`. Conclude with `closure_mono (Set.singleton_subset_iff.mpr h₂) (specializes_iff_mem_closure.mp h₁)`.
-/
theorem exists_isDominant_geometricPoint_of_isPreimmersion {Z W : Scheme.{0}} [IrreducibleSpace W]
    (a : Z ⟶ W) [IsPreimmersion a] [IsDominant a] [QuasiCompact a] :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (t : Sp k ⟶ Z), IsDominant t := by
  have hη : genericPoint W ∈ genericPoints W := by
    rw [genericPoints_eq_singleton]; rfl
  obtain ⟨z, hz⟩ := genericPoints_subset_range_of_isDominant a hη
  let k := AlgebraicClosure (Z.residueField z)
  let t : Sp k ⟶ Z := spMap (algebraMap (Z.residueField z) k) ≫ Z.fromSpecResidueField z
  refine ⟨k, inferInstance, inferInstance, t, ⟨fun z' => ?_⟩⟩
  have h₁ : z ⤳ z' := by
    rw [← a.isEmbedding.isInducing.specializes_iff, hz]
    exact genericPoint_specializes _
  have h₂ : z ∈ Set.range t :=
    ⟨IsLocalRing.closedPoint k, Scheme.fromSpecResidueField_apply z _⟩
  exact closure_mono (Set.singleton_subset_iff.mpr h₂) (specializes_iff_mem_closure.mp h₁)

/- English proof (translation)
Set `r : pullback q q ⟶ X` to `pullback.fst q q ≫ q`. Use `isNormalScheme_of_smooth r` as an intermediate fact. Use `isDominant_pullback_fst_of_isOpenMap j r r.isOpenMap` as an intermediate fact. Establish `h : pullback.lift (f` using `q) (g := j) (pullback.fst r j ≫ pullback.fst q q) (pullback.snd r j) (by rw [Category.assoc]; exact pullback.condition) = pullback.lift (pullback.fst r j ≫ pullback.snd q q) (pullback.snd r j) (by rw [Category.assoc, ← pullback.condition (f := q) (g := q)]`. Conclude with `pullback.condition) := by`.

Rewrite using `[← cancel_mono (pullback.snd q j), pullback.lift_snd, pullback.lift_snd]`. Establish `h' : pullback.fst r j ≫ pullback.fst q q = pullback.fst r j ≫ pullback.snd q q`. Simplify `congrArg (· ≫ pullback.fst q j) h` using `only [pullback.lift_fst]`. Establish `he : pullback.fst q q = pullback.snd q q` using `ext_of_isDominant_of_isSeparated q pullback.condition _ h'`. Establish `: Mono q` using `⟨fun a b hab => by`.

Rewrite using `[← pullback.lift_fst a b hab, he, pullback.lift_snd]⟩`. Conclude with `IsOpenImmersion.of_flat_of_mono q`.
-/
theorem isOpenImmersion_of_etale_of_mono_pullback_snd {X U W : Scheme.{0}}
    [GlobalTheory.IsNormalScheme X] (j : U ⟶ X) [IsDominant j] (q : W ⟶ X) [Etale q] [IsSeparated q]
    [Mono (pullback.snd q j)] : IsOpenImmersion q := by
  let r : pullback q q ⟶ X := pullback.fst q q ≫ q
  have := isNormalScheme_of_smooth r
  have := isDominant_pullback_fst_of_isOpenMap j r r.isOpenMap
  have h : pullback.lift (f := q) (g := j) (pullback.fst r j ≫ pullback.fst q q) (pullback.snd r j)
        (by rw [Category.assoc]; exact pullback.condition) =
      pullback.lift (pullback.fst r j ≫ pullback.snd q q) (pullback.snd r j)
        (by rw [Category.assoc, ← pullback.condition (f := q) (g := q)]
            exact pullback.condition) := by
    rw [← cancel_mono (pullback.snd q j), pullback.lift_snd, pullback.lift_snd]
  have h' : pullback.fst r j ≫ pullback.fst q q = pullback.fst r j ≫ pullback.snd q q := by
    simpa only [pullback.lift_fst] using congrArg (· ≫ pullback.fst q j) h
  have he : pullback.fst q q = pullback.snd q q :=
    ext_of_isDominant_of_isSeparated q pullback.condition _ h'
  have : Mono q := ⟨fun a b hab => by
    rw [← pullback.lift_fst a b hab, he, pullback.lift_snd]⟩
  exact IsOpenImmersion.of_flat_of_mono q

/- English proof (translation)
Introduce `X U _ j hN _ _ _ _ Y p I _ σ _ _ hσ hgeo y`. Use `IsNormalScheme.of_pred hN` as an intermediate fact. Use `isNormalScheme_of_smooth p` as an intermediate fact. Establish `: IsLocallyNoetherian Y` using `LocallyOfFiniteType.isLocallyNoetherian p`. Set `W : Y.Opens` to `IsNormalScheme.component ⟨_, irreducibleComponent_mem_irreducibleComponents y⟩`.

Establish `hy : y ∈ W` using `mem_irreducibleComponent`. Establish `: IsIntegral W.toScheme` using `inferInstance`. Set `q : W.toScheme ⟶ X` to `W.ι ≫ p`. Use `isDominant_pullback_fst_of_isOpenMap j q q.isOpenMap` as an intermediate fact. Establish `: ∀ z, IsIso ((pullback.fst q j).stalkMap z)` using `isIso_stalkMap_of_flat_of_surjectiveOnStalks _`.

Use `IsNormalScheme.of_isIso_stalkMap (pullback.fst q j)` as an intermediate fact. Take `⟨k, _, _, t, _⟩` from `exists_isDominant_geometricPoint_of_isPreimmersion (pullback.fst q j)`. Take `⟨i, hi⟩` from `hgeo k (t ≫ pullback.snd q j) (t ≫ pullback.fst q j ≫ W.ι) (by simp only [Category.assoc]; rw [← pullback.condition])`. Establish `he : pullback.fst q j ≫ W.ι = pullback.snd q j ≫ σ i` using `ext_of_isDominant_of_isSeparated p (by simp only [Category.assoc]; rw [hσ, ← pullback.condition]) t (by rw [hi, Category.assoc])`. Establish `: Mono (pullback.snd q j ≫ σ i)` using `by rw [← he]; infer_instance`.

Establish `: Mono (pullback.snd q j)` using `mono_of_mono _ (σ i)`. Conclude with `⟨i, W, hy, isOpenImmersion_of_etale_of_mono_pullback_snd j q, he⟩`.
-/
theorem exists_opens_isOpenImmersion_extending_section : ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (Y : Scheme.{0}) (p : Y ⟶ X) (I : Type) [Finite I] (σ : I → (U ⟶ Y)), Etale p → IsSeparated p → (∀ i, σ i ≫ p = j) → (∀ (k : Type) [Field k] [IsAlgClosed k] (u : Sp k ⟶ U) (y : Sp k ⟶ Y), y ≫ p = u ≫ j → ∃ i, y = u ≫ σ i) → ∀ y : Y, ∃ (i : I) (W : Y.Opens), y ∈ W ∧ IsOpenImmersion (W.ι ≫ p) ∧ pullback.fst (W.ι ≫ p) j ≫ W.ι = pullback.snd (W.ι ≫ p) j ≫ σ i := by
  intro X U _ j hN _ _ _ _ Y p I _ σ _ _ hσ hgeo y
  have := IsNormalScheme.of_pred hN
  have := isNormalScheme_of_smooth p
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  let W : Y.Opens :=
    IsNormalScheme.component ⟨_, irreducibleComponent_mem_irreducibleComponents y⟩
  have hy : y ∈ W := mem_irreducibleComponent
  have : IsIntegral W.toScheme := inferInstance
  let q : W.toScheme ⟶ X := W.ι ≫ p
  have := isDominant_pullback_fst_of_isOpenMap j q q.isOpenMap
  have : ∀ z, IsIso ((pullback.fst q j).stalkMap z) :=
    isIso_stalkMap_of_flat_of_surjectiveOnStalks _
  have := IsNormalScheme.of_isIso_stalkMap (pullback.fst q j)
  obtain ⟨k, _, _, t, _⟩ := exists_isDominant_geometricPoint_of_isPreimmersion (pullback.fst q j)
  obtain ⟨i, hi⟩ := hgeo k (t ≫ pullback.snd q j) (t ≫ pullback.fst q j ≫ W.ι)
    (by simp only [Category.assoc]; rw [← pullback.condition])
  have he : pullback.fst q j ≫ W.ι = pullback.snd q j ≫ σ i :=
    ext_of_isDominant_of_isSeparated p
      (by simp only [Category.assoc]; rw [hσ, ← pullback.condition]) t
      (by rw [hi, Category.assoc])
  have : Mono (pullback.snd q j ≫ σ i) := by rw [← he]; infer_instance
  have : Mono (pullback.snd q j) := mono_of_mono _ (σ i)
  exact ⟨i, W, hy, isOpenImmersion_of_etale_of_mono_pullback_snd j q, he⟩

end GlobalTheory
