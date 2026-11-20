import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteOfIsClosedTorusZariskiOfPowEqOne

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology

namespace GlobalTheory

namespace RationalPoint

variable {k : Type} [Field k]

noncomputable def pt {X : Over (Sp k)} (y : 𝟙_ (Over (Sp k)) ⟶ X) : X.left :=
  y.left (IsLocalRing.closedPoint k)

/- English proof (translation)
Use `⟨fun h => h ⟨_, rfl⟩, fun h => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Establish `: a = IsLocalRing.closedPoint k` using `Subsingleton.elim (α := PrimeSpectrum k) _ _`. Rewrite using `[this]`. Conclude with `h`.
-/
theorem range_left_subset_iff {X : Over (Sp k)} (y : 𝟙_ (Over (Sp k)) ⟶ X) (Z : Set X.left) :
    Set.range y.left ⊆ Z ↔ pt y ∈ Z := by
  refine ⟨fun h => h ⟨_, rfl⟩, fun h => ?_⟩
  rintro _ ⟨a, rfl⟩
  have : a = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
  rw [this]
  exact h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pt_comp {X Y : Over (Sp k)} (y : 𝟙_ (Over (Sp k)) ⟶ X) (f : X ⟶ Y) :
    pt (y ≫ f) = f.left (pt y) := rfl

@[reducible] noncomputable def zariski (X : Over (Sp k)) :
    TopologicalSpace (𝟙_ (Over (Sp k)) ⟶ X) :=
  TopologicalSpace.induced pt inferInstance

/- English proof (translation)
Use `letI := zariski X`. Use `letI := zariski Y`. Conclude with `continuous_induced_rng.2 (f.left.continuous.comp continuous_induced_dom)`.
-/
theorem continuous_comp {X Y : Over (Sp k)} (f : X ⟶ Y) :
    Continuous[zariski X, zariski Y] fun y => y ≫ f := by
  letI := zariski X
  letI := zariski Y
  exact continuous_induced_rng.2 (f.left.continuous.comp continuous_induced_dom)

/- English proof (translation)
Use `letI := zariski B`. Establish `h : ∀ g y : 𝟙_ (Over (Sp k)) ⟶ B, y ≫ toUnit B ≫ g = g` using `fun g y => by`. Rewrite using `[← Category.assoc, toUnit_unique (y ≫ toUnit B) (𝟙 _), Category.id_comp]`. Use `⟨fun {g} => ?_, fun {g} => ?_⟩` and prove the remaining obligations. Use `continuous_comp ((toUnit B ≫ g) * 𝟙 B) using 2 with y` and compare the differences between its conclusion and the goal.

Rewrite using `[MonObj.comp_mul, h, Category.comp_id]`. Use `continuous_comp (𝟙 B * (toUnit B ≫ g)) using 2 with y` and compare the differences between its conclusion and the goal. Rewrite using `[MonObj.comp_mul, h, Category.comp_id]`.
-/
theorem separatelyContinuousMul (B : Over (Sp k)) [GrpObj B] :
    @SeparatelyContinuousMul (𝟙_ (Over (Sp k)) ⟶ B) (zariski B) _ := by
  letI := zariski B
  have h : ∀ g y : 𝟙_ (Over (Sp k)) ⟶ B, y ≫ toUnit B ≫ g = g := fun g y => by
    rw [← Category.assoc, toUnit_unique (y ≫ toUnit B) (𝟙 _), Category.id_comp]
  refine ⟨fun {g} => ?_, fun {g} => ?_⟩
  · convert continuous_comp ((toUnit B ≫ g) * 𝟙 B) using 2 with y
    rw [MonObj.comp_mul, h, Category.comp_id]
  · convert continuous_comp (𝟙 B * (toUnit B ≫ g)) using 2 with y
    rw [MonObj.comp_mul, h, Category.comp_id]

/- English proof (translation)
Use `letI := zariski B`. Use `⟨?_⟩` and prove the remaining obligations. Use `continuous_comp (𝟙 B)⁻¹ using 2 with y` and compare the differences between its conclusion and the goal. Rewrite using `[GrpObj.comp_inv, Category.comp_id]`.
-/
theorem continuousInv (B : Over (Sp k)) [GrpObj B] :
    @ContinuousInv (𝟙_ (Over (Sp k)) ⟶ B) (zariski B) _ := by
  letI := zariski B
  refine ⟨?_⟩
  convert continuous_comp (𝟙 B)⁻¹ using 2 with y
  rw [GrpObj.comp_inv, Category.comp_id]

variable [IsAlgClosed k]

/- English proof (translation)
The claim follows from `(pointEquivClosedPoint X.hom ⟨y.left, Over.w y⟩).2`.
-/
theorem isClosed_pt {X : Over (Sp k)} [LocallyOfFiniteType X.hom] (y : 𝟙_ (Over (Sp k)) ⟶ X) :
    IsClosed {pt y} :=
  (pointEquivClosedPoint X.hom ⟨y.left, Over.w y⟩).2

/- English proof (translation)
Introduce `x y h` and use `Over.OverMorphism.ext (ext_of_apply_closedPoint_eq X.hom (Over.w x) (Over.w y) h)`.
-/
theorem pt_injective {X : Over (Sp k)} [LocallyOfFiniteType X.hom] :
    Function.Injective (pt : (𝟙_ (Over (Sp k)) ⟶ X) → X.left) := fun x y h =>
  Over.OverMorphism.ext (ext_of_apply_closedPoint_eq X.hom (Over.w x) (Over.w y) h)

/- English proof (translation)
Establish `: JacobsonSpace X.left` using `LocallyOfFiniteType.jacobsonSpace X.hom`. Take `⟨c, hcZ, hc⟩` from `nonempty_inter_closedPoints hne hZ.isLocallyClosed`. Use `replace hc : IsClosed {c} := hc`. Use `⟨Over.homMk (pointOfClosedPoint X.hom c hc) (pointOfClosedPoint_comp X.hom c hc), ?_⟩` and prove the remaining obligations. Establish `: pt (Over.homMk (pointOfClosedPoint X.hom c hc) (pointOfClosedPoint_comp X.hom c hc) : 𝟙_ (Over (Sp k)) ⟶ X) = c` using `pointOfClosedPoint_apply X.hom c hc _`.

Rewrite using `[this]` and apply the resulting hypothesis.
-/
theorem exists_pt_mem {X : Over (Sp k)} [LocallyOfFiniteType X.hom] {Z : Set X.left}
    (hZ : IsClosed Z) (hne : Z.Nonempty) : ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, pt x ∈ Z := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨c, hcZ, hc⟩ := nonempty_inter_closedPoints hne hZ.isLocallyClosed
  replace hc : IsClosed {c} := hc
  refine ⟨Over.homMk (pointOfClosedPoint X.hom c hc) (pointOfClosedPoint_comp X.hom c hc), ?_⟩
  have : pt (Over.homMk (pointOfClosedPoint X.hom c hc) (pointOfClosedPoint_comp X.hom c hc) :
      𝟙_ (Over (Sp k)) ⟶ X) = c := pointOfClosedPoint_apply X.hom c hc _
  rwa [this]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, hzy⟩`. Take `⟨x, hx, hxy⟩` from `exists_pt_mem (Z := Z ∩ f.left ⁻¹' {pt y}) (hZ.inter ((isClosed_pt y).preimage f.left.continuous)) ⟨z, hz, hzy⟩`. Conclude with `⟨x, hx, pt_injective hxy⟩`. Introduce and unpack `⟨x, hx, rfl⟩`.

Conclude with `⟨pt x, hx, rfl⟩`.
-/
theorem pt_mem_image_iff {X Y : Over (Sp k)} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) {Z : Set X.left} (hZ : IsClosed Z)
    (y : 𝟙_ (Over (Sp k)) ⟶ Y) :
    pt y ∈ f.left '' Z ↔ ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, pt x ∈ Z ∧ x ≫ f = y := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := exists_pt_mem (Z := Z ∩ f.left ⁻¹' {pt y})
      (hZ.inter ((isClosed_pt y).preimage f.left.continuous)) ⟨z, hz, hzy⟩
    exact ⟨x, hx, pt_injective hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨pt x, hx, rfl⟩

omit [IsAlgClosed k] in

/- English proof (translation)
Establish `: IsLocallyNoetherian X.left` using `LocallyOfFiniteType.isLocallyNoetherian X.hom`. Establish `: IsLocallyNoetherian Y.left` using `LocallyOfFiniteType.isLocallyNoetherian Y.hom`. Establish `: CompactSpace X.left` using `QuasiCompact.compactSpace_of_compactSpace X.hom`. Establish `: CompactSpace Y.left` using `QuasiCompact.compactSpace_of_compactSpace Y.hom`. Establish `: IsNoetherian X.left` using `{}`.

Establish `: IsNoetherian Y.left` using `{}`. Establish `: LocallyOfFiniteType (f.left ≫ Y.hom)` using `by rw [Over.w f]; infer_instance`. Establish `: LocallyOfFiniteType f.left` using `locallyOfFiniteType_of_comp f.left Y.hom`. Establish `: LocallyOfFinitePresentation f.left` using `inferInstance`. Establish `: QuasiCompact f.left` using `inferInstance`.

Use `f.left.isConstructible_image ?_` and prove the remaining obligations. Conclude with `((TopologicalSpace.NoetherianSpace.isCompact Zᶜ).isConstructible hZ.isOpen_compl).of_compl`.
-/
theorem isConstructible_image_of_isClosed {X Y : Over (Sp k)} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y)
    {Z : Set X.left} (hZ : IsClosed Z) : IsConstructible (f.left '' Z) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian X.left := {}
  have : IsNoetherian Y.left := {}
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : LocallyOfFinitePresentation f.left := inferInstance
  have : QuasiCompact f.left := inferInstance
  refine f.left.isConstructible_image ?_
  exact ((TopologicalSpace.NoetherianSpace.isCompact Zᶜ).isConstructible hZ.isOpen_compl).of_compl

end RationalPoint

open RationalPoint in

/- English proof (translation)
Introduce `k _ _ G B _ _ q _ _ _ _ _ C Z hZ hC`. Use `letI := zariski B`. Use `haveI := separatelyContinuousMul B`. Use `haveI := continuousInv B`. Set `φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ B)` to `MonoidHom.mk' (fun x => x ≫ q) fun x y => MonObj.mul_comp x y q`.

Establish `hcl : IsClosed (C.map φ : Set (𝟙_ (Over (Sp k)) ⟶ B))`. Use `isClosed_subgroup_of_eq_preimage_isConstructible _ (f := pt) continuous_induced_dom (isConstructible_image_of_isClosed q hZ) ?_` and prove the remaining obligations. Use extensionality with `y`. Rewrite using `[Set.mem_preimage, pt_mem_image_iff q hZ]`. Simplify using `only [← range_left_subset_iff, ← hC]`.

Both sides reduce to the same expression. Take `⟨Z', hZ', h⟩` from `isClosed_induced_iff.1 hcl`. Use `⟨Z', hZ', fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[range_left_subset_iff, ← Set.mem_preimage, h]`. Both sides reduce to the same expression.
-/
theorem exists_isClosed_image_of_isClosed_subgroup :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (G B : Over (Sp k)) [GrpObj G] [GrpObj B] (q : G ⟶ B), IsMonHom q → LocallyOfFiniteType G.hom → QuasiCompact G.hom → LocallyOfFiniteType B.hom → QuasiCompact B.hom → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → ∃ Z' : Set B.left, IsClosed Z' ∧ ∀ y : (𝟙_ (Over (Sp k)) ⟶ B), (∃ x ∈ C, x ≫ q = y) ↔ Set.range y.left ⊆ Z' := by
  intro k _ _ G B _ _ q _ _ _ _ _ C Z hZ hC
  letI := zariski B
  haveI := separatelyContinuousMul B
  haveI := continuousInv B
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ B) :=
    MonoidHom.mk' (fun x => x ≫ q) fun x y => MonObj.mul_comp x y q
  have hcl : IsClosed (C.map φ : Set (𝟙_ (Over (Sp k)) ⟶ B)) := by
    refine isClosed_subgroup_of_eq_preimage_isConstructible _ (f := pt) continuous_induced_dom
      (isConstructible_image_of_isClosed q hZ) ?_
    ext y
    rw [Set.mem_preimage, pt_mem_image_iff q hZ]
    simp only [← range_left_subset_iff, ← hC]
    rfl
  obtain ⟨Z', hZ', h⟩ := isClosed_induced_iff.1 hcl
  refine ⟨Z', hZ', fun y => ?_⟩
  rw [range_left_subset_iff, ← Set.mem_preimage, h]
  rfl

end GlobalTheory
