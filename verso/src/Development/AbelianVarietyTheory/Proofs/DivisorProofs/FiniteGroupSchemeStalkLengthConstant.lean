import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteGroupSchemeLength

/- English proof (translation)
Use `letI : Algebra R S := e.toRingHom.toAlgebra`. Establish `h1 : Module.length R S = Module.length S S` using `Module.length_eq_of_surjective (R := S) (M := S) (S := R) e.surjective`. Set `l : R ≃ₗ[R] S` to `{ toFun := e, invFun := e.symm, left_inv := e.left_inv, right_inv := e.right_inv, map_add' := e.map_add, map_smul' := fun r x => by`. Simplify using `only [smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def]`. Use `rfl }`.

Rewrite using `[l.length_eq, h1]`.
-/
theorem length_self_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  have h1 : Module.length R S = Module.length S S :=
    Module.length_eq_of_surjective (R := S) (M := S) (S := R) e.surjective
  let l : R ≃ₗ[R] S :=
    { toFun := e, invFun := e.symm, left_inv := e.left_inv, right_inv := e.right_inv,
      map_add' := e.map_add,
      map_smul' := fun r x => by
        simp only [smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def]
        rfl }
  rw [l.length_eq, h1]

/- English proof (translation)
Establish `hz : f z = IsLocalRing.closedPoint k` using `Subsingleton.elim _ _`. Establish `hc : IsClosed (f ⁻¹' {IsLocalRing.closedPoint k})` using `(IsLocalRing.isClosed_singleton_closedPoint k).preimage f.continuous`. Establish `hd` using `(f.isDiscrete_preimage_singleton (IsLocalRing.closedPoint k)).to_subtype`. Use `hc.isClosedEmbedding_subtypeVal.isClosedMap {⟨z, hz⟩} (isClosed_discrete _)` as an intermediate fact. Rewrite `this` using `[Set.image_singleton]`. Then use the resulting hypothesis.
-/
theorem isClosed_singleton_of_isFinite {k : Type} [Field k] {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of k)) [IsFinite f] (z : H) : IsClosed ({z} : Set H) := by
  have hz : f z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  have hc : IsClosed (f ⁻¹' {IsLocalRing.closedPoint k}) :=
    (IsLocalRing.isClosed_singleton_closedPoint k).preimage f.continuous
  have hd := (f.isDiscrete_preimage_singleton (IsLocalRing.closedPoint k)).to_subtype
  have := hc.isClosedEmbedding_subtypeVal.isClosedMap {⟨z, hz⟩} (isClosed_discrete _)
  rwa [Set.image_singleton] at this

/- English proof (translation)
Introduce `k _ _ G _ hf x x'`. Set `pt : (𝟙_ (Over (Sp k))).left` to `IsLocalRing.closedPoint k`. Establish `hsurj : ∀ y : G.left, ∃ a : 𝟙_ (Over (Sp k)) ⟶ G, a.left pt = y`. Introduce `y`. Establish `hy` using `isClosed_singleton_of_isFinite G.hom y`.

Conclude with `⟨Over.homMk (pointOfClosedPoint G.hom y hy) (pointOfClosedPoint_comp G.hom y hy), pointOfClosedPoint_apply G.hom y hy _⟩`. Take `⟨a, rfl⟩` from `hsurj x`. Take `⟨a', rfl⟩` from `hsurj x'`. Set `φ` to `GrpObj.mulRight (a⁻¹ * a')`. Establish `h : a ≫ φ.hom = a'`.

Establish `: a ≫ φ.hom = a * (a⁻¹ * a')`. Simplify using `[φ, comp_lift_assoc, Hom.mul_def]`. Rewrite using `[this, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul]`. Establish `hx : φ.hom.left (a.left pt) = a'.left pt`. Rewrite using `[← h]`.

Both sides reduce to the same expression. Establish `: IsIso φ.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).mapIso φ).hom)`. Establish `hi : IsIso (φ.hom.left.stalkMap (a.left pt))` using `((isIso_iff_isIso_stalkMap φ.hom.left).1 inferInstance).2 _`. Set `e` to `(asIso (φ.hom.left.stalkMap (a.left pt))).commRingCatIsoToRingEquiv`. Rewrite using `[← length_self_eq_of_ringEquiv e]`.

Apply the tactic sequence `congr 1 <;> rw [hx]`.
-/
theorem length_stalk_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsFinite G.hom → ∀ x x' : G.left, Module.length (G.left.presheaf.stalk x) (G.left.presheaf.stalk x) = Module.length (G.left.presheaf.stalk x') (G.left.presheaf.stalk x') := by
  intro k _ _ G _ hf x x'
  let pt : (𝟙_ (Over (Sp k))).left := IsLocalRing.closedPoint k
  have hsurj : ∀ y : G.left, ∃ a : 𝟙_ (Over (Sp k)) ⟶ G, a.left pt = y := by
    intro y
    have hy := isClosed_singleton_of_isFinite G.hom y
    exact ⟨Over.homMk (pointOfClosedPoint G.hom y hy) (pointOfClosedPoint_comp G.hom y hy),
      pointOfClosedPoint_apply G.hom y hy _⟩
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨a', rfl⟩ := hsurj x'
  let φ := GrpObj.mulRight (a⁻¹ * a')
  have h : a ≫ φ.hom = a' := by
    have : a ≫ φ.hom = a * (a⁻¹ * a') := by
      simp [φ, comp_lift_assoc, Hom.mul_def]
    rw [this, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul]
  have hx : φ.hom.left (a.left pt) = a'.left pt := by
    rw [← h]; rfl
  have : IsIso φ.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso φ).hom)
  have hi : IsIso (φ.hom.left.stalkMap (a.left pt)) :=
    ((isIso_iff_isIso_stalkMap φ.hom.left).1 inferInstance).2 _
  let e := (asIso (φ.hom.left.stalkMap (a.left pt))).commRingCatIsoToRingEquiv
  rw [← length_self_eq_of_ringEquiv e]
  congr 1 <;> rw [hx]

end GlobalTheory.FiniteGroupSchemeLength
