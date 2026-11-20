import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.Linear
import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorSheaf
set_option maxSynthPendingDepth 1

open CategoryTheory AlgebraicGeometry Order Topology

universe u

namespace GroundTheory.Arith.SchemeCoh

section Scalars

variable {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

noncomputable def scalarRingHom : k →+* Γ(X, ⊤) :=
  @algebraMap k Γ(X, ⊤) _ _ (overAlgebra (.of k))

noncomputable instance stalkAlgebra (x : X) : Algebra k (X.presheaf.stalk x) :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp (scalarRingHom X)).toAlgebra

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma algebraMap_stalk (x : X) (c : k) :
    algebraMap k (X.presheaf.stalk x) c = X.presheaf.germ ⊤ x trivial (scalarRingHom X c) := rfl

variable [IsIntegral X]

instance : Nonempty (⊤ : X.Opens) := ⟨⟨(inferInstance : Nonempty X).some, trivial⟩⟩

noncomputable instance functionFieldAlgebra : Algebra k X.functionField :=
  ((X.germToFunctionField ⊤).hom.comp (scalarRingHom X)).toAlgebra

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma algebraMap_functionField (c : k) :
    algebraMap k X.functionField c = X.germToFunctionField ⊤ (scalarRingHom X c) := rfl

instance (x : X) : IsScalarTower k (X.presheaf.stalk x) X.functionField := by
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  rw [algebraMap_functionField, algebraMap_stalk,
    ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (show x ∈ (⊤ : X.Opens) from trivial)]

end Scalars

section DimensionOne

variable {X : Scheme.{u}}

/- English proof (translation)
Set `` to `specializationOrder X`. Establish `h` using `coheight_le_krullDim (irreducibleSetEquivPoints.symm x : TopologicalSpace.IrreducibleCloseds X)`. Rewrite `h` using `[coheight_orderIso]`. Conclude with `h`.
-/
lemma coheight_le_topologicalKrullDim (x : X) :
    (coheight x : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  let := specializationOrder X
  have h := coheight_le_krullDim
    (irreducibleSetEquivPoints.symm x : TopologicalSpace.IrreducibleCloseds X)
  rw [coheight_orderIso] at h
  exact h

/- English proof (translation)
Use `(coheight_le_topologicalKrullDim x).trans hX` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
lemma coheight_le_one (hX : topologicalKrullDim X ≤ 1) (x : X) : coheight x ≤ 1 := by
  have := (coheight_le_topologicalKrullDim x).trans hX
  exact_mod_cast this

variable [IsIntegral X]

/- English proof (translation)
Use `le_antisymm (coheight_le_one hX x) ?_` and prove the remaining obligations. Rewrite using `[Order.one_le_iff_ne_zero, Ne, coheight_eq_zero]`. Introduce `hmax`. Establish `h1 : x ≤ genericPoint X` using `genericPoint_specializes x`. Establish `h2 : genericPoint X ≤ x` using `hmax h1`.

Conclude with `hx (Specializes.antisymm (h2 : x ⤳ genericPoint X) (h1 : genericPoint X ⤳ x)).eq`.
-/
lemma coheight_eq_one (hX : topologicalKrullDim X ≤ 1) {x : X} (hx : x ≠ genericPoint X) :
    coheight x = 1 := by
  refine le_antisymm (coheight_le_one hX x) ?_
  rw [Order.one_le_iff_ne_zero, Ne, coheight_eq_zero]
  intro hmax
  have h1 : x ≤ genericPoint X := genericPoint_specializes x
  have h2 : genericPoint X ≤ x := hmax h1
  exact hx (Specializes.antisymm (h2 : x ⤳ genericPoint X) (h1 : genericPoint X ⤳ x)).eq

/- English proof (translation)
Rewrite using `[ringKrullDim_stalk_eq_coheight, coheight_eq_one hX hx]`. Both sides reduce to the same expression.
-/
lemma ringKrullDim_stalk_eq_one (hX : topologicalKrullDim X ≤ 1) {x : X}
    (hx : x ≠ genericPoint X) : ringKrullDim (X.presheaf.stalk x) = 1 := by
  rw [ringKrullDim_stalk_eq_coheight, coheight_eq_one hX hx]
  rfl

/- English proof (translation)
Introduce `h`. Establish `h1` using `Z.coheight_point`. Rewrite `h1` using `[h, coheight_eq_zero.mpr (fun y _ => genericPoint_specializes y)]`. Conclude with `zero_ne_one h1`.
-/
lemma PrimeDivisor.point_ne_genericPoint (Z : PrimeDivisor X) : Z.point ≠ genericPoint X := by
  intro h
  have h1 := Z.coheight_point
  rw [h, coheight_eq_zero.mpr (fun y _ => genericPoint_specializes y)] at h1
  exact zero_ne_one h1

noncomputable def primeDivisorEquiv (hX : topologicalKrullDim X ≤ 1) :
    PrimeDivisor X ≃ {x : X // x ≠ genericPoint X} where
  toFun Z := ⟨Z.point, Z.point_ne_genericPoint⟩
  invFun x := ⟨x.1, ringKrullDim_stalk_eq_one hX x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Rewrite using `[← closure_subset_iff_isClosed]`. Introduce `y hy`. Rewrite `hy` using `[← specializes_iff_mem_closure]`. Assume the negation of the conclusion as `hne`. Establish `hlt : y < x` using `lt_of_le_not_ge (hy : y ≤ x) fun hxy => hne (Specializes.antisymm (hxy : y ⤳ x) hy).eq`.

Establish `h` using `coheight_add_one_le hlt`. Rewrite `h` using `[coheight_eq_one hX hx]`. Establish `h2` using `coheight_le_one hX y`. Establish `: (1 : ℕ∞) + 1 ≤ 1` using `h.trans h2`. Evaluate the numerical expressions using `at this`.
-/
lemma isClosed_singleton_of_ne (hX : topologicalKrullDim X ≤ 1) {x : X}
    (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  rw [← specializes_iff_mem_closure] at hy
  by_contra hne
  have hlt : y < x := lt_of_le_not_ge (hy : y ≤ x) fun hxy =>
    hne (Specializes.antisymm (hxy : y ⤳ x) hy).eq
  have h := coheight_add_one_le hlt
  rw [coheight_eq_one hX hx] at h
  have h2 := coheight_le_one hX y
  have : (1 : ℕ∞) + 1 ≤ 1 := h.trans h2
  norm_num at this

end DimensionOne

end GroundTheory.Arith.SchemeCoh
