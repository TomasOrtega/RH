import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

/- English proof (translation)
Introduce `R G _ _`. Establish `key : ∀ x : MonoidAlgebra R G, x - algebraMap R (MonoidAlgebra R G) (aug R G x) ∈ augIdeal R G`. Introduce `x`. Proceed by induction on `x using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy`. Rewrite using `[map_add, map_add, add_sub_add_comm]`. Conclude with `add_mem hx hy`. Consider the case `single g r`. Rewrite using `[aug_single]`.

Establish `h1 : MonoidAlgebra.single g r - algebraMap R (MonoidAlgebra R G) r = MonoidAlgebra.single 1 r * (MonoidAlgebra.of R G g - 1)`. Rewrite using `[mul_sub, mul_one, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, one_mul, mul_one, MonoidAlgebra.coe_algebraMap]`. Both sides reduce to the same expression. Rewrite using `[h1]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, rfl⟩)`.

Use `⟨le_antisymm ?_ ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Use `key x` as an intermediate fact. Rewrite `this` using `[RingHom.mem_ker.mp hx, map_zero, sub_zero]`. Then use the resulting hypothesis. Rewrite using `[augIdeal, Ideal.span_le]`.

Introduce and unpack `_ ⟨g, rfl⟩`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, MonoidAlgebra.of_apply, aug_single, sub_self]`. Introduce `r`. Conclude with `⟨MonoidAlgebra.single 1 r, aug_single R G 1 r⟩`.
-/
theorem UpperTheory.V.CF.augKer :
    ∀ (R G : Type) [CommRing R] [CommGroup G], RingHom.ker (aug R G) = augIdeal R G ∧ Function.Surjective (aug R G) := by
  intro R G _ _
  have key : ∀ x : MonoidAlgebra R G,
      x - algebraMap R (MonoidAlgebra R G) (aug R G x) ∈ augIdeal R G := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, map_add, add_sub_add_comm]
      exact add_mem hx hy
    | single g r =>
      rw [aug_single]
      have h1 : MonoidAlgebra.single g r - algebraMap R (MonoidAlgebra R G) r =
          MonoidAlgebra.single 1 r * (MonoidAlgebra.of R G g - 1) := by
        rw [mul_sub, mul_one, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, one_mul,
          mul_one, MonoidAlgebra.coe_algebraMap]
        rfl
      rw [h1]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, rfl⟩)
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · intro x hx
    have := key x
    rwa [RingHom.mem_ker.mp hx, map_zero, sub_zero] at this
  · rw [augIdeal, Ideal.span_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, MonoidAlgebra.of_apply, aug_single,
      sub_self]
  · intro r
    exact ⟨MonoidAlgebra.single 1 r, aug_single R G 1 r⟩
