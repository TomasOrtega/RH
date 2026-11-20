import Development.EtaleCohomology.EtaleSheaves.LeafSpecGenClosed

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

/- English proof (translation)
Introduce `x`. Establish `hx : (x : L) ∈ (Algebra.TensorProduct.productMap A.val B.val).range`. Rewrite using `[Algebra.TensorProduct.productMap_range, A.range_val, B.range_val]`. Use `hD x.2` as an intermediate fact. Rewrite `this` using `[Algebra.adjoin_union, Algebra.adjoin_eq, Algebra.adjoin_eq]`. Then use the resulting hypothesis.

Take `⟨y, hy⟩` from `hx`. Use `⟨y, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[← hy]`. Establish `e : D.val.comp (Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)) = Algebra.TensorProduct.productMap A.val B.val`. Apply the tactic sequence `ext <;> rfl`.

Conclude with `congrArg (fun φ : _ →ₐ[Ω] L => φ y) e`.
-/
theorem prod_surj {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L)
    (hA : A ≤ D) (hB : B ≤ D) (hD : D ≤ Algebra.adjoin Ω ((A : Set L) ∪ B)) :
    Function.Surjective (Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)) := by
  intro x
  have hx : (x : L) ∈ (Algebra.TensorProduct.productMap A.val B.val).range := by
    rw [Algebra.TensorProduct.productMap_range, A.range_val, B.range_val]
    have := hD x.2
    rwa [Algebra.adjoin_union, Algebra.adjoin_eq, Algebra.adjoin_eq] at this
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, Subtype.ext ?_⟩
  rw [← hy]
  have e : D.val.comp (Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)) =
      Algebra.TensorProduct.productMap A.val B.val := by
    ext <;> rfl
  exact congrArg (fun φ : _ →ₐ[Ω] L => φ y) e

/- English proof (translation)
Introduce `Ω L _ _ _ A B D hA hB hD`. Set `φ` to `Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)`. Establish `e : pullback.lift _ _ (spec_w A B D hA hB) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pullbackSpecIso Ω A B).inv`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]`.

Use `congr 1`. Use extensionality with `a`. Simplify using `[φ]`. Rewrite using `[pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]`. Use `congr 1`.

Use extensionality with `a`. Simplify using `[φ]`. Rewrite using `[e]`. Establish `: IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))` using `IsClosedImmersion.spec_of_surjective _ (prod_surj A B D hA hB hD)`. Use `infer_instance`.
-/
theorem spec_subalgebra_pullback_lift_is_closed_immersion : LeafSpecGenClosed := by
  intro Ω L _ _ _ A B D hA hB hD
  let φ := Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)
  have e : pullback.lift _ _ (spec_w A B D hA hB) =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pullbackSpecIso Ω A B).inv := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
      congr 1
      ext a; simp [φ]
    · rw [pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
      congr 1
      ext a; simp [φ]
  rw [e]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ (prod_surj A B D hA hB hD)
  infer_instance

end LateralTheory.E.GluedCurveChartOverlaps
