import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DExtPoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
Introduce `n A G _ _ D D' h`. Establish `key : D.toDet = D'.toDet`. Use `d_ext D.toDet D'.toDet (MonoidHom.mrange (MonoidAlgebra.of A G)) ?_ ?_` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce and unpack `x -`.

Proceed by induction on `x using MonoidAlgebra.induction_linear with`. Consider the case `zero => exact zero_mem _`. Consider the case `add a b ha hb => exact add_mem ha hb`. Consider the case `single g r`. Establish `: MonoidAlgebra.single g r = r • MonoidAlgebra.single g (1 : A)` using `by simp`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)`. Introduce and unpack `x ⟨g, rfl⟩ i h1 h2`. Rewrite using `[(d_toDet D _).2.1, (d_toDet D' _).2.1]`. Conclude with `h g i h1 h2`.

Rewrite using `[← GDet.ofDet_toDet D, key, GDet.ofDet_toDet]`.
-/
theorem UpperTheory.V.CA.d_gext :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (D' : GDet n A G), (∀ (g : G) (i : ℕ), 1 ≤ i → i ≤ n → D.lam i (MonoidAlgebra.single g 1) = D'.lam i (MonoidAlgebra.single g 1)) → D = D' := by
  intro n A G _ _ D D' h
  have key : D.toDet = D'.toDet := by
    refine d_ext D.toDet D'.toDet (MonoidHom.mrange (MonoidAlgebra.of A G)) ?_ ?_
    · rw [eq_top_iff]
      rintro x -
      induction x using MonoidAlgebra.induction_linear with
      | zero => exact zero_mem _
      | add a b ha hb => exact add_mem ha hb
      | single g r =>
        have : MonoidAlgebra.single g r = r • MonoidAlgebra.single g (1 : A) := by simp
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
    · rintro x ⟨g, rfl⟩ i h1 h2
      rw [(d_toDet D _).2.1, (d_toDet D' _).2.1]
      exact h g i h1 h2
  rw [← GDet.ofDet_toDet D, key, GDet.ofDet_toDet]
