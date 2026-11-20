import Development.EtaleCohomology.EtaleTrace.LPdCut

open MvPolynomial

namespace LateralTheory.EtaleTrace.LSmoothPf

noncomputable def polyPres (k : Type) [CommRing k] (N : ℕ) :
    Algebra.SubmersivePresentation k (MvPolynomial (Fin N) k) (Fin N) PEmpty.{1} where
  toGenerators := Algebra.Generators.mvPolynomial k (Fin N)
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    simp only [Set.range_eq_empty, Ideal.span_empty]
    symm
    rw [Algebra.Generators.ker_eq_ker_aeval_val, ← RingHom.injective_iff_ker_eq_bot]
    intro a b h
    simpa using h
  map := PEmpty.elim
  map_inj a := by cases a
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    rw [Matrix.det_isEmpty, map_one]
    exact isUnit_one

/- English proof (translation)
The claim follows from `(polyPres k N).isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])`.
-/
theorem poly_ssmooth (k : Type) [CommRing k] (N : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension N k (MvPolynomial (Fin N) k) :=
  (polyPres k N).isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])

open CategoryTheory AlgebraicGeometry LateralTheory.EtaleTrace.LPdCut
attribute [local instance] MvPolynomial.gradedAlgebra

/- English proof (translation)
Rewrite using `[HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension N)]`. Use `RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_` and prove the remaining obligations. Conclude with `(RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := N) (R := k) (S := MvPolynomial (Fin N) k)).mpr (poly_ssmooth k N)`.
-/
theorem spec_C_smooth (k : Type) [Field k] (N : ℕ) :
    SmoothOfRelativeDimension N (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin N) k))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension N)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := N) (R := k) (S := MvPolynomial (Fin N) k)).mpr
    (poly_ssmooth k N)

/- English proof (translation)
Apply `Proj.iSup_basicOpen_eq_top'` to reduce the goal to its premises. Introduce `i`. Conclude with `⟨1, MvPolynomial.isHomogeneous_X k i⟩`. Rewrite using `[eq_top_iff]`. Introduce `p _hp`.

Use `clear _hp`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `ha : MvPolynomial.C a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0` using `MvPolynomial.isHomogeneous_C _ a`. Establish `: MvPolynomial.C a = algebraMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0) (MvPolynomial (Fin (N + 1)) k) ⟨_, ha⟩` using `rfl`.

Rewrite using `[this]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `add p q hp hq => exact Subalgebra.add_mem _ hp hq`. Consider the case `mul_X p i hp => exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i, rfl⟩)`.
-/
theorem Dp_cover (k : Type) [Field k] (N : ℕ) : ⨆ i, Dp k N i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top'
  · intro i; exact ⟨1, MvPolynomial.isHomogeneous_X k i⟩
  · rw [eq_top_iff]
    intro p _hp
    clear _hp
    induction p using MvPolynomial.induction_on with
    | C a =>
      have ha : MvPolynomial.C a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0 :=
        MvPolynomial.isHomogeneous_C _ a
      have : MvPolynomial.C a = algebraMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0) (MvPolynomial (Fin (N + 1)) k) ⟨_, ha⟩ := rfl
      rw [this]; exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => exact Subalgebra.add_mem _ hp hq
    | mul_X p i hp => exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i, rfl⟩)

/- English proof (translation)
Introduce `k _ N`. Use `choose j hj hc hr using fun i => hC k N i`. Set `𝒰 : (PN k N).OpenCover` to `Scheme.Cover.mkOfCovers (Fin (N + 1)) _ j (fun x => by`. Establish `hx : x ∈ (⊤ : (PN k N).Opens)` using `trivial`. Rewrite `hx` using `[← Dp_cover k N]`.

Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.mp hx`. Establish `: x ∈ Set.range (j i)` using `by rw [hr i]; exact hi`. Take `⟨y, hy⟩` from `this`. Conclude with `⟨i, y, hy⟩) hj`. Establish `hA : ∀ i, IsAffine (𝒰.X i)` using `fun i => by`.

Express the relevant statement in the definitionally equal form `IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin N) k)))`. Use `infer_instance`. Use `HasRingHomProperty.of_source_openCover (P := @SmoothOfRelativeDimension.{0} N) 𝒰 (fun i => ?_)` and prove the remaining obligations. Establish `h : SmoothOfRelativeDimension N (𝒰.f i ≫ PNto k N)`. Express the relevant statement in the definitionally equal form `SmoothOfRelativeDimension N (j i ≫ PNto k N)`.

Rewrite using `[hc i]`. Conclude with `spec_C_smooth k N`. Conclude with `(HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension.{0} N)).mp h`.
-/
theorem LSmooth_of (hC : LChart) : LSmooth := by
  intro k _ N
  choose j hj hc hr using fun i => hC k N i
  let 𝒰 : (PN k N).OpenCover := Scheme.Cover.mkOfCovers (Fin (N + 1)) _ j (fun x => by
    have hx : x ∈ (⊤ : (PN k N).Opens) := trivial
    rw [← Dp_cover k N] at hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have : x ∈ Set.range (j i) := by rw [hr i]; exact hi
    obtain ⟨y, hy⟩ := this
    exact ⟨i, y, hy⟩) hj
  have hA : ∀ i, IsAffine (𝒰.X i) := fun i => by
    change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin N) k))); infer_instance
  refine HasRingHomProperty.of_source_openCover (P := @SmoothOfRelativeDimension.{0} N) 𝒰 (fun i => ?_)
  have h : SmoothOfRelativeDimension N (𝒰.f i ≫ PNto k N) := by
    change SmoothOfRelativeDimension N (j i ≫ PNto k N)
    rw [hc i]
    exact spec_C_smooth k N
  exact (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension.{0} N)).mp h

end LateralTheory.EtaleTrace.LSmoothPf
