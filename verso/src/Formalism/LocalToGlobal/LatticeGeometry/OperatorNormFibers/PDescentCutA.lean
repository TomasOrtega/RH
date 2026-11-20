import Mathlib
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm

set_option linter.deprecated false

open Module NumberField

noncomputable section

namespace Formalism.L2.Geo.ExtensionFiltration

/- English proof (translation)
Establish `hs` using `(NumberField.InfinitePlace.Completion.bijective_extensionEmbedding_of_isComplex hv).2`. Establish `hc : Continuous (NumberField.InfinitePlace.Completion.extensionEmbedding v)` using `(NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).continuous`. Establish `h` using `hs.denseRange.comp (NumberField.InfinitePlace.Completion.denseRange_coe v) hc`. Use `Dense.mono ?_ h` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`.

Use `first`. Consider the case `(refine ⟨WithAbs.equiv _ x, ?_⟩ first`. Consider the case `exact (NumberField.InfinitePlace.Completion.extensionEmbedding_coe v x).symm`. Consider the case `simp [NumberField.InfinitePlace.Completion.extensionEmbedding_coe]`. Consider the case `rfl)`.

Consider the case `(refine ⟨WithAbs.ofAbs x, ?_⟩ first`. Consider the case `exact (NumberField.InfinitePlace.Completion.extensionEmbedding_coe v x).symm`. Consider the case `simp [NumberField.InfinitePlace.Completion.extensionEmbedding_coe]`. Consider the case `rfl)`. Consider the case `(refine ⟨x.1, ?_⟩ first`.

Consider the case `exact (NumberField.InfinitePlace.Completion.extensionEmbedding_coe v x).symm`. Consider the case `simp [NumberField.InfinitePlace.Completion.extensionEmbedding_coe]`. Consider the case `rfl)`.
-/
theorem dense_emb {K : Type} [Field K] [NumberField K] (v : InfinitePlace K) (hv : v.IsComplex) :
    DenseRange v.embedding := by
  have hs := (NumberField.InfinitePlace.Completion.bijective_extensionEmbedding_of_isComplex hv).2
  have hc : Continuous (NumberField.InfinitePlace.Completion.extensionEmbedding v) :=
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).continuous
  have h := hs.denseRange.comp (NumberField.InfinitePlace.Completion.denseRange_coe v) hc
  refine Dense.mono ?_ h
  rintro _ ⟨x, rfl⟩
  first
    | (refine ⟨WithAbs.equiv _ x, ?_⟩
       first
        | exact (NumberField.InfinitePlace.Completion.extensionEmbedding_coe v x).symm
        | simp [NumberField.InfinitePlace.Completion.extensionEmbedding_coe]
        | rfl)
    | (refine ⟨WithAbs.ofAbs x, ?_⟩
       first
        | exact (NumberField.InfinitePlace.Completion.extensionEmbedding_coe v x).symm
        | simp [NumberField.InfinitePlace.Completion.extensionEmbedding_coe]
        | rfl)
    | (refine ⟨x.1, ?_⟩
       first
        | exact (NumberField.InfinitePlace.Completion.extensionEmbedding_coe v x).symm
        | simp [NumberField.InfinitePlace.Completion.extensionEmbedding_coe]
        | rfl)

/- English proof (translation)
Establish `h1 : DenseRange (fun f : ι → K => fun i => v.embedding (f i))` using `DenseRange.piMap (fun _ => dense_emb v (IsTotallyComplex.isComplex v))`. Establish `h12 : DenseRange (fun x : V => Formalism.HermitianLatticesTheory.vecAt b v x)`. Establish `hr : Set.range (fun x : V => Formalism.HermitianLatticesTheory.vecAt b v x) = Set.range (fun f : ι → K => fun i => v.embedding (f i))`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨fun i => b.repr x i, rfl⟩`. Introduce and unpack `⟨f, rfl⟩`. Use `⟨b.equivFun.symm f, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Establish `h` using `congrFun (b.equivFun.apply_symm_apply f) i`. Rewrite `h` using `[Basis.equivFun_apply]`. Simplify using `only [Formalism.HermitianLatticesTheory.vecAt, h]`. Introduce `z`. Rewrite using `[hr]`.

Conclude with `h1 z`. Establish `hg : Continuous fun u : ι → ℂ => (WithLp.toLp 2 (Matrix.mulVec (X v)⁻¹ u) : EuclideanSpace ℂ ι)` using `by fun_prop`. Establish `hsurj : Function.Surjective fun u : ι → ℂ => (WithLp.toLp 2 (Matrix.mulVec (X v)⁻¹ u) : EuclideanSpace ℂ ι)`. Introduce `y`. Use `⟨Matrix.mulVec (X v) (WithLp.ofLp y), ?_⟩` and prove the remaining obligations.

Simplify using `only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hX v), Matrix.one_mulVec, WithLp.toLp_ofLp]`. Conclude with `hsurj.denseRange.comp h12 hg`.
-/
theorem dense_fcoord {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) :
    DenseRange fun x : V => (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x) : EuclideanSpace ℂ ι) := by
  have h1 : DenseRange (fun f : ι → K => fun i => v.embedding (f i)) :=
    DenseRange.piMap (fun _ => dense_emb v (IsTotallyComplex.isComplex v))
  have h12 : DenseRange (fun x : V => Formalism.HermitianLatticesTheory.vecAt b v x) := by
    have hr : Set.range (fun x : V => Formalism.HermitianLatticesTheory.vecAt b v x) =
        Set.range (fun f : ι → K => fun i => v.embedding (f i)) := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨fun i => b.repr x i, rfl⟩
      · rintro ⟨f, rfl⟩
        refine ⟨b.equivFun.symm f, ?_⟩
        funext i
        have h := congrFun (b.equivFun.apply_symm_apply f) i
        rw [Basis.equivFun_apply] at h
        simp only [Formalism.HermitianLatticesTheory.vecAt, h]
    intro z
    rw [hr]
    exact h1 z
  have hg : Continuous fun u : ι → ℂ => (WithLp.toLp 2 (Matrix.mulVec (X v)⁻¹ u) : EuclideanSpace ℂ ι) := by
    fun_prop
  have hsurj : Function.Surjective fun u : ι → ℂ => (WithLp.toLp 2 (Matrix.mulVec (X v)⁻¹ u) : EuclideanSpace ℂ ι) := by
    intro y
    refine ⟨Matrix.mulVec (X v) (WithLp.ofLp y), ?_⟩
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hX v), Matrix.one_mulVec, WithLp.toLp_ofLp]
  exact hsurj.denseRange.comp h12 hg

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Formalism.HermitianLatticesTheory.vecAt]`. Rewrite using `[← LinearMap.toMatrix_mulVec_repr b b' φ f, RingHom.map_mulVec]`. Both sides reduce to the same expression.
-/
private theorem vecAt_apply_linearMap {K V ι W κ : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ] (b : Basis ι K V)
    (b' : Basis κ K W) (φ : V →ₗ[K] W) (v : InfinitePlace K) (f : V) :
    Formalism.HermitianLatticesTheory.vecAt b' v (φ f) = Matrix.mulVec ((LinearMap.toMatrix b b' φ).map v.embedding) (Formalism.HermitianLatticesTheory.vecAt b v f) := by
  funext i
  simp only [Formalism.HermitianLatticesTheory.vecAt]
  rw [← LinearMap.toMatrix_mulVec_repr b b' φ f, RingHom.map_mulVec]
  rfl

/- English proof (translation)
Unfold `Formalism.HN.opNormAt`. Use `ContinuousLinearMap.opNorm_le_bound _ hC fun y => ?_` and prove the remaining obligations. Establish `hd` using `dense_fcoord b X hX v`. Use `hd.induction_on (p := fun y => ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v)) y‖ ≤ C * ‖y‖) y ?_ ?_` and prove the remaining obligations. Conclude with `isClosed_le (by fun_prop) (by fun_prop)`.

Introduce `f`. Establish `hn : ∀ (κ' : Type) [Fintype κ'] (u : κ' → ℂ), ‖(WithLp.toLp 2 u : EuclideanSpace ℂ κ')‖ = Formalism.HermitianLatticesTheory.cnorm u`. Introduce `κ' _ u`. Rewrite using `[EuclideanSpace.norm_eq]`. Both sides reduce to the same expression.

Establish `hm : Matrix.mulVec ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v) (Formalism.HermitianLatticesTheory.fcoord b X v f) = Formalism.HermitianLatticesTheory.fcoord b' X' v (φ f)`. Simplify using `only [Formalism.HermitianLatticesTheory.fcoord, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_right _ _ (hX v)]`. Rewrite using `[vecAt_apply_linearMap b b' φ v f, Matrix.mulVec_mulVec]`. Establish `h'` using `h f`. Simplify using `only [LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_toLp, Matrix.toLin'_apply, hm]`.

Use `first`. Consider the case `exact h'`. Consider the case `(rw [hn, hn]; exact h')`.
-/
theorem opNormAt_le_of_points {K V ι W κ : Type} [Field K] [NumberField K] [StarRing K]
    [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ)
    (hX : ∀ v, IsUnit (X v).det) (φ : V →ₗ[K] W) (v : InfinitePlace K) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f, Formalism.HermitianLatticesTheory.normAt b' X' v (φ f) ≤ C * Formalism.HermitianLatticesTheory.normAt b X v f) :
    Formalism.HN.opNormAt b X b' X' v φ ≤ C := by
  unfold Formalism.HN.opNormAt
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun y => ?_
  have hd := dense_fcoord b X hX v
  refine hd.induction_on (p := fun y => ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v)) y‖ ≤ C * ‖y‖) y ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro f
    have hn : ∀ (κ' : Type) [Fintype κ'] (u : κ' → ℂ), ‖(WithLp.toLp 2 u : EuclideanSpace ℂ κ')‖ = Formalism.HermitianLatticesTheory.cnorm u := by
      intro κ' _ u
      rw [EuclideanSpace.norm_eq]
      rfl
    have hm : Matrix.mulVec ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v) (Formalism.HermitianLatticesTheory.fcoord b X v f) =
        Formalism.HermitianLatticesTheory.fcoord b' X' v (φ f) := by
      simp only [Formalism.HermitianLatticesTheory.fcoord, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_right _ _ (hX v)]
      rw [vecAt_apply_linearMap b b' φ v f, Matrix.mulVec_mulVec]
    have h' := h f
    simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_toLp, Matrix.toLin'_apply, hm]
    first
      | exact h'
      | (rw [hn, hn]; exact h')

/- English proof (translation)
Establish `hS : (B (∑ g, y g) (∑ g, y g)).re = ∑ g, ∑ h, (B (y g) (y h)).re`. Simplify using `only [map_sum, AddMonoidHom.finset_sum_apply, Complex.re_sum]`. Use `first`. Consider the case `rfl`. Consider the case `exact Finset.sum_comm`.

Establish `hD : ∀ g h, (B (y g - y h) (y g - y h)).re = (B (y g) (y g)).re + (B (y h) (y h)).re - (B (y g) (y h)).re - (B (y h) (y g)).re`. Introduce `g h`. Simplify using `only [map_sub, AddMonoidHom.sub_apply, Complex.sub_re]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnn : 0 ≤ ∑ g, ∑ h, (B (y g - y h) (y g - y h)).re` using `Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun h _ => hpos _`.

Establish `expand : ∑ g, ∑ h, (B (y g - y h) (y g - y h)).re = ∑ g, ∑ h : Hb, (B (y g) (y g)).re + ∑ g : Hb, ∑ h, (B (y h) (y h)).re - ∑ g, ∑ h, (B (y g) (y h)).re - ∑ g, ∑ h, (B (y h) (y g)).re`. Simplify using `only [hD, Finset.sum_sub_distrib, Finset.sum_add_distrib]`. Establish `a1 : ∑ g, ∑ h : Hb, (B (y g) (y g)).re = (Fintype.card Hb : ℝ) * ∑ g, (B (y g) (y g)).re`. Rewrite using `[Finset.mul_sum]`. Simplify using the standard rewrite rules.

Establish `a2 : ∑ g : Hb, ∑ h, (B (y h) (y h)).re = (Fintype.card Hb : ℝ) * ∑ g, (B (y g) (y g)).re`. Simplify using the standard rewrite rules. Establish `a3 : ∑ g, ∑ h, (B (y h) (y g)).re = ∑ g, ∑ h, (B (y g) (y h)).re` using `Finset.sum_comm`. Rewrite `hnn` using `[expand, a1, a2, a3]`. Rewrite using `[hS]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sq_sum_le {C Hb : Type} [AddCommGroup C] [Fintype Hb] (B : C →+ C →+ ℂ)
    (hpos : ∀ x, 0 ≤ (B x x).re) (y : Hb → C) :
    (B (∑ g, y g) (∑ g, y g)).re ≤ (Fintype.card Hb : ℝ) * ∑ g, (B (y g) (y g)).re := by
  classical
  have hS : (B (∑ g, y g) (∑ g, y g)).re = ∑ g, ∑ h, (B (y g) (y h)).re := by
    simp only [map_sum, AddMonoidHom.finset_sum_apply, Complex.re_sum]
    first
      | rfl
      | exact Finset.sum_comm
  have hD : ∀ g h, (B (y g - y h) (y g - y h)).re =
      (B (y g) (y g)).re + (B (y h) (y h)).re - (B (y g) (y h)).re - (B (y h) (y g)).re := by
    intro g h
    simp only [map_sub, AddMonoidHom.sub_apply, Complex.sub_re]
    ring
  have hnn : 0 ≤ ∑ g, ∑ h, (B (y g - y h) (y g - y h)).re :=
    Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun h _ => hpos _
  have expand : ∑ g, ∑ h, (B (y g - y h) (y g - y h)).re =
      ∑ g, ∑ h : Hb, (B (y g) (y g)).re + ∑ g : Hb, ∑ h, (B (y h) (y h)).re -
        ∑ g, ∑ h, (B (y g) (y h)).re - ∑ g, ∑ h, (B (y h) (y g)).re := by
    simp only [hD, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have a1 : ∑ g, ∑ h : Hb, (B (y g) (y g)).re = (Fintype.card Hb : ℝ) * ∑ g, (B (y g) (y g)).re := by
    rw [Finset.mul_sum]
    simp
  have a2 : ∑ g : Hb, ∑ h, (B (y h) (y h)).re = (Fintype.card Hb : ℝ) * ∑ g, (B (y g) (y g)).re := by
    simp
  have a3 : ∑ g, ∑ h, (B (y h) (y g)).re = ∑ g, ∑ h, (B (y g) (y h)).re := Finset.sum_comm
  rw [expand, a1, a2, a3] at hnn
  rw [hS]
  linarith

end Formalism.L2.Geo.ExtensionFiltration
