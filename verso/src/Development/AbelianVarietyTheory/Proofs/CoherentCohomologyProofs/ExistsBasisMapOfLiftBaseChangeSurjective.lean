import Mathlib

open Module Function
open scoped TensorProduct Pointwise

namespace GlobalTheory

namespace Avoid

section Union

end Union

section Pick

open Module Function in
open scoped TensorProduct Pointwise in

/- English proof (translation)
Establish `hspanT : Submodule.span L (Set.range fun i => (1 : L) ⊗ₜ[K] v i) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `t -`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact zero_mem _`.

Consider the case `tmul l y`. Establish `hy : y ∈ Submodule.span K (Set.range v)` using `hv ▸ Submodule.mem_top`. Establish `h1 : TensorProduct.mk K L V 1 y ∈ Submodule.span K (TensorProduct.mk K L V 1 '' Set.range v)` using `Submodule.apply_mem_span_image_of_mem_span _ hy`. Establish `h2` using `Submodule.span_le_restrictScalars K L _ h1`. Rewrite `h2` using `[← Set.range_comp]`.

Establish `h3 : l ⊗ₜ[K] y = l • ((1 : L) ⊗ₜ[K] y)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[h3]`. Conclude with `Submodule.smul_mem _ l h2`. Consider the case `add a b ha hb => exact add_mem ha hb`.

Establish `hw : Submodule.span L (Set.range fun i => G ((1 : L) ⊗ₜ[K] v i)) = ⊤`. Establish `h : (Set.range fun i => G ((1 : L) ⊗ₜ[K] v i)) = G '' Set.range fun i => (1 : L) ⊗ₜ[K] v i`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[h, Submodule.span_image, hspanT, Submodule.map_top, LinearMap.range_eq_top.mpr hG]`.

Take `⟨κ, a, ha, hspan, hli⟩` from `exists_linearIndependent' L fun i => G ((1 : L) ⊗ₜ[K] v i)`. Set `b` to `Basis.mk hli (hspan.trans hw).ge`. Use `haveI : Finite κ := Module.Finite.finite_basis b`. Use `haveI := Fintype.ofFinite κ`. Establish `hcard : Fintype.card κ = d` using `by rw [← hd, Module.finrank_eq_card_basis b]`.

Set `e : Fin d ≃ κ` to `(Fintype.equivFinOfCardEq hcard).symm`. Use `⟨a ∘ e, b.reindex e.symm, ha.comp e.injective, fun k => ?_⟩` and prove the remaining obligations. Simplify using `[b, Basis.mk_apply]`.
-/
theorem _root_.GlobalTheory.Avoid.exists_basis_map_one_tmul_of_surjective {K L V W ι : Type*} [CommRing K] [Field L]
    [Algebra K L] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]
    [Module.Finite L W] {d : ℕ} (hd : finrank L W = d) (G : L ⊗[K] V →ₗ[L] W)
    (hG : Surjective G) (v : ι → V) (hv : Submodule.span K (Set.range v) = ⊤) :
    ∃ (σ : Fin d → ι) (b : Basis (Fin d) L W), Injective σ ∧ ∀ k, b k = G (1 ⊗ₜ v (σ k)) := by
  classical
  have hspanT : Submodule.span L (Set.range fun i => (1 : L) ⊗ₜ[K] v i) = ⊤ := by
    rw [eq_top_iff]
    rintro t -
    induction t using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul l y =>
      have hy : y ∈ Submodule.span K (Set.range v) := hv ▸ Submodule.mem_top
      have h1 : TensorProduct.mk K L V 1 y ∈
          Submodule.span K (TensorProduct.mk K L V 1 '' Set.range v) :=
        Submodule.apply_mem_span_image_of_mem_span _ hy
      have h2 := Submodule.span_le_restrictScalars K L _ h1
      rw [← Set.range_comp] at h2
      have h3 : l ⊗ₜ[K] y = l • ((1 : L) ⊗ₜ[K] y) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h3]
      exact Submodule.smul_mem _ l h2
    | add a b ha hb => exact add_mem ha hb
  have hw : Submodule.span L (Set.range fun i => G ((1 : L) ⊗ₜ[K] v i)) = ⊤ := by
    have h : (Set.range fun i => G ((1 : L) ⊗ₜ[K] v i)) =
        G '' Set.range fun i => (1 : L) ⊗ₜ[K] v i := by
      rw [← Set.range_comp]; rfl
    rw [h, Submodule.span_image, hspanT, Submodule.map_top, LinearMap.range_eq_top.mpr hG]
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' L fun i => G ((1 : L) ⊗ₜ[K] v i)
  let b := Basis.mk hli (hspan.trans hw).ge
  haveI : Finite κ := Module.Finite.finite_basis b
  haveI := Fintype.ofFinite κ
  have hcard : Fintype.card κ = d := by rw [← hd, Module.finrank_eq_card_basis b]
  let e : Fin d ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, b.reindex e.symm, ha.comp e.injective, fun k => ?_⟩
  simp [b, Basis.mk_apply]

end Pick

section Minor

open exteriorPower

/- English proof (translation)
Establish `: pairingDual R M r (ιMulti R r fun k => f k ∘ₗ φ) = pairingDual R N r (ιMulti R r f) ∘ₗ exteriorPower.map r φ`. Apply `exteriorPower.linearMap_ext` to reduce the goal to its premises. Use extensionality with `v`. Simplify using `[pairingDual_ιMulti_ιMulti]`. Rewrite using `[this, LinearMap.comp_apply]`.
-/
theorem pairingDual_ιMulti_comp {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {r : ℕ} (φ : M →ₗ[R] N) (f : Fin r → Dual R N)
    (x : ⋀[R]^r M) :
    pairingDual R M r (ιMulti R r fun k => f k ∘ₗ φ) x =
      pairingDual R N r (ιMulti R r f) (exteriorPower.map r φ x) := by
  have : pairingDual R M r (ιMulti R r fun k => f k ∘ₗ φ) =
      pairingDual R N r (ιMulti R r f) ∘ₗ exteriorPower.map r φ := by
    apply exteriorPower.linearMap_ext
    ext v
    simp [pairingDual_ιMulti_ιMulti]
  rw [this, LinearMap.comp_apply]

/- English proof (translation)
Set `φ : V →ₗ[K] (ι → K)` to `LinearMap.pi c`. Establish `hφ : Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `v hv`. Conclude with `hc v fun j => congrFun hv j`.

Establish `hinj : Injective (exteriorPower.map r φ)` using `map_injective_field hφ`. Use `by_contra! h`. Apply `hx` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Apply `((Pi.basisFun K ι).exteriorPower r).repr.injective` to reduce the goal to its premises. Use extensionality with `J`. Rewrite using `[basis_repr_apply, ιMultiDual, ιMulti_family, ← pairingDual_ιMulti_comp, map_zero, Finsupp.zero_apply, ← h J, ιMulti_family]`. Use `congr 3`.
-/
theorem exists_minor_ne_zero_of_separating {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Finite ι] [LinearOrder ι] (c : ι → Dual K V)
    (hc : ∀ v : V, (∀ j, c j v = 0) → v = 0) {r : ℕ} (x : ⋀[K]^r V) (hx : x ≠ 0) :
    ∃ J : Set.powersetCard ι r, pairingDual K V r (ιMulti_family K r c J) x ≠ 0 := by
  let φ : V →ₗ[K] (ι → K) := LinearMap.pi c
  have hφ : Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact hc v fun j => congrFun hv j
  have hinj : Injective (exteriorPower.map r φ) := map_injective_field hφ
  by_contra! h
  apply hx
  apply hinj
  rw [map_zero]
  apply ((Pi.basisFun K ι).exteriorPower r).repr.injective
  ext J
  rw [basis_repr_apply, ιMultiDual, ιMulti_family, ← pairingDual_ιMulti_comp, map_zero,
    Finsupp.zero_apply, ← h J, ιMulti_family]
  congr 3

/- English proof (translation)
Use `exists_minor_ne_zero_of_separating c (fun v hv => ?_) x hx` and prove the remaining obligations. Rewrite using `[← forall_dual_apply_eq_zero_iff K v]`. Establish `: Dual.eval K V v = 0`. Apply `LinearMap.ext_on_range hc` to reduce the goal to its premises. Simplify using `using hv`.

Introduce `f`. Simplify using `using DFunLike.congr_fun this f`.
-/
theorem exists_minor_ne_zero_of_span {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Finite ι] [LinearOrder ι] (c : ι → Dual K V)
    (hc : Submodule.span K (Set.range c) = ⊤) {r : ℕ} (x : ⋀[K]^r V) (hx : x ≠ 0) :
    ∃ J : Set.powersetCard ι r, pairingDual K V r (ιMulti_family K r c J) x ≠ 0 := by
  refine exists_minor_ne_zero_of_separating c (fun v hv => ?_) x hx
  rw [← forall_dual_apply_eq_zero_iff K v]
  have : Dual.eval K V v = 0 := by
    apply LinearMap.ext_on_range hc
    simpa using hv
  intro f
  simpa using DFunLike.congr_fun this f

/- English proof (translation)
The claim follows from `exists_minor_ne_zero_of_span c c.span_eq x hx`.
-/
theorem exists_minor_ne_zero {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Finite ι] [LinearOrder ι] (c : Basis ι K (Dual K V))
    {r : ℕ} (x : ⋀[K]^r V) (hx : x ≠ 0) :
    ∃ J : Set.powersetCard ι r, pairingDual K V r (ιMulti_family K r c J) x ≠ 0 :=
  exists_minor_ne_zero_of_span c c.span_eq x hx

open Module Function in
open scoped TensorProduct Pointwise in
open exteriorPower in

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hall : ∀ φ : ⋀[K]^r (Dual K V), pairingDual K V r φ x = 0`. Introduce `φ`. Establish `hφ : φ ∈ Submodule.span K (Set.range (ιMulti_family K r c))`.

Rewrite using `[ιMulti_family_span_of_span K hc]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨s, rfl⟩` from `hy`.

Conclude with `hne (Set.powersetCard.ofFinEmbEquiv.symm s)`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => simp [hy, hz]`. Consider the case `smul t y _ hy => simp [hy]`. Set `b` to `Basis.ofVectorSpace K V`.

Use `letI : LinearOrder (Basis.ofVectorSpaceIndex K V) := IsWellOrder.linearOrder WellOrderingRel`. Set `B` to `b.exteriorPower r`. Establish `hcoord : ∀ s, B.coord s = ιMultiDual K r b s` using `fun s => B.ext fun t => by`. Establish `hBt : B t = ιMulti_family K r b t` using `by simp [B, Module.Basis.exteriorPower]`. Rewrite using `[Basis.coord_apply, B.repr_self, hBt]`.

Distinguish the cases in `hst : s = t`. Substitute `hst` using the available equality. Rewrite using `[ιMultiDual_apply_diag, Finsupp.single_eq_same]`. Rewrite using `[ιMultiDual_apply_nondiag K r b s t hst, Finsupp.single_eq_of_ne hst]`. Apply `hx` to reduce the goal to its premises.

Use `B.ext_elem fun s => ?_` and prove the remaining obligations. Rewrite using `[map_zero, Finsupp.zero_apply, ← B.coord_apply, hcoord]`. Conclude with `hall _`.
-/
theorem _root_.GlobalTheory.Avoid.exists_orderEmbedding_minor_ne_zero {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Finite ι] [LinearOrder ι] (c : ι → Dual K V)
    (hc : Submodule.span K (Set.range c) = ⊤) {r : ℕ} (x : ⋀[K]^r V) (hx : x ≠ 0) :
    ∃ J : Fin r ↪o ι, pairingDual K V r (ιMulti K r fun k => c (J k)) x ≠ 0 := by
  classical
  by_contra hne
  push_neg at hne
  have hall : ∀ φ : ⋀[K]^r (Dual K V), pairingDual K V r φ x = 0 := by
    intro φ
    have hφ : φ ∈ Submodule.span K (Set.range (ιMulti_family K r c)) := by
      rw [ιMulti_family_span_of_span K hc]; exact Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨s, rfl⟩ := hy
      exact hne (Set.powersetCard.ofFinEmbEquiv.symm s)
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul t y _ hy => simp [hy]
  let b := Basis.ofVectorSpace K V
  letI : LinearOrder (Basis.ofVectorSpaceIndex K V) := IsWellOrder.linearOrder WellOrderingRel
  let B := b.exteriorPower r
  have hcoord : ∀ s, B.coord s = ιMultiDual K r b s := fun s => B.ext fun t => by
    have hBt : B t = ιMulti_family K r b t := by simp [B, Module.Basis.exteriorPower]
    rw [Basis.coord_apply, B.repr_self, hBt]
    by_cases hst : s = t
    · subst hst
      rw [ιMultiDual_apply_diag, Finsupp.single_eq_same]
    · rw [ιMultiDual_apply_nondiag K r b s t hst, Finsupp.single_eq_of_ne hst]
  apply hx
  refine B.ext_elem fun s => ?_
  rw [map_zero, Finsupp.zero_apply, ← B.coord_apply, hcoord]
  exact hall _

/- English proof (translation)
Simplify using `[ιMulti_family, pairingDual_ιMulti_ιMulti]`.
-/
theorem minor_ιMulti {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V] [LinearOrder ι]
    (c : ι → Dual R V) {r : ℕ} (J : Set.powersetCard ι r) (v : Fin r → V) :
    pairingDual R V r (ιMulti_family R r c J) (ιMulti R r v) =
      (Matrix.of fun i j => c (Set.powersetCard.ofFinEmbEquiv.symm J j) (v i)).det := by
  simp [ιMulti_family, pairingDual_ιMulti_ιMulti]

end Minor

end Avoid

universe u v w x y

end GlobalTheory
