import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.InvoluteFfMapsTo
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Establish `e : Matrix.det (1 - A) = Matrix.detRowAlternating ((fun i => (-A) i) + (fun i => (1 : Matrix ι ι ℂ) i))`. Use `congrArg Matrix.detRowAlternating ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i j`. Simplify using `[sub_eq_neg_add]`. Rewrite using `[e, AlternatingMap.map_add_univ]`.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Use `(Matrix.det_piecewise_one_eq_submatrix_det (-A) s).trans ?_` and prove the remaining obligations. Establish `hn : (-A).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) = -(A.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι))`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Rewrite using `[hn, Matrix.det_neg, Fintype.card_coe]`.
-/
theorem det_one_sub_eq_sum_minors {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    (1 - A).det =
      ∑ s : Finset ι, (-1 : ℂ) ^ s.card * (A.submatrix (Subtype.val : s → ι) Subtype.val).det := by
  have e : Matrix.det (1 - A) =
      Matrix.detRowAlternating ((fun i => (-A) i) + (fun i => (1 : Matrix ι ι ℂ) i)) := by
    refine congrArg Matrix.detRowAlternating ?_
    funext i j
    simp [sub_eq_neg_add]
  rw [e, AlternatingMap.map_add_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  refine (Matrix.det_piecewise_one_eq_submatrix_det (-A) s).trans ?_
  have hn : (-A).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) =
      -(A.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)) := by
    ext i j
    simp
  rw [hn, Matrix.det_neg, Fintype.card_coe]

/- English proof (translation)
Establish `h1 : (fockBasis n).repr (ExteriorAlgebra.ιMulti ℂ S.card v) S = (((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv).exteriorPower S.card).repr (exteriorPower.ιMulti ℂ S.card v) (Set.powersetCard.ofCard (rfl : S.card = S.card))`. Rewrite using `[fockBasis, Module.Basis.ExteriorAlgebra, Module.Basis.repr_reindex_apply, Set.powersetCard.prodEquiv_symm_apply]`. Conclude with `DirectSum.IsInternal.collectedBasis_repr_of_mem _ _ (exteriorPower.ιMulti ℂ S.card v).2`. Rewrite using `[h1, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]`. Use `congr 1`.
-/
theorem fock_repr_ιMulti (S : Finset (Fin (n * n))) (v : Fin S.card → (Fin n × Fin n → ℂ)) :
    (fockBasis n).repr (ExteriorAlgebra.ιMulti ℂ S.card v) S =
      (Matrix.of fun i j => v i (finProdFinEquiv.symm (S.orderEmbOfFin rfl j))).det := by
  have h1 : (fockBasis n).repr (ExteriorAlgebra.ιMulti ℂ S.card v) S =
      (((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv).exteriorPower S.card).repr
        (exteriorPower.ιMulti ℂ S.card v) (Set.powersetCard.ofCard (rfl : S.card = S.card)) := by
    rw [fockBasis, Module.Basis.ExteriorAlgebra, Module.Basis.repr_reindex_apply,
      Set.powersetCard.prodEquiv_symm_apply]
    exact DirectSum.IsInternal.collectedBasis_repr_of_mem _ _ (exteriorPower.ιMulti ℂ S.card v).2
  rw [h1, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1

/- English proof (translation)
Rewrite using `[ffMat, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, fockBasis_eq, ff, ExteriorAlgebra.map_apply_ιMulti, fock_repr_ιMulti, ← Matrix.det_transpose]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[adPhys, Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem ffMat_diag_det (k : Matrix (Fin n) (Fin n) ℂ) (S : Finset (Fin (n * n))) :
    ffMat ε k S S = (Matrix.of fun i j : Fin S.card =>
      adMat ε k (finProdFinEquiv.symm (S.orderEmbOfFin rfl i))
        (finProdFinEquiv.symm (S.orderEmbOfFin rfl j))).det := by
  rw [ffMat, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, fockBasis_eq, ff,
    ExteriorAlgebra.map_apply_ιMulti, fock_repr_ιMulti, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [adPhys, Matrix.mulVec, dotProduct, Pi.single_apply]

def physEmb (ε : Fin n → Bool) : {x : Fin n × Fin n // IsPhys ε x} ↪ Fin (n * n) :=
  ⟨fun x => finProdFinEquiv x.1, fun _ _ h => Subtype.ext (finProdFinEquiv.injective h)⟩

/- English proof (translation)
Use `set S := s.map (physEmb ε) with hS`. Rewrite using `[ffMat_diag_det]`. Establish `hmem : ∀ i, ∃ x ∈ s, physEmb ε x = S.orderEmbOfFin rfl i` using `fun i => Finset.mem_map.1 (S.orderEmbOfFin_mem rfl i)`. Set `e : Fin S.card → s` to `fun i => ⟨(hmem i).choose, (hmem i).choose_spec.1⟩`. Establish `he : ∀ i, (((e i : {x : Fin n × Fin n // IsPhys ε x}) : Fin n × Fin n)) = finProdFinEquiv.symm (S.orderEmbOfFin rfl i)`.

Introduce `i`. Rewrite using `[← (hmem i).choose_spec.2]`. Conclude with `(finProdFinEquiv.symm_apply_apply _).symm`. Establish `hp : ∀ i, IsPhys ε (finProdFinEquiv.symm (S.orderEmbOfFin rfl i))` using `fun i => he i ▸ (e i : {x : Fin n × Fin n // IsPhys ε x}).2`. Establish `hinj : Function.Injective e`.

Introduce `i j hij`. Establish `h1` using `he i`. Rewrite `h1` using `[hij, he j]`. Conclude with `(S.orderEmbOfFin rfl).injective (finProdFinEquiv.symm.injective h1.symm)`. Establish `hcard : Fintype.card (Fin S.card) = Fintype.card s` using `by simp [S]`.

Rewrite using `[← Matrix.det_submatrix_equiv_self (Equiv.ofBijective e ((Fintype.bijective_iff_injective_and_card e).2 ⟨hinj, hcard⟩))]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.of_apply, Equiv.ofBijective_apply]`. Rewrite using `[he i, he j]`.

Simplify using `only [adMat, if_pos (hp i), if_pos (hp j)]`.
-/
theorem ffMat_map_physEmb (k : Matrix (Fin n) (Fin n) ℂ) (s : Finset {x : Fin n × Fin n // IsPhys ε x}) :
    ffMat ε k (s.map (physEmb ε)) (s.map (physEmb ε)) =
      ((Matrix.of fun x y : {x : Fin n × Fin n // IsPhys ε x} => k x.1.1 y.1.1 * star (k x.1.2 y.1.2)).submatrix
        (Subtype.val : s → _) Subtype.val).det := by
  classical
  set S := s.map (physEmb ε) with hS
  rw [ffMat_diag_det]
  have hmem : ∀ i, ∃ x ∈ s, physEmb ε x = S.orderEmbOfFin rfl i :=
    fun i => Finset.mem_map.1 (S.orderEmbOfFin_mem rfl i)
  let e : Fin S.card → s := fun i => ⟨(hmem i).choose, (hmem i).choose_spec.1⟩
  have he : ∀ i, (((e i : {x : Fin n × Fin n // IsPhys ε x}) : Fin n × Fin n)) =
      finProdFinEquiv.symm (S.orderEmbOfFin rfl i) := by
    intro i
    rw [← (hmem i).choose_spec.2]
    exact (finProdFinEquiv.symm_apply_apply _).symm
  have hp : ∀ i, IsPhys ε (finProdFinEquiv.symm (S.orderEmbOfFin rfl i)) :=
    fun i => he i ▸ (e i : {x : Fin n × Fin n // IsPhys ε x}).2
  have hinj : Function.Injective e := by
    intro i j hij
    have h1 := he i
    rw [hij, he j] at h1
    exact (S.orderEmbOfFin rfl).injective (finProdFinEquiv.symm.injective h1.symm)
  have hcard : Fintype.card (Fin S.card) = Fintype.card s := by simp [S]
  rw [← Matrix.det_submatrix_equiv_self
    (Equiv.ofBijective e ((Fintype.bijective_iff_injective_and_card e).2 ⟨hinj, hcard⟩))]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Equiv.ofBijective_apply]
  rw [he i, he j]
  simp only [adMat, if_pos (hp i), if_pos (hp j)]

/- English proof (translation)
Establish `h1 : physDet ε k = (1 - Matrix.of fun x y : {x : Fin n × Fin n // IsPhys ε x} => k x.1.1 y.1.1 * star (k x.1.2 y.1.2)).det`. Rewrite using `[physDet]`. Use `congr 1`. Rewrite using `[h1, det_one_sub_eq_sum_minors, strPhys]`. Use `symm`.

Use `Finset.sum_bij (fun s _ => s.map (physEmb ε)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `s _`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, IsPhysSet]`. Introduce `m hm`. Take `⟨x, _, rfl⟩` from `Finset.mem_map.1 hm`.

Use `show IsPhys ε (finProdFinEquiv.symm (finProdFinEquiv x.1))`. Rewrite using `[Equiv.symm_apply_apply]`. Conclude with `x.2`. Introduce `s _ t _ h`. Conclude with `Finset.map_injective _ h`.

Introduce `S hS`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hS`. Use `⟨Finset.univ.filter (fun x => physEmb ε x ∈ S), Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use extensionality with `m`. Simplify using `only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `hx`. Introduce `hm`. Use `⟨⟨finProdFinEquiv.symm m, hS m hm⟩, ?_, finProdFinEquiv.apply_symm_apply m⟩` and prove the remaining obligations.

Use `show finProdFinEquiv (finProdFinEquiv.symm m) ∈ S`. Rewrite using `[Equiv.apply_symm_apply]`. Conclude with `hm`. Introduce `s _`. Rewrite using `[ffMat_map_physEmb, Finset.card_map]`.
-/
theorem strPhys_eq_physDet (k : Matrix (Fin n) (Fin n) ℂ) : strPhys ε k = physDet ε k := by
  classical
  have h1 : physDet ε k = (1 - Matrix.of fun x y : {x : Fin n × Fin n // IsPhys ε x} =>
      k x.1.1 y.1.1 * star (k x.1.2 y.1.2)).det := by
    rw [physDet]
    congr 1
  rw [h1, det_one_sub_eq_sum_minors, strPhys]
  symm
  refine Finset.sum_bij (fun s _ => s.map (physEmb ε)) ?_ ?_ ?_ ?_
  · intro s _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsPhysSet]
    intro m hm
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.1 hm
    show IsPhys ε (finProdFinEquiv.symm (finProdFinEquiv x.1))
    rw [Equiv.symm_apply_apply]
    exact x.2
  · intro s _ t _ h
    exact Finset.map_injective _ h
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    refine ⟨Finset.univ.filter (fun x => physEmb ε x ∈ S), Finset.mem_univ _, ?_⟩
    ext m
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hm
      refine ⟨⟨finProdFinEquiv.symm m, hS m hm⟩, ?_, finProdFinEquiv.apply_symm_apply m⟩
      show finProdFinEquiv (finProdFinEquiv.symm m) ∈ S
      rw [Equiv.apply_symm_apply]
      exact hm
  · intro s _
    rw [ffMat_map_physEmb, Finset.card_map]

end ReciprocityTheory.ChartRestriction.DS.TRGap
