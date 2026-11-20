import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CommonModel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `hU hB C R S W W' X X' _ _ _ _ _ _ _ _ _ _ _ a π mk mk' c c' j j' M M' w w' A s ha h1 hspanC hj hj' hMw hM'w hcw hc'w hex hspanS`. Take `⟨x, b, hb⟩` from `hB C W X a mk hspanC ha`. Use `set P0 : Matrix (Fin a) (Fin a) R := Matrix.of fun i k => c (x k) i with hP0`. Set `v : Fin a → Fin a → S` to `fun k i => π (c (x k) i)`. Establish `hspan : Submodule.span S (Set.range v) = ⊤`.

Rewrite using `[eq_top_iff, ← hspanS, Submodule.span_le]`. Introduce and unpack `_ ⟨y, rfl⟩`. Establish `e1 : (fun i => π (c y i)) = j (mk y)` using `funext fun i => (hj y i).symm`. Establish `e2` using `congrArg j (b.sum_repr (mk y))`. Use `show (fun i => π (c y i)) ∈ Submodule.span S (Set.range v)`.

Rewrite using `[e1, ← e2, map_sum]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hb k, ← algebraMap_smul S (b.repr (mk y) k)]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, ?_⟩)` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Conclude with `(hj (x k) i).symm`. Establish `hunit : IsUnit (π P0.det)`. Rewrite using `[RingHom.map_det]`. Conclude with `hU S a v hspan`. Use `set mb := LinearMap.toMatrix b b M with hmb`.

Establish `hM : ∀ k, M (b k) = ∑ l, mb l k • b l`. Introduce `k`. Simplify using `only [hmb, LinearMap.toMatrix_apply]`. Conclude with `(b.sum_repr _).symm`. Establish `hmat : A.map π * (P0.map s).map π = P0.map π * mb.map (algebraMap C S)`.

Use extensionality with `i k`. Establish `e1 : (A.map π * (P0.map s).map π) i k = π (c (w (x k)) i)`. Rewrite using `[hcw (x k)]`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, hP0]`. Establish `e2 : π (c (w (x k)) i) = (P0.map π * mb.map (algebraMap C S)) i k`.

Rewrite using `[← hj, ← hMw, ← hb k, hM k, map_sum, Finset.sum_apply, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Pi.smul_apply, Algebra.smul_def, hb l, hj, mul_comm (algebraMap C S _)]`. Simplify using `[hP0]`. Rewrite using `[e1, e2]`.

Establish `hdet : π A.det * π (s P0.det) = π P0.det * algebraMap C S mb.det`. Establish `e` using `congrArg Matrix.det hmat`. Simplify using `only [Matrix.det_mul] at e`. Simplify `e` using `only [RingHom.map_det, RingHom.mapMatrix_apply]`. Take `⟨x', hx'⟩` from `hex x`.

Take `⟨d, hd, -⟩` from `M'.existsUnique_eq_smul_id_of_finrank_eq_one h1`. Establish `hdM' : LinearMap.det M' = d`. Rewrite using `[hd, LinearMap.det_smul, LinearMap.det_id, h1, pow_one, mul_one]`. Establish `e3 : j' (M' (mk' x')) = algebraMap C S d * π P0.det`. Rewrite using `[hd, LinearMap.smul_apply, LinearMap.id_apply, map_smul, Algebra.smul_def, hj', hx']`.

Establish `e4 : j' (M' (mk' x')) = π A.det * π (s P0.det)`. Rewrite using `[hM'w, hj', hc'w, hx', map_mul]`. Establish `e5 : algebraMap C S d = algebraMap C S mb.det`. Establish `e6 : algebraMap C S d * π P0.det = algebraMap C S mb.det * π P0.det`. Rewrite using `[← e3, e4, hdet, mul_comm]`.

Conclude with `hunit.mul_left_injective e6`. Rewrite using `[hdM', ← LinearMap.det_toMatrix b M]`. Conclude with `(algebraMap C S).injective e5.symm`.
-/
theorem UpperTheory.Gal.crystallineComparison.detCore_of :
    UnitOfSpan → BasisIn → DetCore := by
  intro hU hB C R S W W' X X' _ _ _ _ _ _ _ _ _ _ _ a π mk mk' c c' j j' M M' w w' A s ha h1
    hspanC hj hj' hMw hM'w hcw hc'w hex hspanS
  obtain ⟨x, b, hb⟩ := hB C W X a mk hspanC ha
  set P0 : Matrix (Fin a) (Fin a) R := Matrix.of fun i k => c (x k) i with hP0
  let v : Fin a → Fin a → S := fun k i => π (c (x k) i)
  have hspan : Submodule.span S (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← hspanS, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    have e1 : (fun i => π (c y i)) = j (mk y) := funext fun i => (hj y i).symm
    have e2 := congrArg j (b.sum_repr (mk y))
    show (fun i => π (c y i)) ∈ Submodule.span S (Set.range v)
    rw [e1, ← e2, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smul, hb k, ← algebraMap_smul S (b.repr (mk y) k)]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, ?_⟩)
    funext i
    exact (hj (x k) i).symm
  have hunit : IsUnit (π P0.det) := by
    rw [RingHom.map_det]
    exact hU S a v hspan
  set mb := LinearMap.toMatrix b b M with hmb
  have hM : ∀ k, M (b k) = ∑ l, mb l k • b l := by
    intro k
    simp only [hmb, LinearMap.toMatrix_apply]
    exact (b.sum_repr _).symm
  have hmat : A.map π * (P0.map s).map π = P0.map π * mb.map (algebraMap C S) := by
    ext i k
    have e1 : (A.map π * (P0.map s).map π) i k = π (c (w (x k)) i) := by
      rw [hcw (x k)]
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, hP0]
    have e2 : π (c (w (x k)) i) = (P0.map π * mb.map (algebraMap C S)) i k := by
      rw [← hj, ← hMw, ← hb k, hM k, map_sum, Finset.sum_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, Pi.smul_apply, Algebra.smul_def, hb l, hj, mul_comm (algebraMap C S _)]
      simp [hP0]
    rw [e1, e2]
  have hdet : π A.det * π (s P0.det) = π P0.det * algebraMap C S mb.det := by
    have e := congrArg Matrix.det hmat
    simp only [Matrix.det_mul] at e
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply] using e
  obtain ⟨x', hx'⟩ := hex x
  obtain ⟨d, hd, -⟩ := M'.existsUnique_eq_smul_id_of_finrank_eq_one h1
  have hdM' : LinearMap.det M' = d := by
    rw [hd, LinearMap.det_smul, LinearMap.det_id, h1, pow_one, mul_one]
  have e3 : j' (M' (mk' x')) = algebraMap C S d * π P0.det := by
    rw [hd, LinearMap.smul_apply, LinearMap.id_apply, map_smul, Algebra.smul_def, hj', hx']
  have e4 : j' (M' (mk' x')) = π A.det * π (s P0.det) := by
    rw [hM'w, hj', hc'w, hx', map_mul]
  have e5 : algebraMap C S d = algebraMap C S mb.det := by
    have e6 : algebraMap C S d * π P0.det = algebraMap C S mb.det * π P0.det := by
      rw [← e3, e4, hdet, mul_comm]
    exact hunit.mul_left_injective e6
  rw [hdM', ← LinearMap.det_toMatrix b M]
  exact (algebraMap C S).injective e5.symm
