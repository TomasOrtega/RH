import Mathlib
open Polynomial
namespace GlobalTheory

/- English proof (translation)
Establish `hd : (Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) F) 0 0 (0 : Matrix (Fin b) (Fin b) F)) = Matrix.diagonal (Sum.elim (fun _ => (1 : F)) (fun _ => 0))`. Rewrite using `[← Matrix.fromBlocks_diagonal]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.rank_submatrix, hd, Matrix.rank_diagonal]`. Simplify using `[Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]`.
-/
private lemma rank_submatrix_fromBlocks_one_zero_eq {F : Type} [Field F] {m : Type} [Fintype m] [DecidableEq m]
    (a b : ℕ) (e : m ≃ Fin a ⊕ Fin b) :
    ((Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) F) 0 0 (0 : Matrix (Fin b) (Fin b) F)).submatrix
      e e).rank = a := by
  classical
  have hd : (Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) F) 0 0 (0 : Matrix (Fin b) (Fin b) F)) =
      Matrix.diagonal (Sum.elim (fun _ => (1 : F)) (fun _ => 0)) := by
    rw [← Matrix.fromBlocks_diagonal]
    simp
  rw [Matrix.rank_submatrix, hd, Matrix.rank_diagonal]
  simp [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]

open Matrix in

/- English proof (translation)
Take `⟨V, U, e, hV, hU, h⟩` from `Matrix.exists_rank_normal_form M`. Establish `hVd : IsUnit (V.map φ).det`. Rewrite using `[show (V.map φ).det = φ V.det from (RingHom.map_det φ V).symm]`. Conclude with `((Matrix.isUnit_iff_isUnit_det V).mp hV).map φ`. Establish `hUd : IsUnit (U.map φ).det`.

Rewrite using `[show (U.map φ).det = φ U.det from (RingHom.map_det φ U).symm]`. Conclude with `((Matrix.isUnit_iff_isUnit_det U).mp hU).map φ`. Establish `h' : V.map φ * M.map φ * U.map φ = (Matrix.fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) L) 0 0 (0 : Matrix (Fin (Fintype.card n - M.rank)) (Fin (Fintype.card n - M.rank)) L)).submatrix e e`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, h]`. Simplify using `[← Matrix.submatrix_map, Matrix.fromBlocks_map]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[rank_mul_eq_left_of_isUnit_det _ _ hUd, rank_mul_eq_right_of_isUnit_det _ _ hVd]`. Use `_ = M.rank := by rw [h']; exact rank_submatrix_fromBlocks_one_zero_eq _ _ e`.
-/
theorem eigDim_rank_map {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) : (M.map φ).rank = M.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, h⟩ := Matrix.exists_rank_normal_form M
  have hVd : IsUnit (V.map φ).det := by
    rw [show (V.map φ).det = φ V.det from (RingHom.map_det φ V).symm]
    exact ((Matrix.isUnit_iff_isUnit_det V).mp hV).map φ
  have hUd : IsUnit (U.map φ).det := by
    rw [show (U.map φ).det = φ U.det from (RingHom.map_det φ U).symm]
    exact ((Matrix.isUnit_iff_isUnit_det U).mp hU).map φ
  have h' : V.map φ * M.map φ * U.map φ =
      (Matrix.fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) L) 0 0
        (0 : Matrix (Fin (Fintype.card n - M.rank)) (Fin (Fintype.card n - M.rank)) L)).submatrix
          e e := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, h]
    simp [← Matrix.submatrix_map, Matrix.fromBlocks_map]
  calc (M.map φ).rank = (V.map φ * M.map φ * U.map φ).rank := by
        rw [rank_mul_eq_left_of_isUnit_det _ _ hUd, rank_mul_eq_right_of_isUnit_det _ _ hVd]
    _ = M.rank := by rw [h']; exact rank_submatrix_fromBlocks_one_zero_eq _ _ e

/- English proof (translation)
Establish `h` using `LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)`. Rewrite `h`, the goal using `[Matrix.toLin'_apply']`. Rewrite `h` using `[Module.finrank_pi]`. Unfold `Matrix.rank`. Use linear arithmetic over natural numbers and integers.
-/
private lemma finrank_ker_toLin'_add_rank_eq_card {L : Type} [Field L] {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n L) :
    Module.finrank L (LinearMap.ker (Matrix.toLin' A)) + A.rank = Fintype.card n := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
  rw [Matrix.toLin'_apply'] at h ⊢
  rw [Module.finrank_pi] at h
  unfold Matrix.rank
  omega

/- English proof (translation)
Establish `h1` using `finrank_ker_toLin'_add_rank_eq_card (M.map φ)`. Establish `h2` using `finrank_ker_toLin'_add_rank_eq_card M`. Rewrite `h1` using `[eigDim_rank_map]`. Use linear arithmetic over natural numbers and integers.
-/
theorem eigDim_ker_map {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) :
    Module.finrank L (LinearMap.ker (Matrix.toLin' (M.map φ))) =
      Module.finrank K (LinearMap.ker (Matrix.toLin' M)) := by
  have h1 := finrank_ker_toLin'_add_rank_eq_card (M.map φ)
  have h2 := finrank_ker_toLin'_add_rank_eq_card M
  rw [eigDim_rank_map] at h1
  omega

/- English proof (translation)
The claim follows from `Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix n n K ≃ₐ[K] _) M f`.
-/
theorem eigDim_aeval_toLin' {K : Type} [Field K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (f : K[X]) :
    aeval (Matrix.toLin' M) f = Matrix.toLin' (aeval M f) :=
  Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix n n K ≃ₐ[K] _) M f

/- English proof (translation)
Establish `h : (φ.mapMatrix : Matrix n n K →+* Matrix n n L).comp (algebraMap K (Matrix n n K)) = (algebraMap L (Matrix n n L)).comp φ`. Use extensionality with `r i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]`. Express the relevant statement in the definitionally equal form `φ.mapMatrix (Polynomial.eval₂ (algebraMap K (Matrix n n K)) M f) = Polynomial.eval₂ (algebraMap L (Matrix n n L)) (M.map φ) (f.map φ)`. Rewrite using `[Polynomial.hom_eval₂, Polynomial.eval₂_map, h]`.

Both sides reduce to the same expression.
-/
theorem eigDim_aeval_map {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (f : K[X]) :
    (aeval M f).map φ = aeval (M.map φ) (f.map φ) := by
  have h : (φ.mapMatrix : Matrix n n K →+* Matrix n n L).comp (algebraMap K (Matrix n n K)) =
      (algebraMap L (Matrix n n L)).comp φ := by
    ext r i j
    by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
  change φ.mapMatrix (Polynomial.eval₂ (algebraMap K (Matrix n n K)) M f) =
    Polynomial.eval₂ (algebraMap L (Matrix n n L)) (M.map φ) (f.map φ)
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map, h]
  rfl

/- English proof (translation)
Rewrite using `[eigDim_aeval_toLin', eigDim_aeval_toLin', ← eigDim_aeval_map, eigDim_ker_map]`.
-/
theorem eigDim_ker_aeval_map {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n K) (f : K[X]) :
    Module.finrank L (LinearMap.ker (aeval (Matrix.toLin' (M.map φ)) (f.map φ))) =
      Module.finrank K (LinearMap.ker (aeval (Matrix.toLin' M) f)) := by
  rw [eigDim_aeval_toLin', eigDim_aeval_toLin', ← eigDim_aeval_map, eigDim_ker_map]

/- English proof (translation)
Rewrite using `[← Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime T h]`. Establish `hd` using `Polynomial.disjoint_ker_aeval_of_isCoprime T h`. Establish `hs` using `Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (aeval T p)) (LinearMap.ker (aeval T q))`. Rewrite `hs` using `[hd.eq_bot]`. Simplify using `using hs`.
-/
theorem eigDim_ker_mul {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {p q : K[X]} (h : IsCoprime p q) :
    Module.finrank K (LinearMap.ker (aeval T (p * q))) =
      Module.finrank K (LinearMap.ker (aeval T p)) +
        Module.finrank K (LinearMap.ker (aeval T q)) := by
  rw [← Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime T h]
  have hd := Polynomial.disjoint_ker_aeval_of_isCoprime T h
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (aeval T p))
    (LinearMap.ker (aeval T q))
  rw [hd.eq_bot] at hs
  simpa using hs

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_empty, map_one, Module.End.one_eq_id, LinearMap.ker_id]`. Simplify using the standard rewrite rules. Introduce `a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, eigDim_ker_mul T, ih]`.

Use `IsCoprime.prod_right fun z hz => ?_` and prove the remaining obligations. Use `Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr ?_).isUnit` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `ha hz`.
-/
theorem eigDim_ker_prod {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (s : Finset K) :
    Module.finrank K (LinearMap.ker (aeval T (∏ z ∈ s, (X - C z)))) =
      ∑ z ∈ s, Module.finrank K (LinearMap.ker (aeval T (X - C z))) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, map_one, Module.End.one_eq_id, LinearMap.ker_id]
    simp
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, eigDim_ker_mul T, ih]
    refine IsCoprime.prod_right fun z hz => ?_
    refine Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr ?_).isUnit
    rintro rfl
    exact ha hz

/- English proof (translation)
Introduce `F _ _ ι _ _ M f y hf hy`. Rewrite using `[← eigDim_ker_aeval_map (algebraMap F (AlgebraicClosure F)) M f]`. Use `set g := f.map (algebraMap F (AlgebraicClosure F)) with hg`. Use `set T := Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F))) with hT`. Establish `hsep : g.Separable` using `(PerfectField.separable_of_irreducible hf).map`.

Establish `hne : g ≠ 0` using `Polynomial.map_ne_zero hf.ne_zero`. Establish `hnd` using `Polynomial.nodup_roots hsep`. Establish `hcard : Multiset.card g.roots = g.natDegree` using `(IsAlgClosed.splits g).natDegree_eq_card_roots.symm`. Establish `hfac` using `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard`. Establish `hprod : (g.roots.map fun a => X - C a).prod = ∏ a ∈ g.roots.toFinset, (X - C a)`.

Rewrite using `[Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]`. Establish `hlc : g.leadingCoeff ≠ 0` using `Polynomial.leadingCoeff_ne_zero.mpr hne`. Establish `hker : aeval T g = g.leadingCoeff • aeval T (∏ a ∈ g.roots.toFinset, (X - C a))` using `by conv_lhs => rw [← hfac, hprod]`. Rewrite using `[map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]`. Establish `hterm : ∀ a ∈ g.roots.toFinset, Module.finrank (AlgebraicClosure F) (LinearMap.ker (aeval T (X - C a))) = Module.finrank (AlgebraicClosure F) (Module.End.eigenspace T y)`.

Introduce `a ha`. Establish `haroot : aeval a f = 0`. Establish `h0` using `Polynomial.IsRoot.eq_zero ((Polynomial.mem_roots hne).mp (Multiset.mem_toFinset.mp ha))`. Rewrite `h0` using `[hg, Polynomial.eval_map_algebraMap]`. Then use the resulting hypothesis. Establish `hmin : minpoly F a = minpoly F y`.

Rewrite using `[← minpoly.eq_of_irreducible hf haroot, ← minpoly.eq_of_irreducible hf hy]`. Take `⟨σ, hσ⟩` from `MulAction.mem_orbit_iff.mp ((Normal.minpoly_eq_iff_mem_orbit (AlgebraicClosure F)).mp hmin)`. Rewrite `hσ` using `[AlgEquiv.smul_def]`. Establish `hmat : (M.map (algebraMap F (AlgebraicClosure F)) - y • (1 : Matrix ι ι (AlgebraicClosure F))).map (σ : AlgebraicClosure F →+* AlgebraicClosure F) = M.map (algebraMap F (AlgebraicClosure F)) - a • 1`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases hij : i = j <;> simp [hij, hσ]`. Establish `e1 : aeval T (X - C a) = Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)) - a • 1)`. Rewrite using `[map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, hT, map_sub, map_smul, Matrix.toLin'_one, Module.End.one_eq_id]`. Establish `e2 : T - y • 1 = Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)) - y • 1)`. Rewrite using `[hT, map_sub, map_smul, Matrix.toLin'_one, Module.End.one_eq_id]`.

Rewrite using `[Module.End.eigenspace_def, e1, e2, ← hmat, eigDim_ker_map]`. Rewrite using `[hker, LinearMap.ker_smul _ _ hlc, eigDim_ker_prod, Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, Multiset.toFinset_card_of_nodup hnd, hcard, hg, Polynomial.natDegree_map]`.
-/
theorem finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace :
    ∀ (F : Type) [Field F] [Finite F] (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι F) (f : F[X]) (y : AlgebraicClosure F), Irreducible f → aeval y f = 0 → Module.finrank F (LinearMap.ker (aeval (Matrix.toLin' M) f)) = f.natDegree * Module.finrank (AlgebraicClosure F) (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)))) y) := by
  intro F _ _ ι _ _ M f y hf hy
  classical
  rw [← eigDim_ker_aeval_map (algebraMap F (AlgebraicClosure F)) M f]
  set g := f.map (algebraMap F (AlgebraicClosure F)) with hg
  set T := Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F))) with hT
  have hsep : g.Separable := (PerfectField.separable_of_irreducible hf).map
  have hne : g ≠ 0 := Polynomial.map_ne_zero hf.ne_zero
  have hnd := Polynomial.nodup_roots hsep
  have hcard : Multiset.card g.roots = g.natDegree :=
    (IsAlgClosed.splits g).natDegree_eq_card_roots.symm
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hprod : (g.roots.map fun a => X - C a).prod = ∏ a ∈ g.roots.toFinset, (X - C a) := by
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
  have hlc : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne
  have hker : aeval T g = g.leadingCoeff • aeval T (∏ a ∈ g.roots.toFinset, (X - C a)) := by
    conv_lhs => rw [← hfac, hprod]
    rw [map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hterm : ∀ a ∈ g.roots.toFinset, Module.finrank (AlgebraicClosure F) (LinearMap.ker (aeval T (X - C a))) =
      Module.finrank (AlgebraicClosure F) (Module.End.eigenspace T y) := by
    intro a ha
    have haroot : aeval a f = 0 := by
      have h0 := Polynomial.IsRoot.eq_zero ((Polynomial.mem_roots hne).mp (Multiset.mem_toFinset.mp ha))
      rwa [hg, Polynomial.eval_map_algebraMap] at h0
    have hmin : minpoly F a = minpoly F y := by
      rw [← minpoly.eq_of_irreducible hf haroot, ← minpoly.eq_of_irreducible hf hy]
    obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp ((Normal.minpoly_eq_iff_mem_orbit (AlgebraicClosure F)).mp hmin)
    rw [AlgEquiv.smul_def] at hσ
    have hmat : (M.map (algebraMap F (AlgebraicClosure F)) - y • (1 : Matrix ι ι (AlgebraicClosure F))).map (σ : AlgebraicClosure F →+* AlgebraicClosure F) = M.map (algebraMap F (AlgebraicClosure F)) - a • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [hij, hσ]
    have e1 : aeval T (X - C a) = Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)) - a • 1) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, hT,
        map_sub, map_smul, Matrix.toLin'_one, Module.End.one_eq_id]
    have e2 : T - y • 1 = Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)) - y • 1) := by
      rw [hT, map_sub, map_smul, Matrix.toLin'_one, Module.End.one_eq_id]
    rw [Module.End.eigenspace_def, e1, e2, ← hmat, eigDim_ker_map]
  rw [hker, LinearMap.ker_smul _ _ hlc, eigDim_ker_prod, Finset.sum_congr rfl hterm,
    Finset.sum_const, smul_eq_mul, Multiset.toFinset_card_of_nodup hnd, hcard, hg,
    Polynomial.natDegree_map]

end GlobalTheory
