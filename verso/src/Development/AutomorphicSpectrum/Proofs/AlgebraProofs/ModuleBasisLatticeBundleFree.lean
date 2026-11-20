import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwistApply

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

open GlobalTheory.CompanionTheory.Ar.Crv

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Use `push_cast`. Conclude with `(v.map_add _ _).trans (max_le ih (le_of_eq v.map_one))`.
-/
private theorem valuation_natCast_le_one_algebra {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))
    (n : ℕ) : v (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    push_cast
    exact (v.map_add _ _).trans (max_le ih (le_of_eq v.map_one))

/- English proof (translation)
Consider the cases of `n with`. Consider the case `ofNat m`. Rewrite using `[Int.ofNat_eq_natCast, Int.cast_natCast]`. Conclude with `valuation_natCast_le_one_algebra v m`. Consider the case `negSucc m`.

Rewrite using `[Int.cast_negSucc, Valuation.map_neg]`. Conclude with `valuation_natCast_le_one_algebra v (m + 1)` after adjusting the coercions.
-/
theorem v_intCast_le_one {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))
    (n : ℤ) : v (n : K) ≤ 1 := by
  cases n with
  | ofNat m =>
    rw [Int.ofNat_eq_natCast, Int.cast_natCast]
    exact valuation_natCast_le_one_algebra v m
  | negSucc m =>
    rw [Int.cast_negSucc, Valuation.map_neg]
    exact_mod_cast valuation_natCast_le_one_algebra v (m + 1)

/- English proof (translation)
Take `⟨x, hli, hL'⟩` from `h`. Use `set e : Fin r × ι → V := fun q => ρ (b q.2) (x q.1) with he`. Take `⟨b0, hb0⟩` from `hL.1 i`. Establish `hb0 : ∀ z : V, z ∈ L i ↔ ∀ q, C.v i (b0.repr z q) ≤ 1` using `hb0`. Establish `hmemL : ∀ y : V, y ∈ L i → y ∈ Submodule.span K (Set.range e)`.

Introduce `y hy`. Take `⟨c, -, rfl⟩` from `(hL' y).1 hy`. Conclude with `Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)`. Establish `hspan : ⊤ ≤ Submodule.span K (Set.range e)`. Rewrite using `[← b0.span_eq]`.

Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Use `hmemL _ ((hb0 _).2 fun q => ?_)` and prove the remaining obligations. Rewrite using `[Module.Basis.repr_self, Finsupp.single_apply]`. Use `split_ifs`.

Conclude with `(map_one _).le`. Rewrite using `[map_zero]`. Conclude with `zero_le_one`. Set `B : Module.Basis (Fin r × ι) K V` to `Module.Basis.mk hli hspan`. Establish `hBe : ∀ q, B q = e q` using `fun q => Module.Basis.mk_apply hli hspan q`.

Establish `key : ∀ (c : Fin r × ι → K) (q : Fin r × ι), B.coord q (∑ q', c q' • e q') = c q`. Introduce `c q`. Establish `hc : ∑ q', c q' • e q' = B.equivFun.symm c`. Rewrite using `[Module.Basis.equivFun_symm_apply]`. Simplify using `only [hBe]`.

Rewrite using `[hc, Module.Basis.coord_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`. Establish `key' : ∀ (c : Fin r × ι → K) (q : Fin r × ι), B.coord q (∑ q', c q' • ρ (b q'.2) (x q'.1)) = c q` using `key`. Establish `hrep : ∀ (o : O) (s' : Fin r), ρ o (x s') = ∑ q : Fin r × ι, (if q.1 = s' then ((b.repr o q.2 : ℤ) : K) else 0) • e q`. Introduce `o s'`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single s' (fun s _ hs => by simp [hs]) (fun h => absurd (Finset.mem_univ _) h)]`.

Use `conv_lhs => rw [← b.sum_repr o]`. Rewrite using `[map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[if_pos rfl, map_zsmul, Int.cast_smul_eq_zsmul]`.

Both sides reduce to the same expression. Use `⟨x, fun l s => ∑ j, algebraMap k K (l (1 ⊗ₜ[ℤ] b j)) • B.coord (s, j), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s`. Rewrite using `[hL']`. Use `⟨fun q => if q.1 = s then ((b.repr 1 q.2 : ℤ) : K) else 0, fun q => ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only split_ifs`. Conclude with `v_intCast_le_one _ _`. Rewrite using `[map_zero]`. Conclude with `zero_le_one`. Conclude with `(LinearMap.congr_fun (map_one ρ) (x s)).symm.trans (hrep 1 s)`.

Introduce `l s s' a dsimp only`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul c o`. Rewrite using `[act_tmul, LinearMap.smul_apply, map_smul, hrep o s']`.

Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, key, smul_eq_mul]`. Use `split_ifs with hss`. Establish `h1 : l (c ⊗ₜ[ℤ] o) = c * l ((1 : k) ⊗ₜ[ℤ] o)`. Rewrite using `[← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Establish `h2 : l ((1 : k) ⊗ₜ[ℤ] o) = ∑ j, b.repr o j • l ((1 : k) ⊗ₜ[ℤ] b j)` using `by conv_lhs => rw [← b.sum_repr o]`.

Rewrite using `[TensorProduct.tmul_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[TensorProduct.tmul_smul, map_zsmul]`. Rewrite using `[h1, h2, map_mul, map_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, zsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[hss]`. Consider the case `add a a' ha ha'`.

Rewrite using `[map_add, LinearMap.add_apply, map_add, ha, ha']`. Apply the tactic sequence `split_ifs <;> simp [map_add]`. Introduce `l s y hy`. Take `⟨c, hc, rfl⟩` from `(hL' y).1 hy`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, key', smul_eq_mul]`.

Use `Valuation.map_sum_le _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_one' (hk _) (hc _)`. Introduce `y`. Establish `hy : y ∈ Submodule.span K (Set.range e)` using `hspan Submodule.mem_top`.

Use `Submodule.span_mono ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `⟨(1 ⊗ₜ[ℤ] b q.2, q.1), by show (act k ρ) ((1 : k) ⊗ₜ[ℤ] b q.2) (x q.1) = e q`. Rewrite using `[act_tmul, map_one, one_smul]⟩`.
-/
theorem freeAt_of_basis_lattice (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O ι k : Type) [CommRing O]
    [Fintype ι] [Field k] [Algebra k K] (b : Module.Basis ι ℤ O) (ρ : O →+* Module.End K V)
    (r : ℕ) (i : C.I) (hL : IsBun C L) (hk : ∀ c : k, C.v i (algebraMap k K c) ≤ 1)
    (h : ∃ x : Fin r → V, LinearIndependent K (fun q : Fin r × ι => ρ (b q.2) (x q.1)) ∧
      ∀ y, y ∈ L i ↔ ∃ c : Fin r × ι → K, (∀ q, C.v i (c q) ≤ 1) ∧
        y = ∑ q, c q • ρ (b q.2) (x q.1)) :
    FreeAt C k (act k ρ) L r i := by
  obtain ⟨x, hli, hL'⟩ := h
  set e : Fin r × ι → V := fun q => ρ (b q.2) (x q.1) with he
  obtain ⟨b0, hb0⟩ := hL.1 i
  have hb0 : ∀ z : V, z ∈ L i ↔ ∀ q, C.v i (b0.repr z q) ≤ 1 := hb0
  have hmemL : ∀ y : V, y ∈ L i → y ∈ Submodule.span K (Set.range e) := by
    intro y hy
    obtain ⟨c, -, rfl⟩ := (hL' y).1 hy
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  have hspan : ⊤ ≤ Submodule.span K (Set.range e) := by
    rw [← b0.span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    refine hmemL _ ((hb0 _).2 fun q => ?_)
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact (map_one _).le
    · rw [map_zero]
      exact zero_le_one
  let B : Module.Basis (Fin r × ι) K V := Module.Basis.mk hli hspan
  have hBe : ∀ q, B q = e q := fun q => Module.Basis.mk_apply hli hspan q
  have key : ∀ (c : Fin r × ι → K) (q : Fin r × ι), B.coord q (∑ q', c q' • e q') = c q := by
    intro c q
    have hc : ∑ q', c q' • e q' = B.equivFun.symm c := by
      rw [Module.Basis.equivFun_symm_apply]
      simp only [hBe]
    rw [hc, Module.Basis.coord_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have key' : ∀ (c : Fin r × ι → K) (q : Fin r × ι),
      B.coord q (∑ q', c q' • ρ (b q'.2) (x q'.1)) = c q := key
  have hrep : ∀ (o : O) (s' : Fin r), ρ o (x s') =
      ∑ q : Fin r × ι, (if q.1 = s' then ((b.repr o q.2 : ℤ) : K) else 0) • e q := by
    intro o s'
    rw [Fintype.sum_prod_type, Finset.sum_eq_single s' (fun s _ hs => by simp [hs])
      (fun h => absurd (Finset.mem_univ _) h)]
    conv_lhs => rw [← b.sum_repr o]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    rw [if_pos rfl, map_zsmul, Int.cast_smul_eq_zsmul]
    rfl
  refine ⟨x, fun l s => ∑ j, algebraMap k K (l (1 ⊗ₜ[ℤ] b j)) • B.coord (s, j), ?_, ?_, ?_, ?_⟩
  · intro s
    rw [hL']
    refine ⟨fun q => if q.1 = s then ((b.repr 1 q.2 : ℤ) : K) else 0, fun q => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact v_intCast_le_one _ _
      · rw [map_zero]
        exact zero_le_one
    · exact (LinearMap.congr_fun (map_one ρ) (x s)).symm.trans (hrep 1 s)
  · intro l s s' a
    dsimp only
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul c o =>
      rw [act_tmul, LinearMap.smul_apply, map_smul, hrep o s']
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, key, smul_eq_mul]
      split_ifs with hss
      · have h1 : l (c ⊗ₜ[ℤ] o) = c * l ((1 : k) ⊗ₜ[ℤ] o) := by
          rw [← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have h2 : l ((1 : k) ⊗ₜ[ℤ] o) = ∑ j, b.repr o j • l ((1 : k) ⊗ₜ[ℤ] b j) := by
          conv_lhs => rw [← b.sum_repr o]
          rw [TensorProduct.tmul_sum, map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [TensorProduct.tmul_smul, map_zsmul]
        rw [h1, h2, map_mul, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_zsmul, zsmul_eq_mul]
        ring
      · simp [hss]
    | add a a' ha ha' =>
      rw [map_add, LinearMap.add_apply, map_add, ha, ha']
      split_ifs <;> simp [map_add]
  · intro l s y hy
    obtain ⟨c, hc, rfl⟩ := (hL' y).1 hy
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, key', smul_eq_mul]
    refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    exact mul_le_one' (hk _) (hc _)
  · intro y
    have hy : y ∈ Submodule.span K (Set.range e) := hspan Submodule.mem_top
    refine Submodule.span_mono ?_ hy
    rintro _ ⟨q, rfl⟩
    exact ⟨(1 ⊗ₜ[ℤ] b q.2, q.1), by
      show (act k ρ) ((1 : k) ⊗ₜ[ℤ] b q.2) (x q.1) = e q
      rw [act_tmul, map_one, one_smul]⟩

end GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
