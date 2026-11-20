import Mathlib
open Polynomial

namespace GlobalTheory.TraceAeval

open Module

/- English proof (translation)
Establish `hk : ∀ k : ℕ, LinearMap.trace ℂ V (g ^ k) = (finrank ℂ V : ℂ) * μ ^ k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Use `LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ ((Commute.refl g).pow_left k) h` as an intermediate fact. Rewrite using `[pow_succ, Module.End.mul_eq_comp, this, ih]`. Expand and normalize the polynomial expressions, which then agree. Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp only [map_add, hp, hq, eval_add]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `monomial k a`. Rewrite using `[aeval_monomial, ← Algebra.smul_def, map_smul, hk, eval_monomial, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trace_aeval_of_isNilpotent {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (g : Module.End ℂ V) (μ : ℂ) (h : IsNilpotent (g - algebraMap ℂ _ μ)) (p : ℂ[X]) :
    LinearMap.trace ℂ V (aeval g p) = (finrank ℂ V : ℂ) * p.eval μ := by
  have hk : ∀ k : ℕ, LinearMap.trace ℂ V (g ^ k) = (finrank ℂ V : ℂ) * μ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ
        ((Commute.refl g).pow_left k) h
      rw [pow_succ, Module.End.mul_eq_comp, this, ih]; ring
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, eval_add]; ring
  | monomial k a =>
    rw [aeval_monomial, ← Algebra.smul_def, map_smul, hk, eval_monomial, smul_eq_mul]; ring

/- English proof (translation)
Establish `hk : ∀ (k : ℕ) (x : N), ((((f.restrict hf) ^ k) x : N) : V) = (f ^ k) x`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => intro x`.

Simplify using `[pow_succ, ih]`. Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `monomial k a => simp [aeval_monomial, hk]`.
-/
theorem coe_aeval_restrict {V : Type*} [AddCommGroup V] [Module ℂ V] (f : Module.End ℂ V)
    (N : Submodule ℂ V) (hf : ∀ x ∈ N, f x ∈ N) (p : ℂ[X]) (x : N) :
    ((aeval (f.restrict hf) p x : N) : V) = aeval f p x := by
  have hk : ∀ (k : ℕ) (x : N), ((((f.restrict hf) ^ k) x : N) : V) = (f ^ k) x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => intro x; simp [pow_succ, ih]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k a => simp [aeval_monomial, hk]

/- English proof (translation)
Establish `hds` using `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top f.independent_maxGenEigenspace (Module.End.iSup_maxGenEigenspace_eq_top f)`. Establish `h_fin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite` using `WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace`. Establish `hf : ∀ μ, ∀ x ∈ f.maxGenEigenspace μ, f x ∈ f.maxGenEigenspace μ` using `fun μ => f.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) μ`. Establish `hp : ∀ μ, Set.MapsTo (aeval f p) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ)`. Introduce `μ x hx`.

Rewrite using `[show aeval f p x = _ from (coe_aeval_restrict f _ (hf μ) p ⟨x, hx⟩).symm]`. Conclude with `Subtype.mem _`. Rewrite using `[LinearMap.trace_eq_sum_trace_restrict' hds h_fin hp]`. Establish `h1 : ∀ μ, LinearMap.trace ℂ _ ((aeval f p).restrict (hp μ)) = (f.charpoly.rootMultiplicity μ : ℂ) * p.eval μ`. Introduce `μ`.

Establish `e : (aeval f p).restrict (hp μ) = aeval (f.restrict (hf μ)) p`. Use extensionality with `x`. Rewrite using `[coe_aeval_restrict]`. Both sides reduce to the same expression. Establish `hn` using `f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ`.

Establish `e2 : f.restrict (hf μ) - algebraMap ℂ _ μ = (f - algebraMap ℂ _ μ).restrict (f.mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ)`. Use extensionality with `x`. Both sides reduce to the same expression. Rewrite using `[e, trace_aeval_of_isNilpotent _ μ (e2 ▸ hn), LinearMap.finrank_maxGenEigenspace_eq]`. Repeatedly rewrite using `[h1]`.

Rewrite using `[Finset.sum_multiset_map_count]`. Establish `hs : h_fin.toFinset = f.charpoly.roots.toFinset`. Use extensionality with `μ`. Rewrite using `[Set.Finite.mem_toFinset, Multiset.mem_toFinset, Set.mem_setOf_eq, ← Multiset.count_ne_zero, count_roots, ← LinearMap.finrank_maxGenEigenspace_eq, Ne, Ne, Submodule.finrank_eq_zero]`. Rewrite using `[hs]`.

Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations. Rewrite using `[count_roots, nsmul_eq_mul]`.
-/
theorem trace_aeval_end {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (f : Module.End ℂ V) (p : ℂ[X]) :
    LinearMap.trace ℂ V (aeval f p) = (f.charpoly.roots.map fun z => p.eval z).sum := by
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.independent_maxGenEigenspace (Module.End.iSup_maxGenEigenspace_eq_top f)
  have h_fin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
  have hf : ∀ μ, ∀ x ∈ f.maxGenEigenspace μ, f x ∈ f.maxGenEigenspace μ :=
    fun μ => f.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) μ
  have hp : ∀ μ, Set.MapsTo (aeval f p) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) := by
    intro μ x hx
    rw [show aeval f p x = _ from (coe_aeval_restrict f _ (hf μ) p ⟨x, hx⟩).symm]
    exact Subtype.mem _
  rw [LinearMap.trace_eq_sum_trace_restrict' hds h_fin hp]
  have h1 : ∀ μ, LinearMap.trace ℂ _ ((aeval f p).restrict (hp μ))
      = (f.charpoly.rootMultiplicity μ : ℂ) * p.eval μ := by
    intro μ
    have e : (aeval f p).restrict (hp μ) = aeval (f.restrict (hf μ)) p := by
      ext x
      rw [coe_aeval_restrict]; rfl
    have hn := f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
    have e2 : f.restrict (hf μ) - algebraMap ℂ _ μ = (f - algebraMap ℂ _ μ).restrict
        (f.mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ) := by
      ext x
      rfl
    rw [e, trace_aeval_of_isNilpotent _ μ (e2 ▸ hn), LinearMap.finrank_maxGenEigenspace_eq]
  simp_rw [h1]
  rw [Finset.sum_multiset_map_count]
  have hs : h_fin.toFinset = f.charpoly.roots.toFinset := by
    ext μ
    rw [Set.Finite.mem_toFinset, Multiset.mem_toFinset, Set.mem_setOf_eq,
      ← Multiset.count_ne_zero, count_roots, ← LinearMap.finrank_maxGenEigenspace_eq,
      Ne, Ne, Submodule.finrank_eq_zero]
  rw [hs]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [count_roots, nsmul_eq_mul]

/- English proof (translation)
Rewrite using `[← Matrix.charpoly_toLin', ← trace_aeval_end, ← Matrix.trace_toLin'_eq]`. Use `congr 1`. Conclude with `(aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)) A p).symm`.
-/
theorem trace_aeval_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (p : ℂ[X]) :
    (aeval A p).trace = (A.charpoly.roots.map fun z => p.eval z).sum := by
  rw [← Matrix.charpoly_toLin', ← trace_aeval_end, ← Matrix.trace_toLin'_eq]
  congr 1
  exact (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)) A p).symm

/- English proof (translation)
Use `aeval_algHom_apply ((Int.castRingHom R).mapMatrix (m := Fin n)).toIntAlgHom A p` as an intermediate fact. Establish `h2 : aeval (A.map (Int.castRingHom R)) p = (aeval A p).map (Int.castRingHom R)` using `this`. Rewrite using `[h2]`. Simplify using `[Matrix.trace]`.
-/
theorem trace_aeval_map {n : ℕ} {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) ℤ)
    (p : ℤ[X]) :
    (aeval (A.map (Int.castRingHom R)) p).trace = (((aeval A p).trace : ℤ) : R) := by
  have := aeval_algHom_apply ((Int.castRingHom R).mapMatrix (m := Fin n)).toIntAlgHom A p
  have h2 : aeval (A.map (Int.castRingHom R)) p = (aeval A p).map (Int.castRingHom R) := this
  rw [h2]
  simp [Matrix.trace]

/- English proof (translation)
Rewrite using `[← trace_aeval_map, ← aeval_map_algebraMap ℂ, trace_aeval_matrix]`. Simplify using `only [eval_map_algebraMap]`.
-/
theorem trace_aeval_int {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (p : ℤ[X]) :
    (((aeval A p).trace : ℤ) : ℂ)
      = ((A.map (Int.castRingHom ℂ)).charpoly.roots.map fun z => aeval z p).sum := by
  rw [← trace_aeval_map, ← aeval_map_algebraMap ℂ, trace_aeval_matrix]
  simp only [eval_map_algebraMap]

noncomputable def powMat {R : Type*} [CommRing R] (n : ℕ) (ψ : R[X]) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => ((X ^ ((j : ℕ) + 1)) %ₘ ψ).coeff i

open Polynomial in
open Module in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [_root_.GlobalTheory.TraceAeval.powMat, Matrix.map_apply, Matrix.of_apply]`. Rewrite using `[← Polynomial.coeff_map, Polynomial.map_modByMonic f h, Polynomial.map_pow, Polynomial.map_X]`.
-/
theorem _root_.GlobalTheory.TraceAeval.powMat_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (n : ℕ) {ψ : R[X]} (h : ψ.Monic) :
    (_root_.GlobalTheory.TraceAeval.powMat n ψ).map f = _root_.GlobalTheory.TraceAeval.powMat n (ψ.map f) := by
  ext i j
  simp only [_root_.GlobalTheory.TraceAeval.powMat, Matrix.map_apply, Matrix.of_apply]
  rw [← Polynomial.coeff_map, Polynomial.map_modByMonic f h, Polynomial.map_pow,
    Polynomial.map_X]

/- English proof (translation)
Establish `h1` using `charpoly_leftMulMatrix (AdjoinRoot.powerBasis' h)`. Establish `h2 : minpoly ℂ (AdjoinRoot.powerBasis' h).gen = ψ`. Rewrite using `[AdjoinRoot.powerBasis'_gen, AdjoinRoot.minpoly_root h.ne_zero, h.leadingCoeff]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[h2]`.

Use `Eq.trans ?_ h1` and prove the remaining obligations. Use `congr 1`. Use extensionality with `i j`. Use `Eq.trans ?_ (Algebra.leftMulMatrix_eq_repr_mul _ _ i j).symm` and prove the remaining obligations. Establish `h3` using `(AdjoinRoot.powerBasis' h).basis_eq_pow j`.

Use `Eq.trans ?_ (congrArg (fun t => (AdjoinRoot.powerBasis' h).basis.repr ((AdjoinRoot.powerBasis' h).gen * t) i) h3).symm` and prove the remaining obligations. Simplify using `only [← pow_succ']`. Express the relevant statement in the definitionally equal form `_ = (AdjoinRoot.powerBasisAux' h).repr ((AdjoinRoot.root ψ) ^ ((j : ℕ) + 1)) i`. Rewrite using `[AdjoinRoot.powerBasisAux'_repr_apply_to_fun, ← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.modByMonicHom_mk]`. Both sides reduce to the same expression.
-/
theorem charpoly_powMat {ψ : ℂ[X]} (h : ψ.Monic) : (powMat ψ.natDegree ψ).charpoly = ψ := by
  have h1 := charpoly_leftMulMatrix (AdjoinRoot.powerBasis' h)
  have h2 : minpoly ℂ (AdjoinRoot.powerBasis' h).gen = ψ := by
    rw [AdjoinRoot.powerBasis'_gen, AdjoinRoot.minpoly_root h.ne_zero, h.leadingCoeff]
    simp
  rw [h2] at h1
  refine Eq.trans ?_ h1
  congr 1
  ext i j
  refine Eq.trans ?_ (Algebra.leftMulMatrix_eq_repr_mul _ _ i j).symm
  have h3 := (AdjoinRoot.powerBasis' h).basis_eq_pow j
  refine Eq.trans ?_ (congrArg (fun t => (AdjoinRoot.powerBasis' h).basis.repr
    ((AdjoinRoot.powerBasis' h).gen * t) i) h3).symm
  simp only [← pow_succ']
  change _ = (AdjoinRoot.powerBasisAux' h).repr ((AdjoinRoot.root ψ) ^ ((j : ℕ) + 1)) i
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun, ← AdjoinRoot.mk_X, ← map_pow,
    AdjoinRoot.modByMonicHom_mk]
  rfl

/- English proof (translation)
Rewrite using `[trace_aeval_int, powMat_map _ _ h, ← h.natDegree_map (Int.castRingHom ℂ), charpoly_powMat (h.map _)]`. Both sides reduce to the same expression.
-/
theorem trace_aeval_powMat {ψ : ℤ[X]} (h : ψ.Monic) (p : ℤ[X]) :
    (((aeval (powMat ψ.natDegree ψ) p).trace : ℤ) : ℂ)
      = ((ψ.aroots ℂ).map fun z => aeval z p).sum := by
  rw [trace_aeval_int, powMat_map _ _ h, ← h.natDegree_map (Int.castRingHom ℂ),
    charpoly_powMat (h.map _)]
  rfl

/- English proof (translation)
Introduce `χ p hχ`. Use `⟨(aeval (powMat χ.natDegree χ) p).trace, trace_aeval_powMat hχ p, ?_⟩` and prove the remaining obligations. Introduce `n M B hB`. Break down `subsingleton_or_nontrivial (ZMod M) with hM | hM` into its components or cases. Conclude with `Subsingleton.elim _ _`.

Establish `hn : χ.natDegree = n`. Rewrite using `[← hχ.natDegree_map (Int.castRingHom (ZMod M)), ← hB, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Use `choose B₀ hB₀ using fun i j => ZMod.intCast_surjective (B i j)`. Establish `hBB : (Matrix.of B₀).map (Int.castRingHom (ZMod M)) = B`. Use extensionality with `i j`.

Simplify using `using hB₀ i j`. Use `set A : Matrix (Fin n) (Fin n) ℤ := Matrix.of B₀`. Establish `hA : A.charpoly.natDegree = n`. Rewrite using `[Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Establish `h1 : (aeval A p).trace = (aeval (powMat n A.charpoly) p).trace`.

Establish `h2` using `trace_aeval_powMat A.charpoly_monic p`. Rewrite `h2` using `[hA]`. Apply `Int.cast_injective (α := ℂ)` to reduce the goal to its premises. Rewrite using `[h2, trace_aeval_int, Matrix.charpoly_map]`. Both sides reduce to the same expression.

Rewrite using `[← hBB, trace_aeval_map, h1, hn, ← trace_aeval_map, ← trace_aeval_map, powMat_map _ _ hχ, powMat_map _ _ A.charpoly_monic, ← Matrix.charpoly_map, hBB, hB]`.
-/
theorem exists_int_trace_aeval_eq_sum_aroots :
    ∀ (χ p : Polynomial ℤ), χ.Monic → ∃ s : ℤ, (s : ℂ) = ((χ.aroots ℂ).map fun z => Polynomial.aeval z p).sum ∧ ∀ (n M : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod M)), B.charpoly = χ.map (Int.castRingHom (ZMod M)) → (Polynomial.aeval B p).trace = (s : ZMod M) := by
  intro χ p hχ
  refine ⟨(aeval (powMat χ.natDegree χ) p).trace, trace_aeval_powMat hχ p, ?_⟩
  intro n M B hB
  rcases subsingleton_or_nontrivial (ZMod M) with hM | hM
  · exact Subsingleton.elim _ _
  have hn : χ.natDegree = n := by
    rw [← hχ.natDegree_map (Int.castRingHom (ZMod M)), ← hB, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  choose B₀ hB₀ using fun i j => ZMod.intCast_surjective (B i j)
  have hBB : (Matrix.of B₀).map (Int.castRingHom (ZMod M)) = B := by
    ext i j; simpa using hB₀ i j
  set A : Matrix (Fin n) (Fin n) ℤ := Matrix.of B₀
  have hA : A.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have h1 : (aeval A p).trace = (aeval (powMat n A.charpoly) p).trace := by
    have h2 := trace_aeval_powMat A.charpoly_monic p
    rw [hA] at h2
    apply Int.cast_injective (α := ℂ)
    rw [h2, trace_aeval_int, Matrix.charpoly_map]
    rfl
  rw [← hBB, trace_aeval_map, h1, hn, ← trace_aeval_map, ← trace_aeval_map,
    powMat_map _ _ hχ, powMat_map _ _ A.charpoly_monic, ← Matrix.charpoly_map, hBB, hB]

end GlobalTheory.TraceAeval
