import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TracePowerSumModEq

open Polynomial Module

namespace GlobalTheory.CompanionTheory.TraceSpec

open GlobalTheory.TraceAeval (powMat powMat_map)

section AlgClosed

variable {C : Type*} [Field C] [IsAlgClosed C]

/- English proof (translation)
Establish `hk : ∀ k : ℕ, LinearMap.trace C V (g ^ k) = (finrank C V : C) * μ ^ k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Use `LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ ((Commute.refl g).pow_left k) h` as an intermediate fact. Rewrite using `[pow_succ, Module.End.mul_eq_comp, this, ih]`. Expand and normalize the polynomial expressions, which then agree. Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp only [map_add, hp, hq, eval_add]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `monomial k a`. Rewrite using `[aeval_monomial, ← Algebra.smul_def, map_smul, hk, eval_monomial, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trace_aeval_of_isNilpotent {V : Type*} [AddCommGroup V] [Module C V] [Module.Finite C V]
    (g : Module.End C V) (μ : C) (h : IsNilpotent (g - algebraMap C _ μ)) (p : C[X]) :
    LinearMap.trace C V (aeval g p) = (finrank C V : C) * p.eval μ := by
  have hk : ∀ k : ℕ, LinearMap.trace C V (g ^ k) = (finrank C V : C) * μ ^ k := by
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
theorem coe_aeval_restrict {V : Type*} [AddCommGroup V] [Module C V] (f : Module.End C V)
    (N : Submodule C V) (hf : ∀ x ∈ N, f x ∈ N) (p : C[X]) (x : N) :
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

Rewrite using `[show aeval f p x = _ from (coe_aeval_restrict f _ (hf μ) p ⟨x, hx⟩).symm]`. Conclude with `Subtype.mem _`. Rewrite using `[LinearMap.trace_eq_sum_trace_restrict' hds h_fin hp]`. Establish `h1 : ∀ μ, LinearMap.trace C _ ((aeval f p).restrict (hp μ)) = (f.charpoly.rootMultiplicity μ : C) * p.eval μ`. Introduce `μ`.

Establish `e : (aeval f p).restrict (hp μ) = aeval (f.restrict (hf μ)) p`. Use extensionality with `x`. Rewrite using `[coe_aeval_restrict]`. Both sides reduce to the same expression. Establish `hn` using `f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ`.

Establish `e2 : f.restrict (hf μ) - algebraMap C _ μ = (f - algebraMap C _ μ).restrict (f.mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ)`. Use extensionality with `x`. Both sides reduce to the same expression. Rewrite using `[e, trace_aeval_of_isNilpotent _ μ (e2 ▸ hn), LinearMap.finrank_maxGenEigenspace_eq]`. Repeatedly rewrite using `[h1]`.

Rewrite using `[Finset.sum_multiset_map_count]`. Establish `hs : h_fin.toFinset = f.charpoly.roots.toFinset`. Use extensionality with `μ`. Rewrite using `[Set.Finite.mem_toFinset, Multiset.mem_toFinset, Set.mem_setOf_eq, ← Multiset.count_ne_zero, count_roots, ← LinearMap.finrank_maxGenEigenspace_eq, Ne, Ne, Submodule.finrank_eq_zero]`. Rewrite using `[hs]`.

Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations. Rewrite using `[count_roots, nsmul_eq_mul]`.
-/
theorem trace_aeval_end {V : Type*} [AddCommGroup V] [Module C V] [Module.Finite C V]
    (f : Module.End C V) (p : C[X]) :
    LinearMap.trace C V (aeval f p) = (f.charpoly.roots.map fun z => p.eval z).sum := by
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
  have h1 : ∀ μ, LinearMap.trace C _ ((aeval f p).restrict (hp μ))
      = (f.charpoly.rootMultiplicity μ : C) * p.eval μ := by
    intro μ
    have e : (aeval f p).restrict (hp μ) = aeval (f.restrict (hf μ)) p := by
      ext x
      rw [coe_aeval_restrict]; rfl
    have hn := f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
    have e2 : f.restrict (hf μ) - algebraMap C _ μ = (f - algebraMap C _ μ).restrict
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
Rewrite using `[← Matrix.charpoly_toLin', ← trace_aeval_end, ← Matrix.trace_toLin'_eq]`. Use `congr 1`. Conclude with `(aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := C) (n := Fin n)) A p).symm`.
-/
theorem trace_aeval_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) C) (p : C[X]) :
    (aeval A p).trace = (A.charpoly.roots.map fun z => p.eval z).sum := by
  rw [← Matrix.charpoly_toLin', ← trace_aeval_end, ← Matrix.trace_toLin'_eq]
  congr 1
  exact (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := C) (n := Fin n)) A p).symm

end AlgClosed

/- English proof (translation)
Establish `hrep : ∀ k : Fin pb.dim, pb.basis.repr (pb.gen ^ (k : ℕ)) = Finsupp.single k 1`. Introduce `k`. Rewrite using `[← pb.basis_eq_pow k]`. Conclude with `pb.basis.repr_self k`. Rewrite using `[aeval_eq_sum_range' hr, map_sum, Finsupp.finset_sum_apply]`.

Rewrite using `[Finset.sum_eq_single (i : ℕ)]`. Rewrite using `[map_smul, Finsupp.smul_apply, hrep i]`. Simplify using the standard rewrite rules. Introduce `b hb hbi`. Rewrite using `[map_smul, Finsupp.smul_apply, hrep ⟨b, Finset.mem_range.1 hb⟩]`.

Establish `hne : (⟨b, Finset.mem_range.1 hb⟩ : Fin pb.dim) ≠ i` using `fun h => hbi (congrArg Fin.val h)`. Simplify using `[Finsupp.single_apply, hne]`. Introduce `h`. Conclude with `(h (Finset.mem_range.2 i.2)).elim`.
-/
theorem repr_aeval {F S : Type*} [Field F] [CommRing S] [Algebra F S] (pb : PowerBasis F S)
    (r : F[X]) (hr : r.natDegree < pb.dim) (i : Fin pb.dim) :
    pb.basis.repr (aeval pb.gen r) i = r.coeff i := by
  have hrep : ∀ k : Fin pb.dim, pb.basis.repr (pb.gen ^ (k : ℕ)) = Finsupp.single k 1 := by
    intro k
    rw [← pb.basis_eq_pow k]
    exact pb.basis.repr_self k
  rw [aeval_eq_sum_range' hr, map_sum, Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single (i : ℕ)]
  · rw [map_smul, Finsupp.smul_apply, hrep i]
    simp
  · intro b hb hbi
    rw [map_smul, Finsupp.smul_apply, hrep ⟨b, Finset.mem_range.1 hb⟩]
    have hne : (⟨b, Finset.mem_range.1 hb⟩ : Fin pb.dim) ≠ i := fun h => hbi (congrArg Fin.val h)
    simp [Finsupp.single_apply, hne]
  · intro h
    exact (h (Finset.mem_range.2 i.2)).elim

/- English proof (translation)
Use extensionality with `i j`. Establish `hm : (minpoly F pb.gen).Monic` using `minpoly.monic pb.isIntegral_gen`. Establish `hne : minpoly F pb.gen ≠ 1`. Introduce `h`. Use `pb.natDegree_minpoly` as an intermediate fact.

Rewrite `this` using `[h, natDegree_one]`. Use `i.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[Algebra.leftMulMatrix_eq_repr_mul, pb.basis_eq_pow j, ← pow_succ']`. Establish `h1 : pb.gen ^ ((j : ℕ) + 1) = aeval pb.gen ((X ^ ((j : ℕ) + 1)) %ₘ minpoly F pb.gen)`.

Rewrite using `[aeval_modByMonic_eq_self_of_root (minpoly.aeval F pb.gen)]`. Simplify using the standard rewrite rules. Rewrite using `[h1, repr_aeval pb _ (lt_of_lt_of_eq (natDegree_modByMonic_lt _ hm hne) pb.natDegree_minpoly)]`. Both sides reduce to the same expression.
-/
theorem leftMulMatrix_gen {F S : Type*} [Field F] [CommRing S] [Algebra F S]
    (pb : PowerBasis F S) :
    Algebra.leftMulMatrix pb.basis pb.gen = powMat pb.dim (minpoly F pb.gen) := by
  ext i j
  have hm : (minpoly F pb.gen).Monic := minpoly.monic pb.isIntegral_gen
  have hne : minpoly F pb.gen ≠ 1 := by
    intro h
    have := pb.natDegree_minpoly
    rw [h, natDegree_one] at this
    have := i.2
    omega
  rw [Algebra.leftMulMatrix_eq_repr_mul, pb.basis_eq_pow j, ← pow_succ']
  have h1 : pb.gen ^ ((j : ℕ) + 1) = aeval pb.gen ((X ^ ((j : ℕ) + 1)) %ₘ minpoly F pb.gen) := by
    rw [aeval_modByMonic_eq_self_of_root (minpoly.aeval F pb.gen)]
    simp
  rw [h1, repr_aeval pb _ (lt_of_lt_of_eq (natDegree_modByMonic_lt _ hm hne) pb.natDegree_minpoly)]
  rfl

/- English proof (translation)
Rewrite using `[Algebra.trace_eq_matrix_trace pb.basis, ← leftMulMatrix_gen, aeval_algHom_apply (Algebra.leftMulMatrix pb.basis) pb.gen p]`.
-/
theorem trace_aeval_gen {F S : Type*} [Field F] [CommRing S] [Algebra F S]
    (pb : PowerBasis F S) (p : F[X]) :
    Algebra.trace F S (aeval pb.gen p)
      = (aeval (powMat pb.dim (minpoly F pb.gen)) p).trace := by
  rw [Algebra.trace_eq_matrix_trace pb.basis, ← leftMulMatrix_gen,
    aeval_algHom_apply (Algebra.leftMulMatrix pb.basis) pb.gen p]

/- English proof (translation)
Rewrite using `[← powMat_map f n hg]`. Establish `h : aeval ((powMat n g).map f) (p.map f) = (aeval (powMat n g) p).map f`. Establish `h1` using `hom_eval₂ p (algebraMap R (Matrix (Fin n) (Fin n) R)) (f.mapMatrix (m := Fin n)) (powMat n g)`. Establish `h2 : (f.mapMatrix (m` using `Fin n)).comp (algebraMap R (Matrix (Fin n) (Fin n) R)) = (algebraMap S (Matrix (Fin n) (Fin n) S)).comp f := by`. Use extensionality with `a i j`.

Simplify using `[Matrix.algebraMap_matrix_apply, apply_ite f]`. Rewrite `h1` using `[h2]`. Rewrite using `[aeval_def, eval₂_map]`. Conclude with `h1.symm`. Rewrite using `[h]`.

Simplify using `[Matrix.trace]`.
-/
theorem trace_aeval_powMat_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    {g : R[X]} (hg : g.Monic) (p : R[X]) :
    (aeval (powMat n (g.map f)) (p.map f)).trace = f (aeval (powMat n g) p).trace := by
  rw [← powMat_map f n hg]
  have h : aeval ((powMat n g).map f) (p.map f) = (aeval (powMat n g) p).map f := by
    have h1 := hom_eval₂ p (algebraMap R (Matrix (Fin n) (Fin n) R))
      (f.mapMatrix (m := Fin n)) (powMat n g)
    have h2 : (f.mapMatrix (m := Fin n)).comp (algebraMap R (Matrix (Fin n) (Fin n) R))
        = (algebraMap S (Matrix (Fin n) (Fin n) S)).comp f := by
      ext a i j
      simp [Matrix.algebraMap_matrix_apply, apply_ite f]
    rw [h2] at h1
    rw [aeval_def, eval₂_map]
    exact h1.symm
  rw [h]
  simp [Matrix.trace]

/- English proof (translation)
Substitute `hn` using the available equality. Establish `h1` using `charpoly_leftMulMatrix (AdjoinRoot.powerBasis' h)`. Establish `h2 : minpoly C (AdjoinRoot.powerBasis' h).gen = ψ`. Rewrite using `[AdjoinRoot.powerBasis'_gen, AdjoinRoot.minpoly_root h.ne_zero, h.leadingCoeff]`. Simplify using the standard rewrite rules.

Rewrite `h1` using `[h2]`. Use `Eq.trans ?_ h1` and prove the remaining obligations. Use `congr 1`. Use extensionality with `i j`. Use `Eq.trans ?_ (Algebra.leftMulMatrix_eq_repr_mul _ _ i j).symm` and prove the remaining obligations.

Establish `h3` using `(AdjoinRoot.powerBasis' h).basis_eq_pow j`. Use `Eq.trans ?_ (congrArg (fun t => (AdjoinRoot.powerBasis' h).basis.repr ((AdjoinRoot.powerBasis' h).gen * t) i) h3).symm` and prove the remaining obligations. Simplify using `only [← pow_succ']`. Express the relevant statement in the definitionally equal form `_ = (AdjoinRoot.powerBasisAux' h).repr ((AdjoinRoot.root ψ) ^ ((j : ℕ) + 1)) i`. Rewrite using `[AdjoinRoot.powerBasisAux'_repr_apply_to_fun, ← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.modByMonicHom_mk]`.

Both sides reduce to the same expression.
-/
theorem charpoly_powMat {C : Type*} [Field C] {ψ : C[X]} (h : ψ.Monic) (n : ℕ)
    (hn : ψ.natDegree = n) : (powMat n ψ).charpoly = ψ := by
  subst hn
  have h1 := charpoly_leftMulMatrix (AdjoinRoot.powerBasis' h)
  have h2 : minpoly C (AdjoinRoot.powerBasis' h).gen = ψ := by
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
Establish `hl : ψ ∈ lifts (algebraMap (Subalgebra.algebraicClosure ℤ C) C)` using `(lifts_iff_coeff_lifts _).2 fun i => ⟨⟨ψ.coeff i, hc i⟩, rfl⟩`. Take `⟨q, rfl⟩` from `mem_lifts _ |>.1 hl`. Establish `h : IsAlgebraic (Subalgebra.algebraicClosure ℤ C) ρ`. Use `⟨q, fun h0 => hψ (by rw [h0, Polynomial.map_zero]), ?_⟩` and prove the remaining obligations. Rewrite using `[aeval_def, ← eval_map]`.

Conclude with `hρ`. Conclude with `h.restrictScalars ℤ`.
-/
theorem isAlgebraic_of_root {C : Type*} [Field C] (ψ : C[X]) (hψ : ψ ≠ 0)
    (hc : ∀ i, IsAlgebraic ℤ (ψ.coeff i)) {ρ : C} (hρ : ψ.eval ρ = 0) : IsAlgebraic ℤ ρ := by
  have hl : ψ ∈ lifts (algebraMap (Subalgebra.algebraicClosure ℤ C) C) :=
    (lifts_iff_coeff_lifts _).2 fun i => ⟨⟨ψ.coeff i, hc i⟩, rfl⟩
  obtain ⟨q, rfl⟩ := mem_lifts _ |>.1 hl
  have h : IsAlgebraic (Subalgebra.algebraicClosure ℤ C) ρ := by
    refine ⟨q, fun h0 => hψ (by rw [h0, Polynomial.map_zero]), ?_⟩
    rw [aeval_def, ← eval_map]
    exact hρ
  exact h.restrictScalars ℤ

/- English proof (translation)
Take `⟨pb⟩ : Nonempty (PowerBasis K L)` from `⟨Field.powerBasisOfFiniteOfSeparable K L⟩`. Establish `hint : IsIntegral K pb.gen` using `pb.isIntegral_gen`. Use `choose P hP using fun b : L => pb.exists_eq_aeval' b`. Use `⟨(minpoly K pb.gen).coeffs ∪ (insert x B₀).biUnion fun b => (P b).coeffs, fun A' hB' => ?_⟩` and prove the remaining obligations. Establish `hmc : (↑(minpoly K pb.gen).coeffs : Set K) ⊆ A'` using `fun c hc => hB' (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hc)))`.

Establish `hPc : ∀ b ∈ insert x B₀, (↑(P b).coeffs : Set K) ⊆ A'` using `fun b hb c hc => hB' (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨b, hb, Finset.mem_coe.1 hc⟩)))`. Set `m' : A'[X]` to `(minpoly K pb.gen).toSubring A' hmc`. Establish `hm'map : m'.map A'.subtype = minpoly K pb.gen` using `map_toSubring _ _ _`. Establish `hm' : m'.Monic` using `(monic_toSubring _ _ _).2 (minpoly.monic hint)`. Set `Q : ∀ b ∈ insert x B₀, A'[X]` to `fun b hb => (P b).toSubring A' (hPc b hb)`.

Establish `hQ : ∀ b hb, (Q b hb).map A'.subtype = P b` using `fun b hb => map_toSubring _ _ _`. Set `f : A'[X] →+* L` to `eval₂RingHom ((algebraMap K L).comp A'.subtype) pb.gen`. Establish `hf : ∀ p : A'[X], f p = aeval pb.gen (p.map A'.subtype)` using `fun p => by`. Rewrite using `[aeval_def, eval₂_map]`. Both sides reduce to the same expression.

Establish `hfQ : ∀ b hb, f (Q b hb) = b` using `fun b hb => by rw [hf, hQ b hb, ← hP b]`. Establish `hdvd : ∀ p : A'[X], f p = 0 → m' ∣ p`. Introduce `p hp`. Rewrite `hp` using `[hf]`. Establish `h2 : minpoly K pb.gen ∣ p.map A'.subtype` using `minpoly.dvd K pb.gen hp`.

Establish `h3 : (p %ₘ m').map A'.subtype = 0`. Rewrite using `[map_modByMonic _ hm', hm'map]`. Conclude with `(modByMonic_eq_zero_iff_dvd (minpoly.monic hint)).2 h2`. Establish `h4 : p %ₘ m' = 0` using `map_injective _ Subtype.val_injective (by rw [h3, Polynomial.map_zero])`. Conclude with `(modByMonic_eq_zero_iff_dvd hm').1 h4`.

Establish `hxm` using `Finset.mem_insert_self x B₀`. Establish `hT : Algebra.trace K L x = ((aeval (powMat pb.dim m') (Q x hxm)).trace : A')`. Establish `h` using `trace_aeval_powMat_map A'.subtype pb.dim hm' (Q x hxm)`. Rewrite `h` using `[hm'map, hQ x hxm, ← trace_aeval_gen pb, ← hP x]`. Conclude with `h`.

Establish `hTm : Algebra.trace K L x ∈ A'` using `hT ▸ Subtype.mem _`. Establish `hAm : ∀ a : A', algebraMap K L a ∈ f.range` using `fun a => ⟨Polynomial.C a, by simp [f]⟩`. Establish `hxA : x ∈ f.range` using `⟨Q x hxm, hfQ x hxm⟩`. Use `⟨f.range, hAm, fun b hb => ⟨Q b (Finset.mem_insert_of_mem hb), hfQ b (Finset.mem_insert_of_mem hb)⟩, hxA, hTm, ?_⟩` and prove the remaining obligations. Introduce `C _ _ ev hev`.

Set `ψ` to `m'.map ev`. Establish `hψ : ψ.Monic` using `hm'.map ev`. Establish `hnat : ψ.natDegree = pb.dim`. Rewrite using `[hm'.natDegree_map ev, ← hm'.natDegree_map A'.subtype, hm'map, pb.natDegree_minpoly]`. Establish `hker : ∀ ρ, ψ.eval ρ = 0 → ∃ e : f.range →+* C, ∀ p, e (f.rangeRestrict p) = eval₂ ev ρ p`.

Introduce `ρ hρ`. Establish `hk : RingHom.ker f.rangeRestrict ≤ RingHom.ker (eval₂RingHom ev ρ)`. Introduce `p hp`. Establish `hp0 : f p = 0` using `congrArg Subtype.val ((RingHom.mem_ker).1 hp)`. Take `⟨q, rfl⟩` from `hdvd p hp0`.

Rewrite using `[RingHom.mem_ker, coe_eval₂RingHom, eval₂_mul, ← eval_map, show m'.map ev = ψ from rfl, hρ, zero_mul]`. Conclude with `⟨f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨_, hk⟩, fun p => RingHom.liftOfRightInverse_comp_apply _ _ _ _ p⟩`. Set `l` to `ψ.roots.toList`. Establish `hl : ∀ j : Fin l.length, ψ.eval (l.get j) = 0` using `fun j => by`. Establish `h : l.get j ∈ ψ.roots` using `Multiset.mem_toList.1 (List.get_mem _ _)`.

Conclude with `(mem_roots hψ.ne_zero).1 h`. Use `choose e he using fun j => hker (l.get j) (hl j)`. Establish `hρ : ∀ j, IsAlgebraic ℤ (l.get j)` using `fun j => isAlgebraic_of_root ψ hψ.ne_zero (fun i => by rw [coeff_map]; exact hev _) (hl j)`. Use `⟨l.length, e, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j a`.

Establish `h : (⟨algebraMap K L a, hAm a⟩ : f.range) = f.rangeRestrict (Polynomial.C a)` using `Subtype.ext (by simp [f])`. Rewrite using `[h, he, eval₂_C]`. Introduce and unpack `j ⟨_, p, rfl⟩`. Establish `h : (⟨f p, ⟨p, rfl⟩⟩ : f.range) = f.rangeRestrict p` using `rfl`. Rewrite using `[h, he, eval₂_eq_sum_range]`.

Conclude with `(Subalgebra.algebraicClosure ℤ C).sum_mem fun i _ => mul_mem (hev _) (pow_mem (hρ j) _)`. Establish `h1 : (⟨Algebra.trace K L x, hTm⟩ : A') = (aeval (powMat pb.dim m') (Q x hxm)).trace` using `Subtype.ext hT`. Establish `h2 : (⟨x, hxA⟩ : f.range) = f.rangeRestrict (Q x hxm)` using `Subtype.ext (hfQ x hxm).symm`. Rewrite using `[h1, ← trace_aeval_powMat_map ev pb.dim hm', trace_aeval_matrix, charpoly_powMat hψ _ hnat, h2]`. Simplify using `only [he, ← eval_map]`.

Express the relevant statement in the definitionally equal form `(ψ.roots.map fun z => eval z ((Q x hxm).map ev)).sum = _`. Rewrite using `[← Multiset.coe_toList ψ.roots, Multiset.map_coe, Multiset.sum_coe]`. Conclude with `(Fin.sum_univ_fun_getElem l fun z => eval z ((Q x hxm).map ev)).symm`.
-/
theorem exists_spec {K L : Type} [Field K] [Field L] [CharZero K] [Algebra K L]
    [FiniteDimensional K L] (B₀ : Finset L) (x : L) :
    ∃ B' : Finset K, ∀ A' : Subring K, (↑B' : Set K) ⊆ A' →
      ∃ (A : Subring L) (hA : ∀ a : A', algebraMap K L a ∈ A) (_ : (↑B₀ : Set L) ⊆ A)
        (hx : x ∈ A) (ht : Algebra.trace K L x ∈ A'),
        ∀ (C : Type) [Field C] [IsAlgClosed C] (ev : A' →+* C), (∀ a, IsAlgebraic ℤ (ev a)) →
          ∃ (n : ℕ) (ev' : Fin n → (A →+* C)),
            (∀ j (a : A'), ev' j ⟨algebraMap K L a, hA a⟩ = ev a) ∧
            (∀ j a, IsAlgebraic ℤ (ev' j a)) ∧ ev ⟨_, ht⟩ = ∑ j, ev' j ⟨x, hx⟩ := by
  classical
  obtain ⟨pb⟩ : Nonempty (PowerBasis K L) := ⟨Field.powerBasisOfFiniteOfSeparable K L⟩
  have hint : IsIntegral K pb.gen := pb.isIntegral_gen
  choose P hP using fun b : L => pb.exists_eq_aeval' b
  refine ⟨(minpoly K pb.gen).coeffs ∪ (insert x B₀).biUnion fun b => (P b).coeffs,
    fun A' hB' => ?_⟩
  have hmc : (↑(minpoly K pb.gen).coeffs : Set K) ⊆ A' := fun c hc =>
    hB' (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hc)))
  have hPc : ∀ b ∈ insert x B₀, (↑(P b).coeffs : Set K) ⊆ A' := fun b hb c hc =>
    hB' (Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨b, hb, Finset.mem_coe.1 hc⟩)))
  let m' : A'[X] := (minpoly K pb.gen).toSubring A' hmc
  have hm'map : m'.map A'.subtype = minpoly K pb.gen := map_toSubring _ _ _
  have hm' : m'.Monic := (monic_toSubring _ _ _).2 (minpoly.monic hint)
  let Q : ∀ b ∈ insert x B₀, A'[X] := fun b hb => (P b).toSubring A' (hPc b hb)
  have hQ : ∀ b hb, (Q b hb).map A'.subtype = P b := fun b hb => map_toSubring _ _ _
  let f : A'[X] →+* L := eval₂RingHom ((algebraMap K L).comp A'.subtype) pb.gen
  have hf : ∀ p : A'[X], f p = aeval pb.gen (p.map A'.subtype) := fun p => by
    rw [aeval_def, eval₂_map]; rfl
  have hfQ : ∀ b hb, f (Q b hb) = b := fun b hb => by rw [hf, hQ b hb, ← hP b]
  have hdvd : ∀ p : A'[X], f p = 0 → m' ∣ p := by
    intro p hp
    rw [hf] at hp
    have h2 : minpoly K pb.gen ∣ p.map A'.subtype := minpoly.dvd K pb.gen hp
    have h3 : (p %ₘ m').map A'.subtype = 0 := by
      rw [map_modByMonic _ hm', hm'map]
      exact (modByMonic_eq_zero_iff_dvd (minpoly.monic hint)).2 h2
    have h4 : p %ₘ m' = 0 :=
      map_injective _ Subtype.val_injective (by rw [h3, Polynomial.map_zero])
    exact (modByMonic_eq_zero_iff_dvd hm').1 h4
  have hxm := Finset.mem_insert_self x B₀
  have hT : Algebra.trace K L x = ((aeval (powMat pb.dim m') (Q x hxm)).trace : A') := by
    have h := trace_aeval_powMat_map A'.subtype pb.dim hm' (Q x hxm)
    rw [hm'map, hQ x hxm, ← trace_aeval_gen pb, ← hP x] at h
    exact h
  have hTm : Algebra.trace K L x ∈ A' := hT ▸ Subtype.mem _
  have hAm : ∀ a : A', algebraMap K L a ∈ f.range := fun a =>
    ⟨Polynomial.C a, by simp [f]⟩
  have hxA : x ∈ f.range := ⟨Q x hxm, hfQ x hxm⟩
  refine ⟨f.range, hAm, fun b hb => ⟨Q b (Finset.mem_insert_of_mem hb), hfQ b (Finset.mem_insert_of_mem hb)⟩, hxA, hTm, ?_⟩
  intro C _ _ ev hev
  let ψ := m'.map ev
  have hψ : ψ.Monic := hm'.map ev
  have hnat : ψ.natDegree = pb.dim := by
    rw [hm'.natDegree_map ev, ← hm'.natDegree_map A'.subtype, hm'map, pb.natDegree_minpoly]
  have hker : ∀ ρ, ψ.eval ρ = 0 →
      ∃ e : f.range →+* C, ∀ p, e (f.rangeRestrict p) = eval₂ ev ρ p := by
    intro ρ hρ
    have hk : RingHom.ker f.rangeRestrict ≤ RingHom.ker (eval₂RingHom ev ρ) := by
      intro p hp
      have hp0 : f p = 0 := congrArg Subtype.val ((RingHom.mem_ker).1 hp)
      obtain ⟨q, rfl⟩ := hdvd p hp0
      rw [RingHom.mem_ker, coe_eval₂RingHom, eval₂_mul, ← eval_map, show m'.map ev = ψ from rfl,
        hρ, zero_mul]
    exact ⟨f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨_, hk⟩, fun p =>
      RingHom.liftOfRightInverse_comp_apply _ _ _ _ p⟩
  let l := ψ.roots.toList
  have hl : ∀ j : Fin l.length, ψ.eval (l.get j) = 0 := fun j => by
    have h : l.get j ∈ ψ.roots := Multiset.mem_toList.1 (List.get_mem _ _)
    exact (mem_roots hψ.ne_zero).1 h
  choose e he using fun j => hker (l.get j) (hl j)
  have hρ : ∀ j, IsAlgebraic ℤ (l.get j) := fun j =>
    isAlgebraic_of_root ψ hψ.ne_zero (fun i => by rw [coeff_map]; exact hev _) (hl j)
  refine ⟨l.length, e, ?_, ?_, ?_⟩
  · intro j a
    have h : (⟨algebraMap K L a, hAm a⟩ : f.range) = f.rangeRestrict (Polynomial.C a) :=
      Subtype.ext (by simp [f])
    rw [h, he, eval₂_C]
  · rintro j ⟨_, p, rfl⟩
    have h : (⟨f p, ⟨p, rfl⟩⟩ : f.range) = f.rangeRestrict p := rfl
    rw [h, he, eval₂_eq_sum_range]
    exact (Subalgebra.algebraicClosure ℤ C).sum_mem fun i _ =>
      mul_mem (hev _) (pow_mem (hρ j) _)
  · have h1 : (⟨Algebra.trace K L x, hTm⟩ : A') = (aeval (powMat pb.dim m') (Q x hxm)).trace :=
      Subtype.ext hT
    have h2 : (⟨x, hxA⟩ : f.range) = f.rangeRestrict (Q x hxm) := Subtype.ext (hfQ x hxm).symm
    rw [h1, ← trace_aeval_powMat_map ev pb.dim hm', trace_aeval_matrix,
      charpoly_powMat hψ _ hnat, h2]
    simp only [he, ← eval_map]
    change (ψ.roots.map fun z => eval z ((Q x hxm).map ev)).sum = _
    rw [← Multiset.coe_toList ψ.roots, Multiset.map_coe, Multiset.sum_coe]
    exact (Fin.sum_univ_fun_getElem l fun z => eval z ((Q x hxm).map ev)).symm

/- English proof (translation)
Introduce `K L _ _ _ φ B₀ x hfd`. Use `letI := φ.toAlgebra`. Use `haveI : FiniteDimensional K L := hfd`. Conclude with `exists_spec B₀ x`.
-/
theorem trace_specialisation : ∀ (K L : Type) [Field K] [Field L] [CharZero K] (φ : K →+* L) (B₀ : Finset L) (x : L), (letI := φ.toAlgebra; FiniteDimensional K L) → ∃ B' : Finset K, ∀ A' : Subring K, (↑B' : Set K) ⊆ A' → ∃ (A : Subring L) (hA : ∀ a : A', φ a ∈ A) (_ : (↑B₀ : Set L) ⊆ A) (hx : x ∈ A) (ht : (letI := φ.toAlgebra; Algebra.trace K L x) ∈ A'), ∀ (C : Type) [Field C] [IsAlgClosed C] (ev : A' →+* C), (∀ a, IsAlgebraic ℤ (ev a)) → ∃ (n : ℕ) (ev' : Fin n → (A →+* C)), (∀ j (a : A'), ev' j ⟨φ a, hA a⟩ = ev a) ∧ (∀ j a, IsAlgebraic ℤ (ev' j a)) ∧ ev ⟨_, ht⟩ = ∑ j, ev' j ⟨x, hx⟩ := by
  intro K L _ _ _ φ B₀ x hfd
  letI := φ.toAlgebra
  haveI : FiniteDimensional K L := hfd
  exact exists_spec B₀ x

end GlobalTheory.CompanionTheory.TraceSpec
