import Mathlib

namespace GroundTheory.Automorphic

open Polynomial Module Matrix

section AlgClosed

variable {K W : Type*} [Field K] [IsAlgClosed K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

/- English proof (translation)
Use `set n := finrank K W`. Establish `hdeg : f.charpoly.natDegree = n` using `LinearMap.charpoly_natDegree f`. Establish `hnd` using `nodup_roots hf`. Set `s : Finset K` to `⟨f.charpoly.roots, hnd⟩`. Establish `hs : s.card = n`.

Express the relevant statement in the definitionally equal form `f.charpoly.roots.card = n`. Rewrite using `[IsAlgClosed.card_roots_eq_natDegree, hdeg]`. Set `e : Fin n ≃ s` to `(s.equivFin.trans (finCongr hs)).symm`. Set `μ : Fin n → K` to `fun j => (e j : K)`. Establish `hμ : Function.Injective μ` using `Subtype.coe_injective.comp e.injective`.

Establish `hroot : ∀ j, f.charpoly.IsRoot (μ j)` using `fun j => (mem_roots hf.ne_zero).1 (e j).2`. Establish `hev : ∀ j, f.HasEigenvalue (μ j)` using `fun j => (Module.End.hasEigenvalue_iff_isRoot_charpoly f _).2 (hroot j)`. Use `choose w hw using fun j => (hev j).exists_hasEigenvector`. Establish `hli : LinearIndependent K w` using `f.eigenvectors_linearIndependent' μ hμ w hw`. Establish `hpow : ∀ (k : ℕ) j, (f ^ k) (w j) = μ j ^ k • w j`.

Introduce `k j`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ih, map_smul, (hw j).apply_eq_smul, smul_smul, pow_succ]`.

Use `⟨∑ j, w j, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Establish `hsum : ∀ j, ∑ k : Fin n, c k * μ j ^ (k : ℕ) = 0`. Establish `h2 : ∑ j, (∑ k : Fin n, c k * μ j ^ (k : ℕ)) • w j = 0`.

Rewrite using `[← hc]`. Simplify using `only [map_sum, hpow, Finset.smul_sum, smul_smul, Finset.sum_smul]`. Conclude with `Finset.sum_comm`. Conclude with `fun j => (Fintype.linearIndependent_iff.1 hli) _ h2 j`. Establish `hV : Matrix.vandermonde μ *ᵥ c = 0`.

Use extensionality with `j`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply]`. Rewrite using `[← hsum j]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Establish `hdet : (Matrix.vandermonde μ).det ≠ 0` using `Matrix.det_vandermonde_ne_zero_iff.2 hμ`.

Conclude with `congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hV)`.
-/
theorem exists_linearIndependent_pow_apply_of_isAlgClosed (f : Module.End K W)
    (hf : f.charpoly.Separable) :
    ∃ w : W, LinearIndependent K (fun k : Fin (finrank K W) => (f ^ (k : ℕ)) w) := by
  set n := finrank K W
  have hdeg : f.charpoly.natDegree = n := LinearMap.charpoly_natDegree f
  have hnd := nodup_roots hf
  let s : Finset K := ⟨f.charpoly.roots, hnd⟩
  have hs : s.card = n := by
    change f.charpoly.roots.card = n
    rw [IsAlgClosed.card_roots_eq_natDegree, hdeg]
  let e : Fin n ≃ s := (s.equivFin.trans (finCongr hs)).symm
  let μ : Fin n → K := fun j => (e j : K)
  have hμ : Function.Injective μ := Subtype.coe_injective.comp e.injective
  have hroot : ∀ j, f.charpoly.IsRoot (μ j) := fun j =>
    (mem_roots hf.ne_zero).1 (e j).2
  have hev : ∀ j, f.HasEigenvalue (μ j) := fun j =>
    (Module.End.hasEigenvalue_iff_isRoot_charpoly f _).2 (hroot j)
  choose w hw using fun j => (hev j).exists_hasEigenvector
  have hli : LinearIndependent K w := f.eigenvectors_linearIndependent' μ hμ w hw
  have hpow : ∀ (k : ℕ) j, (f ^ k) (w j) = μ j ^ k • w j := by
    intro k j
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, (hw j).apply_eq_smul, smul_smul,
        pow_succ]
  refine ⟨∑ j, w j, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hsum : ∀ j, ∑ k : Fin n, c k * μ j ^ (k : ℕ) = 0 := by
    have h2 : ∑ j, (∑ k : Fin n, c k * μ j ^ (k : ℕ)) • w j = 0 := by
      rw [← hc]
      simp only [map_sum, hpow, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact fun j => (Fintype.linearIndependent_iff.1 hli) _ h2 j
  have hV : Matrix.vandermonde μ *ᵥ c = 0 := by
    ext j
    simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply]
    rw [← hsum j]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hdet : (Matrix.vandermonde μ).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.2 hμ
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hV)

end AlgClosed

section Krylov

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

def krylov (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i k => (M ^ (k : ℕ) *ᵥ v) i

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem krylov_col (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (k : Fin n) :
    (krylov M v).col k = M ^ (k : ℕ) *ᵥ v := rfl

/- English proof (translation)
Use extensionality with `i k`. Simplify using `only [krylov, Matrix.map_apply, Matrix.of_apply]`. Rewrite using `[RingHom.map_mulVec]`. Use `congr 2`. Conclude with `(map_pow φ.mapMatrix M k)`.
-/
theorem map_krylov (φ : R →+* S) (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    (krylov M v).map φ = krylov (M.map φ) (φ ∘ v) := by
  ext i k
  simp only [krylov, Matrix.map_apply, Matrix.of_apply]
  rw [RingHom.map_mulVec]
  congr 2
  exact (map_pow φ.mapMatrix M k)

variable {E : Type*} [Field E]

/- English proof (translation)
Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, map_krylov]`.
-/
theorem map_det_krylov_C_X {T : Type*} [CommRing T] (M : Matrix (Fin n) (Fin n) E)
    (ψ : MvPolynomial (Fin n) E →+* T) :
    ψ (krylov (M.map MvPolynomial.C) (fun i => MvPolynomial.X i)).det =
      (krylov ((M.map MvPolynomial.C).map ψ) (ψ ∘ fun i => MvPolynomial.X i)).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_krylov]

variable [Infinite E]

/- English proof (translation)
Use `set D : MvPolynomial (Fin n) E := (krylov (M.map MvPolynomial.C) (fun i => MvPolynomial.X i)).det with hD`. Establish `hD0 : D ≠ 0`. Introduce `h0`. Use `map_det_krylov_C_X M (MvPolynomial.eval₂Hom φ w)` as an intermediate fact. Rewrite `this` using `[← hD]`.

Rewrite `this` using `[h0, map_zero]`. Apply `hw` to reduce the goal to its premises. Rewrite using `[this]`. Use `congr 2`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Use extensionality with `i`. Simplify using the standard rewrite rules. Assume the negation of the conclusion as `hne`. Use `push Not at hne`.

Apply `hD0` to reduce the goal to its premises. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`. Rewrite using `[map_zero]`. Use `map_det_krylov_C_X M (MvPolynomial.eval x)` as an intermediate fact.

Rewrite `this` using `[← hD]`. Rewrite using `[this]`. Use `hne x using 3` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem exists_det_krylov_ne_zero {L : Type*} [Field L] (φ : E →+* L)
    (M : Matrix (Fin n) (Fin n) E) (w : Fin n → L) (hw : (krylov (M.map φ) w).det ≠ 0) :
    ∃ v : Fin n → E, (krylov M v).det ≠ 0 := by
  classical
  set D : MvPolynomial (Fin n) E :=
    (krylov (M.map MvPolynomial.C) (fun i => MvPolynomial.X i)).det with hD
  have hD0 : D ≠ 0 := by
    intro h0
    have := map_det_krylov_C_X M (MvPolynomial.eval₂Hom φ w)
    rw [← hD] at this
    rw [h0, map_zero] at this
    apply hw
    rw [this]
    congr 2
    · ext i j; simp
    · ext i; simp
  by_contra hne
  push Not at hne
  apply hD0
  apply MvPolynomial.funext
  intro x
  rw [map_zero]
  have := map_det_krylov_C_X M (MvPolynomial.eval x)
  rw [← hD] at this
  rw [this]
  convert hne x using 3
  · ext i j; simp
  · ext i; simp

end Krylov

section Cyclic

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]

/- English proof (translation)
Use `set n := finrank E V`. Set `b : Basis (Fin n) E V` to `Module.finBasis E V`. Use `set M := LinearMap.toMatrix b b f with hM`. Set `φ : E →+* AlgebraicClosure E` to `algebraMap E (AlgebraicClosure E)`. Establish `hchar : (Matrix.toLin' (M.map φ)).charpoly = f.charpoly.map φ`.

Rewrite using `[Matrix.charpoly_toLin', Matrix.charpoly_map, hM, LinearMap.charpoly_toMatrix]`. Establish `hsep : (Matrix.toLin' (M.map φ)).charpoly.Separable`. Rewrite using `[hchar]`. Conclude with `hf.map`. Take `⟨w, hw⟩` from `exists_linearIndependent_pow_apply_of_isAlgClosed _ hsep`.

Rewrite `hw` using `[Module.finrank_fin_fun]`. Establish `hw' : (krylov (M.map φ) w).det ≠ 0`. Rewrite using `[← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]`. Establish `hcol : (krylov (M.map φ) w).col = fun k : Fin n => (Matrix.toLin' (M.map φ) ^ (k : ℕ)) w` using `by ext1 k`. Rewrite using `[krylov_col, ← Matrix.toLin'_pow, Matrix.toLin'_apply]`.

Rewrite using `[hcol]`. Conclude with `hw`. Take `⟨v₀, hv₀⟩` from `exists_det_krylov_ne_zero φ M w hw'`. Establish `hli : LinearIndependent E (krylov M v₀).col`. Rewrite using `[Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]`.

Conclude with `hv₀`. Use `⟨b.equivFun.symm v₀, ?_⟩` and prove the remaining obligations. Establish `key : (fun k : Fin n => (f ^ (k : ℕ)) (b.equivFun.symm v₀)) = b.equivFun.symm ∘ (krylov M v₀).col` using `by ext1 k`. Simplify using `only [Function.comp_apply, krylov_col]`. Apply `b.equivFun.injective` to reduce the goal to its premises.

Rewrite using `[LinearEquiv.apply_symm_apply, Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr b b, hM, LinearMap.toMatrix_pow]`. Use `congr 1`. Rewrite using `[← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`. Rewrite using `[key]`. Conclude with `hli.map' _ (LinearEquiv.ker _)`.
-/
theorem exists_linearIndependent_pow_apply [Infinite E] (f : Module.End E V)
    (hf : f.charpoly.Separable) :
    ∃ v : V, LinearIndependent E (fun k : Fin (finrank E V) => (f ^ (k : ℕ)) v) := by
  classical
  set n := finrank E V
  let b : Basis (Fin n) E V := Module.finBasis E V
  set M := LinearMap.toMatrix b b f with hM
  let φ : E →+* AlgebraicClosure E := algebraMap E (AlgebraicClosure E)
  have hchar : (Matrix.toLin' (M.map φ)).charpoly = f.charpoly.map φ := by
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map, hM, LinearMap.charpoly_toMatrix]
  have hsep : (Matrix.toLin' (M.map φ)).charpoly.Separable := by
    rw [hchar]; exact hf.map
  obtain ⟨w, hw⟩ := exists_linearIndependent_pow_apply_of_isAlgClosed _ hsep
  rw [Module.finrank_fin_fun] at hw
  have hw' : (krylov (M.map φ) w).det ≠ 0 := by
    rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
      ← Matrix.linearIndependent_cols_iff_isUnit]
    have hcol : (krylov (M.map φ) w).col = fun k : Fin n => (Matrix.toLin' (M.map φ) ^ (k : ℕ)) w := by
      ext1 k
      rw [krylov_col, ← Matrix.toLin'_pow, Matrix.toLin'_apply]
    rw [hcol]
    exact hw
  obtain ⟨v₀, hv₀⟩ := exists_det_krylov_ne_zero φ M w hw'
  have hli : LinearIndependent E (krylov M v₀).col := by
    rw [Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero]
    exact hv₀
  refine ⟨b.equivFun.symm v₀, ?_⟩
  have key : (fun k : Fin n => (f ^ (k : ℕ)) (b.equivFun.symm v₀)) =
      b.equivFun.symm ∘ (krylov M v₀).col := by
    ext1 k
    simp only [Function.comp_apply, krylov_col]
    apply b.equivFun.injective
    rw [LinearEquiv.apply_symm_apply, Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr b b,
      hM, LinearMap.toMatrix_pow]
    congr 1
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [key]
  exact hli.map' _ (LinearEquiv.ker _)

end Cyclic

section Consequences

variable {E V V' : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [AddCommGroup V'] [Module E V'] [FiniteDimensional E V']

def IsCyclicVector (f : Module.End E V) (v : V) : Prop :=
  LinearIndependent E (fun k : Fin (finrank E V) => (f ^ (k : ℕ)) v)

/- English proof (translation)
The claim follows from `exists_linearIndependent_pow_apply f hf`.
-/
theorem exists_isCyclicVector [Infinite E] (f : Module.End E V) (hf : f.charpoly.Separable) :
    ∃ v, IsCyclicVector f v :=
  exists_linearIndependent_pow_apply f hf

variable {f : Module.End E V} {v : V}

noncomputable def cyclicBasis (hv : IsCyclicVector f v) : Basis (Fin (finrank E V)) E V :=
  basisOfLinearIndependentOfCardEqFinrank' _ hv (Fintype.card_fin _)

/- English proof (translation)
The claim follows from `congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' (K := E) _ hv _) k`.
-/
theorem cyclicBasis_apply (hv : IsCyclicVector f v) (k : Fin (finrank E V)) :
    cyclicBasis hv k = (f ^ (k : ℕ)) v :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' (K := E) _ hv _) k

omit [FiniteDimensional E V] in
/- English proof (translation)
Simplify using `[Module.algebraMap_end_apply]`.
-/
theorem aeval_C_mul_X_pow_apply (f : Module.End E V) (a : E) (k : ℕ) (x : V) :
    aeval f (C a * X ^ k) x = a • (f ^ k) x := by
  simp [Module.algebraMap_end_apply]

/- English proof (translation)
Use `⟨∑ k : Fin (finrank E V), C ((cyclicBasis hv).repr x k) * X ^ (k : ℕ), ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← (cyclicBasis hv).sum_repr x]`. Rewrite using `[map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[aeval_C_mul_X_pow_apply, cyclicBasis_apply]`.
-/
theorem IsCyclicVector.exists_aeval_apply_eq (hv : IsCyclicVector f v) (x : V) :
    ∃ p : E[X], aeval f p v = x := by
  refine ⟨∑ k : Fin (finrank E V), C ((cyclicBasis hv).repr x k) * X ^ (k : ℕ), ?_⟩
  conv_rhs => rw [← (cyclicBasis hv).sum_repr x]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [aeval_C_mul_X_pow_apply, cyclicBasis_apply]

/- English proof (translation)
Take `⟨p, hp⟩` from `hv.exists_aeval_apply_eq (g v)`. Use `⟨p, (cyclicBasis hv).ext fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[cyclicBasis_apply, ← Module.End.mul_apply, ← ((hg.pow_left (k : ℕ)).eq), Module.End.mul_apply, ← hp, ← Module.End.mul_apply, ← Module.End.mul_apply, ← aeval_X_pow (R := E) f, ← map_mul, ← map_mul, mul_comm]`.
-/
theorem IsCyclicVector.exists_eq_aeval (hv : IsCyclicVector f v) {g : Module.End E V}
    (hg : Commute f g) : ∃ p : E[X], g = aeval f p := by
  obtain ⟨p, hp⟩ := hv.exists_aeval_apply_eq (g v)
  refine ⟨p, (cyclicBasis hv).ext fun k => ?_⟩
  rw [cyclicBasis_apply, ← Module.End.mul_apply, ← ((hg.pow_left (k : ℕ)).eq), Module.End.mul_apply,
    ← hp, ← Module.End.mul_apply, ← Module.End.mul_apply, ← aeval_X_pow (R := E) f, ← map_mul,
    ← map_mul, mul_comm]

/- English proof (translation)
Take `⟨p, rfl⟩` from `hv.exists_eq_aeval hg`. Take `⟨q, rfl⟩` from `hv.exists_eq_aeval hg'`. Conclude with `(Commute.all p q).map (aeval f)`.
-/
theorem IsCyclicVector.commute_of_commute (hv : IsCyclicVector f v) {g g' : Module.End E V}
    (hg : Commute f g) (hg' : Commute f g') : Commute g g' := by
  obtain ⟨p, rfl⟩ := hv.exists_eq_aeval hg
  obtain ⟨q, rfl⟩ := hv.exists_eq_aeval hg'
  exact (Commute.all p q).map (aeval f)

/- English proof (translation)
Establish `hmon` using `LinearMap.charpoly_monic f`. Use `conv_lhs => rw [← modByMonic_add_div p f.charpoly]`. Rewrite using `[map_add, map_mul, LinearMap.aeval_self_charpoly, zero_mul, add_zero]`. Distinguish the cases in `h0 : p %ₘ f.charpoly = 0`. Simplify using `[h0]`.

Establish `hdeg : (p %ₘ f.charpoly).natDegree < finrank E V`. Rewrite using `[Polynomial.natDegree_lt_iff_degree_lt h0, ← LinearMap.charpoly_natDegree f, ← degree_eq_natDegree hmon.ne_zero]`. Conclude with `degree_modByMonic_lt p hmon`. Rewrite using `[aeval_eq_sum_range' hdeg, LinearMap.sum_apply, Finset.sum_range (fun i => ((p %ₘ f.charpoly).coeff i • f ^ i) v)]`. Both sides reduce to the same expression.
-/
theorem aeval_apply_eq_sum_modByMonic (f : Module.End E V) (v : V) (p : E[X]) :
    aeval f p v = ∑ k : Fin (finrank E V), (p %ₘ f.charpoly).coeff k • (f ^ (k : ℕ)) v := by
  have hmon := LinearMap.charpoly_monic f
  conv_lhs => rw [← modByMonic_add_div p f.charpoly]
  rw [map_add, map_mul, LinearMap.aeval_self_charpoly, zero_mul, add_zero]
  by_cases h0 : p %ₘ f.charpoly = 0
  · simp [h0]
  have hdeg : (p %ₘ f.charpoly).natDegree < finrank E V := by
    rw [Polynomial.natDegree_lt_iff_degree_lt h0, ← LinearMap.charpoly_natDegree f,
      ← degree_eq_natDegree hmon.ne_zero]
    exact degree_modByMonic_lt p hmon
  rw [aeval_eq_sum_range' hdeg, LinearMap.sum_apply,
    Finset.sum_range (fun i => ((p %ₘ f.charpoly).coeff i • f ^ i) v)]
  rfl

/- English proof (translation)
Establish `hdim : finrank E V = finrank E V'`. Rewrite using `[← LinearMap.charpoly_natDegree f, ← LinearMap.charpoly_natDegree f', hch]`. Set `e : V ≃ₗ[E] V'` to `(cyclicBasis hv).equiv (cyclicBasis hv') (finCongr hdim)`. Establish `he : ∀ k : Fin (finrank E V), e ((f ^ (k : ℕ)) v) = (f' ^ (k : ℕ)) v'`. Introduce `k`.

Rewrite using `[← cyclicBasis_apply hv, Basis.equiv_apply, cyclicBasis_apply]`. Both sides reduce to the same expression. Establish `hp : ∀ p : E[X], e (aeval f p v) = aeval f' p v'`. Introduce `p`. Rewrite using `[aeval_apply_eq_sum_modByMonic, aeval_apply_eq_sum_modByMonic, map_sum, ← hch]`.

Rewrite using `[← (finCongr hdim).sum_comp]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, he]`. Both sides reduce to the same expression. Use `⟨e, fun x => ?_⟩` and prove the remaining obligations.

Take `⟨p, rfl⟩` from `hv.exists_aeval_apply_eq x`. Establish `h1 : f (aeval f p v) = aeval f (X * p) v`. Rewrite using `[map_mul, aeval_X, Module.End.mul_apply]`. Rewrite using `[h1, hp, hp, map_mul, aeval_X, Module.End.mul_apply]`.
-/
theorem IsCyclicVector.exists_conj {f' : Module.End E V'} {v' : V'} (hv : IsCyclicVector f v)
    (hv' : IsCyclicVector f' v') (hch : f.charpoly = f'.charpoly) :
    ∃ e : V ≃ₗ[E] V', ∀ x, e (f x) = f' (e x) := by
  have hdim : finrank E V = finrank E V' := by
    rw [← LinearMap.charpoly_natDegree f, ← LinearMap.charpoly_natDegree f', hch]
  let e : V ≃ₗ[E] V' := (cyclicBasis hv).equiv (cyclicBasis hv') (finCongr hdim)
  have he : ∀ k : Fin (finrank E V), e ((f ^ (k : ℕ)) v) = (f' ^ (k : ℕ)) v' := by
    intro k
    rw [← cyclicBasis_apply hv, Basis.equiv_apply, cyclicBasis_apply]
    rfl
  have hp : ∀ p : E[X], e (aeval f p v) = aeval f' p v' := by
    intro p
    rw [aeval_apply_eq_sum_modByMonic, aeval_apply_eq_sum_modByMonic, map_sum, ← hch]
    rw [← (finCongr hdim).sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, he]
    rfl
  refine ⟨e, fun x => ?_⟩
  obtain ⟨p, rfl⟩ := hv.exists_aeval_apply_eq x
  have h1 : f (aeval f p v) = aeval f (X * p) v := by
    rw [map_mul, aeval_X, Module.End.mul_apply]
  rw [h1, hp, hp, map_mul, aeval_X, Module.End.mul_apply]

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_isCyclicVector f hf`. Take `⟨v', hv'⟩` from `exists_isCyclicVector f' (hch ▸ hf)`. Conclude with `hv.exists_conj hv' hch`.
-/
theorem exists_conj_of_charpoly_eq [Infinite E] {f f' : Module.End E V}
    (hf : f.charpoly.Separable) (hch : f.charpoly = f'.charpoly) :
    ∃ e : V ≃ₗ[E] V, ∀ x, e (f x) = f' (e x) := by
  obtain ⟨v, hv⟩ := exists_isCyclicVector f hf
  obtain ⟨v', hv'⟩ := exists_isCyclicVector f' (hch ▸ hf)
  exact hv.exists_conj hv' hch

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_isCyclicVector f hf`. Conclude with `hv.commute_of_commute hg hg'`.
-/
theorem commute_of_commute_of_separable [Infinite E] {f g g' : Module.End E V}
    (hf : f.charpoly.Separable) (hg : Commute f g) (hg' : Commute f g') : Commute g g' := by
  obtain ⟨v, hv⟩ := exists_isCyclicVector f hf
  exact hv.commute_of_commute hg hg'

end Consequences

end GroundTheory.Automorphic
