import Mathlib

namespace GlobalTheory.CardQuotientPow

open Module Submodule

/- English proof (translation)
Establish `key : ∀ I : Ideal R, Nat.card (R ⧸ I) = I.toAddSubgroup.index` using `fun I => rfl`. Proceed by induction on `k with`. Consider the case `zero => rw [key]`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Rewrite using `[pow_succ (Nat.card (R ⧸ Ideal.span {p})) k, ← ih, key, key, key]`. Establish `hle : (Ideal.span {p ^ (k+1)}).toAddSubgroup ≤ (Ideal.span {p ^ k}).toAddSubgroup`. Introduce `x hx`. Conclude with `Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow p (Nat.le_succ k)) hx`. Rewrite using `[← AddSubgroup.relIndex_mul_index hle, mul_comm]`.

Use `congr 1`. Set `f : R →+ R` to `AddMonoidHom.mulLeft (p ^ k)`. Establish `hr : f.range = (Ideal.span {p ^ k}).toAddSubgroup`. Use extensionality with `x`. Simplify using `only [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton', f, AddMonoidHom.coe_mulLeft]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨y, mul_comm _ _⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨y, mul_comm _ _⟩`.

Establish `hc : (Ideal.span {p ^ (k+1)}).toAddSubgroup.comap f = (Ideal.span {p}).toAddSubgroup`. Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton, f, AddMonoidHom.coe_mulLeft]`. Rewrite using `[pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)]`. Rewrite using `[← hr, ← AddSubgroup.index_comap, hc]`.
-/
theorem card_quot_pow {R : Type} [CommRing R] [IsDomain R] {p : R} (hp : Irreducible p) (k : ℕ) :
    Nat.card (R ⧸ Ideal.span {p ^ k}) = Nat.card (R ⧸ Ideal.span {p}) ^ k := by
  have key : ∀ I : Ideal R, Nat.card (R ⧸ I) = I.toAddSubgroup.index := fun I => rfl
  induction k with
  | zero => rw [key]; simp
  | succ k ih =>
    rw [pow_succ (Nat.card (R ⧸ Ideal.span {p})) k, ← ih, key, key, key]
    have hle : (Ideal.span {p ^ (k+1)}).toAddSubgroup ≤ (Ideal.span {p ^ k}).toAddSubgroup := by
      intro x hx
      exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow p (Nat.le_succ k)) hx
    rw [← AddSubgroup.relIndex_mul_index hle, mul_comm]
    congr 1
    let f : R →+ R := AddMonoidHom.mulLeft (p ^ k)
    have hr : f.range = (Ideal.span {p ^ k}).toAddSubgroup := by
      ext x
      simp only [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton', f,
        AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩
      · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩
    have hc : (Ideal.span {p ^ (k+1)}).toAddSubgroup.comap f = (Ideal.span {p}).toAddSubgroup := by
      ext x
      simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton, f,
        AddMonoidHom.coe_mulLeft]
      rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)]
    rw [← hr, ← AddSubgroup.index_comap, hc]

/- English proof (translation)
Use `set N := LinearMap.range φ with hN`. Set `e : M ≃ₗ[R] N` to `LinearEquiv.ofInjective φ hφ`. Establish `h : finrank R N = finrank R M` using `e.finrank_eq.symm`. Set `a` to `smithNormalFormCoeffs b h`. Set `b'` to `smithNormalFormTopBasis b h`.

Set `ab` to `smithNormalFormBotBasis b h`. Establish `ab_eq` using `smithNormalFormBotBasis_def b h`. Set `f : M →ₗ[R] M` to `N.subtype ∘ₗ (b'.equiv ab (Equiv.refl _) : M →ₗ[R] N)`. Establish `ha : ∀ i, f (b' i) = a i • b' i`. Introduce `i`.

Simplify using `only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, b'.equiv_apply, Equiv.refl_apply, Submodule.subtype_apply]`. Conclude with `ab_eq i`. Establish `hdetf : LinearMap.det f = ∏ i, a i`. Rewrite using `[← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]`. Use `congr 1`.

Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]`. Distinguish the cases in `hij : i = j`. Rewrite using `[hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]`. Rewrite using `[Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]`.

Establish `hφf : Associated (LinearMap.det φ) (LinearMap.det f)`. Establish `: φ = N.subtype ∘ₗ (e : M →ₗ[R] N)` using `by ext x; rfl`. Rewrite using `[this]`. Conclude with `LinearMap.associated_det_comp_equiv _ _ _`. Use `choose k hk using fun i => IsDiscreteValuationRing.associated_pow_irreducible (smithNormalFormCoeffs_ne_zero b h i) hp`.

Use `⟨∑ i, k i, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.prod_pow_eq_pow_sum]`. Use `hφf.trans ?_` and prove the remaining obligations. Rewrite using `[hdetf]`. Conclude with `Associated.prod _ _ _ fun i _ => hk i`.

Rewrite using `[Nat.card_congr (quotientEquivPiSpan N b h).toEquiv, Nat.card_pi, ← Finset.prod_pow_eq_pow_sum]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← card_quot_pow hp, Ideal.span_singleton_eq_span_singleton.mpr (hk i)]`.
-/
theorem main {R M ι : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] [Fintype ι] (b : Module.Basis ι R M) {p : R}
    (hp : Irreducible p) (φ : M →ₗ[R] M) (hφ : Function.Injective φ) :
    ∃ m : ℕ, Associated (LinearMap.det φ) (p ^ m) ∧
      Nat.card (M ⧸ LinearMap.range φ) = Nat.card (R ⧸ Ideal.span {p}) ^ m := by
  classical
  set N := LinearMap.range φ with hN
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective φ hφ
  have h : finrank R N = finrank R M := e.finrank_eq.symm
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  have ab_eq := smithNormalFormBotBasis_def b h
  let f : M →ₗ[R] M := N.subtype ∘ₗ (b'.equiv ab (Equiv.refl _) : M →ₗ[R] N)
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, b'.equiv_apply, Equiv.refl_apply,
      Submodule.subtype_apply]
    exact ab_eq i
  have hdetf : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1; ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
      mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hφf : Associated (LinearMap.det φ) (LinearMap.det f) := by
    have : φ = N.subtype ∘ₗ (e : M →ₗ[R] N) := by ext x; rfl
    rw [this]
    exact LinearMap.associated_det_comp_equiv _ _ _
  choose k hk using fun i =>
    IsDiscreteValuationRing.associated_pow_irreducible (smithNormalFormCoeffs_ne_zero b h i) hp
  refine ⟨∑ i, k i, ?_, ?_⟩
  · rw [← Finset.prod_pow_eq_pow_sum]
    refine hφf.trans ?_
    rw [hdetf]
    exact Associated.prod _ _ _ fun i _ => hk i
  · rw [Nat.card_congr (quotientEquivPiSpan N b h).toEquiv, Nat.card_pi,
      ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← card_quot_pow hp, Ideal.span_singleton_eq_span_singleton.mpr (hk i)]

end GlobalTheory.CardQuotientPow
