import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersSqrtNegThreeModFour

open NumberField Module

namespace GlobalTheory.Mem.ImagQuad

open QuadraticZeta

/- English proof (translation)
Establish `hd' : (0 : ℚ) < d` using `by exact_mod_cast hd`. Use `set p : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.C (d : ℚ) with hp`. Establish `hpdeg : p.natDegree = 2`. Rewrite using `[hp]`. Use `compute_degree!`.

Establish `hpmon : p.Monic`. Rewrite using `[hp]`. Use `monicity!`. Establish `hroot : ∀ x : ℚ, ¬ p.IsRoot x`. Introduce `x hx`.

Simplify using `only [hp, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hx`. Use polynomial arithmetic with `[sq_nonneg x]`. Establish `hirr : Irreducible p` using `Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hpdeg]; decide) hroot`. Establish `: Fact (Irreducible p)` using `⟨hirr⟩`. Set `pb` to `AdjoinRoot.powerBasis hirr.ne_zero`.

Establish `: FiniteDimensional ℚ (AdjoinRoot p)` using `pb.finite`. Establish `: NumberField (AdjoinRoot p)` using `⟨⟩`. Use `⟨AdjoinRoot p, inferInstance, inferInstance, AdjoinRoot.root p, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pb.finrank, AdjoinRoot.powerBasis_dim, hpdeg]`. Establish `h` using `AdjoinRoot.eval₂_root p`.

Simplify using `only [hp, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C] at h`. Rewrite using `[eq_neg_iff_add_eq_zero, ← h]`. Simplify using the standard rewrite rules.
-/
theorem exists_field_sq_eq_neg (d : ℕ) (hd : 0 < d) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (r : K),
      finrank ℚ K = 2 ∧ r ^ 2 = -(d : K) := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  set p : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.C (d : ℚ) with hp
  have hpdeg : p.natDegree = 2 := by
    rw [hp]; compute_degree!
  have hpmon : p.Monic := by
    rw [hp]; monicity!
  have hroot : ∀ x : ℚ, ¬ p.IsRoot x := by
    intro x hx
    simp only [hp, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hx
    nlinarith [sq_nonneg x]
  have hirr : Irreducible p :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hpdeg]; decide) hroot
  have : Fact (Irreducible p) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  have : FiniteDimensional ℚ (AdjoinRoot p) := pb.finite
  have : NumberField (AdjoinRoot p) := ⟨⟩
  refine ⟨AdjoinRoot p, inferInstance, inferInstance, AdjoinRoot.root p, ?_, ?_⟩
  · rw [pb.finrank, AdjoinRoot.powerBasis_dim, hpdeg]
  · have h := AdjoinRoot.eval₂_root p
    simp only [hp, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at h
    rw [eq_neg_iff_add_eq_zero, ← h]
    simp

/- English proof (translation)
Introduce `d hdp hd4`. Take `⟨K, _, _, r, h2, hr⟩` from `exists_field_sq_eq_neg d hdp.pos`. Establish `hsq : Squarefree d` using `hdp.squarefree`. Take `⟨w, bar, hw, -, hspan, hemb, -⟩` from `GlobalTheory.ringOfIntegers_sqrt_neg_three_mod_four d hsq hd4 K h2 r hr`. Establish `hwr : 2 * (w : K) - 1 = r` using `by rw [hw]; ring`.

Establish `hcoe : algebraMap (𝓞 K) K (2 * w - 1) = r`. Rewrite using `[← hwr]`. Simplify using `only [map_sub, map_mul, map_one, map_ofNat]`. Establish `hw2 : (2 * w - 1) ^ 2 = -(d : 𝓞 K)`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises.

Rewrite using `[map_pow, hcoe, hr, map_neg, map_natCast]`. Take `⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 4 * k` from `⟨(d + 1) / 4, by omega⟩`. Establish `hwsq : w * w = w - (k : 𝓞 K)`. Establish `h4 : (4 : 𝓞 K) * (w * w - w + k) = 0`. Establish `: ((d : ℕ) : 𝓞 K) + 1 = 4 * (k : 𝓞 K)` using `by exact_mod_cast hk`.

Take the linear combination `hw2 - this`. Establish `h4ne : (4 : 𝓞 K) ≠ 0`. Introduce `h`. Establish `: ((4 : 𝓞 K) : K) = 0` using `by rw [h]; simp`. Evaluate the numerical expressions using `at this`.

Use `(mul_eq_zero.mp h4).resolve_left h4ne` as an intermediate fact. Take the linear combination `this`. Establish `hli : LinearIndependent ℤ ![(1 : 𝓞 K), w]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`.

Establish `hK : (s : K) + t * (w : K) = 0`. Use `congrArg (fun z : 𝓞 K => (z : K)) hst` as an intermediate fact. Simplify `this` using `[zsmul_eq_mul]`. Establish `ht : t = 0`. Assume the negation of the conclusion as `ht`.

Establish `htK : (t : K) ≠ 0` using `by exact_mod_cast ht`. Use `set q : ℚ := -(2 * s + t) / t with hqdef`. Establish `hrq : r = algebraMap ℚ K q`. Simplify using `only [hqdef, map_div₀, map_neg, map_add, map_mul, map_ofNat, map_intCast]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `(2 : K) * hK + (-(t : K)) * hwr`. Establish `hq : q ^ 2 = -(d : ℚ)`. Apply `(algebraMap ℚ K).injective` to reduce the goal to its premises. Rewrite using `[map_pow, ← hrq, hr]`. Simplify using the standard rewrite rules.

Establish `hdpos : (0 : ℚ) < d` using `by exact_mod_cast hdp.pos`. Use polynomial arithmetic with `[sq_nonneg q]`. Substitute `ht` using the available equality. Use `⟨?_, rfl⟩` and prove the remaining obligations. Establish `: (s : K) = 0` using `by simpa using hK`.

Conclude with `this` after adjusting the coercions. Establish `hsp : ⊤ ≤ Submodule.span ℤ (Set.range ![(1 : 𝓞 K), w])`. Introduce `z _`. Take `⟨a, b, rfl⟩` from `hspan z`. Establish `hr' : Set.range ![(1 : 𝓞 K), w] = {1, w}`.

Rewrite using `[Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty]`. Both sides reduce to the same expression. Rewrite using `[hr', Submodule.mem_span_pair]`. Conclude with `⟨a, b, by simp [zsmul_eq_mul]⟩`. Set `B` to `Basis.mk hli hsp`.

Establish `hB0 : B 0 = 1` using `by simp [B]`. Establish `hB1 : B 1 = w` using `by simp [B]`. Establish `hrepr : ∀ s t : ℤ, B.repr ((s : 𝓞 K) + t * w) = Finsupp.single 0 s + Finsupp.single 1 t`. Introduce `s t`. Establish `: (s : 𝓞 K) + t * w = s • B 0 + t • B 1`.

Rewrite using `[hB0, hB1]`. Simplify using `[zsmul_eq_mul]`. Rewrite using `[this, map_add, map_zsmul, map_zsmul, B.repr_self, B.repr_self]`. Simplify using the standard rewrite rules. Use `⟨K, inferInstance, inferInstance, w, ?_, h2, ?_, hw2, hspan, ?_⟩` and prove the remaining obligations.

Use `⟨fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[InfinitePlace.isComplex_iff]`. Conclude with `(hemb v.embedding).1`. Conclude with `GlobalTheory.discr_eq_neg_of_sq_eq h2 hsq hd4 hr`. Introduce `a b`.

Rewrite using `[Algebra.norm_eq_matrix_det B, Matrix.det_fin_two]`. Establish `e00 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 0 0 = a`. Rewrite using `[Algebra.leftMulMatrix_eq_repr_mul, hB0, mul_one, hrepr]`. Simplify using the standard rewrite rules. Establish `e10 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 1 0 = b`.

Rewrite using `[Algebra.leftMulMatrix_eq_repr_mul, hB0, mul_one, hrepr]`. Simplify using the standard rewrite rules. Establish `hx1 : ((a : 𝓞 K) + b * w) * w = ((-(b * k) : ℤ) : 𝓞 K) + ((a + b : ℤ) : 𝓞 K) * w`. Use `push_cast`. Take the linear combination `(b : 𝓞 K) * hwsq`.

Establish `e01 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 0 1 = -(b * k)`. Rewrite using `[Algebra.leftMulMatrix_eq_repr_mul, hB1, hx1, hrepr]`. Simplify using the standard rewrite rules. Establish `e11 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 1 1 = a + b`. Rewrite using `[Algebra.leftMulMatrix_eq_repr_mul, hB1, hx1, hrepr]`.

Simplify using the standard rewrite rules. Rewrite using `[e00, e10, e01, e11]`. Establish `hk' : (d : ℤ) + 1 = 4 * k` using `by exact_mod_cast hk`. Take the linear combination `(-(b ^ 2) : ℤ) * hk'`.
-/
theorem exists_imagQuad_integers : ∀ d : ℕ, d.Prime → d % 4 = 3 →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (ω : 𝓞 K), IsTotallyComplex K ∧
      Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) ∧ (2 * ω - 1) ^ 2 = -(d : 𝓞 K) ∧
      (∀ z : 𝓞 K, ∃ a b : ℤ, z = a + b * ω) ∧
      ∀ a b : ℤ, Algebra.norm ℤ ((a : 𝓞 K) + b * ω) * 4 = (2 * a + b) ^ 2 + d * b ^ 2 := by
  intro d hdp hd4
  obtain ⟨K, _, _, r, h2, hr⟩ := exists_field_sq_eq_neg d hdp.pos
  have hsq : Squarefree d := hdp.squarefree
  obtain ⟨w, bar, hw, -, hspan, hemb, -⟩ :=
    GlobalTheory.ringOfIntegers_sqrt_neg_three_mod_four d hsq hd4 K h2 r hr
  have hwr : 2 * (w : K) - 1 = r := by rw [hw]; ring
  have hcoe : algebraMap (𝓞 K) K (2 * w - 1) = r := by
    rw [← hwr]
    simp only [map_sub, map_mul, map_one, map_ofNat]
  have hw2 : (2 * w - 1) ^ 2 = -(d : 𝓞 K) := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, hcoe, hr, map_neg, map_natCast]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 4 * k := ⟨(d + 1) / 4, by omega⟩
  have hwsq : w * w = w - (k : 𝓞 K) := by
    have h4 : (4 : 𝓞 K) * (w * w - w + k) = 0 := by
      have : ((d : ℕ) : 𝓞 K) + 1 = 4 * (k : 𝓞 K) := by exact_mod_cast hk
      linear_combination hw2 - this
    have h4ne : (4 : 𝓞 K) ≠ 0 := by
      intro h
      have : ((4 : 𝓞 K) : K) = 0 := by rw [h]; simp
      norm_num at this
    have := (mul_eq_zero.mp h4).resolve_left h4ne
    linear_combination this
  have hli : LinearIndependent ℤ ![(1 : 𝓞 K), w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hK : (s : K) + t * (w : K) = 0 := by
      have := congrArg (fun z : 𝓞 K => (z : K)) hst
      simpa [zsmul_eq_mul] using this
    have ht : t = 0 := by
      by_contra ht
      have htK : (t : K) ≠ 0 := by exact_mod_cast ht
      set q : ℚ := -(2 * s + t) / t with hqdef
      have hrq : r = algebraMap ℚ K q := by
        simp only [hqdef, map_div₀, map_neg, map_add, map_mul, map_ofNat, map_intCast]
        field_simp
        linear_combination (2 : K) * hK + (-(t : K)) * hwr
      have hq : q ^ 2 = -(d : ℚ) := by
        apply (algebraMap ℚ K).injective
        rw [map_pow, ← hrq, hr]
        simp
      have hdpos : (0 : ℚ) < d := by exact_mod_cast hdp.pos
      nlinarith [sq_nonneg q]
    subst ht
    refine ⟨?_, rfl⟩
    have : (s : K) = 0 := by simpa using hK
    exact_mod_cast this
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range ![(1 : 𝓞 K), w]) := by
    intro z _
    obtain ⟨a, b, rfl⟩ := hspan z
    have hr' : Set.range ![(1 : 𝓞 K), w] = {1, w} := by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty]; rfl
    rw [hr', Submodule.mem_span_pair]
    exact ⟨a, b, by simp [zsmul_eq_mul]⟩
  let B := Basis.mk hli hsp
  have hB0 : B 0 = 1 := by simp [B]
  have hB1 : B 1 = w := by simp [B]
  have hrepr : ∀ s t : ℤ, B.repr ((s : 𝓞 K) + t * w) = Finsupp.single 0 s + Finsupp.single 1 t := by
    intro s t
    have : (s : 𝓞 K) + t * w = s • B 0 + t • B 1 := by
      rw [hB0, hB1]; simp [zsmul_eq_mul]
    rw [this, map_add, map_zsmul, map_zsmul, B.repr_self, B.repr_self]
    simp
  refine ⟨K, inferInstance, inferInstance, w, ?_, h2, ?_, hw2, hspan, ?_⟩
  · refine ⟨fun v => ?_⟩
    rw [InfinitePlace.isComplex_iff]
    exact (hemb v.embedding).1
  · exact GlobalTheory.discr_eq_neg_of_sq_eq h2 hsq hd4 hr
  · intro a b
    rw [Algebra.norm_eq_matrix_det B, Matrix.det_fin_two]
    have e00 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 0 0 = a := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB0, mul_one, hrepr]; simp
    have e10 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 1 0 = b := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB0, mul_one, hrepr]; simp
    have hx1 : ((a : 𝓞 K) + b * w) * w = ((-(b * k) : ℤ) : 𝓞 K) + ((a + b : ℤ) : 𝓞 K) * w := by
      push_cast
      linear_combination (b : 𝓞 K) * hwsq
    have e01 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 0 1 = -(b * k) := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB1, hx1, hrepr]; simp
    have e11 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 1 1 = a + b := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB1, hx1, hrepr]; simp
    rw [e00, e10, e01, e11]
    have hk' : (d : ℤ) + 1 = 4 * k := by exact_mod_cast hk
    linear_combination (-(b ^ 2) : ℤ) * hk'

end GlobalTheory.Mem.ImagQuad
