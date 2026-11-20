import Mathlib

universe u_1

namespace GlobalTheory.IntegralTrace

open Polynomial

/- English proof (translation)
Use `haveI : Module.Finite R L := Module.Finite.iff_fg.mpr hL`. Set `g : Module.End R (Fin n → E)` to `(Matrix.toLin' M).restrictScalars R`. Establish `hg : ∀ x ∈ L, g x ∈ L` using `fun x hx => by simpa [g] using hM x hx`. Take `⟨p, hp, hp0⟩` from `LinearMap.exists_monic_and_aeval_eq_zero R (g.restrict hg)`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations.

Establish `key : ∀ (q : R[X]) (x : L), ((aeval (g.restrict hg) q x : L) : Fin n → E) = (aeval M (q.map (algebraMap R E))).mulVec x`. Introduce `q`. Proceed by induction on `q using Polynomial.induction_on with`. Consider the case `C a`. Introduce `x`.

Simplify using `[Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]`. Consider the case `add a b ha hb`. Introduce `x`. Simplify using `only [map_add, Polynomial.map_add, LinearMap.add_apply, Submodule.coe_add, ha, hb, Matrix.add_mulVec]`. Consider the case `monomial k a ih`.

Introduce `x`. Rewrite using `[pow_succ, ← mul_assoc, map_mul, Polynomial.map_mul, map_mul (aeval M), Module.End.mul_apply, ih, Polynomial.map_X, aeval_X, aeval_X, ← Matrix.mulVec_mulVec]`. Both sides reduce to the same expression. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Apply `LinearMap.ext_on hspan` to reduce the goal to its premises. Introduce `x hx`. Use `key p ⟨x, hx⟩` as an intermediate fact. Rewrite `this` using `[hp0]`. Simplify using `using this.symm`.
-/
theorem exists_monic_aeval_eq_zero {R E : Type*} [CommRing R] [Field E] [Algebra R E] {n : ℕ}
    (L : Submodule R (Fin n → E)) (hL : L.FG)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, M.mulVec x ∈ L) :
    ∃ p : R[X], p.Monic ∧ aeval M (p.map (algebraMap R E)) = 0 := by
  haveI : Module.Finite R L := Module.Finite.iff_fg.mpr hL
  let g : Module.End R (Fin n → E) := (Matrix.toLin' M).restrictScalars R
  have hg : ∀ x ∈ L, g x ∈ L := fun x hx => by simpa [g] using hM x hx
  obtain ⟨p, hp, hp0⟩ := LinearMap.exists_monic_and_aeval_eq_zero R (g.restrict hg)
  refine ⟨p, hp, ?_⟩
  have key : ∀ (q : R[X]) (x : L), ((aeval (g.restrict hg) q x : L) : Fin n → E)
      = (aeval M (q.map (algebraMap R E))).mulVec x := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x
      simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
    | add a b ha hb =>
      intro x
      simp only [map_add, Polynomial.map_add, LinearMap.add_apply, Submodule.coe_add, ha, hb,
        Matrix.add_mulVec]
    | monomial k a ih =>
      intro x
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.map_mul, map_mul (aeval M), Module.End.mul_apply,
        ih,
        Polynomial.map_X, aeval_X, aeval_X, ← Matrix.mulVec_mulVec]
      rfl
  apply Matrix.toLin'.injective
  rw [map_zero]
  apply LinearMap.ext_on hspan
  intro x hx
  have := key p ⟨x, hx⟩
  rw [hp0] at this
  simpa using this.symm

/- English proof (translation)
Take `⟨p, hp, hp0⟩` from `exists_monic_aeval_eq_zero L hL hspan M hM`. Set `K` to `AlgebraicClosure E`. Set `N : Matrix (Fin n) (Fin n) K` to `(algebraMap E K).mapMatrix M`. Establish `hN : aeval N (p.map (algebraMap (NumberField.RingOfIntegers E) K)) = 0`. Establish `h1` using `Polynomial.aeval_algHom_apply ((Algebra.ofId E K).mapMatrix (m := Fin n)) M (p.map (algebraMap (NumberField.RingOfIntegers E) E))`.

Rewrite `h1` using `[hp0, map_zero]`. Rewrite using `[IsScalarTower.algebraMap_eq (NumberField.RingOfIntegers E) E K, ← Polynomial.map_map, aeval_map_algebraMap]`. Conclude with `h1`. Rewrite using `[← isIntegral_algebraMap_iff (algebraMap E K).injective]`. Establish `htr : algebraMap E K M.trace = N.trace`.

Simplify using `[N, Matrix.trace]`. Rewrite using `[htr, Matrix.trace_eq_sum_roots_charpoly]`. Apply `IsIntegral.multiset_sum` to reduce the goal to its premises. Introduce `z hz`. Establish `hz1 : z ∈ spectrum K N`.

Rewrite using `[Matrix.mem_spectrum_iff_isRoot_charpoly]`. Conclude with `(Polynomial.mem_roots N.charpoly_monic.ne_zero).mp hz`. Establish `hz2` using `spectrum.subset_polynomial_aeval N (p.map (algebraMap (NumberField.RingOfIntegers E) K)) ⟨z, hz1, rfl⟩`. Rewrite `hz2` using `[hN]`. Establish `hz3 : eval z (p.map (algebraMap (NumberField.RingOfIntegers E) K)) = 0`.

Assume the negation of the conclusion as `h`. Rewrite `hz2` using `[spectrum.mem_iff]`. Apply `hz2` to reduce the goal to its premises. Rewrite using `[sub_zero]`. Conclude with `(IsUnit.mk0 _ h).map _`.

Establish `hz4 : IsIntegral (NumberField.RingOfIntegers E) z` using `⟨p, hp, by rwa [eval_map] at hz3⟩`. Conclude with `isIntegral_trans z hz4`.
-/
theorem isIntegral_trace {E : Type u_1} [inst : Field E] [NumberField E] (_φ : E →+* ℂ) {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.FG L)
    (hspan : Submodule.span E (↑L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, Matrix.mulVec M x ∈ L) :
    IsIntegral ℤ (Matrix.trace M) := by
  obtain ⟨p, hp, hp0⟩ := exists_monic_aeval_eq_zero L hL hspan M hM
  let K := AlgebraicClosure E
  let N : Matrix (Fin n) (Fin n) K := (algebraMap E K).mapMatrix M
  have hN : aeval N (p.map (algebraMap (NumberField.RingOfIntegers E) K)) = 0 := by
    have h1 := Polynomial.aeval_algHom_apply ((Algebra.ofId E K).mapMatrix (m := Fin n)) M
      (p.map (algebraMap (NumberField.RingOfIntegers E) E))
    rw [hp0, map_zero] at h1
    rw [IsScalarTower.algebraMap_eq (NumberField.RingOfIntegers E) E K, ← Polynomial.map_map,
      aeval_map_algebraMap]
    exact h1
  rw [← isIntegral_algebraMap_iff (algebraMap E K).injective]
  have htr : algebraMap E K M.trace = N.trace := by
    simp [N, Matrix.trace]
  rw [htr, Matrix.trace_eq_sum_roots_charpoly]
  apply IsIntegral.multiset_sum
  intro z hz
  have hz1 : z ∈ spectrum K N := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
    exact (Polynomial.mem_roots N.charpoly_monic.ne_zero).mp hz
  have hz2 := spectrum.subset_polynomial_aeval N
    (p.map (algebraMap (NumberField.RingOfIntegers E) K)) ⟨z, hz1, rfl⟩
  rw [hN] at hz2
  have hz3 : eval z (p.map (algebraMap (NumberField.RingOfIntegers E) K)) = 0 := by
    by_contra h
    rw [spectrum.mem_iff] at hz2
    apply hz2
    rw [sub_zero]
    exact (IsUnit.mk0 _ h).map _
  have hz4 : IsIntegral (NumberField.RingOfIntegers E) z := ⟨p, hp, by rwa [eval_map] at hz3⟩
  exact isIntegral_trans z hz4

end GlobalTheory.IntegralTrace
