import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open Polynomial

/- English proof (translation)
Use `choose r hr using hN`. Use `⟨∑ m ∈ N.support, MvPolynomial.monomial m (r m), ?_⟩` and prove the remaining obligations. Rewrite using `[← MvPolynomial.map_iterateFrobenius_expand p, map_sum, map_sum]`. Use `conv_rhs => rw [N.as_sum, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Simplify using `[MvPolynomial.expand_monomial, iterateFrobenius_def, hr]`.
-/
theorem exists_pow_eq_map_expand {σ k k' : Type*} [Field k] [Field k'] [Algebra k k'] (p : ℕ)
    [Fact p.Prime] [CharP k' p] (e : ℕ) (N : MvPolynomial σ k)
    (hN : ∀ m, ∃ z : k', z ^ p ^ e = algebraMap k k' (N.coeff m)) :
    ∃ N' : MvPolynomial σ k',
      N' ^ p ^ e = MvPolynomial.map (algebraMap k k') (MvPolynomial.expand (p ^ e) N) := by
  choose r hr using hN
  refine ⟨∑ m ∈ N.support, MvPolynomial.monomial m (r m), ?_⟩
  rw [← MvPolynomial.map_iterateFrobenius_expand p, map_sum, map_sum]
  conv_rhs => rw [N.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [MvPolynomial.expand_monomial, iterateFrobenius_def, hr]

/- English proof (translation)
Use `set θ := (MvPolynomial.mapAlgHom (σ := σ) (Algebra.ofId k k')).comp (MvPolynomial.expand q)`. Set `: Algebra (MvPolynomial σ k) (MvPolynomial σ k')` to `θ.toRingHom.toAlgebra`. Establish `: IsScalarTower k (MvPolynomial σ k) (MvPolynomial σ k')` using `IsScalarTower.of_algebraMap_eq fun x => (θ.commutes x).symm`. Establish `hX : ∀ i, IsIntegral (MvPolynomial σ k) (MvPolynomial.X i : MvPolynomial σ k')`. Introduce `i`.

Use `IsIntegral.of_pow hq ?_` and prove the remaining obligations. Establish `: (MvPolynomial.X i : MvPolynomial σ k') ^ q = algebraMap (MvPolynomial σ k) (MvPolynomial σ k') (MvPolynomial.X i)`. Express the relevant statement in the definitionally equal form `_ = θ (MvPolynomial.X i)`. Simplify using `[θ]`. Rewrite using `[this]`.

Conclude with `isIntegral_algebraMap`. Establish `: Algebra.IsIntegral (MvPolynomial σ k) (MvPolynomial σ k')`. Prove the components needed by the constructor for the conclusion. Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`.

Consider the case `C a`. Establish `h1 : IsIntegral k (algebraMap k' (MvPolynomial σ k') a)` using `(Algebra.IsIntegral.isIntegral (R := k) a).map (IsScalarTower.toAlgHom k k' _)`. Rewrite `h1` using `[MvPolynomial.algebraMap_eq]`. Conclude with `h1.tower_top`. Consider the case `add f g hf hg => exact hf.add hg`.

Consider the case `mul_X f i hf => exact hf.mul (hX i)`. Establish `: Algebra.FiniteType k (MvPolynomial σ k')` using `Algebra.FiniteType.trans (S := k') inferInstance inferInstance`. Establish `: Algebra.FiniteType (MvPolynomial σ k) (MvPolynomial σ k')` using `Algebra.FiniteType.of_restrictScalars_finiteType k _ _`. Conclude with `Algebra.IsIntegral.finite`.
-/
theorem finite_mapExpand (k k' : Type*) [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] (σ : Type*) [Finite σ] (q : ℕ) (hq : 0 < q) :
    ((MvPolynomial.mapAlgHom (σ := σ) (Algebra.ofId k k')).comp
      (MvPolynomial.expand q)).toRingHom.Finite := by
  set θ := (MvPolynomial.mapAlgHom (σ := σ) (Algebra.ofId k k')).comp (MvPolynomial.expand q)
  let : Algebra (MvPolynomial σ k) (MvPolynomial σ k') := θ.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial σ k) (MvPolynomial σ k') :=
    IsScalarTower.of_algebraMap_eq fun x => (θ.commutes x).symm
  have hX : ∀ i, IsIntegral (MvPolynomial σ k) (MvPolynomial.X i : MvPolynomial σ k') := by
    intro i
    refine IsIntegral.of_pow hq ?_
    have : (MvPolynomial.X i : MvPolynomial σ k') ^ q =
        algebraMap (MvPolynomial σ k) (MvPolynomial σ k') (MvPolynomial.X i) := by
      change _ = θ (MvPolynomial.X i)
      simp [θ]
    rw [this]
    exact isIntegral_algebraMap
  have : Algebra.IsIntegral (MvPolynomial σ k) (MvPolynomial σ k') := by
    constructor
    intro f
    induction f using MvPolynomial.induction_on with
    | C a =>
      have h1 : IsIntegral k (algebraMap k' (MvPolynomial σ k') a) :=
        (Algebra.IsIntegral.isIntegral (R := k) a).map (IsScalarTower.toAlgHom k k' _)
      rw [MvPolynomial.algebraMap_eq] at h1
      exact h1.tower_top
    | add f g hf hg => exact hf.add hg
    | mul_X f i hf => exact hf.mul (hX i)
  have : Algebra.FiniteType k (MvPolynomial σ k') :=
    Algebra.FiniteType.trans (S := k') inferInstance inferInstance
  have : Algebra.FiniteType (MvPolynomial σ k) (MvPolynomial σ k') :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  exact Algebra.IsIntegral.finite

/- English proof (translation)
Establish `: RingHom.ker ψ = ⊥`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := B)` to reduce the goal to its premises. Rewrite using `[RingHom.comap_ker]`. Conclude with `(RingHom.injective_iff_ker_eq_bot _).mp h`. Conclude with `(RingHom.injective_iff_ker_eq_bot ψ).mpr this`.
-/
theorem injective_of_isIntegral {B B' Ω : Type*} [CommRing B] [Nontrivial B] [CommRing B']
    [IsDomain B'] [CommRing Ω] [Algebra B B'] [Algebra.IsIntegral B B'] (ψ : B' →+* Ω)
    (h : Function.Injective (ψ.comp (algebraMap B B'))) : Function.Injective ψ := by
  have : RingHom.ker ψ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := B)
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).mp h
  exact (RingHom.injective_iff_ker_eq_bot ψ).mpr this

/- English proof (translation)
Use `choose d hd using hc`. Use `set h : F'[X] := ∑ i ∈ Finset.range (g.natDegree + 1), C (d i) * X ^ i`. Establish `hmap : (h.map (algebraMap F' Ω)).map (iterateFrobenius Ω p e) = g.map (algebraMap F Ω)`. Use extensionality with `i`. Simplify using `only [h, coeff_map, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, finsetSum_coeff, coeff_C_mul_X_pow]`.

Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with hi`. Rewrite using `[iterateFrobenius_def, hd]`. Rewrite using `[coeff_eq_zero_of_natDegree_lt (by simp at hi; omega), map_zero]`. Establish `hsepΩ : (h.map (algebraMap F' Ω)).Separable`.

Rewrite using `[← separable_map (iterateFrobenius Ω p e), hmap]`. Conclude with `hg.map`. Establish `hsep : h.Separable` using `(separable_map (algebraMap F' Ω)).mp hsepΩ`. Establish `hroot : aeval ω h = 0`. Establish `: (aeval ω h) ^ p ^ e = 0`.

Rewrite using `[aeval_def, ← eval_map, ← iterateFrobenius_def (R := Ω) p e, ← eval₂_hom, ← eval_map, hmap, eval_map, iterateFrobenius_def, ← aeval_def, hω]`. Conclude with `pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) |>.mp this`. Conclude with `hsep.of_dvd (minpoly.dvd F' ω hroot)`.
-/
theorem isSeparable_of_pow_coeff {F F' Ω : Type*} [Field F] [Field F'] [Field Ω] [Algebra F Ω]
    [Algebra F' Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (e : ℕ) (g : F[X]) (hg : g.Separable)
    (ω : Ω) (hω : aeval (ω ^ p ^ e) g = 0)
    (hc : ∀ i, ∃ d : F', algebraMap F' Ω d ^ p ^ e = algebraMap F Ω (g.coeff i)) :
    IsSeparable F' ω := by
  choose d hd using hc
  set h : F'[X] := ∑ i ∈ Finset.range (g.natDegree + 1), C (d i) * X ^ i
  have hmap : (h.map (algebraMap F' Ω)).map (iterateFrobenius Ω p e) = g.map (algebraMap F Ω) := by
    ext i
    simp only [h, coeff_map, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_X,
      map_C, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with hi
    · rw [iterateFrobenius_def, hd]
    · rw [coeff_eq_zero_of_natDegree_lt (by simp at hi; omega), map_zero]
  have hsepΩ : (h.map (algebraMap F' Ω)).Separable := by
    rw [← separable_map (iterateFrobenius Ω p e), hmap]
    exact hg.map
  have hsep : h.Separable := (separable_map (algebraMap F' Ω)).mp hsepΩ
  have hroot : aeval ω h = 0 := by
    have : (aeval ω h) ^ p ^ e = 0 := by
      rw [aeval_def, ← eval_map, ← iterateFrobenius_def (R := Ω) p e, ← eval₂_hom,
        ← eval_map, hmap, eval_map, iterateFrobenius_def, ← aeval_def, hω]
    exact pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) |>.mp this
  exact hsep.of_dvd (minpoly.dvd F' ω hroot)

end GroundTheory.Heights₂.Heights.FieldNumbers
