import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.TracePowCharpoly

open Polynomial Finset

/- English proof (translation)
Establish `h` using `congrArg (MvPolynomial.aeval f) (MvPolynomial.mul_esymm_eq_sum σ ℂ k)`. Simplify `h` using `only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast, MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X]`.
-/
theorem newton_fn {σ : Type} [Fintype σ] (f : σ → ℂ) (k : ℕ) :
    (k : ℂ) * (univ.val.map f).esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k,
        (-1) ^ a.1 * (univ.val.map f).esymm a.1 * ∑ i, f i ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval f) (MvPolynomial.mul_esymm_eq_sum σ ℂ k)
  simpa only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X] using h

/- English proof (translation)
Establish `hs : s = (univ : Finset (Fin s.toList.length)).val.map (fun i => s.toList.get i)`. Rewrite using `[Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]`. Establish `h` using `newton_fn (fun i : Fin s.toList.length => s.toList.get i) k`. Rewrite `h` using `[← hs]`. Rewrite using `[h]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `e : ∀ n : ℕ, (s.map (· ^ n)).sum = ∑ i : Fin s.toList.length, s.toList.get i ^ n`. Introduce `n`.

Use `conv_lhs => rw [hs]`. Rewrite using `[Multiset.map_map]`. Both sides reduce to the same expression. Conclude with `(e a.2).symm`.
-/
theorem newton_multiset (s : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
  have hs : s = (univ : Finset (Fin s.toList.length)).val.map (fun i => s.toList.get i) := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have h := newton_fn (fun i : Fin s.toList.length => s.toList.get i) k
  rw [← hs] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have e : ∀ n : ℕ, (s.map (· ^ n)).sum = ∑ i : Fin s.toList.length, s.toList.get i ^ n := by
    intro n
    conv_lhs => rw [hs]
    rw [Multiset.map_map]
    rfl
  exact (e a.2).symm

/- English proof (translation)
Introduce `k`. Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Simplify using `[Multiset.esymm, Multiset.powersetCard_zero_left]`.

Establish `hk0 : (k : ℂ) ≠ 0` using `by exact_mod_cast hk.ne'`. Apply `mul_left_cancel₀ hk0` to reduce the goal to its premises. Rewrite using `[newton_multiset, newton_multiset]`. Use `congr 1`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations.

Rewrite using `[ih a.1 (Finset.mem_filter.mp ha).2, h a.2]`.
-/
theorem esymm_eq_of_psum_eq (s t : Multiset ℂ) (h : ∀ k, (s.map (· ^ k)).sum = (t.map (· ^ k)).sum) :
    ∀ k, s.esymm k = t.esymm k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    · have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      apply mul_left_cancel₀ hk0
      rw [newton_multiset, newton_multiset]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [ih a.1 (Finset.mem_filter.mp ha).2, h a.2]

/- English proof (translation)
Use extensionality with `k`. Distinguish the cases in `hk : k ≤ Multiset.card s`. Rewrite using `[Multiset.prod_X_sub_C_coeff s hk, Multiset.prod_X_sub_C_coeff t (hc ▸ hk), hc, esymm_eq_of_psum_eq s t h]`. Use `push_neg at hk`. Rewrite using `[coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt]`.

Rewrite using `[natDegree_multiset_prod_X_sub_C_eq_card]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[natDegree_multiset_prod_X_sub_C_eq_card]`. Use linear arithmetic over natural numbers and integers.
-/
theorem prod_eq_of_psum_eq (s t : Multiset ℂ) (hc : Multiset.card s = Multiset.card t)
    (h : ∀ k, (s.map (· ^ k)).sum = (t.map (· ^ k)).sum) :
    (s.map (fun a => X - C a)).prod = (t.map (fun a => X - C a)).prod := by
  ext k
  by_cases hk : k ≤ Multiset.card s
  · rw [Multiset.prod_X_sub_C_coeff s hk, Multiset.prod_X_sub_C_coeff t (hc ▸ hk), hc,
      esymm_eq_of_psum_eq s t h]
  · push_neg at hk
    rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt]
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega

end GlobalTheory.TracePowCharpoly

namespace GlobalTheory.TracePowCharpoly

open Polynomial

/- English proof (translation)
Rewrite using `[LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V), ← GlobalTheory.CharpolyPow.roots_charpoly_pow, ← Matrix.trace_eq_sum_roots_charpoly]`. Use `congr 1`. Proceed by induction on `k with`. Consider the case `zero => simp [LinearMap.toMatrix_one]`. Consider the case `succ n ih => rw [pow_succ, LinearMap.toMatrix_mul, ih, pow_succ]`.
-/
theorem trace_pow_eq_sum_roots {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (k : ℕ) :
    LinearMap.trace ℂ V (f ^ k) =
      ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f).charpoly.roots.map
        (· ^ k)).sum := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V), ← GlobalTheory.CharpolyPow.roots_charpoly_pow,
    ← Matrix.trace_eq_sum_roots_charpoly]
  congr 1
  induction k with
  | zero => simp [LinearMap.toMatrix_one]
  | succ n ih => rw [pow_succ, LinearMap.toMatrix_mul, ih, pow_succ]

/- English proof (translation)
Rewrite using `[← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V)]`. Conclude with `(IsAlgClosed.splits _).eq_prod_roots_of_monic (Matrix.charpoly_monic _)`.
-/
theorem charpoly_eq_prod_roots {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) :
    f.charpoly = ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f).charpoly.roots.map
        (fun a => X - C a)).prod := by
  classical
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V)]
  exact (IsAlgClosed.splits _).eq_prod_roots_of_monic (Matrix.charpoly_monic _)

/- English proof (translation)
Introduce `V V' _ _ _ _ _ _ f g h`. Establish `hdim : Module.finrank ℂ V = Module.finrank ℂ V'`. Establish `h0` using `h 0`. Simplify using `only [pow_zero, LinearMap.trace_one] at h0`. Conclude with `h0` after adjusting the coercions.

Rewrite using `[charpoly_eq_prod_roots f, charpoly_eq_prod_roots g]`. Apply `prod_eq_of_psum_eq` to reduce the goal to its premises. Rewrite using `[GlobalTheory.CharpolyPow.card_roots_charpoly, GlobalTheory.CharpolyPow.card_roots_charpoly, hdim]`. Introduce `k`. Rewrite using `[← trace_pow_eq_sum_roots, ← trace_pow_eq_sum_roots, h k]`.
-/
theorem charpoly_eq_of_trace_pow_eq : ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (f : Module.End ℂ V) (g : Module.End ℂ V'), (∀ k : ℕ, LinearMap.trace ℂ V (f ^ k) = LinearMap.trace ℂ V' (g ^ k)) → f.charpoly = g.charpoly := by
  intro V V' _ _ _ _ _ _ f g h
  have hdim : Module.finrank ℂ V = Module.finrank ℂ V' := by
    have h0 := h 0
    simp only [pow_zero, LinearMap.trace_one] at h0
    exact_mod_cast h0
  rw [charpoly_eq_prod_roots f, charpoly_eq_prod_roots g]
  apply prod_eq_of_psum_eq
  · rw [GlobalTheory.CharpolyPow.card_roots_charpoly, GlobalTheory.CharpolyPow.card_roots_charpoly, hdim]
  · intro k
    rw [← trace_pow_eq_sum_roots, ← trace_pow_eq_sum_roots, h k]

end GlobalTheory.TracePowCharpoly
