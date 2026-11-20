import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem ideal_le_prime_pow_iff_le_count {R : Type} [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) {J : Ideal R} (hJ : J ≠ 0) (n : ℕ) :
    J ≤ v.asIdeal ^ n ↔ n ≤ (Associates.mk v.asIdeal).count (Associates.mk J).factors := by
  classical
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) v.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]

/- English proof (translation)
Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Simplify using the standard rewrite rules. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Use linear arithmetic over natural numbers and integers. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem count_map_ideal_eq_mul_of_valuation_pow (k k' : Type) [Field k] [NumberField k] [Field k']
    [NumberField k'] (i : k →+* k') (J : Ideal (𝓞 k)) (𝔭 : HeightOneSpectrum (𝓞 k))
    (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ)
    (h : ∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) :
    FractionalIdeal.count k' 𝔓 ((J.map (RingOfIntegers.mapRingHom i) : Ideal (𝓞 k')) :
      FractionalIdeal (nonZeroDivisors (𝓞 k')) k') =
    ε * FractionalIdeal.count k 𝔭 (J : FractionalIdeal (nonZeroDivisors (𝓞 k)) k) := by
  classical
  by_cases hJ : J = 0
  · subst hJ
    simp [FractionalIdeal.count_zero]
  have hv : ∀ x : 𝓞 k, 𝔓.intValuation (RingOfIntegers.mapRingHom i x) = 𝔭.intValuation x ^ ε := by
    intro x
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := k'),
      ← HeightOneSpectrum.valuation_of_algebraMap (K := k), ← h]
    rfl
  have hinj : Function.Injective (RingOfIntegers.mapRingHom i) := by
    intro x y hxy
    apply RingOfIntegers.ext
    apply i.injective
    exact congrArg (fun t : 𝓞 k' => (t : k')) hxy
  have hJ' : J.map (RingOfIntegers.mapRingHom i) ≠ 0 := fun h0 =>
    hJ ((Ideal.map_eq_bot_iff_of_injective hinj).mp h0)
  rw [FractionalIdeal.count_coe k' 𝔓 hJ', FractionalIdeal.count_coe k 𝔭 hJ]
  set m := (Associates.mk 𝔭.asIdeal).count (Associates.mk J).factors with hm
  set m' := (Associates.mk 𝔓.asIdeal).count
    (Associates.mk (J.map (RingOfIntegers.mapRingHom i))).factors with hm'
  have hle : J ≤ 𝔭.asIdeal ^ m := (ideal_le_prime_pow_iff_le_count 𝔭 hJ m).mpr le_rfl
  have hle' : J.map (RingOfIntegers.mapRingHom i) ≤ 𝔓.asIdeal ^ m' :=
    (ideal_le_prime_pow_iff_le_count 𝔓 hJ' m').mpr le_rfl
  have hnle : ¬ J ≤ 𝔭.asIdeal ^ (m + 1) := fun h1 => by
    have := (ideal_le_prime_pow_iff_le_count 𝔭 hJ (m + 1)).mp h1
    omega
  have h1 : ε * m ≤ m' := by
    apply (ideal_le_prime_pow_iff_le_count 𝔓 hJ' _).mp
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← 𝔓.intValuation_le_pow_iff_mem, hv]
    have hx' := (𝔭.intValuation_le_pow_iff_mem x m).mpr (hle hx)
    refine (pow_le_pow_left' hx' ε).trans (le_of_eq ?_)
    rw [← WithZero.exp_nsmul]
    congr 1
    push_cast
    simp
  have h2 : m' ≤ ε * m := by
    obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.mp hnle
    have hx0 : x ≠ 0 := fun h0 => hxn (h0 ▸ zero_mem _)
    rw [← 𝔭.intValuation_le_pow_iff_mem, not_le] at hxn
    have hx' := (𝔭.intValuation_le_pow_iff_mem x m).mpr (hle hx)
    have h3 := (𝔓.intValuation_le_pow_iff_mem _ m').mpr (hle' (Ideal.mem_map_of_mem _ hx))
    rw [hv] at h3
    have hne : 𝔭.intValuation x ≠ 0 := 𝔭.intValuation_ne_zero x hx0
    rw [← WithZero.exp_log hne] at hxn hx' h3
    rw [← WithZero.exp_nsmul, WithZero.exp_le_exp] at h3
    rw [WithZero.exp_lt_exp] at hxn
    rw [WithZero.exp_le_exp] at hx'
    have h4 : WithZero.log (𝔭.intValuation x) = -(m : ℤ) := by
      push_cast at hxn
      omega
    rw [h4, nsmul_eq_mul] at h3
    have : (m' : ℤ) ≤ ε * m := by linarith
    exact_mod_cast this
  have : m' = ε * m := le_antisymm h2 h1
  rw [this]
  push_cast
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem count_map_comp_ideal_eq_mul_of_valuation_pow : ∀ (E : Type) [Field E] [NumberField E] (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (τ : E →+* k) (𝔞 : Ideal (𝓞 E)) (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ), (∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) → FractionalIdeal.count k' 𝔓 ((𝔞.map (RingOfIntegers.mapRingHom (i.comp τ)) : Ideal (𝓞 k')) : FractionalIdeal (nonZeroDivisors (𝓞 k')) k') = ε * FractionalIdeal.count k 𝔭 ((𝔞.map (RingOfIntegers.mapRingHom τ) : Ideal (𝓞 k)) : FractionalIdeal (nonZeroDivisors (𝓞 k)) k) := by
  intro E _ _ k k' _ _ _ _ i τ 𝔞 𝔭 𝔓 ε h
  have hc : RingOfIntegers.mapRingHom (i.comp τ) =
      (RingOfIntegers.mapRingHom i).comp (RingOfIntegers.mapRingHom τ) := by
    ext x
    rfl
  rw [hc, ← Ideal.map_map]
  exact count_map_ideal_eq_mul_of_valuation_pow k k' i _ 𝔭 𝔓 ε h

end GlobalTheory
