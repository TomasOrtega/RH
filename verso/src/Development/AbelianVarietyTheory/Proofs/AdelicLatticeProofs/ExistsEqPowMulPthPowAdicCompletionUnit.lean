import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm IsLocalRing
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Take `⟨g, hg⟩` from `IsCyclic.exists_generator (α := G)`. Take `⟨a, rfl⟩` from `Subgroup.mem_zpowers_iff.1 (hg x)`. Take `⟨b, rfl⟩` from `Subgroup.mem_zpowers_iff.1 (hg y)`. Establish `hpa : ¬ (p : ℤ) ∣ a`. Introduce and unpack `⟨c, rfl⟩`.

Conclude with `hx (g ^ c) (by rw [← zpow_natCast, ← zpow_mul, mul_comm])`. Establish `hcop : IsCoprime (p : ℤ) a` using `((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd).2 hpa`. Take `⟨u, w, huw⟩` from `hcop`. Establish `hp0 : (p : ℤ) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Take `⟨k, hk⟩` from `Int.eq_ofNat_of_zero_le (Int.emod_nonneg (b * w) hp0)`.

Use `⟨k, g ^ (b * u + a * (b * w / p)), ?_⟩` and prove the remaining obligations. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hk]`. Use `congr 1`. Use `Int.emod_add_mul_ediv (b * w) p` as an intermediate fact. Take the linear combination `(-b) * huw - a * this`.
-/
theorem exists_eq_pow_mul_pow_of_isCyclic {G : Type*} [CommGroup G] [IsCyclic G] {p : ℕ}
    (hp : p.Prime) {x : G} (hx : ∀ r : G, r ^ p ≠ x) (y : G) :
    ∃ (k : ℕ) (r : G), y = x ^ k * r ^ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg y)
  have hpa : ¬ (p : ℤ) ∣ a := by
    rintro ⟨c, rfl⟩
    exact hx (g ^ c) (by rw [← zpow_natCast, ← zpow_mul, mul_comm])
  have hcop : IsCoprime (p : ℤ) a :=
    ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd).2 hpa
  obtain ⟨u, w, huw⟩ := hcop
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg (b * w) hp0)
  refine ⟨k, g ^ (b * u + a * (b * w / p)), ?_⟩
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hk]
  congr 1
  have := Int.emod_add_mul_ediv (b * w) p
  linear_combination (-b) * huw - a * this

/- English proof (translation)
Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hn`. Take `⟨a, rfl⟩` from `residue_surjective c`. Establish `ha : IsUnit a`.

Establish `: IsUnit (residue R a ^ n)` using `hc ▸ hu.map _`. Conclude with `(isUnit_map_iff (residue R) a).1 ((isUnit_pow_iff hn0).1 this)`. Take `⟨v, hv, -⟩` from `HenselianRing.is_henselian (I := maximalIdeal R) (X ^ n - C u : R[X]) (monic_X_pow_sub_C u hn0) a (by rw [← residue_eq_zero_iff]; simp [hc]) (IsUnit.map _ (by simpa [derivative_X_pow] using hn.mul (ha.pow _)))`. Conclude with `⟨v, by simpa [sub_eq_zero] using hv⟩`.
-/
theorem exists_pow_eq_of_residue_pow {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] {n : ℕ} (hn : IsUnit (n : R)) {u : R} (hu : IsUnit u)
    (c : ResidueField R) (hc : c ^ n = residue R u) : ∃ v : R, v ^ n = u := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨a, rfl⟩ := residue_surjective c
  have ha : IsUnit a := by
    have : IsUnit (residue R a ^ n) := hc ▸ hu.map _
    exact (isUnit_map_iff (residue R) a).1 ((isUnit_pow_iff hn0).1 this)
  obtain ⟨v, hv, -⟩ := HenselianRing.is_henselian (I := maximalIdeal R) (X ^ n - C u : R[X])
    (monic_X_pow_sub_C u hn0) a
    (by rw [← residue_eq_zero_iff]; simp [hc])
    (IsUnit.map _ (by simpa [derivative_X_pow] using hn.mul (ha.pow _)))
  exact ⟨v, by simpa [sub_eq_zero] using hv⟩

/- English proof (translation)
Set `f : Rˣ →* (ResidueField R)ˣ` to `Units.map (residue R : R →* ResidueField R)`. Establish `hx' : ∀ r : (ResidueField R)ˣ, r ^ p ≠ f x`. Introduce `r hr`. Take `⟨s, hs⟩` from `exists_pow_eq_of_residue_pow hn x.isUnit (r : ResidueField R) (by rw [← Units.val_pow_eq_pow_val, hr]; rfl)`. Conclude with `hx s hs`.

Take `⟨k, r, hr⟩` from `exists_eq_pow_mul_pow_of_isCyclic hp hx' (f y)`. Establish `h1 : r ^ p = f ((x ^ k)⁻¹ * y)`. Rewrite using `[map_mul, map_inv, map_pow, hr, inv_mul_cancel_left]`. Take `⟨s, hs⟩` from `exists_pow_eq_of_residue_pow hn ((x ^ k)⁻¹ * y).isUnit (r : ResidueField R) (by rw [← Units.val_pow_eq_pow_val, h1]; rfl)`. Use `⟨k, s, ?_⟩` and prove the remaining obligations.

Rewrite using `[hs, ← Units.val_pow_eq_pow_val, ← Units.val_mul, mul_inv_cancel_left]`.
-/
theorem exists_eq_pow_mul_pow_of_henselian {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] [Finite (ResidueField R)] {p : ℕ} (hp : p.Prime)
    (hn : IsUnit (p : R)) (x y : Rˣ) (hx : ∀ r : R, r ^ p ≠ x) :
    ∃ (k : ℕ) (r : R), (y : R) = x ^ k * r ^ p := by
  let f : Rˣ →* (ResidueField R)ˣ := Units.map (residue R : R →* ResidueField R)
  have hx' : ∀ r : (ResidueField R)ˣ, r ^ p ≠ f x := by
    intro r hr
    obtain ⟨s, hs⟩ := exists_pow_eq_of_residue_pow hn x.isUnit (r : ResidueField R)
      (by rw [← Units.val_pow_eq_pow_val, hr]; rfl)
    exact hx s hs
  obtain ⟨k, r, hr⟩ := exists_eq_pow_mul_pow_of_isCyclic hp hx' (f y)
  have h1 : r ^ p = f ((x ^ k)⁻¹ * y) := by
    rw [map_mul, map_inv, map_pow, hr, inv_mul_cancel_left]
  obtain ⟨s, hs⟩ := exists_pow_eq_of_residue_pow hn ((x ^ k)⁻¹ * y).isUnit (r : ResidueField R)
    (by rw [← Units.val_pow_eq_pow_val, h1]; rfl)
  refine ⟨k, s, ?_⟩
  rw [hs, ← Units.val_pow_eq_pow_val, ← Units.val_mul, mul_inv_cancel_left]

/- English proof (translation)
Introduce `p F _ _ v x y hp hv hx hy hx'`. Use `haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v`. Use `haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v`. Set `a : v.adicCompletionIntegers F` to `⟨x, hx.le⟩`. Set `b : v.adicCompletionIntegers F` to `⟨y, hy.le⟩`.

Establish `ha : IsUnit a` using `HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hx`. Establish `hb : IsUnit b` using `HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hy`. Establish `hn : IsUnit (p : v.adicCompletionIntegers F)`. Rewrite using `[HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]`. Establish `h` using `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (p : F)).trans hv`.

Establish `e : ((p : v.adicCompletionIntegers F) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (p : F)` using `by simp`. Rewrite using `[e]`. Conclude with `h`. Take `⟨k, r, hr⟩` from `exists_eq_pow_mul_pow_of_henselian hp hn ha.unit hb.unit (fun r hr => hx' r (congrArg Subtype.val hr))`. Conclude with `⟨k, r, congrArg Subtype.val hr⟩`.
-/
theorem exists_eq_pow_mul_pow_of_unit : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F), p.Prime → v.valuation F (p : F) = 1 → Valued.v x = 1 → Valued.v y = 1 → (∀ r : v.adicCompletion F, r ^ p ≠ x) → ∃ (k : ℕ) (r : v.adicCompletion F), y = x ^ k * r ^ p := by
  intro p F _ _ v x y hp hv hx hy hx'
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  let a : v.adicCompletionIntegers F := ⟨x, hx.le⟩
  let b : v.adicCompletionIntegers F := ⟨y, hy.le⟩
  have ha : IsUnit a := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hx
  have hb : IsUnit b := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hy
  have hn : IsUnit (p : v.adicCompletionIntegers F) := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have h := (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (p : F)).trans hv
    have e : ((p : v.adicCompletionIntegers F) : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (p : F) := by simp
    rw [e]
    exact h
  obtain ⟨k, r, hr⟩ := exists_eq_pow_mul_pow_of_henselian hp hn ha.unit hb.unit
    (fun r hr => hx' r (congrArg Subtype.val hr))
  exact ⟨k, r, congrArg Subtype.val hr⟩

end GlobalTheory.CNorm
