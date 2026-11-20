import Mathlib
import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom

namespace GlobalTheory

open MvPolynomial

/- English proof (translation)
Rewrite using `[IsLocalRing.residue_ne_zero_iff_isUnit, ValuationSubring.valuation_eq_one_iff]`. Conclude with `(Valuation.isEquiv_valuation_valuationSubring v).symm.eq_one_iff_eq_one`.
-/
theorem residue_valuationSubring_ne_zero_iff {U Γ : Type*} [Field U]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation U Γ) (x : v.valuationSubring) :
    IsLocalRing.residue v.valuationSubring x ≠ 0 ↔ v (x : U) = 1 := by
  rw [IsLocalRing.residue_ne_zero_iff_isUnit, ValuationSubring.valuation_eq_one_iff]
  exact (Valuation.isEquiv_valuation_valuationSubring v).symm.eq_one_iff_eq_one

/- English proof (translation)
Use `letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f`. Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_comp_left]`. Use `congr 1`.
-/
private theorem residue_eval₂_comap {F U : Type} [Field F] [Field U] (f : F →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (σ : Type) (t : σ → U)
    (ht : ∀ s, t s ∈ v.valuationSubring) (p : MvPolynomial σ (v.valuationSubring.comap f)) :
    letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f
    IsLocalRing.residue v.valuationSubring
        (MvPolynomial.eval₂ (ReciprocityTheory.MultiplicativeHeights.comapInclusion v.valuationSubring f)
          (fun s => ⟨t s, ht s⟩) p) =
      MvPolynomial.aeval (fun s => IsLocalRing.residue v.valuationSubring ⟨t s, ht s⟩)
        (MvPolynomial.map (IsLocalRing.residue (v.valuationSubring.comap f)) p) := by
  letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_comp_left]
  congr 1

/- English proof (translation)
Rewrite using `[MvPolynomial.eval₂_map]`. Conclude with `MvPolynomial.eval₂_comp_left v.valuationSubring.subtype _ _ p`.
-/
private theorem coe_eval₂_comapInclusion_eq_eval₂_map {F U : Type} [Field F] [Field U] (f : F →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (σ : Type) (t : σ → U)
    (ht : ∀ s, t s ∈ v.valuationSubring) (p : MvPolynomial σ (v.valuationSubring.comap f)) :
    ((MvPolynomial.eval₂ (ReciprocityTheory.MultiplicativeHeights.comapInclusion v.valuationSubring f)
          (fun s => (⟨t s, ht s⟩ : v.valuationSubring)) p : v.valuationSubring) : U) =
      MvPolynomial.eval₂ f t (MvPolynomial.map (v.valuationSubring.comap f).subtype p) := by
  rw [MvPolynomial.eval₂_map]
  exact MvPolynomial.eval₂_comp_left v.valuationSubring.subtype _ _ p

/- English proof (translation)
Establish `h` using `residue_valuationSubring_ne_zero_iff v (ReciprocityTheory.MultiplicativeHeights.comapInclusion v.valuationSubring f c)`. Rewrite `h` using `[← IsLocalRing.ResidueField.map_residue, map_ne_zero]`. Conclude with `h`.
-/
private theorem residue_comap_ne_zero_iff_valuation_eq_one {F U : Type} [Field F] [Field U] (f : F →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (c : v.valuationSubring.comap f) :
    IsLocalRing.residue (v.valuationSubring.comap f) c ≠ 0 ↔ v (f c) = 1 := by
  have h := residue_valuationSubring_ne_zero_iff v (ReciprocityTheory.MultiplicativeHeights.comapInclusion v.valuationSubring f c)
  rw [← IsLocalRing.ResidueField.map_residue, map_ne_zero] at h
  exact h

/- English proof (translation)
Use `letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f`. Rewrite using `[algebraicIndependent_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hind p hle hone`. Choose the witnesses or unpack the hypotheses as in `⟨q, rfl⟩ : p ∈ Set.range (MvPolynomial.map (v.valuationSubring.comap f).subtype) := by`.

Rewrite using `[MvPolynomial.mem_range_map_iff_coeffs_subset]`. Introduce `c hc`. Take `⟨α, -, rfl⟩` from `MvPolynomial.mem_coeffs_iff.mp hc`. Conclude with `⟨⟨p.coeff α, ValuationSubring.mem_comap.mpr ((v.mem_valuationSubring_iff _).mpr (hle α))⟩, rfl⟩`. Take `⟨α, hα⟩` from `hone`.

Rewrite `hα` using `[MvPolynomial.coeff_map]`. Rewrite using `[← coe_eval₂_comapInclusion_eq_eval₂_map f v σ t ht q, ← residue_valuationSubring_ne_zero_iff, residue_eval₂_comap]`. Introduce `h0`. Establish `hq` using `congrArg (MvPolynomial.coeff α) (hind _ h0)`. Rewrite `hq` using `[MvPolynomial.coeff_map, MvPolynomial.coeff_zero]`.

Conclude with `(residue_comap_ne_zero_iff_valuation_eq_one f v (q.coeff α)).mpr hα hq`. Introduce `hg r hr`. Assume the negation of the conclusion as `hne`. Take `⟨q, rfl⟩` from `MvPolynomial.map_surjective _ IsLocalRing.residue_surjective r`. Take `⟨α, hα⟩` from `MvPolynomial.ne_zero_iff.mp hne`.

Rewrite `hα` using `[MvPolynomial.coeff_map]`. Establish `hle : ∀ β, v (f ((MvPolynomial.map (v.valuationSubring.comap f).subtype q).coeff β)) ≤ 1`. Introduce `β`. Rewrite using `[MvPolynomial.coeff_map]`. Conclude with `(v.mem_valuationSubring_iff _).mp (ValuationSubring.mem_comap.mp (q.coeff β).2)`.

Establish `h1` using `hg _ hle ⟨α, by`. Rewrite using `[MvPolynomial.coeff_map]`. Conclude with `(residue_comap_ne_zero_iff_valuation_eq_one f v (q.coeff α)).mp hα⟩`. Rewrite `h1` using `[← coe_eval₂_comapInclusion_eq_eval₂_map f v σ t ht q, ← residue_valuationSubring_ne_zero_iff, residue_eval₂_comap]`. Conclude with `h1 hr`.
-/
theorem algebraicIndependent_residue_iff_gauss (F U : Type) [Field F] [Field U] (f : F →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (σ : Type) (t : σ → U)
    (ht : ∀ s, t s ∈ v.valuationSubring) :
    (letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f
     AlgebraicIndependent (IsLocalRing.ResidueField (v.valuationSubring.comap f))
      (fun s => IsLocalRing.residue v.valuationSubring ⟨t s, ht s⟩)) ↔
    ∀ p : MvPolynomial σ F, (∀ α, v (f (p.coeff α)) ≤ 1) → (∃ α, v (f (p.coeff α)) = 1) →
      v (MvPolynomial.eval₂ f t p) = 1 := by
  letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f
  rw [algebraicIndependent_iff]
  constructor
  · intro hind p hle hone
    obtain ⟨q, rfl⟩ : p ∈ Set.range (MvPolynomial.map (v.valuationSubring.comap f).subtype) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨α, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
      exact ⟨⟨p.coeff α, ValuationSubring.mem_comap.mpr ((v.mem_valuationSubring_iff _).mpr (hle α))⟩, rfl⟩
    obtain ⟨α, hα⟩ := hone
    rw [MvPolynomial.coeff_map] at hα
    rw [← coe_eval₂_comapInclusion_eq_eval₂_map f v σ t ht q, ← residue_valuationSubring_ne_zero_iff, residue_eval₂_comap]
    intro h0
    have hq := congrArg (MvPolynomial.coeff α) (hind _ h0)
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at hq
    exact (residue_comap_ne_zero_iff_valuation_eq_one f v (q.coeff α)).mpr hα hq
  · intro hg r hr
    by_contra hne
    obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective r
    obtain ⟨α, hα⟩ := MvPolynomial.ne_zero_iff.mp hne
    rw [MvPolynomial.coeff_map] at hα
    have hle : ∀ β, v (f ((MvPolynomial.map (v.valuationSubring.comap f).subtype q).coeff β)) ≤ 1 := by
      intro β
      rw [MvPolynomial.coeff_map]
      exact (v.mem_valuationSubring_iff _).mp (ValuationSubring.mem_comap.mp (q.coeff β).2)
    have h1 := hg _ hle ⟨α, by
      rw [MvPolynomial.coeff_map]
      exact (residue_comap_ne_zero_iff_valuation_eq_one f v (q.coeff α)).mp hα⟩
    rw [← coe_eval₂_comapInclusion_eq_eval₂_map f v σ t ht q, ← residue_valuationSubring_ne_zero_iff, residue_eval₂_comap] at h1
    exact h1 hr

end GlobalTheory
