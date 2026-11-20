import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZpowersOfTameGen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
open NumberField IsDedekindDomain

namespace GlobalTheory.WildOpenKernel

/- English proof (translation)
Establish `hvl : ¬ A.valuation (l : Ω) < 1`. Introduce `h`. Apply `hlv` to reduce the goal to its premises. Rewrite using `[← hA]`. Simplify using `using h`.

Establish `hvl1 : A.valuation (l : Ω) = 1` using `le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)`. Take `⟨L, hL, hsub⟩` from `(krullTopology_mem_nhds_one_iff E Ω _).mp (hop.mem_nhds (by simp))`. Establish `: IsGalois E Ω` using `IsAlgClosure.isGalois E Ω`. Establish `hidx : L.fixingSubgroup.index ≠ 0`. Rewrite using `[← IntermediateField.finrank_eq_fixingSubgroup_index]`.

Conclude with `Module.finrank_pos.ne'`. Take `⟨N, hN, -, hmem⟩` from `Subgroup.exists_pow_mem_of_index_ne_zero hidx σ`. Take `⟨a, n, hn, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one`. Establish `hτ : σ ^ n ∈ L.fixingSubgroup`. Rewrite `hmem`, the goal using `[IntermediateField.mem_fixingSubgroup_iff]`.

Introduce `x hx`. Use `GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ ^ n) (GlobalTheory.WildInertiaChar.wild_pow A σ hσ n) (l ^ a) ?_ x ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_pow, map_pow, hvl1, one_pow]`. Conclude with `lt_irrefl _`. Rewrite using `[← pow_mul, mul_comm]`.

Conclude with `hmem x hx`. Establish `h1 : φ σ ^ n = 1`. Establish `h2 : σ ^ n ∈ φ.ker` using `hsub hτ`. Rewrite `h2` using `[MonoidHom.mem_ker, map_pow]`. Conclude with `h2`.

Establish `hc : Nat.Coprime l n` using `(Nat.Prime.coprime_iff_not_dvd hl).mpr hn`. Use `(pow_gcd_eq_one (a := φ σ) (m := l) (n := n)).mpr ⟨hσl, h1⟩` as an intermediate fact. Rewrite `this` using `[hc, pow_one]`. Then use the resulting hypothesis.
-/
theorem eq_one_of_wild_prime {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M)
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (hA : Formalism.ConjugateSelfDual.IsPlaceOver A P)
    (hop : IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω))) (l : ℕ) (hl : l.Prime)
    (hlv : ((l : ℕ) : 𝓞 E) ∉ P.asIdeal) (σ : Formalism.ConjugateSelfDual.G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (hσl : φ σ ^ l = 1) : φ σ = 1 := by
  have hvl : ¬ A.valuation (l : Ω) < 1 := by
    intro h
    apply hlv
    rw [← hA]
    simpa using h
  have hvl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp
    (hop.mem_nhds (by simp))
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  have hidx : L.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ
  obtain ⟨a, n, hn, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
  have hτ : σ ^ n ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
    intro x hx
    refine GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ ^ n)
      (GlobalTheory.WildInertiaChar.wild_pow A σ hσ n) (l ^ a) ?_ x ?_
    · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
    · rw [← pow_mul, mul_comm]; exact hmem x hx
  have h1 : φ σ ^ n = 1 := by
    have h2 : σ ^ n ∈ φ.ker := hsub hτ
    rw [MonoidHom.mem_ker, map_pow] at h2
    exact h2
  have hc : Nat.Coprime l n := (Nat.Prime.coprime_iff_not_dvd hl).mpr hn
  have := (pow_gcd_eq_one (a := φ σ) (m := l) (n := n)).mpr ⟨hσl, h1⟩
  rwa [hc, pow_one] at this

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ M _ φ P A m hA hop hm τ hτ ⟨N, hN⟩`. Assume the negation of the conclusion as `hne`. Establish `hd : orderOf (φ τ) ∣ m ^ N` using `orderOf_dvd_of_pow_eq_one hN`. Establish `hne1 : orderOf (φ τ) ≠ 1` using `by rwa [Ne, orderOf_eq_one_iff]`. Take `⟨l, hl, k, hk⟩` from `Nat.exists_prime_and_dvd hne1`.

Establish `hlm : l ∣ m` using `hl.dvd_of_dvd_pow (dvd_trans ⟨k, hk⟩ hd)`. Establish `hlv : ((l : ℕ) : 𝓞 E) ∉ P.asIdeal`. Introduce `h`. Apply `hm` to reduce the goal to its premises. Take `⟨c, hc⟩` from `hlm`.

Rewrite using `[hc]`. Use `push_cast`. Conclude with `Ideal.mul_mem_right _ _ h`. Establish `h1 : φ (τ ^ k) = 1`. Use `eq_one_of_wild_prime φ P A hA hop l hl hlv _ (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_` and prove the remaining obligations.

Rewrite using `[map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]`. Rewrite `h1` using `[map_pow]`. Establish `h2` using `orderOf_dvd_of_pow_eq_one h1`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hm (by simp)`. Establish `ho : orderOf (φ τ) ≠ 0` using `fun h => pow_ne_zero N hm0 (Nat.eq_zero_of_zero_dvd (h ▸ hd))`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Conclude with `ho (by simpa using hk)`.

Establish `h3` using `Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2`. Rewrite `h3` using `[hk]`. Use `hl.two_le` as an intermediate fact. Use `Nat.pos_of_ne_zero hk0` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem eq_one_of_wild : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (m : ℕ),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal →
    ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → (∃ N : ℕ, φ τ ^ (m ^ N) = 1) → φ τ = 1 := by
  intro E Ω _ _ _ _ _ M _ φ P A m hA hop hm τ hτ ⟨N, hN⟩
  by_contra hne
  have hd : orderOf (φ τ) ∣ m ^ N := orderOf_dvd_of_pow_eq_one hN
  have hne1 : orderOf (φ τ) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  obtain ⟨l, hl, k, hk⟩ := Nat.exists_prime_and_dvd hne1
  have hlm : l ∣ m := hl.dvd_of_dvd_pow (dvd_trans ⟨k, hk⟩ hd)
  have hlv : ((l : ℕ) : 𝓞 E) ∉ P.asIdeal := by
    intro h
    apply hm
    obtain ⟨c, hc⟩ := hlm
    rw [hc]
    push_cast
    exact Ideal.mul_mem_right _ _ h
  have h1 : φ (τ ^ k) = 1 := by
    refine eq_one_of_wild_prime φ P A hA hop l hl hlv _
      (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_
    rw [map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
  rw [map_pow] at h1
  have h2 := orderOf_dvd_of_pow_eq_one h1
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have ho : orderOf (φ τ) ≠ 0 := fun h =>
    pow_ne_zero N hm0 (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact ho (by simpa using hk)
  have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2
  rw [hk] at h3
  have := hl.two_le
  have := Nat.pos_of_ne_zero hk0
  nlinarith

end GlobalTheory.WildOpenKernel
