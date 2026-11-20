import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedOfPowFixed
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.TameGenPowers
open scoped Pointwise

/- English proof (translation)
Establish `hv : ∀ y : Ω, A.valuation (σ y) = A.valuation y`. Introduce `y`. Break down `eq_or_ne y 0 with rfl | hy` into its components or cases. Simplify using the standard rewrite rules. Establish `h` using `A.valuation.map_one_add_of_lt (hσ y hy)`.

Rewrite `h` using `[add_sub_cancel, map_div₀, div_eq_one_iff_eq (by simpa using hy)]`. Conclude with `h`. Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Use `show σ • A = A`. Use extensionality with `x`.

Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← A.valuation_le_one_iff, ← A.valuation_le_one_iff, ← hv, mul_inv_apply]`. Break down `eq_or_ne x 0 with rfl | hx0` into its components or cases. Simplify using the standard rewrite rules. Establish `e : σ x - x = (σ x / x - 1) * x` using `by field_simp`. Rewrite using `[e, map_mul]`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' hx) (hσ x hx0)`.
-/
theorem wild_mem_Ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {σ : Formalism.ConjugateSelfDual.G E Ω}
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ Ine (F := E) A := by
  have hv : ∀ y : Ω, A.valuation (σ y) = A.valuation y := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have h := A.valuation.map_one_add_of_lt (hσ y hy)
    rw [add_sub_cancel, map_div₀, div_eq_one_iff_eq (by simpa using hy)] at h
    exact h
  refine ⟨?_, fun x hx => ?_⟩
  · show σ • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      ← A.valuation_le_one_iff, ← A.valuation_le_one_iff, ← hv, mul_inv_apply]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    have e : σ x - x = (σ x / x - 1) * x := by field_simp
    rw [e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hx) (hσ x hx0)

/- English proof (translation)
Use `haveI : NeZero m := ⟨hm⟩`. Establish `: Finite (rootsOfUnity m K)` using `inferInstance`. Establish `h` using `Set.toFinite ((rootsOfUnity m K : Subgroup Kˣ) : Set Kˣ)`. Conclude with `h.subset fun u hu => (mem_rootsOfUnity m u).2 hu`.
-/
theorem finite_roots (K : Type) [Field K] (m : ℕ) (hm : m ≠ 0) :
    {u : Kˣ | u ^ m = 1}.Finite := by
  haveI : NeZero m := ⟨hm⟩
  have : Finite (rootsOfUnity m K) := inferInstance
  have h := Set.toFinite ((rootsOfUnity m K : Subgroup Kˣ) : Set Kˣ)
  exact h.subset fun u hu => (mem_rootsOfUnity m u).2 hu

/- English proof (translation)
Establish `hvl : ¬ A.valuation (l : Ω) < 1`. Introduce `h`. Apply `hlv` to reduce the goal to its premises. Rewrite using `[← hA]`. Simplify using `using h`.

Establish `hvl1 : A.valuation (l : Ω) = 1` using `le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)`. Establish `hfin : ({u : Kˣ | u ^ l = 1} \ {1}).Finite` using `(finite_roots K l hl.ne_zero).diff`. Establish `hop : IsOpen (r ⁻¹' ({u : Kˣ | u ^ l = 1} \ {1})ᶜ)` using `hfin.isClosed.isOpen_compl.preimage hr`. Take `⟨L, hL, hsub⟩` from `(krullTopology_mem_nhds_one_iff E Ω _).mp (hop.mem_nhds (by simp))`. Establish `: IsGalois E Ω` using `IsAlgClosure.isGalois E Ω`.

Establish `hidx : L.fixingSubgroup.index ≠ 0`. Rewrite using `[← IntermediateField.finrank_eq_fixingSubgroup_index]`. Conclude with `Module.finrank_pos.ne'`. Take `⟨N, hN, -, hmem⟩` from `Subgroup.exists_pow_mem_of_index_ne_zero hidx σ`. Take `⟨a, n, hn, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one`.

Establish `hτ : σ ^ n ∈ L.fixingSubgroup`. Rewrite `hmem`, the goal using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Use `GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ ^ n) (GlobalTheory.WildInertiaChar.wild_pow A σ hσ n) (l ^ a) ?_ x ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_pow, map_pow, hvl1, one_pow]`.

Conclude with `lt_irrefl _`. Rewrite using `[← pow_mul, mul_comm]`. Conclude with `hmem x hx`. Establish `h1 : r σ ^ n = 1`. Establish `h2 : r (σ ^ n) ∉ ({u : Kˣ | u ^ l = 1} \ {1})` using `hsub hτ`.

Assume the negation of the conclusion as `hne`. Apply `h2` to reduce the goal to its premises. Use `⟨?_, by rwa [map_pow]⟩` and prove the remaining obligations. Use `show r (σ ^ n) ^ l = 1`. Rewrite using `[map_pow, ← pow_mul, mul_comm, pow_mul, hσl, one_pow]`.

Establish `hc : Nat.Coprime l n` using `(Nat.Prime.coprime_iff_not_dvd hl).mpr hn`. Use `(pow_gcd_eq_one (a := r σ) (m := l) (n := n)).mpr ⟨hσl, h1⟩` as an intermediate fact. Rewrite `this` using `[hc, pow_one]`. Then use the resulting hypothesis.
-/
theorem eq_one_of_wild_prime (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω)
    (hA : IsPlaceOver A v) (K : Type) [Field K] [TopologicalSpace K] [T2Space K]
    (r : Formalism.ConjugateSelfDual.G E Ω →* Kˣ) (hr : Continuous r) (l : ℕ) (hl : l.Prime)
    (hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) (σ : Formalism.ConjugateSelfDual.G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (hσl : r σ ^ l = 1) : r σ = 1 := by
  have hvl : ¬ A.valuation (l : Ω) < 1 := by
    intro h
    apply hlv
    rw [← hA]
    simpa using h
  have hvl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)
  have hfin : ({u : Kˣ | u ^ l = 1} \ {1}).Finite := (finite_roots K l hl.ne_zero).diff
  have hop : IsOpen (r ⁻¹' ({u : Kˣ | u ^ l = 1} \ {1})ᶜ) :=
    hfin.isClosed.isOpen_compl.preimage hr
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
  have h1 : r σ ^ n = 1 := by
    have h2 : r (σ ^ n) ∉ ({u : Kˣ | u ^ l = 1} \ {1}) := hsub hτ
    by_contra hne
    apply h2
    refine ⟨?_, by rwa [map_pow]⟩
    show r (σ ^ n) ^ l = 1
    rw [map_pow, ← pow_mul, mul_comm, pow_mul, hσl, one_pow]
  have hc : Nat.Coprime l n := (Nat.Prime.coprime_iff_not_dvd hl).mpr hn
  have := (pow_gcd_eq_one (a := r σ) (m := l) (n := n)).mpr ⟨hσl, h1⟩
  rwa [hc, pow_one] at this

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ v A hA γ hγ K _ _ _ r hr m hm hI σ hσ`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Conclude with `hm (by simp)`. Establish `hw : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → r τ = 1`.

Introduce `τ hτ`. Assume the negation of the conclusion as `hne`. Establish `hd : orderOf (r τ) ∣ m` using `orderOf_dvd_of_pow_eq_one (hI τ (wild_mem_Ine hτ))`. Establish `hne1 : orderOf (r τ) ≠ 1` using `by rwa [Ne, orderOf_eq_one_iff]`. Take `⟨l, hl, k, hk⟩` from `Nat.exists_prime_and_dvd hne1`.

Establish `hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal`. Introduce `h`. Apply `hm` to reduce the goal to its premises. Take `⟨c, hc⟩` from `hd`. Rewrite using `[hc, hk]`.

Use `push_cast`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h)`. Establish `h1 : r (τ ^ k) = 1`. Use `eq_one_of_wild_prime E Ω v A hA K r hr l hl hlv _ (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_` and prove the remaining obligations. Rewrite using `[map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]`.

Rewrite `h1` using `[map_pow]`. Establish `h2` using `orderOf_dvd_of_pow_eq_one h1`. Establish `ho : orderOf (r τ) ≠ 0` using `fun h => hm0 (by simpa [h] using hd)`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`.

Conclude with `ho (by simpa using hk)`. Establish `h3` using `Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2`. Rewrite `h3` using `[hk]`. Use `hl.two_le` as an intermediate fact. Use `Nat.pos_of_ne_zero hk0` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `hfin : ((Subgroup.zpowers (r γ) : Subgroup Kˣ) : Set Kˣ).Finite`. Use `(finite_roots K m hm0).subset ?_` and prove the remaining obligations. Introduce and unpack `u ⟨z, rfl⟩`. Use `show (r γ ^ z) ^ m = 1`.

Rewrite using `[← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hI γ hγ.1, one_zpow]`. Establish `hc : IsClosed (((Subgroup.zpowers (r γ)).comap r : Subgroup (Formalism.ConjugateSelfDual.G E Ω)) : Set (Formalism.ConjugateSelfDual.G E Ω))` using `hfin.isClosed.preimage hr`. Use `closure_minimal (SetLike.coe_subset_coe.2 ((Subgroup.closure_le _).2 ?_)) hc (hγ.2 hσ)` and prove the remaining obligations. Introduce and unpack `τ (rfl | hτ)`. Conclude with `Subgroup.mem_zpowers _`.

Use `show r τ ∈ Subgroup.zpowers (r γ)`. Rewrite using `[hw τ hτ]`. Conclude with `one_mem _`.
-/
theorem mem_zpowers_of_tameGen : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (γ : Formalism.ConjugateSelfDual.G E Ω), TameGenAt A γ → ∀ (K : Type) [Field K] [TopologicalSpace K] [T2Space K] (r : Formalism.ConjugateSelfDual.G E Ω →* Kˣ), Continuous r → ∀ m : ℕ, ((m : ℕ) : 𝓞 E) ∉ v.asIdeal → (∀ σ ∈ Ine (F := E) A, r σ ^ m = 1) → ∀ σ ∈ Ine (F := E) A, r σ ∈ Subgroup.zpowers (r γ) := by
  intro E Ω _ _ _ _ _ v A hA γ hγ K _ _ _ r hr m hm hI σ hσ
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have hw : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → r τ = 1 := by
    intro τ hτ
    by_contra hne
    have hd : orderOf (r τ) ∣ m := orderOf_dvd_of_pow_eq_one (hI τ (wild_mem_Ine hτ))
    have hne1 : orderOf (r τ) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
    obtain ⟨l, hl, k, hk⟩ := Nat.exists_prime_and_dvd hne1
    have hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal := by
      intro h
      apply hm
      obtain ⟨c, hc⟩ := hd
      rw [hc, hk]
      push_cast
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h)
    have h1 : r (τ ^ k) = 1 := by
      refine eq_one_of_wild_prime E Ω v A hA K r hr l hl hlv _
        (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_
      rw [map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
    rw [map_pow] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    have ho : orderOf (r τ) ≠ 0 := fun h => hm0 (by simpa [h] using hd)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact ho (by simpa using hk)
    have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2
    rw [hk] at h3
    have := hl.two_le
    have := Nat.pos_of_ne_zero hk0
    nlinarith
  have hfin : ((Subgroup.zpowers (r γ) : Subgroup Kˣ) : Set Kˣ).Finite := by
    refine (finite_roots K m hm0).subset ?_
    rintro u ⟨z, rfl⟩
    show (r γ ^ z) ^ m = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hI γ hγ.1, one_zpow]
  have hc : IsClosed (((Subgroup.zpowers (r γ)).comap r : Subgroup (Formalism.ConjugateSelfDual.G E Ω)) :
      Set (Formalism.ConjugateSelfDual.G E Ω)) := hfin.isClosed.preimage hr
  refine closure_minimal (SetLike.coe_subset_coe.2 ((Subgroup.closure_le _).2 ?_)) hc (hγ.2 hσ)
  rintro τ (rfl | hτ)
  · exact Subgroup.mem_zpowers _
  · show r τ ∈ Subgroup.zpowers (r γ)
    rw [hw τ hτ]
    exact one_mem _

end GlobalTheory.TameGenPowers
