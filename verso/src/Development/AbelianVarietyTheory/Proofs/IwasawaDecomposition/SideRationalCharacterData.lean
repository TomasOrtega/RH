import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormVEqAbsNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIneOfUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaPowResidueCardSubOneApplyOfPowMem

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.ChiTame

section General

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `e : x ^ (k + 1) - y ^ (k + 1) = (x ^ k - y ^ k) * x + (x - y) * y ^ k` using `by ring`. Rewrite using `[e]`.

Use `Valuation.map_add_lt _ ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' hx) ih`. Rewrite using `[map_mul, map_pow]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hy k)) h`.
-/
theorem val_pow_sub_pow_lt (A : ValuationSubring Ω) {x y : Ω} (hx : A.valuation x ≤ 1) (hy : A.valuation y ≤ 1)
    (h : A.valuation (x - y) < 1) (k : ℕ) : A.valuation (x ^ k - y ^ k) < 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : x ^ (k + 1) - y ^ (k + 1) = (x ^ k - y ^ k) * x + (x - y) * y ^ k := by ring
    rw [e]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hx) ih
    · rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hy k)) h

/- English proof (translation)
Establish `hζ1 : A.valuation ζ = 1` using `GlobalTheory.val_eq_one_of_pow_eq_one A hm0 hζ`. Establish `hζ0 : ζ ≠ 0` using `by intro h; rw [h, zero_pow hm0] at hζ; exact zero_ne_one hζ`. Establish `hclose : A.valuation (ρ ζ - ζ) < 1` using `hρ.2 ζ hζ1.le`. Establish `hξ : ρ ζ * ζ⁻¹ = 1`. Use `GlobalTheory.eq_one_of_pow_eq_one_of_val_sub_lt A hm ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_pow, ← map_pow, inv_pow, hζ, map_one, inv_one, one_mul]`. Establish `e : ρ ζ * ζ⁻¹ - 1 = (ρ ζ - ζ) * ζ⁻¹` using `by field_simp`. Rewrite using `[e, Valuation.map_mul, map_inv₀, hζ1, inv_one, mul_one]`. Conclude with `hclose`. Conclude with `(mul_inv_eq_one₀ hζ0).1 hξ`.
-/
theorem ine_fix_root {A : ValuationSubring Ω} {m : ℕ} (hm : A.valuation (m : Ω) = 1) (hm0 : m ≠ 0) {ζ : Ω}
    (hζ : ζ ^ m = 1) {ρ : G E Ω} (hρ : ρ ∈ Ine (F := E) A) : ρ ζ = ζ := by
  have hζ1 : A.valuation ζ = 1 := GlobalTheory.val_eq_one_of_pow_eq_one A hm0 hζ
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, zero_pow hm0] at hζ; exact zero_ne_one hζ
  have hclose : A.valuation (ρ ζ - ζ) < 1 := hρ.2 ζ hζ1.le
  have hξ : ρ ζ * ζ⁻¹ = 1 := by
    refine GlobalTheory.eq_one_of_pow_eq_one_of_val_sub_lt A hm ?_ ?_
    · rw [mul_pow, ← map_pow, inv_pow, hζ, map_one, inv_one, one_mul]
    · have e : ρ ζ * ζ⁻¹ - 1 = (ρ ζ - ζ) * ζ⁻¹ := by field_simp
      rw [e, Valuation.map_mul, map_inv₀, hζ1, inv_one, mul_one]; exact hclose
  exact (mul_inv_eq_one₀ hζ0).1 hξ

/- English proof (translation)
Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Conclude with `hm (by simp)`. Assume the negation of the conclusion as `hne`. Establish `hd : orderOf (r τ) ∣ m` using `orderOf_dvd_of_pow_eq_one (hI τ (GlobalTheory.TameGenPowers.wild_mem_Ine hτ))`.

Establish `hne1 : orderOf (r τ) ≠ 1` using `by rwa [Ne, orderOf_eq_one_iff]`. Take `⟨l, hl, k, hk⟩` from `Nat.exists_prime_and_dvd hne1`. Establish `hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal`. Introduce `h`. Apply `hm` to reduce the goal to its premises.

Take `⟨c, hc⟩` from `hd`. Rewrite using `[hc, hk]`. Use `push_cast`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h)`. Establish `h1 : r (τ ^ k) = 1`.

Use `GlobalTheory.TameGenPowers.eq_one_of_wild_prime E Ω v A hA K r hr l hl hlv _ (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_` and prove the remaining obligations. Rewrite using `[map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]`. Rewrite `h1` using `[map_pow]`. Establish `h2` using `orderOf_dvd_of_pow_eq_one h1`. Establish `ho : orderOf (r τ) ≠ 0` using `fun h => hm0 (by simpa [h] using hd)`.

Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Conclude with `ho (by simpa using hk)`. Establish `h3` using `Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2`. Rewrite `h3` using `[hk]`.

Use `hl.two_le` as an intermediate fact. Use `Nat.pos_of_ne_zero hk0` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem eq_one_of_wild [IsAlgClosure E Ω] {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) {K : Type} [Field K] [TopologicalSpace K] [T2Space K] (r : G E Ω →* Kˣ)
    (hr : Continuous r) {m : ℕ} (hm : ((m : ℕ) : 𝓞 E) ∉ v.asIdeal) (hI : ∀ σ ∈ Ine (F := E) A, r σ ^ m = 1)
    (τ : G E Ω) (hτ : ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) : r τ = 1 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  by_contra hne
  have hd : orderOf (r τ) ∣ m := orderOf_dvd_of_pow_eq_one (hI τ (GlobalTheory.TameGenPowers.wild_mem_Ine hτ))
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
    refine GlobalTheory.TameGenPowers.eq_one_of_wild_prime E Ω v A hA K r hr l hl hlv _
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

/- English proof (translation)
Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Conclude with `hm (by simp)`. Establish `hmA : A.valuation (m : Ω) = 1`. Use `le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A m)) (not_lt.mp fun h => hm ?_)` and prove the remaining obligations.

Rewrite using `[← hA]`. Simplify using `using h`. Establish `hroot : ∀ σ : G E Ω, (σ π / π) ^ m = 1` using `fun σ => by`. Rewrite using `[div_pow, ← map_pow, hπ, σ.commutes, ← hπ, div_self (pow_ne_zero _ hπ0)]`. Use `set ζ := γ π / π with hζ`.

Establish `hζm : ζ ^ m = 1` using `hroot γ`. Take `⟨m', rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hm0`. Establish `hK : ∀ σ ∈ Subgroup.closure (insert γ {σ : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}), σ ∈ Ine (F` using `E) A ∧ ∃ n : ℕ, σ π = ζ ^ n * π ∧ r σ = r γ ^ n := by`. Introduce `σ hσ`. Proceed by induction on `hσ using Subgroup.closure_induction with`.

Consider the case `mem τ hτ`. Break down `hτ with rfl | hτ` into its components or cases. Conclude with `⟨hγ.1, 1, by rw [pow_one, hζ, div_mul_cancel₀ _ hπ0], (pow_one _).symm⟩`. Use `⟨GlobalTheory.TameGenPowers.wild_mem_Ine hτ, 0, ?_, by rw [pow_zero, eq_one_of_wild hA r hr hm hI τ hτ]⟩` and prove the remaining obligations. Use `GlobalTheory.eq_one_of_pow_eq_one_of_val_sub_lt A hmA (hroot τ) (hτ π hπ0)` as an intermediate fact.

Rewrite using `[pow_zero, one_mul]`. Conclude with `(div_eq_one_iff_eq hπ0).1 this`. Consider the case `one => exact ⟨one_mem _, 0, by simp, by simp⟩`. Consider the case `mul σ τ _ _ h1 h2`. Take `⟨i1, a, a1, a2⟩` from `h1`.

Take `⟨i2, b, b1, b2⟩` from `h2`. Use `⟨mul_mem i1 i2, a + b, ?_, by rw [map_mul, a2, b2, pow_add]⟩` and prove the remaining obligations. Rewrite using `[AlgEquiv.mul_apply, b1, map_mul, map_pow, ine_fix_root hmA hm0 hζm i1, a1]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `inv σ _ h1`.

Take `⟨i1, a, a1, a2⟩` from `h1`. Use `⟨inv_mem i1, a * m', ?_, ?_⟩` and prove the remaining obligations. Apply `σ.injective` to reduce the goal to its premises. Rewrite using `[mul_inv_apply, map_mul, map_pow, ine_fix_root hmA hm0 hζm i1, a1, ← mul_assoc, ← pow_add, show a * m' + a = (m' + 1) * a by ring, pow_mul, hζm, one_pow, one_mul]`. Rewrite using `[map_inv, a2, inv_eq_iff_mul_eq_one, ← pow_add, show a + a * m' = (m' + 1) * a by ring, pow_mul, hI γ hγ.1, one_pow]`.

Use `haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω`. Establish `hfin : ({u : Kˣ | u ^ (m' + 1) = 1} \ {r ρ}).Finite` using `(GlobalTheory.TameGenPowers.finite_roots K _ hm0).diff`. Establish `ho1 : IsOpen (r ⁻¹' ({u : Kˣ | u ^ (m' + 1) = 1} \ {r ρ})ᶜ)` using `hfin.isClosed.isOpen_compl.preimage hr`. Establish `ho2` using `(stabilizer_isOpen_of_isIntegral (K := E) π).preimage (continuous_const_mul ρ⁻¹)`. Take `⟨σ, ⟨h1, h2⟩, h3⟩` from `mem_closure_iff.1 (hγ.2 hρ) _ (ho1.inter ho2) ⟨by simp, by simp⟩`.

Take `⟨i1, n, n1, n2⟩` from `hK σ h3`. Use `⟨n, ?_, ?_⟩` and prove the remaining obligations. Establish `h4 : (ρ⁻¹ * σ) π = π` using `h2`. Rewrite using `[← n1]`. Use `conv_lhs => rw [← h4]`.

Rewrite using `[AlgEquiv.mul_apply, mul_inv_apply]`. Rewrite using `[← n2]`. Assume the negation of the conclusion as `hne`. Conclude with `h1 ⟨hI σ i1, fun h => hne (Eq.symm h)⟩`.
-/
theorem exists_pow_pair [IsAlgClosure E Ω] {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) {γ : G E Ω} (hγ : TameGenAt A γ) {K : Type} [Field K] [TopologicalSpace K] [T2Space K]
    (r : G E Ω →* Kˣ) (hr : Continuous r) {m : ℕ} (hm : ((m : ℕ) : 𝓞 E) ∉ v.asIdeal)
    (hI : ∀ σ ∈ Ine (F := E) A, r σ ^ m = 1) {π : Ω} (hπ0 : π ≠ 0) {c : E} (hπ : π ^ m = algebraMap E Ω c)
    {ρ : G E Ω} (hρ : ρ ∈ Ine (F := E) A) : ∃ n : ℕ, ρ π = (γ π / π) ^ n * π ∧ r ρ = r γ ^ n := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have hmA : A.valuation (m : Ω) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A m)) (not_lt.mp fun h => hm ?_)
    rw [← hA]
    simpa using h
  have hroot : ∀ σ : G E Ω, (σ π / π) ^ m = 1 := fun σ => by
    rw [div_pow, ← map_pow, hπ, σ.commutes, ← hπ, div_self (pow_ne_zero _ hπ0)]
  set ζ := γ π / π with hζ
  have hζm : ζ ^ m = 1 := hroot γ
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hK : ∀ σ ∈ Subgroup.closure (insert γ {σ : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}),
      σ ∈ Ine (F := E) A ∧ ∃ n : ℕ, σ π = ζ ^ n * π ∧ r σ = r γ ^ n := by
    intro σ hσ
    induction hσ using Subgroup.closure_induction with
    | mem τ hτ =>
      rcases hτ with rfl | hτ
      · exact ⟨hγ.1, 1, by rw [pow_one, hζ, div_mul_cancel₀ _ hπ0], (pow_one _).symm⟩
      · refine ⟨GlobalTheory.TameGenPowers.wild_mem_Ine hτ, 0, ?_, by rw [pow_zero, eq_one_of_wild hA r hr hm hI τ hτ]⟩
        have := GlobalTheory.eq_one_of_pow_eq_one_of_val_sub_lt A hmA (hroot τ) (hτ π hπ0)
        rw [pow_zero, one_mul]
        exact (div_eq_one_iff_eq hπ0).1 this
    | one => exact ⟨one_mem _, 0, by simp, by simp⟩
    | mul σ τ _ _ h1 h2 =>
      obtain ⟨i1, a, a1, a2⟩ := h1
      obtain ⟨i2, b, b1, b2⟩ := h2
      refine ⟨mul_mem i1 i2, a + b, ?_, by rw [map_mul, a2, b2, pow_add]⟩
      rw [AlgEquiv.mul_apply, b1, map_mul, map_pow, ine_fix_root hmA hm0 hζm i1, a1]
      ring
    | inv σ _ h1 =>
      obtain ⟨i1, a, a1, a2⟩ := h1
      refine ⟨inv_mem i1, a * m', ?_, ?_⟩
      · apply σ.injective
        rw [mul_inv_apply, map_mul, map_pow, ine_fix_root hmA hm0 hζm i1, a1, ← mul_assoc, ← pow_add,
          show a * m' + a = (m' + 1) * a by ring, pow_mul, hζm, one_pow, one_mul]
      · rw [map_inv, a2, inv_eq_iff_mul_eq_one, ← pow_add, show a + a * m' = (m' + 1) * a by ring, pow_mul,
          hI γ hγ.1, one_pow]
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  have hfin : ({u : Kˣ | u ^ (m' + 1) = 1} \ {r ρ}).Finite := (GlobalTheory.TameGenPowers.finite_roots K _ hm0).diff
  have ho1 : IsOpen (r ⁻¹' ({u : Kˣ | u ^ (m' + 1) = 1} \ {r ρ})ᶜ) := hfin.isClosed.isOpen_compl.preimage hr
  have ho2 := (stabilizer_isOpen_of_isIntegral (K := E) π).preimage (continuous_const_mul ρ⁻¹)
  obtain ⟨σ, ⟨h1, h2⟩, h3⟩ := mem_closure_iff.1 (hγ.2 hρ) _ (ho1.inter ho2) ⟨by simp, by simp⟩
  obtain ⟨i1, n, n1, n2⟩ := hK σ h3
  refine ⟨n, ?_, ?_⟩
  · have h4 : (ρ⁻¹ * σ) π = π := h2
    rw [← n1]
    conv_lhs => rw [← h4]
    rw [AlgEquiv.mul_apply, mul_inv_apply]
  · rw [← n2]
    by_contra hne
    exact h1 ⟨hI σ i1, fun h => hne (Eq.symm h)⟩

/- English proof (translation)
Use `haveI : Fact g.Prime := ⟨hg⟩`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E`. Establish `hg2` using `hg.two_le`. Establish `hm : 0 < g - 1` using `by omega`. Establish `hg1 : ((g - 1 : ℕ) : 𝓞 E) ∉ v.asIdeal` using `fun h => by`.

Apply `v.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Use `v.asIdeal.sub_mem hgv h` as an intermediate fact. Rewrite `this` using `[Nat.cast_sub hg.one_le, Nat.cast_one, sub_sub_cancel]`. Then use the resulting hypothesis. Take `⟨π, hπ⟩` from `IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (((g : ℕ) : 𝓞 E) : E)) hm`.

Establish `hgE : (((g : ℕ) : 𝓞 E) : E) ≠ 0` using `by simpa using hg.ne_zero`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Rewrite `hπ` using `[zero_pow hm.ne', eq_comm, map_eq_zero]`. Conclude with `hgE hπ`.

Take `⟨b, hb⟩` from `IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod g)ˣ)`. Rewrite `hb` using `[Nat.card_eq_fintype_card, ZMod.card_units]`. Use `set a : ℕ := (b : ZMod g).val with hadef`. Establish `hac : a.Coprime g` using `ZMod.val_coe_unit_coprime b`. Establish `ha0 : ((a : 𝓞 E) : E) ≠ 0`.

Establish `: a ≠ 0`. Introduce `h`. Rewrite `hac` using `[h, Nat.coprime_zero_left]`. Conclude with `hg.ne_one hac`. Simplify using `using this`.

Establish `hx` using `hunit a hac (Units.mk0 _ ha0) (by simp)`. Take `⟨σ, hσ, eσ, vσ⟩` from `GlobalTheory.TameRecip.exists_ine_of_unit hP E Ω art ha v A hA g hgv hgv2 π (by rw [hN]; exact hπ) _ (a : 𝓞 E) hx (by show Valued.v (algebraMap E (v.adicCompletion E) ((a : 𝓞 E) : E) - _) < 1`. Rewrite using `[sub_self, map_zero]`. Conclude with `zero_lt_one)`. Take `⟨n, n1, n2⟩` from `exists_pow_pair hA hγ r hr hg1 hI hπ0 hπ hσ`.

Use `set ζ := γ π / π with hζ`. Establish `hζm : ζ ^ (g - 1) = 1`. Rewrite using `[hζ, div_pow, ← map_pow, hπ, γ.commutes, ← hπ, div_self (pow_ne_zero _ hπ0)]`. Rewrite `vσ` using `[n1, mul_div_cancel_right₀ _ hπ0]`. Establish `hζ1 : A.valuation (ζ ^ n) ≤ 1`.

Rewrite using `[map_pow, GlobalTheory.val_eq_one_of_pow_eq_one A hm.ne' hζm, one_pow]`. Establish `haA : A.valuation (algebraMap E Ω ((a : 𝓞 E) : E)) ≤ 1`. Establish `: algebraMap E Ω ((a : 𝓞 E) : E) = (a : Ω)` using `by simp`. Rewrite using `[this]`. Conclude with `(A.valuation_le_one_iff _).mpr (natCast_mem A a)`.

Establish `hpow` using `val_pow_sub_pow_lt A hζ1 haA vσ`. Establish `hcop : n.Coprime (g - 1)`. Take `⟨e, he⟩` from `Nat.gcd_dvd_right n (g - 1)`. Take `⟨n', hn'⟩` from `Nat.gcd_dvd_left n (g - 1)`. Establish `h1 : (ζ ^ n) ^ e = 1`.

Rewrite using `[← pow_mul, show n * e = (g - 1) * n' by rw [he]; nth_rewrite 1 [hn']; ring, pow_mul, hζm, one_pow]`. Establish `h2` using `hpow e`. Rewrite `h2` using `[h1]`. Establish `h3 : ((1 - (a : ℤ) ^ e : ℤ) : 𝓞 E) ∈ v.asIdeal`. Rewrite using `[← hA]`.

Simplify using `using h2`. Establish `h4 : (g : ℤ) ∣ 1 - (a : ℤ) ^ e`. Assume the negation of the conclusion as `hnd`. Take `⟨s, t, hst⟩` from `((Nat.prime_iff_prime_int.1 hg).irreducible.coprime_iff_not_dvd.2 hnd).map (Int.castRingHom (𝓞 E))`. Apply `v.isPrime.ne_top` to reduce the goal to its premises.

Rewrite using `[Ideal.eq_top_iff_one, ← hst]`. Conclude with `v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ (by simpa using hgv)) (v.asIdeal.mul_mem_left _ h3)`. Establish `h5 : b ^ e = 1`. Use `(ZMod.intCast_zmod_eq_zero_iff_dvd _ g).2 h4` as an intermediate fact. Apply `Units.ext` to reduce the goal to its premises.

Move the coercions through the operations in `at this`. Rewrite `this` using `[hadef, ZMod.natCast_zmod_val, sub_eq_zero]`. Rewrite using `[Units.val_pow_eq_pow_val, ← this, Units.val_one]`. Establish `h6` using `orderOf_dvd_of_pow_eq_one h5`. Rewrite `h6` using `[hb]`.

Establish `he0 : 0 < e` using `Nat.pos_of_ne_zero (by rintro rfl; omega)`. Establish `h7` using `Nat.le_of_dvd he0 h6`. Establish `h8 : 0 < Nat.gcd n (g - 1)` using `Nat.gcd_pos_of_pos_right _ hm`. Use `show Nat.gcd n (g - 1) = 1`. Generalize the expression as in `Nat.gcd n (g - 1) = d at *`.

Use the polynomial consequences of the given equalities and inequalities. Take `⟨k, hk⟩ : ∃ k, n * k ≡ 1 [MOD g - 1]` from `⟨n ^ (Nat.totient (g - 1) - 1), by`. Rewrite using `[← pow_succ', Nat.sub_add_cancel (Nat.totient_pos.2 hm)]`. Conclude with `Nat.ModEq.pow_totient hcop⟩`. Establish `hu : (((a : 𝓞 E) ^ k : 𝓞 E) : E) ≠ 0`.

Use `push_cast`. Conclude with `pow_ne_zero _ (by simpa using ha0)`. Establish `hmk : Units.mk0 _ hu = Units.mk0 _ ha0 ^ k` using `Units.ext (by simp)`. Use `⟨(a : 𝓞 E) ^ k, hu, ⟨A, hA, hγ.1, g, π, hgv, hgv2, by rw [hN]; exact hπ, ?_⟩, hunit (a ^ k) (hac.pow_left k) _ (by simp), σ ^ k, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hpow k`.

Rewrite `h1` using `[← pow_mul, pow_eq_pow_of_modEq hk hζm, pow_one, ← map_pow]`. Simplify using `using h1`. Rewrite using `[hmk, map_pow, map_pow, map_pow, map_pow, eσ]`. Rewrite using `[map_pow, n2, ← pow_mul, pow_eq_pow_of_modEq hk (hI γ hγ.1), pow_one]`.
-/
theorem exists_tameRep (hP : GlobalTheory.Published.GlobalArtinReciprocity) [IsTotallyComplex E] [IsAlgClosure E Ω]
    {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) {g : ℕ} (hg : g.Prime) (hN : normV v = g) (hgv : ((g : ℕ) : 𝓞 E) ∈ v.asIdeal)
    (hgv2 : ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2)
    (hunit : ∀ a : ℕ, a.Coprime g → ∀ x : Eˣ, (x : E) = a → IsUnitAt v (atFin v x))
    {γ : G E Ω} (hγ : TameGenAt A γ) {K : Type} [Field K] [TopologicalSpace K] [T2Space K]
    (r : G E Ω →* Kˣ) (hr : Continuous r) (hI : ∀ σ ∈ Ine (F := E) A, r σ ^ (g - 1) = 1) :
    ∃ (u : 𝓞 E) (hu : (u : E) ≠ 0), NX.TameRep v 1 γ u ∧ IsUnitAt v (atFin v (Units.mk0 (u : E) hu)) ∧
      ∃ σ : G E Ω, art (localIdele E v (atFin v (Units.mk0 (u : E) hu))) = toAb E Ω σ ∧ r σ = r γ := by
  haveI : Fact g.Prime := ⟨hg⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hg2 := hg.two_le
  have hm : 0 < g - 1 := by omega
  have hg1 : ((g - 1 : ℕ) : 𝓞 E) ∉ v.asIdeal := fun h => by
    apply v.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have := v.asIdeal.sub_mem hgv h
    rwa [Nat.cast_sub hg.one_le, Nat.cast_one, sub_sub_cancel] at this
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (((g : ℕ) : 𝓞 E) : E)) hm
  have hgE : (((g : ℕ) : 𝓞 E) : E) ≠ 0 := by simpa using hg.ne_zero
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne', eq_comm, map_eq_zero] at hπ
    exact hgE hπ
  obtain ⟨b, hb⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod g)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hb
  set a : ℕ := (b : ZMod g).val with hadef
  have hac : a.Coprime g := ZMod.val_coe_unit_coprime b
  have ha0 : ((a : 𝓞 E) : E) ≠ 0 := by
    have : a ≠ 0 := by
      intro h
      rw [h, Nat.coprime_zero_left] at hac
      exact hg.ne_one hac
    simpa using this
  have hx := hunit a hac (Units.mk0 _ ha0) (by simp)
  obtain ⟨σ, hσ, eσ, vσ⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hP E Ω art ha v A hA g hgv hgv2 π (by rw [hN]; exact hπ)
    _ (a : 𝓞 E) hx (by
      show Valued.v (algebraMap E (v.adicCompletion E) ((a : 𝓞 E) : E) - _) < 1
      rw [sub_self, map_zero]
      exact zero_lt_one)
  obtain ⟨n, n1, n2⟩ := exists_pow_pair hA hγ r hr hg1 hI hπ0 hπ hσ
  set ζ := γ π / π with hζ
  have hζm : ζ ^ (g - 1) = 1 := by
    rw [hζ, div_pow, ← map_pow, hπ, γ.commutes, ← hπ, div_self (pow_ne_zero _ hπ0)]
  rw [n1, mul_div_cancel_right₀ _ hπ0] at vσ
  have hζ1 : A.valuation (ζ ^ n) ≤ 1 := by
    rw [map_pow, GlobalTheory.val_eq_one_of_pow_eq_one A hm.ne' hζm, one_pow]
  have haA : A.valuation (algebraMap E Ω ((a : 𝓞 E) : E)) ≤ 1 := by
    have : algebraMap E Ω ((a : 𝓞 E) : E) = (a : Ω) := by simp
    rw [this]
    exact (A.valuation_le_one_iff _).mpr (natCast_mem A a)
  have hpow := val_pow_sub_pow_lt A hζ1 haA vσ
  have hcop : n.Coprime (g - 1) := by
    obtain ⟨e, he⟩ := Nat.gcd_dvd_right n (g - 1)
    obtain ⟨n', hn'⟩ := Nat.gcd_dvd_left n (g - 1)
    have h1 : (ζ ^ n) ^ e = 1 := by
      rw [← pow_mul, show n * e = (g - 1) * n' by rw [he]; nth_rewrite 1 [hn']; ring, pow_mul, hζm, one_pow]
    have h2 := hpow e
    rw [h1] at h2
    have h3 : ((1 - (a : ℤ) ^ e : ℤ) : 𝓞 E) ∈ v.asIdeal := by
      rw [← hA]
      simpa using h2
    have h4 : (g : ℤ) ∣ 1 - (a : ℤ) ^ e := by
      by_contra hnd
      obtain ⟨s, t, hst⟩ := ((Nat.prime_iff_prime_int.1 hg).irreducible.coprime_iff_not_dvd.2 hnd).map
        (Int.castRingHom (𝓞 E))
      apply v.isPrime.ne_top
      rw [Ideal.eq_top_iff_one, ← hst]
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ (by simpa using hgv)) (v.asIdeal.mul_mem_left _ h3)
    have h5 : b ^ e = 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ g).2 h4
      apply Units.ext
      push_cast at this
      rw [hadef, ZMod.natCast_zmod_val, sub_eq_zero] at this
      rw [Units.val_pow_eq_pow_val, ← this, Units.val_one]
    have h6 := orderOf_dvd_of_pow_eq_one h5
    rw [hb] at h6
    have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have h7 := Nat.le_of_dvd he0 h6
    have h8 : 0 < Nat.gcd n (g - 1) := Nat.gcd_pos_of_pos_right _ hm
    show Nat.gcd n (g - 1) = 1
    generalize Nat.gcd n (g - 1) = d at *
    nlinarith
  obtain ⟨k, hk⟩ : ∃ k, n * k ≡ 1 [MOD g - 1] :=
    ⟨n ^ (Nat.totient (g - 1) - 1), by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.totient_pos.2 hm)]
      exact Nat.ModEq.pow_totient hcop⟩
  have hu : (((a : 𝓞 E) ^ k : 𝓞 E) : E) ≠ 0 := by
    push_cast
    exact pow_ne_zero _ (by simpa using ha0)
  have hmk : Units.mk0 _ hu = Units.mk0 _ ha0 ^ k := Units.ext (by simp)
  refine ⟨(a : 𝓞 E) ^ k, hu, ⟨A, hA, hγ.1, g, π, hgv, hgv2, by rw [hN]; exact hπ, ?_⟩,
    hunit (a ^ k) (hac.pow_left k) _ (by simp), σ ^ k, ?_, ?_⟩
  · have h1 := hpow k
    rw [← pow_mul, pow_eq_pow_of_modEq hk hζm, pow_one, ← map_pow] at h1
    simpa using h1
  · rw [hmk, map_pow, map_pow, map_pow, map_pow, eσ]
  · rw [map_pow, n2, ← pow_mul, pow_eq_pow_of_modEq hk (hI γ hγ.1), pow_one]

end General

/- English proof (translation)
Assemble the required witnesses or components as `⟨D.host.g_prime k⟩; ∃ u : (ZMod (D.host.g k))ˣ, (u = D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩ ∨ u = (D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩)⁻¹) ∧ iotaO X.nd Y.naut i ((X.nd.chi i 1 (D.ntypes.tg k v) : (X.nd.O i)ˣ) : X.nd.O i) = D.ntyp …`.
-/
theorem chi_one_tameGen : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), AutSpec A M tp.tup Sp.iq Y Cb → ∀ (i : X.nd.Loc) k v, X.nd.l i ≠ D.host.g k → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ u : (ZMod (D.host.g k))ˣ, (u = D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩ ∨ u = (D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩)⁻¹) ∧ iotaO X.nd Y.naut i ((X.nd.chi i 1 (D.ntypes.tg k v) : (X.nd.O i)ˣ) : X.nd.O i) = D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k))) := by
  intro hP D cf jE A low Pq S hL eig θ Bs M C tp h1 h2 h3 he h5 h6 big X T Sp Y Cb hAu i k v hl
  obtain ⟨art, ha⟩ := hP D.host.E D.nd.Om
  have hj := X.nd.j_range i
  let j' : Fin D.R.m := ⟨X.nd.j i - 1, by omega⟩
  obtain ⟨n, hG⟩ := GlobalTheory.ChiLocGal.chi1_loc_isGal D cf jE A low Pq S hL eig θ Bs M C tp h1 h2 h3 he h5 h6 big X T Sp Y Cb
    hAu art ha i j' (by simp only [j']; omega)
  let C' : GlobalTheory.Mem.Chr.HFrame D.host (eExp D) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  have hlp : (X.nd.l i).Prime := Fact.out
  have hgp := D.host.g_prime k
  have hwg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  obtain ⟨hN, hg2, -⟩ := GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ hgp (D.nd.g_split k) _ hwg
  have hwl : ((X.nd.l i : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal :=
    GlobalTheory.GalChar.notMem_of_ne hgp hlp hl.symm hwg
  have hA := D.nd.plOm.2 (D.naut.plGw k v)
  obtain ⟨hp, -, hpg, -, hD⟩ := GlobalTheory.GalChar.inertialOrderFifteenChar_auxiliaryPrime_spec C' (l := X.nd.l i)
  have hdel : (cf.delAt (X.nd.l i)).UnrAt (D.naut.plGw k v) :=
    hD.unr _ (GlobalTheory.GalChar.notMem_of_ne hgp hp (hpg k).symm hwg)
  have hloc : ∀ x, IsUnitAt (D.naut.plGw k v) x →
      (GlobalTheory.GalChar.block (cf.mu0 j' * cf.delAt (X.nd.l i)) cf.eta D.R.r).loc (D.naut.plGw k v) x =
        (cf.mu0 j').loc (D.naut.plGw k v) x := fun x hx => by
    rw [GlobalTheory.GalChar.block_loc (cf.isEta.unr _) hx, HChar.loc_mul, hdel x hx, mul_one]
  have hI := (hG.ine_pow_iff ha (Or.inl hwl) hA (D.host.g k - 1)).2 fun x hx => by
    rw [hloc x hx, ← hN]
    exact (GlobalTheory.Mem.WildChar.orders_on_units _ _ _).1 ((cf.isMu0 j').tame _) x hx
  haveI := D.host.isCMField_hostE
  obtain ⟨u, hu, hrep, hunit, σ, eσ, hσ⟩ := exists_tameRep hP ha hA hgp
    ((GlobalTheory.ChiLocGal.normV_eq_absNorm _).trans hN) hwg hg2 (fun a ha' x hx => isUnitAt_nat hwg ha' hx)
    (D.ntypes.tg_gen k v) _ (hG.cont (X.nd.O_adic i) (Sp.iq_alg i)) fun σ hσ => by
      rw [← map_pow, GlobalTheory.GalChar.inQ_eq_one, map_pow, hI σ hσ]
  obtain ⟨c, hc, hcv⟩ := A.chiT k v j' u hu hrep
  refine ⟨c, hc, ?_⟩
  have hvS : D.naut.plGw k v ∈ X.nd.S i := by
    rw [X.nd.S_def i]
    refine ⟨?_, hwl⟩
    fin_cases k
    · exact Or.inl hwg
    · exact Or.inr (Or.inl hwg)
  have hvQ : D.naut.plGw k v ∉ X.nd.Q i := fun h => (Finset.disjoint_left.mp (X.nd.SQ_disj i) hvS) h
  have hψ : T.psiL i (D.ntypes.tg k v) = 1 := by
    by_contra hne
    exact hvQ ((T.psiL_ram i _ _ hA).mp ⟨_, D.ntypes.tg_mem k v, hne⟩)
  have e1 := hG.loc (Or.inl hwl) eσ
  rw [GlobalTheory.GalChar.inQ_inj _ hσ, hloc _ hunit] at e1
  have e2 : X.nd.chi i 1 (D.ntypes.tg k v) = ((Units.map (T.twist₂ i).toMonoidHom).comp
      (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i))) (D.ntypes.tg k v) := by
    refine (DFunLike.congr_fun (T.chi_tw i) _).trans ?_
    exact (congrArg (_ * ·) hψ).trans (mul_one _)
  rw [← hcv, e2]
  refine Eq.trans ?_ e1
  unfold iotaO
  rw [hAu.iotaQ i]
  rfl

end GlobalTheory.ChiTame

end
