import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.TaylorExpansion

namespace FunctorialResolution.EmbeddedResolution

section

variable {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ m ih`. Take `⟨c, hc⟩` from `ih`. Use `⟨c + Δ b, ?_⟩` and prove the remaining obligations.

Establish `hbp : b ^ (m + 1) = b * b ^ m` using `by ring`. Establish `hl : Δ (b * b ^ m) = b * Δ (b ^ m) + b ^ m * Δ b`. Simplify using the standard rewrite rules. Rewrite using `[hbp, hl]`. Take the linear combination `b * hc`.
-/
private theorem exists_mul_deriv_pow_eq_pow_mul {k : Type*} [CommRing k] {S : Type*}
    [CommRing S] [Algebra k S] (Δ : Derivation k S S) (b : S) (n : ℕ) :
    ∃ c : S, b * Δ (b ^ n) = b ^ n * c := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c + Δ b, ?_⟩
      have hbp : b ^ (m + 1) = b * b ^ m := by ring
      have hl : Δ (b * b ^ m) = b * Δ (b ^ m) + b ^ m * Δ b := by
        simp
      rw [hbp, hl]
      linear_combination b * hc

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `g hg`. Simplify using `using hg`.

Consider the case `succ j ih`. Introduce `g hg`. Establish `hIH : b ^ j * (⇑Δ)^[j] g ∈ J` using `ih g hg`. Establish `hkey : b * Δ (b ^ j * (⇑Δ)^[j] g) ∈ J` using `hMJ (Ideal.mul_mem_mul hb (derivation_apply_mem_derivIdeal k J Δ hIH))`. Take `⟨c, hc⟩` from `exists_mul_deriv_pow_eq_pow_mul Δ b j`.

Establish `hleib : Δ (b ^ j * (⇑Δ)^[j] g) = b ^ j * Δ ((⇑Δ)^[j] g) + (⇑Δ)^[j] g * Δ (b ^ j)`. Simplify using the standard rewrite rules. Establish `hiter : (⇑Δ)^[j + 1] g = Δ ((⇑Δ)^[j] g)` using `Function.iterate_succ_apply' (⇑Δ) j g`. Establish `hEq : b ^ (j + 1) * (⇑Δ)^[j + 1] g = b * Δ (b ^ j * (⇑Δ)^[j] g) - c * (b ^ j * (⇑Δ)^[j] g)`. Rewrite using `[hiter, hleib]`.

Take the linear combination `(-((⇑Δ)^[j] g)) * hc`. Rewrite using `[hEq]`. Conclude with `Submodule.sub_mem J hkey (Ideal.mul_mem_left J c hIH)`.
-/
theorem pow_mul_iterate_deriv_mem_of_mul_derivIdeal_le (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (M J : Ideal S) (Δ : Derivation k S S) (b : S)
    (hMJ : M * derivIdeal k J ≤ J) (hb : b ∈ M) :
    ∀ (j : ℕ) (g : S), g ∈ J → b ^ j * (⇑Δ)^[j] g ∈ J := by
  intro j
  induction j with
  | zero =>
      intro g hg
      simpa using hg
  | succ j ih =>
      intro g hg
      have hIH : b ^ j * (⇑Δ)^[j] g ∈ J := ih g hg
      have hkey : b * Δ (b ^ j * (⇑Δ)^[j] g) ∈ J :=
        hMJ (Ideal.mul_mem_mul hb (derivation_apply_mem_derivIdeal k J Δ hIH))
      obtain ⟨c, hc⟩ := exists_mul_deriv_pow_eq_pow_mul Δ b j
      have hleib : Δ (b ^ j * (⇑Δ)^[j] g)
          = b ^ j * Δ ((⇑Δ)^[j] g) + (⇑Δ)^[j] g * Δ (b ^ j) := by
        simp
      have hiter : (⇑Δ)^[j + 1] g = Δ ((⇑Δ)^[j] g) := Function.iterate_succ_apply' (⇑Δ) j g
      have hEq : b ^ (j + 1) * (⇑Δ)^[j + 1] g
          = b * Δ (b ^ j * (⇑Δ)^[j] g) - c * (b ^ j * (⇑Δ)^[j] g) := by
        rw [hiter, hleib]
        linear_combination (-((⇑Δ)^[j] g)) * hc
      rw [hEq]
      exact Submodule.sub_mem J hkey (Ideal.mul_mem_left J c hIH)

end

section

variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]

/- English proof (translation)
Simplify using `[TaylorExpansion.truncatedSeries_apply]`.
-/
theorem truncatedSeries_length_one (σ : R →+* S) (D : Derivation A R R) (β : S) (f : R) :
    TaylorExpansion.truncatedSeries σ D β 1 f = σ f := by
  simp [TaylorExpansion.truncatedSeries_apply]

/- English proof (translation)
Establish `h2 : (⇑D)^[2] f = 0`. Rewrite using `[show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]`. Simplify using `[hf]`. Establish `hvan : ∀ j : ℕ, 2 ≤ j → (⇑D)^[j] f = 0`. Introduce `j hj`.

Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le hj`. Rewrite using `[Nat.add_comm, Function.iterate_add_apply, h2]`. Conclude with `Function.iterate_fixed (by simp) m`. Establish `hsub : Finset.range 2 ⊆ Finset.range N` using `fun j hj => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hN)`. Establish `hsum : ∑ j ∈ Finset.range 2, algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * β ^ j = ∑ j ∈ Finset.range N, algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * β ^ j`.

Use `Finset.sum_subset hsub ?_` and prove the remaining obligations. Introduce `j _ hj`. Establish `hj2 : 2 ≤ j`. Break down `Nat.lt_or_ge j 2 with h | h` into its components or cases. Conclude with `absurd (Finset.mem_range.mpr h) hj`.

Conclude with `h`. Rewrite using `[hvan j hj2]`. Simplify using the standard rewrite rules. Rewrite using `[TaylorExpansion.truncatedSeries_apply, ← hsum]`. Simplify using `[Finset.sum_range_succ]`.
-/
theorem truncatedSeries_of_deriv_deriv_eq_zero (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (hN : 2 ≤ N) (f : R) (hf : D (D f) = 0) :
    TaylorExpansion.truncatedSeries σ D β N f = σ f + σ (D f) * β := by
  have h2 : (⇑D)^[2] f = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]
    simp [hf]
  have hvan : ∀ j : ℕ, 2 ≤ j → (⇑D)^[j] f = 0 := by
    intro j hj
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [Nat.add_comm, Function.iterate_add_apply, h2]
    exact Function.iterate_fixed (by simp) m
  have hsub : Finset.range 2 ⊆ Finset.range N := fun j hj =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hN)
  have hsum : ∑ j ∈ Finset.range 2,
        algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * β ^ j
      = ∑ j ∈ Finset.range N,
        algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * β ^ j := by
    refine Finset.sum_subset hsub ?_
    intro j _ hj
    have hj2 : 2 ≤ j := by
      rcases Nat.lt_or_ge j 2 with h | h
      · exact absurd (Finset.mem_range.mpr h) hj
      · exact h
    rw [hvan j hj2]
    simp
  rw [TaylorExpansion.truncatedSeries_apply, ← hsum]
  simp [Finset.sum_range_succ]

/- English proof (translation)
Rewrite using `[TaylorExpansion.truncatedSeries_apply]`. Use `Ideal.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Establish `h : φ (b ^ j * (⇑D)^[j] g) ∈ Ideal.map φ J` using `Ideal.mem_map_of_mem φ (hstab j g hg)`. Rewrite `h` using `[map_mul, map_pow]`. Establish `h2` using `Ideal.mul_mem_left (Ideal.map φ J) (algebraMap ℚ B ((j.factorial : ℚ)⁻¹)) h`.

Establish `h3 : algebraMap ℚ B ((j.factorial : ℚ)⁻¹) * φ ((⇑D)^[j] g) * φ b ^ j = algebraMap ℚ B ((j.factorial : ℚ)⁻¹) * (φ b ^ j * φ ((⇑D)^[j] g))`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3]`. Conclude with `h2`.
-/
theorem truncatedSeries_mem_map {A R B : Type*} [CommRing A] [CommRing R] [CommRing B] [Algebra A R]
    [Algebra ℚ B] (φ : R →+* B) (D : Derivation A R R) (b : R) (J : Ideal R)
    (hstab : ∀ (j : ℕ) (g : R), g ∈ J → b ^ j * (⇑D)^[j] g ∈ J)
    (N : ℕ) (g : R) (hg : g ∈ J) :
    TaylorExpansion.truncatedSeries φ D (φ b) N g ∈ Ideal.map φ J := by
  rw [TaylorExpansion.truncatedSeries_apply]
  refine Ideal.sum_mem _ fun j _ => ?_
  have h : φ (b ^ j * (⇑D)^[j] g) ∈ Ideal.map φ J :=
    Ideal.mem_map_of_mem φ (hstab j g hg)
  rw [map_mul, map_pow] at h
  have h2 := Ideal.mul_mem_left (Ideal.map φ J) (algebraMap ℚ B ((j.factorial : ℚ)⁻¹)) h
  have h3 : algebraMap ℚ B ((j.factorial : ℚ)⁻¹) * φ ((⇑D)^[j] g) * φ b ^ j
      = algebraMap ℚ B ((j.factorial : ℚ)⁻¹) * (φ b ^ j * φ ((⇑D)^[j] g)) := by
    ring
  rw [h3]
  exact h2

end

section

open IsLocalRing

def IsTaylorExpansionOn (P : Type*) [CommRing P] {A R B : Type*} [CommRing A] [CommRing R]
    [CommRing B] [Algebra P R] [Algebra A R] [IsLocalRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ x : P,
    TaylorExpansion.truncatedSeries φ D β N (algebraMap P R x) - φ' (algebraMap P R x) ∈ maximalIdeal B ^ N

/- English proof (translation)
Introduce `N hN x`. Establish `hβN : β ^ N ∈ maximalIdeal B ^ N` using `Ideal.pow_mem_pow hβ N`. Establish `key : (TaylorExpansion.truncatedSeriesRingHom φ D β N (maximalIdeal B ^ N) hN hβN).comp (algebraMap (MvPolynomial ι k) R) = ((Ideal.Quotient.mk (maximalIdeal B ^ N)).comp φ').comp (algebraMap (MvPolynomial ι k) R)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`.

Establish `h1 : TaylorExpansion.truncatedSeries φ D β N (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) = φ' (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c))`. Rewrite using `[TaylorExpansion.truncatedSeries_of_deriv_eq_zero φ D β N hN (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) (hDconst c)]`. Conclude with `hconst c`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, TaylorExpansion.truncatedSeriesRingHom_apply, h1]`. Introduce `i`.

Simplify using `only [RingHom.coe_comp, Function.comp_apply, TaylorExpansion.truncatedSeriesRingHom_apply]`. Conclude with `Ideal.Quotient.eq.2 (hvar i N hN)`. Establish `h` using `RingHom.congr_fun key x`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, TaylorExpansion.truncatedSeriesRingHom_apply] at h`. Conclude with `Ideal.Quotient.eq.1 h`.
-/
theorem isTaylorExpansionOn_mvPolynomial {k : Type*} [CommRing k] {ι : Type*}
    {A R B : Type*} [CommRing A] [CommRing R] [CommRing B]
    [Algebra (MvPolynomial ι k) R] [Algebra A R] [IsLocalRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hβ : β ∈ maximalIdeal B)
    (hconst : ∀ c : k,
      φ (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) =
        φ' (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)))
    (hDconst : ∀ c : k, D (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) = 0)
    (hvar : ∀ (i : ι) (N : ℕ), 1 ≤ N →
      TaylorExpansion.truncatedSeries φ D β N (algebraMap (MvPolynomial ι k) R (MvPolynomial.X i)) -
          φ' (algebraMap (MvPolynomial ι k) R (MvPolynomial.X i)) ∈ maximalIdeal B ^ N) :
    IsTaylorExpansionOn (MvPolynomial ι k) φ φ' D β := by
  intro N hN x
  have hβN : β ^ N ∈ maximalIdeal B ^ N := Ideal.pow_mem_pow hβ N
  have key :
      (TaylorExpansion.truncatedSeriesRingHom φ D β N (maximalIdeal B ^ N) hN hβN).comp
          (algebraMap (MvPolynomial ι k) R) =
        ((Ideal.Quotient.mk (maximalIdeal B ^ N)).comp φ').comp
          (algebraMap (MvPolynomial ι k) R) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have h1 : TaylorExpansion.truncatedSeries φ D β N
            (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c))
          = φ' (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) := by
        rw [TaylorExpansion.truncatedSeries_of_deriv_eq_zero φ D β N hN
          (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) (hDconst c)]
        exact hconst c
      simp only [RingHom.coe_comp, Function.comp_apply, TaylorExpansion.truncatedSeriesRingHom_apply, h1]
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply, TaylorExpansion.truncatedSeriesRingHom_apply]
      exact Ideal.Quotient.eq.2 (hvar i N hN)
  have h := RingHom.congr_fun key x
  simp only [RingHom.coe_comp, Function.comp_apply, TaylorExpansion.truncatedSeriesRingHom_apply] at h
  exact Ideal.Quotient.eq.1 h

/- English proof (translation)
Establish `h0 : KaehlerDifferential.D P R x = 0` using `Subsingleton.elim _ _`. Establish `h1 : (Derivation.liftKaehlerDifferential d) (KaehlerDifferential.D P R x) = d x` using `Derivation.liftKaehlerDifferential_comp_D d x`. Rewrite `h1` using `[h0, map_zero]`. Conclude with `h1.symm`.
-/
private theorem derivation_apply_eq_zero_of_formallyUnramified {P R : Type*} [CommRing P]
    [CommRing R] [Algebra P R] [Algebra.FormallyUnramified P R] {M : Type*} [AddCommGroup M]
    [Module P M] [Module R M] [IsScalarTower P R M] (d : Derivation P R M) (x : R) : d x = 0 := by
  have h0 : KaehlerDifferential.D P R x = 0 := Subsingleton.elim _ _
  have h1 : (Derivation.liftKaehlerDifferential d) (KaehlerDifferential.D P R x) = d x :=
    Derivation.liftKaehlerDifferential_comp_D d x
  rw [h0, map_zero] at h1
  exact h1.symm

/- English proof (translation)
Set `_ : Algebra R B` to `φ'.toAlgebra`. Set `_ : Algebra P B` to `(φ'.comp (algebraMap P R)).toAlgebra`. Establish `: IsScalarTower P R B` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: IsScalarTower P R (B ⧸ m ^ (k + 1))` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `hleib : ∀ a b : R, T (a * b) - φ' (a * b) - (φ' a * (T b - φ' b) + φ' b * (T a - φ' a)) ∈ m ^ (k + 1)`.

Introduce `a b`. Establish `h1 : T (a * b) - T a * T b ∈ m ^ (k + 1)` using `hmul a b`. Establish `h2 : (T a - φ' a) * (T b - φ' b) ∈ m ^ (k + 1)`. Establish `h3 : (T a - φ' a) * (T b - φ' b) ∈ m ^ k * m ^ k` using `Ideal.mul_mem_mul (hind a) (hind b)`. Establish `h4 : m ^ k * m ^ k ≤ m ^ (k + 1)`.

Rewrite using `[← pow_add]`. Conclude with `Ideal.pow_le_pow_right (by omega)`. Conclude with `h4 h3`. Establish `heq : T (a * b) - φ' (a * b) - (φ' a * (T b - φ' b) + φ' b * (T a - φ' a)) = T (a * b) - T a * T b + (T a - φ' a) * (T b - φ' b)`. Rewrite using `[map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Conclude with `Ideal.add_mem _ h1 h2`. Set `d : Derivation P R (B ⧸ m ^ (k + 1))` to `{ toFun := fun y => Ideal.Quotient.mk (m ^ (k + 1)) (T y - φ' y) map_add' := by`. Introduce `a b`.

Use `show Ideal.Quotient.mk (m ^ (k + 1)) (T (a + b) - φ' (a + b)) = Ideal.Quotient.mk (m ^ (k + 1)) (T a - φ' a) + Ideal.Quotient.mk (m ^ (k + 1)) (T b - φ' b)`. Establish `harg : T (a + b) - φ' (a + b) = T a - φ' a + (T b - φ' b)`. Rewrite using `[hadd, map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[harg, map_add]`.

Use the proof step `map_smul' := by`. Introduce `p a`. Use `show Ideal.Quotient.mk (m ^ (k + 1)) (T (p • a) - φ' (p • a)) = p • Ideal.Quotient.mk (m ^ (k + 1)) (T a - φ' a)`. Simplify using `only [Algebra.smul_def]`. Establish `halg : (algebraMap P (B ⧸ m ^ (k + 1))) p = Ideal.Quotient.mk (m ^ (k + 1)) (φ' (algebraMap P R p))` using `rfl`.

Rewrite using `[halg, ← map_mul]`. Use `Ideal.Quotient.eq.mpr ?_` and prove the remaining obligations. Establish `h1` using `hleib (algebraMap P R p) a`. Establish `h2 : φ' a * (T (algebraMap P R p) - φ' (algebraMap P R p)) ∈ m ^ (k + 1)` using `Ideal.mul_mem_left _ _ (hP p)`. Establish `h3` using `Ideal.add_mem _ h1 h2`.

Establish `heq : T (algebraMap P R p * a) - φ' (algebraMap P R p * a) - (φ' (algebraMap P R p) * (T a - φ' a) + φ' a * (T (algebraMap P R p) - φ' (algebraMap P R p))) + φ' a * (T (algebraMap P R p) - φ' (algebraMap P R p)) = T (algebraMap P R p * a) - φ' (algebraMap P R p * a) - φ' (algebra …`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h3` using `[heq]`. Conclude with `h3`. Use the proof step `map_one_eq_zero' := by show Ideal.Quotient.mk (m ^ (k + 1)) (T 1 - φ' 1) = 0`.

Rewrite using `[hone, map_one, sub_self, map_zero]`. Use the proof step `leibniz' := by`. Introduce `a b`. Use `show Ideal.Quotient.mk (m ^ (k + 1)) (T (a * b) - φ' (a * b)) = a • Ideal.Quotient.mk (m ^ (k + 1)) (T b - φ' b) + b • Ideal.Quotient.mk (m ^ (k + 1)) (T a - φ' a)`. Simplify using `only [Algebra.smul_def]`.

Establish `halg : ∀ y : R, (algebraMap R (B ⧸ m ^ (k + 1))) y = Ideal.Quotient.mk (m ^ (k + 1)) (φ' y)` using `fun _ => rfl`. Rewrite using `[halg a, halg b, ← map_mul, ← map_mul, ← map_add]`. Conclude with `Ideal.Quotient.eq.mpr (hleib a b) }`. Establish `hdx : Ideal.Quotient.mk (m ^ (k + 1)) (T x - φ' x) = 0` using `derivation_apply_eq_zero_of_formallyUnramified d x`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp hdx`.
-/
private theorem sub_mem_pow_succ_of_sub_mem_pow (P : Type*) {R B : Type*} [CommRing P] [CommRing R]
    [CommRing B] [Algebra P R] [Algebra.FormallyUnramified P R]
    (φ' : R →+* B) (m : Ideal B) (T : R → B) (k : ℕ) (hk : 1 ≤ k)
    (hadd : ∀ x y : R, T (x + y) = T x + T y)
    (hone : T 1 = 1)
    (hmul : ∀ x y : R, T (x * y) - T x * T y ∈ m ^ (k + 1))
    (hP : ∀ x : P, T (algebraMap P R x) - φ' (algebraMap P R x) ∈ m ^ (k + 1))
    (hind : ∀ x : R, T x - φ' x ∈ m ^ k) (x : R) :
    T x - φ' x ∈ m ^ (k + 1) := by
  let _ : Algebra R B := φ'.toAlgebra
  let _ : Algebra P B := (φ'.comp (algebraMap P R)).toAlgebra
  have : IsScalarTower P R B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower P R (B ⧸ m ^ (k + 1)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hleib : ∀ a b : R,
      T (a * b) - φ' (a * b) - (φ' a * (T b - φ' b) + φ' b * (T a - φ' a)) ∈ m ^ (k + 1) := by
    intro a b
    have h1 : T (a * b) - T a * T b ∈ m ^ (k + 1) := hmul a b
    have h2 : (T a - φ' a) * (T b - φ' b) ∈ m ^ (k + 1) := by
      have h3 : (T a - φ' a) * (T b - φ' b) ∈ m ^ k * m ^ k :=
        Ideal.mul_mem_mul (hind a) (hind b)
      have h4 : m ^ k * m ^ k ≤ m ^ (k + 1) := by
        rw [← pow_add]
        exact Ideal.pow_le_pow_right (by omega)
      exact h4 h3
    have heq : T (a * b) - φ' (a * b) - (φ' a * (T b - φ' b) + φ' b * (T a - φ' a))
        = T (a * b) - T a * T b + (T a - φ' a) * (T b - φ' b) := by
      rw [map_mul]
      ring
    rw [heq]
    exact Ideal.add_mem _ h1 h2
  let d : Derivation P R (B ⧸ m ^ (k + 1)) :=
    { toFun := fun y => Ideal.Quotient.mk (m ^ (k + 1)) (T y - φ' y)
      map_add' := by
        intro a b
        show Ideal.Quotient.mk (m ^ (k + 1)) (T (a + b) - φ' (a + b))
            = Ideal.Quotient.mk (m ^ (k + 1)) (T a - φ' a)
              + Ideal.Quotient.mk (m ^ (k + 1)) (T b - φ' b)
        have harg : T (a + b) - φ' (a + b) = T a - φ' a + (T b - φ' b) := by
          rw [hadd, map_add]
          ring
        rw [harg, map_add]
      map_smul' := by
        intro p a
        show Ideal.Quotient.mk (m ^ (k + 1)) (T (p • a) - φ' (p • a))
            = p • Ideal.Quotient.mk (m ^ (k + 1)) (T a - φ' a)
        simp only [Algebra.smul_def]
        have halg : (algebraMap P (B ⧸ m ^ (k + 1))) p
            = Ideal.Quotient.mk (m ^ (k + 1)) (φ' (algebraMap P R p)) := rfl
        rw [halg, ← map_mul]
        refine Ideal.Quotient.eq.mpr ?_
        have h1 := hleib (algebraMap P R p) a
        have h2 : φ' a * (T (algebraMap P R p) - φ' (algebraMap P R p)) ∈ m ^ (k + 1) :=
          Ideal.mul_mem_left _ _ (hP p)
        have h3 := Ideal.add_mem _ h1 h2
        have heq : T (algebraMap P R p * a) - φ' (algebraMap P R p * a)
              - (φ' (algebraMap P R p) * (T a - φ' a)
                + φ' a * (T (algebraMap P R p) - φ' (algebraMap P R p)))
              + φ' a * (T (algebraMap P R p) - φ' (algebraMap P R p))
            = T (algebraMap P R p * a) - φ' (algebraMap P R p * a)
              - φ' (algebraMap P R p) * (T a - φ' a) := by
          ring
        rw [heq] at h3
        exact h3
      map_one_eq_zero' := by
        show Ideal.Quotient.mk (m ^ (k + 1)) (T 1 - φ' 1) = 0
        rw [hone, map_one, sub_self, map_zero]
      leibniz' := by
        intro a b
        show Ideal.Quotient.mk (m ^ (k + 1)) (T (a * b) - φ' (a * b))
            = a • Ideal.Quotient.mk (m ^ (k + 1)) (T b - φ' b)
              + b • Ideal.Quotient.mk (m ^ (k + 1)) (T a - φ' a)
        simp only [Algebra.smul_def]
        have halg : ∀ y : R, (algebraMap R (B ⧸ m ^ (k + 1))) y
            = Ideal.Quotient.mk (m ^ (k + 1)) (φ' y) := fun _ => rfl
        rw [halg a, halg b, ← map_mul, ← map_mul, ← map_add]
        exact Ideal.Quotient.eq.mpr (hleib a b) }
  have hdx : Ideal.Quotient.mk (m ^ (k + 1)) (T x - φ' x) = 0 :=
    derivation_apply_eq_zero_of_formallyUnramified d x
  exact Ideal.Quotient.eq_zero_iff_mem.mp hdx

/- English proof (translation)
Establish `hβN : β ^ N ∈ maximalIdeal B ^ N` using `Ideal.pow_mem_pow hβ N`. Establish `hmulN : ∀ x y : R, TaylorExpansion.truncatedSeries φ D β N (x * y) - TaylorExpansion.truncatedSeries φ D β N x * TaylorExpansion.truncatedSeries φ D β N y ∈ maximalIdeal B ^ N` using `fun x y => TaylorExpansion.truncatedSeries_mul_sub_mem φ D β N (maximalIdeal B ^ N) hβN x y`. Establish `hbound : ∀ x : P, TaylorExpansion.truncatedSeries φ D β N (algebraMap P R x) - φ' (algebraMap P R x) ∈ maximalIdeal B ^ N` using `fun x => hrep N hN x`. Establish `hbase : ∀ x : R, TaylorExpansion.truncatedSeries φ D β N x - φ' x ∈ maximalIdeal B ^ 1`. Introduce `x`.

Rewrite using `[pow_one]`. Establish `h1 : TaylorExpansion.truncatedSeries φ D β N x - φ x ∈ Ideal.span ({β} : Set B)` using `TaylorExpansion.truncatedSeries_sub_mem_span_singleton φ D β N hN x`. Establish `h2 : Ideal.span ({β} : Set B) ≤ maximalIdeal B`. Rewrite using `[Ideal.span_le]`. Simplify using `using hβ`.

Establish `h4 : TaylorExpansion.truncatedSeries φ D β N x - φ' x = TaylorExpansion.truncatedSeries φ D β N x - φ x + (φ x - φ' x)` using `by ring`. Rewrite using `[h4]`. Conclude with `Ideal.add_mem _ (h2 h1) (hcong x)`. Establish `key : ∀ k : ℕ, 1 ≤ k → k ≤ N → ∀ x : R, TaylorExpansion.truncatedSeries φ D β N x - φ' x ∈ maximalIdeal B ^ k`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => intro h; exact absurd h (by omega)`. Consider the case `succ k ih`. Introduce `_ hkN`. Break down `Nat.eq_zero_or_pos k with hk0 | hk1` into its components or cases.

Substitute `hk0` using the available equality. Conclude with `hbase`. Establish `hk1' : 1 ≤ k` using `hk1`. Establish `hkle : maximalIdeal B ^ N ≤ maximalIdeal B ^ (k + 1)` using `Ideal.pow_le_pow_right hkN`. Conclude with `fun x => sub_mem_pow_succ_of_sub_mem_pow P φ' (maximalIdeal B) (TaylorExpansion.truncatedSeries φ D β N) k hk1' (fun a b => TaylorExpansion.truncatedSeries_add φ D β N a b) (TaylorExpansion.truncatedSeries_one φ D β N hN) (fun a b => hkle (hmulN a b)) (fun p => hkle (hbound p)) ( …`.

Conclude with `key N hN le_rfl f`.
-/
theorem truncatedSeries_sub_mem_maximalIdeal_pow (P : Type*) [CommRing P] {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R]
    [Algebra.FormallyUnramified P R] [IsLocalRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (N : ℕ) (hN : 1 ≤ N) (f : R) :
    TaylorExpansion.truncatedSeries φ D β N f - φ' f ∈ maximalIdeal B ^ N := by
  have hβN : β ^ N ∈ maximalIdeal B ^ N := Ideal.pow_mem_pow hβ N
  have hmulN : ∀ x y : R,
      TaylorExpansion.truncatedSeries φ D β N (x * y)
        - TaylorExpansion.truncatedSeries φ D β N x * TaylorExpansion.truncatedSeries φ D β N y
        ∈ maximalIdeal B ^ N :=
    fun x y => TaylorExpansion.truncatedSeries_mul_sub_mem φ D β N (maximalIdeal B ^ N) hβN x y
  have hbound : ∀ x : P,
      TaylorExpansion.truncatedSeries φ D β N (algebraMap P R x) - φ' (algebraMap P R x)
        ∈ maximalIdeal B ^ N := fun x => hrep N hN x
  have hbase : ∀ x : R, TaylorExpansion.truncatedSeries φ D β N x - φ' x ∈ maximalIdeal B ^ 1 := by
    intro x
    rw [pow_one]
    have h1 : TaylorExpansion.truncatedSeries φ D β N x - φ x ∈ Ideal.span ({β} : Set B) :=
      TaylorExpansion.truncatedSeries_sub_mem_span_singleton φ D β N hN x
    have h2 : Ideal.span ({β} : Set B) ≤ maximalIdeal B := by
      rw [Ideal.span_le]
      simpa using hβ
    have h4 : TaylorExpansion.truncatedSeries φ D β N x - φ' x
        = TaylorExpansion.truncatedSeries φ D β N x - φ x + (φ x - φ' x) := by ring
    rw [h4]
    exact Ideal.add_mem _ (h2 h1) (hcong x)
  have key : ∀ k : ℕ, 1 ≤ k → k ≤ N →
      ∀ x : R, TaylorExpansion.truncatedSeries φ D β N x - φ' x ∈ maximalIdeal B ^ k := by
    intro k
    induction k with
    | zero => intro h; exact absurd h (by omega)
    | succ k ih =>
      intro _ hkN
      rcases Nat.eq_zero_or_pos k with hk0 | hk1
      · subst hk0
        exact hbase
      · have hk1' : 1 ≤ k := hk1
        have hkle : maximalIdeal B ^ N ≤ maximalIdeal B ^ (k + 1) :=
          Ideal.pow_le_pow_right hkN
        exact fun x =>
          sub_mem_pow_succ_of_sub_mem_pow P φ' (maximalIdeal B) (TaylorExpansion.truncatedSeries φ D β N) k hk1'
            (fun a b => TaylorExpansion.truncatedSeries_add φ D β N a b)
            (TaylorExpansion.truncatedSeries_one φ D β N hN)
            (fun a b => hkle (hmulN a b))
            (fun p => hkle (hbound p))
            (ih hk1' (by omega)) x
  exact key N hN le_rfl f

/- English proof (translation)
Establish `h1 : TaylorExpansion.truncatedSeries φ D β N f - φ f ∈ Ideal.span ({β} : Set B)` using `TaylorExpansion.truncatedSeries_sub_mem_span_singleton φ D β N hN f`. Establish `h2 : TaylorExpansion.truncatedSeries φ D β N f - φ' f ∈ maximalIdeal B ^ N` using `truncatedSeries_sub_mem_maximalIdeal_pow P φ φ' D β hcong hβ hrep N hN f`. Establish `hEq : φ f - φ' f = (TaylorExpansion.truncatedSeries φ D β N f - φ' f) - (TaylorExpansion.truncatedSeries φ D β N f - φ f)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hEq]`.

Conclude with `Submodule.sub_mem _ (Submodule.mem_sup_right h2) (Submodule.mem_sup_left h1)`.
-/
theorem sub_mem_span_sup_maximalIdeal_pow (P : Type*) [CommRing P] {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R]
    [Algebra.FormallyUnramified P R] [IsLocalRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (N : ℕ) (hN : 1 ≤ N) (f : R) :
    φ f - φ' f ∈ Ideal.span ({β} : Set B) ⊔ maximalIdeal B ^ N := by
  have h1 : TaylorExpansion.truncatedSeries φ D β N f - φ f ∈ Ideal.span ({β} : Set B) :=
    TaylorExpansion.truncatedSeries_sub_mem_span_singleton φ D β N hN f
  have h2 : TaylorExpansion.truncatedSeries φ D β N f - φ' f ∈ maximalIdeal B ^ N :=
    truncatedSeries_sub_mem_maximalIdeal_pow P φ φ' D β hcong hβ hrep N hN f
  have hEq : φ f - φ' f
      = (TaylorExpansion.truncatedSeries φ D β N f - φ' f) - (TaylorExpansion.truncatedSeries φ D β N f - φ f) := by
    ring
  rw [hEq]
  exact Submodule.sub_mem _ (Submodule.mem_sup_right h2) (Submodule.mem_sup_left h1)

/- English proof (translation)
Use `Submodule.mem_iInf _ |>.2 ?_` and prove the remaining obligations. Introduce `N`. Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Establish `h0 : (Ideal.span ({β} : Set B) ⊔ maximalIdeal B ^ 0) = ⊤`. Rewrite using `[pow_zero, Ideal.one_eq_top, sup_top_eq]`.

Rewrite using `[h0]`. Conclude with `Submodule.mem_top`. Conclude with `sub_mem_span_sup_maximalIdeal_pow P φ φ' D β hcong hβ hrep N hN f`.
-/
theorem sub_mem_iInf_span_sup_maximalIdeal_pow (P : Type*) [CommRing P] {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R]
    [Algebra.FormallyUnramified P R] [IsLocalRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (f : R) :
    φ f - φ' f ∈ ⨅ N : ℕ, (Ideal.span ({β} : Set B) ⊔ maximalIdeal B ^ N) := by
  refine Submodule.mem_iInf _ |>.2 ?_
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : (Ideal.span ({β} : Set B) ⊔ maximalIdeal B ^ 0) = ⊤ := by
      rw [pow_zero, Ideal.one_eq_top, sup_top_eq]
    rw [h0]
    exact Submodule.mem_top
  · exact sub_mem_span_sup_maximalIdeal_pow P φ φ' D β hcong hβ hrep N hN f

/- English proof (translation)
Establish `hmne : IsLocalRing.maximalIdeal B ≠ ⊤` using `(IsLocalRing.maximalIdeal.isMaximal B).ne_top`. Establish `hJne : J ≠ ⊤`. Introduce `h`. Apply `hmne` to reduce the goal to its premises. Rewrite using `[eq_top_iff]`.

Rewrite `hJ` using `[h]`. Conclude with `hJ`. Establish `: Nontrivial (B ⧸ J)`. Use `⟨0, 1, fun h => hJne ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.eq_top_iff_one]`.

Use `Ideal.Quotient.eq_zero_iff_mem.1 ?_` and prove the remaining obligations. Rewrite using `[map_one]`. Conclude with `h.symm`. Establish `: IsLocalRing (B ⧸ J)` using `IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective`. Establish `hIne : Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B) ≠ ⊤`.

Introduce `h`. Establish `h1 : (1 : B ⧸ J) ∈ Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B)`. Rewrite using `[h]`. Conclude with `Submodule.mem_top`. Take `⟨y, hy, hy1⟩` from `(Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).1 h1`.

Establish `h2 : (1 : B) - y ∈ J`. Use `Ideal.Quotient.eq_zero_iff_mem.1 ?_` and prove the remaining obligations. Rewrite using `[map_sub, hy1, map_one, sub_self]`. Establish `h3 : (1 : B) ∈ IsLocalRing.maximalIdeal B`. Establish `h4` using `Submodule.add_mem (IsLocalRing.maximalIdeal B) (hJ h2) hy`.

Simplify using `at h4`. Conclude with `hmne ((Ideal.eq_top_iff_one _).2 h3)`. Establish `hbot : (⨅ i : ℕ, (Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B)) ^ i) = ⊥`. Apply `Ideal.iInf_pow_eq_bot_of_isLocalRing` to reduce the goal to its premises. Conclude with `hIne`.

Establish `hmem : ∀ N : ℕ, Ideal.Quotient.mk J x ∈ (Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B)) ^ N`. Introduce `N`. Take `⟨j, hj, y, hy, hxy⟩` from `Submodule.mem_sup.1 (hx N)`. Establish `hxe : Ideal.Quotient.mk J x = Ideal.Quotient.mk J y`. Rewrite using `[← hxy, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add]`.

Rewrite using `[hxe]`. Conclude with `(Ideal.map_pow (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B) N).le (Ideal.mem_map_of_mem _ hy)`. Establish `hfin : Ideal.Quotient.mk J x ∈ (⨅ i : ℕ, (Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B)) ^ i)` using `(Submodule.mem_iInf _).2 hmem`. Rewrite `hfin` using `[hbot, Ideal.mem_bot]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 hfin`.
-/
private theorem mem_of_forall_mem_sup_maximalIdeal_pow {B : Type*} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] (J : Ideal B) (hJ : J ≤ IsLocalRing.maximalIdeal B) (x : B)
    (hx : ∀ N : ℕ, x ∈ J ⊔ IsLocalRing.maximalIdeal B ^ N) : x ∈ J := by
  have hmne : IsLocalRing.maximalIdeal B ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal B).ne_top
  have hJne : J ≠ ⊤ := by
    intro h
    apply hmne
    rw [eq_top_iff]
    rw [h] at hJ
    exact hJ
  have : Nontrivial (B ⧸ J) := by
    refine ⟨0, 1, fun h => hJne ?_⟩
    rw [Ideal.eq_top_iff_one]
    refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [map_one]
    exact h.symm
  have : IsLocalRing (B ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hIne : Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B) ≠ ⊤ := by
    intro h
    have h1 : (1 : B ⧸ J) ∈ Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B) := by
      rw [h]
      exact Submodule.mem_top
    obtain ⟨y, hy, hy1⟩ :=
      (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).1 h1
    have h2 : (1 : B) - y ∈ J := by
      refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
      rw [map_sub, hy1, map_one, sub_self]
    have h3 : (1 : B) ∈ IsLocalRing.maximalIdeal B := by
      have h4 := Submodule.add_mem (IsLocalRing.maximalIdeal B) (hJ h2) hy
      simp at h4
    exact hmne ((Ideal.eq_top_iff_one _).2 h3)
  have hbot : (⨅ i : ℕ,
      (Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B)) ^ i) = ⊥ := by
    apply Ideal.iInf_pow_eq_bot_of_isLocalRing
    exact hIne
  have hmem : ∀ N : ℕ, Ideal.Quotient.mk J x ∈
      (Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B)) ^ N := by
    intro N
    obtain ⟨j, hj, y, hy, hxy⟩ := Submodule.mem_sup.1 (hx N)
    have hxe : Ideal.Quotient.mk J x = Ideal.Quotient.mk J y := by
      rw [← hxy, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add]
    rw [hxe]
    exact (Ideal.map_pow (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B) N).le
      (Ideal.mem_map_of_mem _ hy)
  have hfin : Ideal.Quotient.mk J x ∈
      (⨅ i : ℕ, (Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B)) ^ i) :=
    (Submodule.mem_iInf _).2 hmem
  rw [hbot, Ideal.mem_bot] at hfin
  exact Ideal.Quotient.eq_zero_iff_mem.1 hfin

/- English proof (translation)
Establish `h` using `sub_mem_iInf_span_sup_maximalIdeal_pow P φ φ' D β hcong hβ hrep f`. Establish `hall : ∀ N : ℕ, φ f - φ' f ∈ Ideal.span ({β} : Set B) ⊔ maximalIdeal B ^ N` using `(Submodule.mem_iInf _).1 h`. Conclude with `mem_of_forall_mem_sup_maximalIdeal_pow (Ideal.span ({β} : Set B)) (Ideal.span_le.2 (Set.singleton_subset_iff.2 hβ)) (φ f - φ' f) hall`.
-/
theorem sub_mem_span_singleton_of_isTaylorExpansionOn (P : Type*) [CommRing P] {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R]
    [Algebra.FormallyUnramified P R] [IsLocalRing B] [IsNoetherianRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (f : R) :
    φ f - φ' f ∈ Ideal.span ({β} : Set B) := by
  have h := sub_mem_iInf_span_sup_maximalIdeal_pow P φ φ' D β hcong hβ hrep f
  have hall : ∀ N : ℕ, φ f - φ' f ∈ Ideal.span ({β} : Set B) ⊔ maximalIdeal B ^ N :=
    (Submodule.mem_iInf _).1 h
  exact mem_of_forall_mem_sup_maximalIdeal_pow (Ideal.span ({β} : Set B))
    (Ideal.span_le.2 (Set.singleton_subset_iff.2 hβ)) (φ f - φ' f) hall

/- English proof (translation)
Establish `hmem : φ f - φ' f ∈ Ideal.span ({β} : Set B)` using `sub_mem_span_singleton_of_isTaylorExpansionOn P φ φ' D β hcong hβ hrep f`. Establish `hle : Ideal.span ({β} : Set B) ≤ I` using `Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hI)`. Conclude with `hle hmem`.
-/
theorem sub_mem_of_isTaylorExpansionOn (P : Type*) [CommRing P] {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R]
    [Algebra.FormallyUnramified P R] [IsLocalRing B] [IsNoetherianRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (I : Ideal B) (hI : β ∈ I) (f : R) :
    φ f - φ' f ∈ I := by
  have hmem : φ f - φ' f ∈ Ideal.span ({β} : Set B) :=
    sub_mem_span_singleton_of_isTaylorExpansionOn P φ φ' D β hcong hβ hrep f
  have hle : Ideal.span ({β} : Set B) ≤ I :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hI)
  exact hle hmem

/- English proof (translation)
Use `Ideal.map_le_iff_le_comap.mpr fun g hg => ?_` and prove the remaining obligations. Use `Ideal.mem_comap.mpr ?_` and prove the remaining obligations. Distinguish the cases in `htop : Ideal.map φ J = ⊤`. Rewrite using `[htop]`. Conclude with `Submodule.mem_top`.

Use `mem_of_forall_mem_sup_maximalIdeal_pow (Ideal.map φ J) (IsLocalRing.le_maximalIdeal htop) (φ' g) ?_` and prove the remaining obligations. Introduce `n`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality. Rewrite using `[pow_zero, Ideal.one_eq_top, sup_top_eq]`.

Conclude with `Submodule.mem_top`. Establish `hn1 : 1 ≤ n` using `Nat.one_le_iff_ne_zero.mpr hn`. Establish `h1 : TaylorExpansion.truncatedSeries φ D β n g ∈ Ideal.map φ J`. Establish `hmem` using `truncatedSeries_mem_map φ D b J hstab n g hg`. Rewrite `hmem` using `[hb]`. Then use the resulting hypothesis.

Establish `h2 : TaylorExpansion.truncatedSeries φ D β n g - φ' g ∈ maximalIdeal B ^ n` using `truncatedSeries_sub_mem_maximalIdeal_pow P φ φ' D β hcong hβ hrep n hn1 g`. Establish `hEq : φ' g = TaylorExpansion.truncatedSeries φ D β n g - (TaylorExpansion.truncatedSeries φ D β n g - φ' g)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hEq]`. Conclude with `Submodule.sub_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)`.
-/
theorem map_le_map_of_pow_mul_iterate_deriv_mem (P : Type*) [CommRing P] {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R]
    [Algebra.FormallyUnramified P R] [IsLocalRing B] [IsNoetherianRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B) (b : R) (J : Ideal R)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (hb : φ b = β)
    (hstab : ∀ (j : ℕ) (g : R), g ∈ J → b ^ j * (⇑D)^[j] g ∈ J) :
    Ideal.map φ' J ≤ Ideal.map φ J := by
  refine Ideal.map_le_iff_le_comap.mpr fun g hg => ?_
  refine Ideal.mem_comap.mpr ?_
  by_cases htop : Ideal.map φ J = ⊤
  · rw [htop]
    exact Submodule.mem_top
  · refine mem_of_forall_mem_sup_maximalIdeal_pow (Ideal.map φ J)
      (IsLocalRing.le_maximalIdeal htop) (φ' g) ?_
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [pow_zero, Ideal.one_eq_top, sup_top_eq]
      exact Submodule.mem_top
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have h1 : TaylorExpansion.truncatedSeries φ D β n g ∈ Ideal.map φ J := by
        have hmem := truncatedSeries_mem_map φ D b J hstab n g hg
        rwa [hb] at hmem
      have h2 : TaylorExpansion.truncatedSeries φ D β n g - φ' g ∈ maximalIdeal B ^ n :=
        truncatedSeries_sub_mem_maximalIdeal_pow P φ φ' D β hcong hβ hrep n hn1 g
      have hEq : φ' g = TaylorExpansion.truncatedSeries φ D β n g - (TaylorExpansion.truncatedSeries φ D β n g - φ' g) := by
        ring
      rw [hEq]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)

end

end FunctorialResolution.EmbeddedResolution
