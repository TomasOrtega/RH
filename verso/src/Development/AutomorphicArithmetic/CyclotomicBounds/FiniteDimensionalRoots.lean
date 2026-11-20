import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AutomorphicArithmetic.PrimeDiscriminants.CycImage

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial

namespace UpperTheory.KStar.Cyc

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hfin : ({x : Om l | x ^ M = 1} : Set (Om l)).Finite`. Apply `(Polynomial.nthRootsFinset M (1 : Om l)).finite_toSet.subset` to reduce the goal to its premises. Introduce `x hx`. Simplify `hx` using `[Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hM)]`. Use `haveI : Finite ({x : Om l | x ^ M = 1} : Set (Om l)) := hfin.to_subtype`.

Apply `IntermediateField.finiteDimensional_adjoin` to reduce the goal to its premises. Introduce `x hx`. Use `⟨Polynomial.X ^ M - 1, Polynomial.monic_X_pow_sub_C 1 hM, ?_⟩` and prove the remaining obligations. Simplify using `[Set.mem_setOf_eq.mp hx]`.
-/
theorem finiteDimensional_roots {M : ℕ} (hM : M ≠ 0) :
    FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ M = 1}) := by
  have hfin : ({x : Om l | x ^ M = 1} : Set (Om l)).Finite := by
    apply (Polynomial.nthRootsFinset M (1 : Om l)).finite_toSet.subset
    intro x hx
    simpa [Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hM)] using hx
  haveI : Finite ({x : Om l | x ^ M = 1} : Set (Om l)) := hfin.to_subtype
  apply IntermediateField.finiteDimensional_adjoin
  intro x hx
  refine ⟨Polynomial.X ^ M - 1, Polynomial.monic_X_pow_sub_C 1 hM, ?_⟩
  simp [Set.mem_setOf_eq.mp hx]

def rootsExt (l : ℕ) [Fact l.Prime] (M : ℕ) (hM : M ≠ 0) : FinExt l :=
  ⟨IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ M = 1}, finiteDimensional_roots hM⟩

/- English proof (translation)
The claim follows from `h (IntermediateField.subset_adjoin _ _ hx)`.
-/
theorem mem_of_rootsExt_le {M : ℕ} (hM : M ≠ 0) {LL : FinExt l} (h : (rootsExt l M hM).1 ≤ LL.1) (x : Om l)
    (hx : x ^ M = 1) : x ∈ LL.1 :=
  h (IntermediateField.subset_adjoin _ _ hx)

/- English proof (translation)
Use `set A := IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ M = 1} with hA`. Use `haveI : FiniteDimensional ℚ_[l] A := finiteDimensional_roots hM`. Establish `hrange : Set.range J ⊆ (A : Set (Om l))`. Introduce and unpack `_ ⟨y, rfl⟩`. Apply `H.image_mem_of_roots J A.toSubfield` to reduce the goal to its premises.

Introduce `z hz`. Apply `IntermediateField.subset_adjoin` to reduce the goal to its premises. Take `⟨k, hk⟩` from `hN`. Use `show z ^ M = 1`. Rewrite using `[hk, pow_mul, hz, one_pow]`.

Establish `hclosed : IsClosed (A : Set (Om l))` using `Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule A.toSubalgebra)`. Introduce `x hx`. Conclude with `closure_minimal hrange hclosed (hdense hx)`.
-/
theorem le_roots_of_dense {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (J : H.E →+* Om l) (K : FinExt l) {M : ℕ} (hM : M ≠ 0)
    (hN : H.condN ∣ M) (hdense : (K.1 : Set (Om l)) ⊆ closure (Set.range J)) :
    K.1 ≤ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ M = 1} := by
  set A := IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ M = 1} with hA
  haveI : FiniteDimensional ℚ_[l] A := finiteDimensional_roots hM
  have hrange : Set.range J ⊆ (A : Set (Om l)) := by
    rintro _ ⟨y, rfl⟩
    apply H.image_mem_of_roots J A.toSubfield
    intro z hz
    apply IntermediateField.subset_adjoin
    obtain ⟨k, hk⟩ := hN
    show z ^ M = 1
    rw [hk, pow_mul, hz, one_pow]
  have hclosed : IsClosed (A : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule A.toSubalgebra)
  intro x hx
  exact closure_minimal hrange hclosed (hdense hx)

/- English proof (translation)
The claim follows from `Nat.lcm_ne_zero (Fact.out : l.Prime).ne_zero H.condN_ne_zero`.
-/
theorem lcm_ne_zero {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) : Nat.lcm l H.condN ≠ 0 :=
  Nat.lcm_ne_zero (Fact.out : l.Prime).ne_zero H.condN_ne_zero

/- English proof (translation)
The claim follows from `le_roots_of_dense H (B.j.comp (algebraMap H.E Ω)) B.Kw (lcm_ne_zero H) (Nat.dvd_lcm_right _ _) B.j_dense`.
-/
theorem kw_le_roots {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) {Ω : Type} [Field Ω] [Algebra H.E Ω]
    {Gw : Subgroup (Ω ≃ₐ[H.E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (B : LocBridge l H.E Ω Gw O) :
    B.Kw.1 ≤ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ Nat.lcm l H.condN = 1} :=
  le_roots_of_dense H (B.j.comp (algebraMap H.E Ω)) B.Kw (lcm_ne_zero H) (Nat.dvd_lcm_right _ _) B.j_dense

/- English proof (translation)
The claim follows from `H.image_mem_of_roots J (RingHom.eqLocusField σ (RingHom.id Ω)) h x`.
-/
theorem fix_of_roots {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) {Ω : Type} [Field Ω] [IsAlgClosed Ω] (J : H.E →+* Ω)
    (σ : Ω →+* Ω) (h : ∀ t : Ω, t ^ H.condN = 1 → σ t = t) (x : H.E) : σ (J x) = J x :=
  H.image_mem_of_roots J (RingHom.eqLocusField σ (RingHom.id Ω)) h x

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hm0 : m ≠ 0` using `fun e => hm (e ▸ dvd_zero l)`. Establish `hsum : ∑ i ∈ Finset.range m, u ^ i = 0`. Use `mul_geom_sum u m` as an intermediate fact. Rewrite `this` using `[hu, sub_self]`.

Conclude with `(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)`. Establish `hvu : A.valuation u = 1`. Establish `: A.valuation u ^ m = 1` using `by rw [← map_pow, hu, map_one]`. Break down `lt_trichotomy (A.valuation u) 1 with h' | h' | h'` into its components or cases. Conclude with `absurd this (pow_lt_one₀ zero_le h' hm0).ne`.

Conclude with `h'`. Conclude with `absurd this (one_lt_pow₀ h' hm0).ne'`. Establish `hpow : ∀ i : ℕ, A.valuation (u ^ i - 1) < 1`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero => simp`. Consider the case `succ i ih`. Establish `e : u ^ (i + 1) - 1 = u ^ i * (u - 1) + (u ^ i - 1)` using `by ring`. Rewrite using `[e]`. Use `Valuation.map_add_lt _ ?_ ih` and prove the remaining obligations.

Rewrite using `[map_mul, map_pow, hvu, one_pow, one_mul]`. Conclude with `h`. Establish `hmv : A.valuation (m : Ω) < 1`. Establish `e : (m : Ω) = -∑ i ∈ Finset.range m, (u ^ i - 1)`. Rewrite using `[Finset.sum_sub_distrib, hsum]`.

Simplify using the standard rewrite rules. Rewrite using `[e, Valuation.map_neg]`. Conclude with `Valuation.map_sum_lt _ one_ne_zero fun i _ => hpow i`. Establish `hcop : Nat.Coprime l m` using `((Fact.out : l.Prime).coprime_iff_not_dvd).2 hm`. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.2 hcop`.

Establish `hint : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1` using `fun z => (A.valuation_le_one_iff _).2 (intCast_mem A z)`. Establish `e : (a : Ω) * l + b * m = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab`. Establish `: A.valuation ((a : Ω) * l + b * m) < 1`. Apply the tactic sequence `refine Valuation.map_add_lt _ ?_ ?_ <;> rw [map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_right (hint a) zero_le hA`.

Conclude with `mul_lt_one_of_nonneg_of_lt_one_right (hint b) zero_le hmv`. Rewrite `this` using `[e, map_one]`. Conclude with `lt_irrefl _ this`.
-/
theorem root_eq_of_congr {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) {m : ℕ}
    (hm : ¬ l ∣ m) {u : Ω} (hu : u ^ m = 1) (h : A.valuation (u - 1) < 1) : u = 1 := by
  by_contra hne
  have hm0 : m ≠ 0 := fun e => hm (e ▸ dvd_zero l)
  have hsum : ∑ i ∈ Finset.range m, u ^ i = 0 := by
    have := mul_geom_sum u m
    rw [hu, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have hvu : A.valuation u = 1 := by
    have : A.valuation u ^ m = 1 := by rw [← map_pow, hu, map_one]
    rcases lt_trichotomy (A.valuation u) 1 with h' | h' | h'
    · exact absurd this (pow_lt_one₀ zero_le h' hm0).ne
    · exact h'
    · exact absurd this (one_lt_pow₀ h' hm0).ne'
  have hpow : ∀ i : ℕ, A.valuation (u ^ i - 1) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : u ^ (i + 1) - 1 = u ^ i * (u - 1) + (u ^ i - 1) := by ring
      rw [e]
      refine Valuation.map_add_lt _ ?_ ih
      rw [map_mul, map_pow, hvu, one_pow, one_mul]; exact h
  have hmv : A.valuation (m : Ω) < 1 := by
    have e : (m : Ω) = -∑ i ∈ Finset.range m, (u ^ i - 1) := by
      rw [Finset.sum_sub_distrib, hsum]; simp
    rw [e, Valuation.map_neg]
    exact Valuation.map_sum_lt _ one_ne_zero fun i _ => hpow i
  have hcop : Nat.Coprime l m := ((Fact.out : l.Prime).coprime_iff_not_dvd).2 hm
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hint : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => (A.valuation_le_one_iff _).2 (intCast_mem A z)
  have e : (a : Ω) * l + b * m = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have : A.valuation ((a : Ω) * l + b * m) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_ <;> rw [map_mul]
    · exact mul_lt_one_of_nonneg_of_lt_one_right (hint a) zero_le hA
    · exact mul_lt_one_of_nonneg_of_lt_one_right (hint b) zero_le hmv
  rw [e, map_one] at this
  exact lt_irrefl _ this

/- English proof (translation)
Establish `ht0 : t ≠ 0`. Introduce and unpack `rfl`. Rewrite `ht` using `[zero_pow h0]`. Conclude with `zero_ne_one ht`. Take `⟨x, y, hxy⟩` from `Nat.isCoprime_iff_coprime.2 hab`.

Establish `h1 : σ (t ^ b) = t ^ b` using `ha _ (by rw [← pow_mul, mul_comm, ht])`. Establish `h2 : σ (t ^ a) = t ^ a` using `hb _ (by rw [← pow_mul, ht])`. Establish `e : t = (t ^ a) ^ x * (t ^ b) ^ y`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ ht0, mul_comm (a : ℤ), mul_comm (b : ℤ), hxy, zpow_one]`. Rewrite using `[e, map_mul, map_zpow₀, map_zpow₀, h1, h2]`.
-/
theorem fix_mul {Ω : Type} [Field Ω] (σ : Ω →+* Ω) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : ∀ t : Ω, t ^ a = 1 → σ t = t) (hb : ∀ t : Ω, t ^ b = 1 → σ t = t) (h0 : a * b ≠ 0) (t : Ω)
    (ht : t ^ (a * b) = 1) : σ t = t := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow h0] at ht
    exact zero_ne_one ht
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 hab
  have h1 : σ (t ^ b) = t ^ b := ha _ (by rw [← pow_mul, mul_comm, ht])
  have h2 : σ (t ^ a) = t ^ a := hb _ (by rw [← pow_mul, ht])
  have e : t = (t ^ a) ^ x * (t ^ b) ^ y := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ ht0, mul_comm (a : ℤ), mul_comm (b : ℤ), hxy,
      zpow_one]
  rw [e, map_mul, map_zpow₀, map_zpow₀, h1, h2]

end UpperTheory.KStar.Cyc

end
