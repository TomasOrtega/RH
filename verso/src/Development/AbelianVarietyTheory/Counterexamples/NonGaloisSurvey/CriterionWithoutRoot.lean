import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.WachHeightTest

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.DeltaInvariantLattices PowerSeries

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h` using `W.q₀_def`. Establish `h2 : (PowerSeries.X : PowerSeries O) * ∑ k ∈ Finset.range PD.p, (1 + PowerSeries.X) ^ k = (1 + PowerSeries.X) ^ PD.p - 1`. Use `mul_geom_sum (1 + (PowerSeries.X : PowerSeries O)) PD.p` as an intermediate fact. Simplify using `using this`.

Establish `h3` using `PowerSeries.X_mul_cancel (h.trans h2.symm)`. Simplify using `[LocWach.q, h3, letπ, Finset.sum_apply]`.
-/
theorem q_eq : W.q = ∑ k ∈ Finset.range PD.p, (1 + (letπ : LetA O n)) ^ k := by
  funext i
  have h := W.q₀_def
  have h2 : (PowerSeries.X : PowerSeries O) * ∑ k ∈ Finset.range PD.p, (1 + PowerSeries.X) ^ k =
      (1 + PowerSeries.X) ^ PD.p - 1 := by
    have := mul_geom_sum (1 + (PowerSeries.X : PowerSeries O)) PD.p
    simpa using this
  have h3 := PowerSeries.X_mul_cancel (h.trans h2.symm)
  simp [LocWach.q, h3, letπ, Finset.sum_apply]

/- English proof (translation)
Rewrite using `[map_add, map_one, W.φA_π]`. Use function extensionality and compare the values at `i`. Establish `h` using `W.q₀_def`. Simplify using `only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.one_apply, letπ, LocWach.q, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem φ_one_add : W.φA (1 + letπ) = (1 + (letπ : LetA O n)) ^ PD.p := by
  rw [map_add, map_one, W.φA_π]
  funext i
  have h := W.q₀_def
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.one_apply, letπ, LocWach.q, h]
  ring

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih => rw [pow_succ', AlgHom.mul_apply, ih, map_pow, φ_one_add, ← pow_mul, pow_succ']`.
-/
theorem φpow_one_add (j : ℕ) : (W.φA ^ j) (1 + letπ) = (1 + (letπ : LetA O n)) ^ (PD.p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', AlgHom.mul_apply, ih, map_pow, φ_one_add, ← pow_mul, pow_succ']

/- English proof (translation)
Rewrite using `[LocWach.Q, q_eq, map_sum]`. Simplify using `only [map_pow, φpow_one_add]`.
-/
theorem Q_eq : W.Q = ∑ k ∈ Finset.range PD.p, ((1 + (letπ : LetA O n)) ^ (PD.p ^ (W.s - 1))) ^ k := by
  rw [LocWach.Q, q_eq, map_sum]
  simp only [map_pow, φpow_one_add]

/- English proof (translation)
Take `⟨E, hE, -, h⟩` from `W.lev_π i ζ hζ`. Rewrite using `[Q_eq]`. Simplify using `only [map_sum, map_pow, map_add, map_one]`. Establish `: 1 + PowerSeries.constantCoeff (W.lev i ζ letπ) = ζ`. Use `congrArg PowerSeries.constantCoeff h` as an intermediate fact.

Simplify `this` using `[hE]`. Rewrite using `[this]`.
-/
theorem value_Q (i : ZMod n) (ζ : LL) (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    PowerSeries.constantCoeff (W.lev i ζ W.Q) =
      ∑ k ∈ Finset.range PD.p, (ζ ^ (PD.p ^ (W.s - 1))) ^ k := by
  obtain ⟨E, hE, -, h⟩ := W.lev_π i ζ hζ
  rw [Q_eq]
  simp only [map_sum, map_pow, map_add, map_one]
  have : 1 + PowerSeries.constantCoeff (W.lev i ζ letπ) = ζ := by
    have := congrArg PowerSeries.constantCoeff h
    simpa [hE] using this
  rw [this]

include W in
/- English proof (translation)
Introduce `h`. Use `W.v_l` as an intermediate fact. Rewrite `this` using `[h, AddValuation.map_zero]`. Conclude with `WithTop.top_ne_one this`.
-/
theorem p_ne_zero : ((PD.p : ℕ) : LL) ≠ 0 := by
  intro h
  have := W.v_l
  rw [h, AddValuation.map_zero] at this
  exact WithTop.top_ne_one this

/- English proof (translation)
Use `haveI : Fact PD.p.Prime := ⟨PD.hp⟩`. Establish `hs : W.s = W.s - 1 + 1` using `by have := W.s_pos; omega`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hc, ⟨m, hm⟩, h0⟩`. Use `⟨hc, ?_⟩` and prove the remaining obligations.

Establish `hprim : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)`. Take `⟨j, -, hj⟩` from `(Nat.dvd_prime_pow PD.hp).1 (orderOf_dvd_of_pow_eq_one hm)`. Conclude with `⟨j, hj ▸ IsPrimitiveRoot.orderOf ζ⟩`. Rewrite `h0` using `[value_Q W i ζ hprim]`. Establish `h1 : ¬ ζ ^ PD.p ^ (W.s - 1) = 1`.

Introduce `h`. Rewrite `h0` using `[h]`. Apply `p_ne_zero W` to reduce the goal to its premises. Simplify using `using h0`. Establish `h2 : ζ ^ PD.p ^ (W.s - 1 + 1) = 1`.

Use `geom_sum_mul (ζ ^ PD.p ^ (W.s - 1)) PD.p` as an intermediate fact. Rewrite `this` using `[h0, zero_mul]`. Rewrite using `[pow_succ, pow_mul]`. Conclude with `(sub_eq_zero.1 this.symm)`. Use `orderOf_eq_prime_pow h1 h2` as an intermediate fact.

Rewrite using `[hs, ← this]`. Conclude with `IsPrimitiveRoot.orderOf ζ`. Introduce and unpack `⟨hc, hp⟩`. Use `⟨hc, ⟨W.s, hp.pow_eq_one⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[value_Q W i ζ ⟨_, hp⟩]`.

Establish `h1 : ζ ^ PD.p ^ (W.s - 1) ≠ 1` using `hp.pow_ne_one_of_pos_of_lt (pow_pos PD.hp.pos _).ne' (Nat.pow_lt_pow_right PD.hp.one_lt (by omega))`. Use `geom_sum_mul (ζ ^ PD.p ^ (W.s - 1)) PD.p` as an intermediate fact. Rewrite `this` using `[← pow_mul, ← pow_succ, ← hs, hp.pow_eq_one, sub_self]`. Conclude with `(mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 h1)`.
-/
theorem qRoot_iff (i : ZMod n) (ζ : LL) :
    QRoot W i ζ ↔ (∃ c : O, algebraMap O LL c = ζ) ∧ IsPrimitiveRoot ζ (PD.p ^ W.s) := by
  haveI : Fact PD.p.Prime := ⟨PD.hp⟩
  have hs : W.s = W.s - 1 + 1 := by have := W.s_pos; omega
  constructor
  · rintro ⟨hc, ⟨m, hm⟩, h0⟩
    refine ⟨hc, ?_⟩
    have hprim : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow PD.hp).1 (orderOf_dvd_of_pow_eq_one hm)
      exact ⟨j, hj ▸ IsPrimitiveRoot.orderOf ζ⟩
    rw [value_Q W i ζ hprim] at h0
    have h1 : ¬ ζ ^ PD.p ^ (W.s - 1) = 1 := by
      intro h
      rw [h] at h0
      apply p_ne_zero W
      simpa using h0
    have h2 : ζ ^ PD.p ^ (W.s - 1 + 1) = 1 := by
      have := geom_sum_mul (ζ ^ PD.p ^ (W.s - 1)) PD.p
      rw [h0, zero_mul] at this
      rw [pow_succ, pow_mul]
      exact (sub_eq_zero.1 this.symm)
    have := orderOf_eq_prime_pow h1 h2
    rw [hs, ← this]
    exact IsPrimitiveRoot.orderOf ζ
  · rintro ⟨hc, hp⟩
    refine ⟨hc, ⟨W.s, hp.pow_eq_one⟩, ?_⟩
    rw [value_Q W i ζ ⟨_, hp⟩]
    have h1 : ζ ^ PD.p ^ (W.s - 1) ≠ 1 :=
      hp.pow_ne_one_of_pos_of_lt (pow_pos PD.hp.pos _).ne'
        (Nat.pow_lt_pow_right PD.hp.one_lt (by omega))
    have := geom_sum_mul (ζ ^ PD.p ^ (W.s - 1)) PD.p
    rw [← pow_mul, ← pow_succ, ← hs, hp.pow_eq_one, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 h1)

end Local

end GlobalTheory.WachHeightTest
