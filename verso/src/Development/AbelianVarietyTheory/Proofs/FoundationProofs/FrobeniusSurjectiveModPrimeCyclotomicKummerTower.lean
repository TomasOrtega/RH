import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PAdicCompletionLaurentEqSumPthPowersModPStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

def IsPowModP {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) (p : ℕ)
    (x : A) : Prop :=
  ∃ y ∈ S, ∃ z ∈ S, x = y ^ p + (p : A) * z

section Closure

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) {p : ℕ}

/- English proof (translation)
Take `⟨y, hy, z, hz, rfl⟩` from `hx`. Take `⟨y', hy', z', hz', rfl⟩` from `hx'`. Take `⟨r, hr⟩` from `exists_add_pow_prime_eq hp (⟨y, hy⟩ : S) ⟨y', hy'⟩`. Establish `hr'` using `congrArg Subtype.val hr`. Move the coercions through the operations in `at hr'`.

Use `⟨y + y', S.add_mem hy hy', z + z' - y * y' * r, ?_, ?_⟩` and prove the remaining obligations. Conclude with `S.sub_mem (S.add_mem hz hz') (S.mul_mem (S.mul_mem hy hy') r.2)`. Rewrite using `[hr']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isPthPowerModP_add (hp : p.Prime) {x x' : A} (hx : IsPowModP S p x) (hx' : IsPowModP S p x') :
    IsPowModP S p (x + x') := by
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  obtain ⟨y', hy', z', hz', rfl⟩ := hx'
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (⟨y, hy⟩ : S) ⟨y', hy'⟩
  have hr' := congrArg Subtype.val hr
  push_cast at hr'
  refine ⟨y + y', S.add_mem hy hy', z + z' - y * y' * r, ?_, ?_⟩
  · exact S.sub_mem (S.add_mem hz hz') (S.mul_mem (S.mul_mem hy hy') r.2)
  · rw [hr']; ring

/- English proof (translation)
Take `⟨y, hy, z, hz, rfl⟩` from `hx`. Take `⟨y', hy', z', hz', rfl⟩` from `hx'`. Use `⟨y * y', S.mul_mem hy hy', z * y' ^ p + y ^ p * z' + (p : A) * z * z', ?_, ?_⟩` and prove the remaining obligations. Use `S.add_mem (S.add_mem (S.mul_mem hz (S.pow_mem hy' _)) (S.mul_mem (S.pow_mem hy _) hz')) (S.mul_mem (S.mul_mem ?_ hz) hz')` and prove the remaining obligations. Conclude with `S.natCast_mem p`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem isPthPowerModP_mul {x x' : A} (hx : IsPowModP S p x) (hx' : IsPowModP S p x') :
    IsPowModP S p (x * x') := by
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  obtain ⟨y', hy', z', hz', rfl⟩ := hx'
  refine ⟨y * y', S.mul_mem hy hy', z * y' ^ p + y ^ p * z' + (p : A) * z * z', ?_, ?_⟩
  · refine S.add_mem (S.add_mem (S.mul_mem hz (S.pow_mem hy' _))
      (S.mul_mem (S.pow_mem hy _) hz')) (S.mul_mem (S.mul_mem ?_ hz) hz')
    exact S.natCast_mem p
  · ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨y, hy, 0, S.zero_mem, by ring⟩`.
-/
theorem isPthPowerModP_pow {y : A} (hy : y ∈ S) : IsPowModP S p (y ^ p) :=
  ⟨y, hy, 0, S.zero_mem, by ring⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, S.zero_mem, 0, S.zero_mem, by rw [zero_pow hp.ne_zero]; ring⟩`.
-/
theorem isPthPowerModP_zero (hp : p.Prime) : IsPowModP S p 0 :=
  ⟨0, S.zero_mem, 0, S.zero_mem, by rw [zero_pow hp.ne_zero]; ring⟩

/- English proof (translation)
Take `⟨y, hy, z, hz, rfl⟩` from `hx`. Conclude with `⟨y, hy, z + h, S.add_mem hz hh, by ring⟩`.
-/
theorem isPthPowerModP_add_p_mul {x h : A} (hx : IsPowModP S p x) (hh : h ∈ S) :
    IsPowModP S p (x + (p : A) * h) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  exact ⟨y, hy, z + h, S.add_mem hz hh, by ring⟩

end Closure

/- English proof (translation)
Introduce `p hp Ω _ _ T x hx`. Use `set S := Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) with hS`. Establish `hpp : p.Prime` using `hp.out`. Establish `hζ : ∀ n, T.ζ n ∈ S` using `fun n => Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩)`. Establish `hq : ∀ n, T.qq n ∈ S` using `fun n => Algebra.subset_adjoin (Or.inr ⟨n, rfl⟩)`.

It suffices to establish `IsPowModP S p x from this`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨n, rfl⟩ | ⟨n, rfl⟩` into its components or cases. Rewrite using `[← T.ζpow n]`.

Conclude with `isPthPowerModP_pow S (hζ _)`. Rewrite using `[← T.qpow n]`. Conclude with `isPthPowerModP_pow S (hq _)`. Consider the case `algebraMap r`. Take `⟨g, h, rfl⟩` from `GlobalTheory.T.pAdicCompletionLaurent_eq_sum_pthPowers_mod_p p r`.

Rewrite using `[map_add, map_sum, map_mul, map_natCast]`. Use `isPthPowerModP_add_p_mul S ?_ ?_` and prove the remaining obligations. Use `Finset.sum_induction _ (IsPowModP S p) (fun a b ha hb => isPthPowerModP_add S hpp ha hb) (isPthPowerModP_zero S hpp) ?_` and prove the remaining obligations. Introduce `j _`. Establish `e : algebraMap (O0 p) Ω (qO p ^ (j : ℕ) * g j ^ p) = (T.qq 1 ^ (j : ℕ) * algebraMap (O0 p) Ω (g j)) ^ p`.

Rewrite using `[map_mul, map_pow, map_pow, ← T.q0, ← T.qpow 0, mul_pow, ← pow_mul, ← pow_mul, mul_comm p]`. Rewrite using `[e]`. Conclude with `isPthPowerModP_pow S (S.mul_mem (S.pow_mem (hq 1) _) (S.algebraMap_mem _))`. Conclude with `S.algebraMap_mem _`. Consider the case `add x y _ _ hx hy => exact isPthPowerModP_add S hpp hx hy`.

Consider the case `mul x y _ _ hx hy => exact isPthPowerModP_mul S hx hy`.
-/
theorem frob_surj_adjoin_tower : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
    (T : Tower p Ω), ∀ x ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq),
      ∃ y ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq),
      ∃ z ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), x = y ^ p + (p : Ω) * z := by
  intro p hp Ω _ _ T x hx
  set S := Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) with hS
  have hpp : p.Prime := hp.out
  have hζ : ∀ n, T.ζ n ∈ S := fun n => Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩)
  have hq : ∀ n, T.qq n ∈ S := fun n => Algebra.subset_adjoin (Or.inr ⟨n, rfl⟩)
  suffices IsPowModP S p x from this
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · rw [← T.ζpow n]; exact isPthPowerModP_pow S (hζ _)
    · rw [← T.qpow n]; exact isPthPowerModP_pow S (hq _)
  | algebraMap r =>
    obtain ⟨g, h, rfl⟩ := GlobalTheory.T.pAdicCompletionLaurent_eq_sum_pthPowers_mod_p p r
    rw [map_add, map_sum, map_mul, map_natCast]
    refine isPthPowerModP_add_p_mul S ?_ ?_
    · refine Finset.sum_induction _ (IsPowModP S p) (fun a b ha hb => isPthPowerModP_add S hpp ha hb)
        (isPthPowerModP_zero S hpp) ?_
      intro j _
      have e : algebraMap (O0 p) Ω (qO p ^ (j : ℕ) * g j ^ p) =
          (T.qq 1 ^ (j : ℕ) * algebraMap (O0 p) Ω (g j)) ^ p := by
        rw [map_mul, map_pow, map_pow, ← T.q0, ← T.qpow 0, mul_pow, ← pow_mul, ← pow_mul, mul_comm p]
      rw [e]
      exact isPthPowerModP_pow S (S.mul_mem (S.pow_mem (hq 1) _) (S.algebraMap_mem _))
    · exact S.algebraMap_mem _
  | add x y _ _ hx hy => exact isPthPowerModP_add S hpp hx hy
  | mul x y _ _ hx hy => exact isPthPowerModP_mul S hx hy

end GlobalTheory.K5
