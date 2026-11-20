import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5

namespace GlobalTheory.K5.Span

/- English proof (translation)
Establish `h1` using `Finset.sum_range_succ' f M`. Establish `h2` using `Finset.sum_range_succ f M`. Establish `h3 : f M = f 0` using `by simpa using hf 0`. Rewrite `h2` using `[h3]`. Conclude with `add_right_cancel (h1.symm.trans h2)`.
-/
theorem sum_range_shift_one {A : Type*} [AddCommGroup A] {M : ℕ} (f : ℕ → A)
    (hf : ∀ i, f (i + M) = f i) :
    ∑ i ∈ Finset.range M, f (i + 1) = ∑ i ∈ Finset.range M, f i := by
  have h1 := Finset.sum_range_succ' f M
  have h2 := Finset.sum_range_succ f M
  have h3 : f M = f 0 := by simpa using hf 0
  rw [h3] at h2
  exact add_right_cancel (h1.symm.trans h2)

/- English proof (translation)
Proceed by induction on `s generalizing f with`. Consider the case `zero => simp`. Consider the case `succ s ih`. Use `sum_range_shift_one (fun i => f (i + s)) (fun i => by show f (i + M + s) = f (i + s)` as an intermediate fact. Rewrite using `[add_right_comm, hf])`.

Rewrite using `[← ih f hf, ← this]`. Conclude with `Finset.sum_congr rfl fun i _ => by congr 1; omega`.
-/
theorem sum_range_shift {A : Type*} [AddCommGroup A] {M : ℕ} (f : ℕ → A)
    (hf : ∀ i, f (i + M) = f i) (s : ℕ) :
    ∑ i ∈ Finset.range M, f (i + s) = ∑ i ∈ Finset.range M, f i := by
  induction s generalizing f with
  | zero => simp
  | succ s ih =>
    have := sum_range_shift_one (fun i => f (i + s)) (fun i => by
      show f (i + M + s) = f (i + s)
      rw [add_right_comm, hf])
    rw [← ih f hf, ← this]
    exact Finset.sum_congr rfl fun i _ => by congr 1; omega

/- English proof (translation)
Introduce `p _ Ω _ _ hΩ T τ hτ hτq N z hz`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap hΩ.inj`. Establish `hprim : IsPrimitiveRoot (T.ζ N) (p ^ N)` using `T.prim N`. Establish `hMpos : 0 < p ^ N` using `pow_pos (Fact.out : p.Prime).pos N`. Establish `hq0 : T.qq N ≠ 0` using `Basic.qq_ne_zero T N`.

Establish `hqpow : T.qq N ^ p ^ N = algebraMap (O0 p) Ω (qO p)` using `Basic.qq_pow T N`. Establish `hτqN` using `hτq N`. Use `set M := p ^ N with hMdef`. Use `set ζ := T.ζ N with hζdef`. Use `set q := T.qq N with hqdef`.

Establish `hM0 : (M : Ω) ≠ 0` using `by exact_mod_cast hMpos.ne'`. Establish `hζ0 : ζ ≠ 0` using `hprim.ne_zero hMpos.ne'`. Establish `hζalg : IsAlgZp p ζ`. Use `⟨Polynomial.X ^ M - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero hMpos 1, ?_⟩` and prove the remaining obligations. Simplify using `[hprim.pow_eq_one]`.

Establish `hfixζ : ∀ g ∈ Ggeo p Ω, g ζ = ζ` using `fun g hg => hg ζ hζalg`. Establish `hτpow : ∀ i : ℕ, (τ ^ i) q = ζ ^ i * q`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => simp`.

Consider the case `succ i ih`. Rewrite using `[pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hfixζ τ hτ, hτqN, pow_succ']`. Expand and normalize the polynomial expressions, which then agree. Establish `hτG : ∀ i : ℕ, τ ^ i ∈ Ggeo p Ω` using `fun i => Subgroup.pow_mem _ hτ i`. Establish `hconj : ∀ g ∈ Ggeo p Ω, g q = q → ∀ i : ℕ, g ((τ ^ i) z) = (τ ^ i) z`.

Introduce `g hg hgq i`. Establish `hk : (τ ^ i)⁻¹ * g * τ ^ i ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) q`. Use `Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hτG i)) hg) (hτG i), MulAction.mem_stabilizer_iff.2 ?_⟩` and prove the remaining obligations. Use `show ((τ ^ i)⁻¹ * g * τ ^ i) q = q`. Rewrite using `[AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτpow, map_mul, map_pow, hfixζ g hg, hgq, ← hτpow, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]`.

Establish `hkz` using `hz _ hk`. Establish `e : τ ^ i * ((τ ^ i)⁻¹ * g * τ ^ i) = g * τ ^ i` using `by group`. Combine the equalities or inequalities in the displayed calculation. Establish `hdec : ∀ g ∈ Ggeo p Ω, ∃ s : ℕ, g q = ζ ^ s * q ∧ ∀ i : ℕ, g ((τ ^ i) z) = (τ ^ (s + i)) z`. Introduce `g hg`.

Establish `h1 : (g q / q) ^ M = 1`. Rewrite using `[div_pow, ← map_pow, hqpow, AlgEquiv.commutes, ← hqpow, div_self (pow_ne_zero _ hq0)]`. Take `⟨s, -, hse⟩` from `hprim.eq_pow_of_pow_eq_one h1`. Establish `hgq : g q = ζ ^ s * q` using `by rw [hse, div_mul_cancel₀ _ hq0]`. Use `⟨s, hgq, fun i => ?_⟩` and prove the remaining obligations.

Establish `hh : (τ ^ s)⁻¹ * g ∈ Ggeo p Ω` using `Subgroup.mul_mem _ (Subgroup.inv_mem _ (hτG s)) hg`. Establish `hhq : ((τ ^ s)⁻¹ * g) q = q`. Rewrite using `[AlgEquiv.mul_apply, hgq, ← hτpow, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]`. Establish `e : g = τ ^ s * ((τ ^ s)⁻¹ * g)` using `by group`. Rewrite using `[e, AlgEquiv.mul_apply, hconj _ hh hhq i, ← AlgEquiv.mul_apply, ← pow_add]`.

Establish `hτMz : (τ ^ M) z = z`. Use `hz _ (Subgroup.mem_inf.2 ⟨hτG M, MulAction.mem_stabilizer_iff.2 ?_⟩)` and prove the remaining obligations. Use `show (τ ^ M) q = q`. Rewrite using `[hτpow, hprim.pow_eq_one, one_mul]`. Use `set η := ζ⁻¹ with hηdef`.

Establish `hηprim : IsPrimitiveRoot η M` using `hprim.inv`. Establish `hfixη : ∀ g ∈ Ggeo p Ω, g η = η`. Introduce `g hg`. Rewrite using `[hηdef, map_inv₀, hfixζ g hg]`. Take `⟨P, hP⟩ : ∃ P : ℕ → Ω, ∀ j, P j = (M : Ω)⁻¹ * ∑ i ∈ Finset.range M, η ^ (i * j) * (τ ^ i) z` from `⟨_, fun _ => rfl⟩`.

Establish `hgP : ∀ g ∈ Ggeo p Ω, ∀ s : ℕ, (∀ i : ℕ, g ((τ ^ i) z) = (τ ^ (s + i)) z) → ∀ j, g (P j) = ζ ^ (s * j) * P j`. Introduce `g hg s hs j`. Rewrite using `[hP, map_mul, map_inv₀, map_natCast, map_sum]`. Establish `hper : ∀ i, (fun i => η ^ (i * j) * (τ ^ i) z) (i + M) = (fun i => η ^ (i * j) * (τ ^ i) z) i`. Introduce `i`.

Use `show η ^ ((i + M) * j) * (τ ^ (i + M)) z = η ^ (i * j) * (τ ^ i) z`. Rewrite using `[add_mul, pow_add, show η ^ (M * j) = 1 by rw [pow_mul, hηprim.pow_eq_one, one_pow], mul_one, pow_add, AlgEquiv.mul_apply, hτMz]`. Establish `hsh` using `sum_range_shift (M := M) (fun i => η ^ (i * j) * (τ ^ i) z) hper s`. Rewrite using `[← hsh, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_pow, hfixη g hg, hs, add_comm s i]`. Establish `hζη : ζ ^ (s * j) * η ^ (s * j) = 1`. Rewrite using `[← mul_pow, hηdef, mul_inv_cancel₀ hζ0, one_pow]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hζη, one_mul]`.

Use `_ = ζ ^ (s * j) * ((M : Ω)⁻¹ * (η ^ ((i + s) * j) * (τ ^ (i + s)) z)) := by`. Rewrite using `[add_mul, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨c, hc⟩ : ∃ c : ℕ → Ω, ∀ j, c j = P j / q ^ j` from `⟨_, fun _ => rfl⟩`. Use `⟨c, ?_, ?_⟩` and prove the remaining obligations.

Introduce `j g hg`. Take `⟨s, hgq, hs⟩` from `hdec g hg`. Rewrite using `[hc, map_div₀, map_pow, hgq, hgP g hg s hs j, mul_pow, ← pow_mul, mul_div_mul_left _ _ (pow_ne_zero _ hζ0)]`. Establish `hgeom : ∀ i ∈ Finset.range M, ∑ j ∈ Finset.range M, η ^ (i * j) = if i = 0 then (M : Ω) else 0`. Introduce `i hi`.

Use `split_ifs with h0`. Simplify using `[h0]`. Establish `hne : η ^ i ≠ 1` using `hηprim.pow_ne_one_of_pos_of_lt h0 (Finset.mem_range.1 hi)`. Repeatedly rewrite using `[pow_mul]`. Rewrite using `[geom_sum_eq hne, pow_right_comm, hηprim.pow_eq_one, one_pow, sub_self, zero_div]`.

Establish `e1 : ∑ i ∈ Finset.range M, (∑ j ∈ Finset.range M, η ^ (i * j)) * (τ ^ i) z = ∑ i ∈ Finset.range M, (if i = 0 then (M : Ω) else 0) * (τ ^ i) z` using `Finset.sum_congr rfl fun i hi => by rw [hgeom i hi]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 hMpos) (fun b _ hb => by simp [hb])]`. Simplify using `[hM0]`. Use `_ = ∑ j ∈ Finset.range M, P j := by`.

Simplify using `only [hP]`. Rewrite using `[← Finset.mul_sum, Finset.sum_comm]`. Simplify using `only [Finset.sum_mul]`. Use `_ = ∑ j ∈ Finset.range M, c j * q ^ j := Finset.sum_congr rfl fun j _ => by rw [hc, div_mul_cancel₀ _ (pow_ne_zero j hq0)]`.
-/
theorem span : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (z : Ω), (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) ∧ z = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j := by
  intro p _ Ω _ _ hΩ T τ hτ hτq N z hz
  haveI : CharZero Ω := charZero_of_injective_algebraMap hΩ.inj
  have hprim : IsPrimitiveRoot (T.ζ N) (p ^ N) := T.prim N
  have hMpos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N
  have hq0 : T.qq N ≠ 0 := Basic.qq_ne_zero T N
  have hqpow : T.qq N ^ p ^ N = algebraMap (O0 p) Ω (qO p) := Basic.qq_pow T N
  have hτqN := hτq N
  set M := p ^ N with hMdef
  set ζ := T.ζ N with hζdef
  set q := T.qq N with hqdef
  have hM0 : (M : Ω) ≠ 0 := by exact_mod_cast hMpos.ne'
  have hζ0 : ζ ≠ 0 := hprim.ne_zero hMpos.ne'

  have hζalg : IsAlgZp p ζ := by
    refine ⟨Polynomial.X ^ M - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero hMpos 1, ?_⟩
    simp [hprim.pow_eq_one]
  have hfixζ : ∀ g ∈ Ggeo p Ω, g ζ = ζ := fun g hg => hg ζ hζalg
  have hτpow : ∀ i : ℕ, (τ ^ i) q = ζ ^ i * q := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hfixζ τ hτ, hτqN, pow_succ']
      ring
  have hτG : ∀ i : ℕ, τ ^ i ∈ Ggeo p Ω := fun i => Subgroup.pow_mem _ hτ i
  have hconj : ∀ g ∈ Ggeo p Ω, g q = q → ∀ i : ℕ, g ((τ ^ i) z) = (τ ^ i) z := by
    intro g hg hgq i
    have hk : (τ ^ i)⁻¹ * g * τ ^ i ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) q := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hτG i)) hg)
        (hτG i), MulAction.mem_stabilizer_iff.2 ?_⟩
      show ((τ ^ i)⁻¹ * g * τ ^ i) q = q
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτpow, map_mul, map_pow, hfixζ g hg, hgq, ← hτpow,
        AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    have hkz := hz _ hk
    have e : τ ^ i * ((τ ^ i)⁻¹ * g * τ ^ i) = g * τ ^ i := by group
    calc g ((τ ^ i) z) = (g * τ ^ i) z := rfl
      _ = (τ ^ i * ((τ ^ i)⁻¹ * g * τ ^ i)) z := by rw [e]
      _ = (τ ^ i) (((τ ^ i)⁻¹ * g * τ ^ i) z) := rfl
      _ = (τ ^ i) z := by rw [hkz]
  have hdec : ∀ g ∈ Ggeo p Ω, ∃ s : ℕ, g q = ζ ^ s * q ∧ ∀ i : ℕ, g ((τ ^ i) z) = (τ ^ (s + i)) z := by
    intro g hg
    have h1 : (g q / q) ^ M = 1 := by
      rw [div_pow, ← map_pow, hqpow, AlgEquiv.commutes, ← hqpow, div_self (pow_ne_zero _ hq0)]
    obtain ⟨s, -, hse⟩ := hprim.eq_pow_of_pow_eq_one h1
    have hgq : g q = ζ ^ s * q := by rw [hse, div_mul_cancel₀ _ hq0]
    refine ⟨s, hgq, fun i => ?_⟩
    have hh : (τ ^ s)⁻¹ * g ∈ Ggeo p Ω := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hτG s)) hg
    have hhq : ((τ ^ s)⁻¹ * g) q = q := by
      rw [AlgEquiv.mul_apply, hgq, ← hτpow, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    have e : g = τ ^ s * ((τ ^ s)⁻¹ * g) := by group
    rw [e, AlgEquiv.mul_apply, hconj _ hh hhq i, ← AlgEquiv.mul_apply, ← pow_add]

  have hτMz : (τ ^ M) z = z := by
    refine hz _ (Subgroup.mem_inf.2 ⟨hτG M, MulAction.mem_stabilizer_iff.2 ?_⟩)
    show (τ ^ M) q = q
    rw [hτpow, hprim.pow_eq_one, one_mul]
  set η := ζ⁻¹ with hηdef
  have hηprim : IsPrimitiveRoot η M := hprim.inv
  have hfixη : ∀ g ∈ Ggeo p Ω, g η = η := by
    intro g hg; rw [hηdef, map_inv₀, hfixζ g hg]
  obtain ⟨P, hP⟩ : ∃ P : ℕ → Ω, ∀ j,
      P j = (M : Ω)⁻¹ * ∑ i ∈ Finset.range M, η ^ (i * j) * (τ ^ i) z := ⟨_, fun _ => rfl⟩
  have hgP : ∀ g ∈ Ggeo p Ω, ∀ s : ℕ, (∀ i : ℕ, g ((τ ^ i) z) = (τ ^ (s + i)) z) →
      ∀ j, g (P j) = ζ ^ (s * j) * P j := by
    intro g hg s hs j
    rw [hP, map_mul, map_inv₀, map_natCast, map_sum]
    have hper : ∀ i, (fun i => η ^ (i * j) * (τ ^ i) z) (i + M) = (fun i => η ^ (i * j) * (τ ^ i) z) i := by
      intro i
      show η ^ ((i + M) * j) * (τ ^ (i + M)) z = η ^ (i * j) * (τ ^ i) z
      rw [add_mul, pow_add, show η ^ (M * j) = 1 by rw [pow_mul, hηprim.pow_eq_one, one_pow],
        mul_one, pow_add, AlgEquiv.mul_apply, hτMz]
    have hsh := sum_range_shift (M := M) (fun i => η ^ (i * j) * (τ ^ i) z) hper s
    rw [← hsh, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hfixη g hg, hs, add_comm s i]
    have hζη : ζ ^ (s * j) * η ^ (s * j) = 1 := by
      rw [← mul_pow, hηdef, mul_inv_cancel₀ hζ0, one_pow]
    calc (M : Ω)⁻¹ * (η ^ (i * j) * (τ ^ (i + s)) z)
        = (M : Ω)⁻¹ * ((ζ ^ (s * j) * η ^ (s * j)) * η ^ (i * j) * (τ ^ (i + s)) z) := by
          rw [hζη, one_mul]
      _ = ζ ^ (s * j) * ((M : Ω)⁻¹ * (η ^ ((i + s) * j) * (τ ^ (i + s)) z)) := by
          rw [add_mul, pow_add]; ring
  obtain ⟨c, hc⟩ : ∃ c : ℕ → Ω, ∀ j, c j = P j / q ^ j := ⟨_, fun _ => rfl⟩
  refine ⟨c, ?_, ?_⟩
  · intro j g hg
    obtain ⟨s, hgq, hs⟩ := hdec g hg
    rw [hc, map_div₀, map_pow, hgq, hgP g hg s hs j, mul_pow, ← pow_mul,
      mul_div_mul_left _ _ (pow_ne_zero _ hζ0)]
  · have hgeom : ∀ i ∈ Finset.range M,
        ∑ j ∈ Finset.range M, η ^ (i * j) = if i = 0 then (M : Ω) else 0 := by
      intro i hi
      split_ifs with h0
      · simp [h0]
      · have hne : η ^ i ≠ 1 :=
          hηprim.pow_ne_one_of_pos_of_lt h0 (Finset.mem_range.1 hi)
        simp_rw [pow_mul]
        rw [geom_sum_eq hne, pow_right_comm, hηprim.pow_eq_one, one_pow, sub_self, zero_div]
    have e1 : ∑ i ∈ Finset.range M, (∑ j ∈ Finset.range M, η ^ (i * j)) * (τ ^ i) z =
        ∑ i ∈ Finset.range M, (if i = 0 then (M : Ω) else 0) * (τ ^ i) z :=
      Finset.sum_congr rfl fun i hi => by rw [hgeom i hi]
    calc z = (M : Ω)⁻¹ * ∑ i ∈ Finset.range M, (∑ j ∈ Finset.range M, η ^ (i * j)) * (τ ^ i) z := by
          rw [e1, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 hMpos) (fun b _ hb => by simp [hb])]
          simp [hM0]
      _ = ∑ j ∈ Finset.range M, P j := by
          simp only [hP]
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_mul]
      _ = ∑ j ∈ Finset.range M, c j * q ^ j :=
          Finset.sum_congr rfl fun j _ => by rw [hc, div_mul_cancel₀ _ (pow_ne_zero j hq0)]

end GlobalTheory.K5.Span
