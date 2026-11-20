import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowDivPrimeZpowIntegralClosureUnitStatement
open GlobalTheory.K5

namespace GlobalTheory.K5.ResidueIndep

open Polynomial

/- English proof (translation)
Use `haveI : ExpChar K p := ExpChar.prime hp.out`. Take `⟨n, y, hf⟩` from `(minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C (F := K) p (x := t)).1 ((minpoly.natSepDegree_eq_one_iff_pow_mem (F := K) p (x := t)).2 ⟨N, ⟨⟨_, ha⟩, rfl⟩⟩)`. Establish `hy : t ^ p ^ n = (y : k)`. Use `minpoly.aeval K t` as an intermediate fact. Rewrite `this` using `[hf]`.

Simplify using `only [map_sub, map_pow, aeval_X, aeval_C] at this`. Conclude with `sub_eq_zero.1 this`. Establish `hNn : N ≤ n`. Assume the negation of the conclusion as `h`. Take `⟨r, rfl⟩` from `Nat.exists_eq_add_of_lt (not_le.1 h)`.

Use `hna ((y : k) ^ p ^ r) (K.pow_mem y.2 _) ?_` and prove the remaining obligations. Rewrite using `[← hy, ← pow_mul, ← pow_mul, pow_add, pow_add, pow_one, mul_assoc]`. Set `c' : ℕ → K` to `fun j => if h : j < p ^ N then ⟨c j, hc j h⟩ else 0`. Set `P : K[X]` to `∑ j ∈ Finset.range (p ^ N), monomial j (c' j)`. Establish `hP : aeval t P = 0`.

Rewrite using `[← hs, map_sum]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial]`. Simplify using `only [c', dif_pos (Finset.mem_range.1 hj)]`. Both sides reduce to the same expression.

Establish `hP0 : P = 0`. Assume the negation of the conclusion as `h`. Establish `h1` using `minpoly.degree_le_of_ne_zero K t h hP`. Establish `h2 : P.degree < ((p ^ N : ℕ) : WithBot ℕ)`. Use `(degree_sum_le _ _).trans_lt ?_` and prove the remaining obligations.

Rewrite using `[Finset.sup_lt_iff (WithBot.bot_lt_coe _)]`. Introduce `j hj`. Conclude with `(degree_monomial_le _ _).trans_lt (by exact_mod_cast Finset.mem_range.1 hj)`. Rewrite `h1` using `[hf, degree_X_pow_sub_C (pow_pos hp.out.pos n)]`. Establish `h3` using `h1.trans_lt h2`.

Establish `h4 : p ^ n < p ^ N` using `by exact_mod_cast h3`. Conclude with `absurd (Nat.pow_le_pow_right hp.out.pos hNn) (not_le.2 h4)`. Introduce `j hj`. Establish `h1 : P.coeff j = c' j`. Simplify using `only [P, finset_sum_coeff, coeff_monomial]`.

Rewrite using `[Finset.sum_ite_eq' , if_pos (Finset.mem_range.2 hj)]`. Rewrite `h1` using `[hP0, coeff_zero]`. Establish `h2` using `congrArg Subtype.val h1`. Simplify using `only [c', dif_pos hj] at h2`. Conclude with `h2.symm`.
-/
theorem field_indep {k : Type} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] (K : Subfield k)
    (N : ℕ) (t : k) (ha : t ^ p ^ N ∈ K) (hna : ∀ b ∈ K, b ^ p ≠ t ^ p ^ N)
    (c : ℕ → k) (hc : ∀ j < p ^ N, c j ∈ K)
    (hs : ∑ j ∈ Finset.range (p ^ N), c j * t ^ j = 0) : ∀ j < p ^ N, c j = 0 := by
  classical
  haveI : ExpChar K p := ExpChar.prime hp.out
  obtain ⟨n, y, hf⟩ := (minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C (F := K) p (x := t)).1
    ((minpoly.natSepDegree_eq_one_iff_pow_mem (F := K) p (x := t)).2 ⟨N, ⟨⟨_, ha⟩, rfl⟩⟩)
  have hy : t ^ p ^ n = (y : k) := by
    have := minpoly.aeval K t
    rw [hf] at this
    simp only [map_sub, map_pow, aeval_X, aeval_C] at this
    exact sub_eq_zero.1 this
  have hNn : N ≤ n := by
    by_contra h
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt (not_le.1 h)
    refine hna ((y : k) ^ p ^ r) (K.pow_mem y.2 _) ?_
    rw [← hy, ← pow_mul, ← pow_mul, pow_add, pow_add, pow_one, mul_assoc]
  let c' : ℕ → K := fun j => if h : j < p ^ N then ⟨c j, hc j h⟩ else 0
  let P : K[X] := ∑ j ∈ Finset.range (p ^ N), monomial j (c' j)
  have hP : aeval t P = 0 := by
    rw [← hs, map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [aeval_monomial]
    simp only [c', dif_pos (Finset.mem_range.1 hj)]
    rfl
  have hP0 : P = 0 := by
    by_contra h
    have h1 := minpoly.degree_le_of_ne_zero K t h hP
    have h2 : P.degree < ((p ^ N : ℕ) : WithBot ℕ) := by
      refine (degree_sum_le _ _).trans_lt ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro j hj
      exact (degree_monomial_le _ _).trans_lt (by exact_mod_cast Finset.mem_range.1 hj)
    rw [hf, degree_X_pow_sub_C (pow_pos hp.out.pos n)] at h1
    have h3 := h1.trans_lt h2
    have h4 : p ^ n < p ^ N := by exact_mod_cast h3
    exact absurd (Nat.pow_le_pow_right hp.out.pos hNn) (not_le.2 h4)
  intro j hj
  have h1 : P.coeff j = c' j := by
    simp only [P, finset_sum_coeff, coeff_monomial]
    rw [Finset.sum_ite_eq' , if_pos (Finset.mem_range.2 hj)]
  rw [hP0, coeff_zero] at h1
  have h2 := congrArg Subtype.val h1
  simp only [c', dif_pos hj] at h2
  exact h2.symm

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

/- English proof (translation)
Use `haveI := Basic.charZero_of_isClo h`. Establish `hp0 : (p : Ω) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn⟩`. Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.1 hn`.

Use `⟨n + 1, n.succ_pos, ?_⟩` and prove the remaining obligations. Establish `h1 : (z : Ω) * p = (x : Ω) ^ n` using `by exact_mod_cast congrArg Subtype.val hz`. Establish `h2 : (x : Ω) ^ (n + 1) / p = ((z * x : integralClosure (O0 p) Ω) : Ω)`. Rewrite using `[pow_succ, ← h1]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[h2]`. Conclude with `(z * x).2`. Introduce and unpack `⟨m, -, hm⟩`. Use `⟨m, Ideal.mem_span_singleton'.2 ⟨⟨_, hm⟩, Subtype.ext ?_⟩⟩` and prove the remaining obligations.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem mem_rad_iff (h : IsClo p Ω) (x : integralClosure (O0 p) Ω) :
    x ∈ (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical ↔
      ∃ m : ℕ, 0 < m ∧ IsInt p ((x : Ω) ^ m / (p : Ω)) := by
  haveI := Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hn
    refine ⟨n + 1, n.succ_pos, ?_⟩
    have h1 : (z : Ω) * p = (x : Ω) ^ n := by exact_mod_cast congrArg Subtype.val hz
    have h2 : (x : Ω) ^ (n + 1) / p = ((z * x : integralClosure (O0 p) Ω) : Ω) := by
      rw [pow_succ, ← h1]; push_cast; field_simp
    rw [h2]
    exact (z * x).2
  · rintro ⟨m, -, hm⟩
    refine ⟨m, Ideal.mem_span_singleton'.2 ⟨⟨_, hm⟩, Subtype.ext ?_⟩⟩
    push_cast
    field_simp

/- English proof (translation)
Use `haveI := Basic.charZero_of_isClo h`. Establish `hp0 : (p : Ω) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`. Establish `hpi : IsIntegral (O0 p) (p : Ω)` using `by exact_mod_cast Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hx ⟨1, one_pos, by simpa [IsInt] using isIntegral_zero⟩`. Use `⟨hx0, ?_⟩` and prove the remaining obligations. Take `⟨a, b, hb, h1, h2⟩` from `GlobalTheory.T.exists_pow_div_prime_zpow_integralClosure_unit p Ω h x hx0`. Distinguish the cases in `ha : 0 < a`. It suffices to derive a contradiction.

Take `⟨n, rfl⟩ : ∃ n : ℕ, a = (n + 1 : ℕ)` from `⟨(a - 1).toNat, by push_cast; omega⟩`. Use `hx ⟨b, hb, ?_⟩` and prove the remaining obligations. Establish `: x ^ b / (p : Ω) = x ^ b / (p : Ω) ^ ((n + 1 : ℕ) : ℤ) * (p : Ω) ^ n`. Rewrite using `[zpow_natCast]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `IsIntegral.mul h1 (hpi.pow n)`. Take `⟨n, rfl⟩ : ∃ n : ℕ, a = -(n : ℤ)` from `⟨(-a).toNat, by omega⟩`. Use `IsIntegral.of_pow hb ?_` and prove the remaining obligations.

Establish `: x⁻¹ ^ b = (p : Ω) ^ (-(n : ℤ)) / x ^ b * (p : Ω) ^ n`. Rewrite using `[zpow_neg, zpow_natCast, inv_pow]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `IsIntegral.mul h2 (hpi.pow n)`.
-/
theorem isInt_inv (h : IsClo p Ω) (x : Ω)
    (hx : ¬ ∃ m : ℕ, 0 < m ∧ IsInt p (x ^ m / (p : Ω))) : x ≠ 0 ∧ IsInt p x⁻¹ := by
  haveI := Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpi : IsIntegral (O0 p) (p : Ω) := by exact_mod_cast Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx ⟨1, one_pos, by simpa [IsInt] using isIntegral_zero⟩
  refine ⟨hx0, ?_⟩
  obtain ⟨a, b, hb, h1, h2⟩ := GlobalTheory.T.exists_pow_div_prime_zpow_integralClosure_unit p Ω h x hx0
  by_cases ha : 0 < a
  · exfalso
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = (n + 1 : ℕ) := ⟨(a - 1).toNat, by push_cast; omega⟩
    refine hx ⟨b, hb, ?_⟩
    have : x ^ b / (p : Ω) = x ^ b / (p : Ω) ^ ((n + 1 : ℕ) : ℤ) * (p : Ω) ^ n := by
      rw [zpow_natCast]; field_simp; ring
    rw [this]
    exact IsIntegral.mul h1 (hpi.pow n)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = -(n : ℤ) := ⟨(-a).toNat, by omega⟩
    refine IsIntegral.of_pow hb ?_
    have : x⁻¹ ^ b = (p : Ω) ^ (-(n : ℤ)) / x ^ b * (p : Ω) ^ n := by
      rw [zpow_neg, zpow_natCast, inv_pow]; field_simp
    rw [this]
    exact IsIntegral.mul h2 (hpi.pow n)

/- English proof (translation)
Use `haveI := Basic.charZero_of_isClo h`. Establish `hp0 : (p : Ω) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`. Rewrite using `[Ideal.isMaximal_iff]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[mem_rad_iff h]`.

Introduce and unpack `⟨m, -, hm⟩`. Use `Basic.not_cong_one_zero h 1 one_ne_zero ⟨_, hm, ?_⟩` and prove the remaining obligations. Simplify using `[hp0]`. Introduce `J x _ hx hxJ`. Rewrite `hx` using `[mem_rad_iff h]`.

Take `⟨h0, h1⟩` from `isInt_inv h _ hx`. Establish `: (1 : integralClosure (O0 p) Ω) = ⟨_, h1⟩ * x` using `Subtype.ext (inv_mul_cancel₀ h0).symm`. Rewrite using `[this]`. Conclude with `J.mul_mem_left _ hxJ`.
-/
theorem rad_isMaximal (h : IsClo p Ω) :
    (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical.IsMaximal := by
  haveI := Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [Ideal.isMaximal_iff]
  constructor
  · rw [mem_rad_iff h]
    rintro ⟨m, -, hm⟩
    refine Basic.not_cong_one_zero h 1 one_ne_zero ⟨_, hm, ?_⟩
    simp [hp0]
  · intro J x _ hx hxJ
    rw [mem_rad_iff h] at hx
    obtain ⟨h0, h1⟩ := isInt_inv h _ hx
    have : (1 : integralClosure (O0 p) Ω) = ⟨_, h1⟩ * x :=
      Subtype.ext (inv_mul_cancel₀ h0).symm
    rw [this]
    exact J.mul_mem_left _ hxJ

/- English proof (translation)
Introduce `p hp Ω _ _ h E hE hq T N d hd hs`. Use `set M := (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical with hM`. Establish `hmem : ∀ x : integralClosure (O0 p) Ω, Ideal.Quotient.mk M x = 0 ↔ ∃ m : ℕ, 0 < m ∧ IsInt p ((x : Ω) ^ m / (p : Ω))` using `fun x => by`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, hM, mem_rad_iff h]`. Use `haveI : M.IsMaximal := rad_isMaximal h`.

Use `letI : Field (integralClosure (O0 p) Ω ⧸ M) := Ideal.Quotient.field M`. Use `haveI : CharP (integralClosure (O0 p) Ω ⧸ M) p := by`. Rewrite using `[CharP.charP_iff_prime_eq_zero hp.out, ← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.le_radical (Ideal.mem_span_singleton_self _)`. Set `K : Subfield (integralClosure (O0 p) Ω ⧸ M)` to `{ (E.toSubring.comap (integralClosure (O0 p) Ω).val.toRingHom).map (Ideal.Quotient.mk M) with inv_mem' := by`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Distinguish the cases in `h0 : Ideal.Quotient.mk M y = 0`. Conclude with `⟨0, E.zero_mem, by rw [h0, inv_zero, map_zero]⟩`. Take `⟨h1, h2⟩` from `isInt_inv h (y : Ω) (fun hh => h0 ((hmem y).2 hh))`. Use `⟨⟨_, h2⟩, E.inv_mem hy, ?_⟩` and prove the remaining obligations.

Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Rewrite using `[← map_mul, ← map_one (Ideal.Quotient.mk M)]`. Use `congr 1`. Conclude with `Subtype.ext (inv_mul_cancel₀ h1) }`. Establish `hqi : IsIntegral (O0 p) (T.qq N)` using `IsIntegral.of_pow (pow_pos hp.out.pos N) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)`.

Set `t : integralClosure (O0 p) Ω` to `⟨_, hqi⟩`. Establish `ht : ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) = algebraMap (O0 p) Ω (qO p)`. Rewrite using `[← Basic.qq_pow T N]`. Both sides reduce to the same expression. Set `d' : ℕ → integralClosure (O0 p) Ω` to `fun j => if hj : j < p ^ N then ⟨d j, (hd j hj).2⟩ else 0`.

Establish `hd' : ∀ j < p ^ N, (d' j : Ω) = d j` using `fun j hj => by simp only [d', dif_pos hj]`. Establish `key` using `field_indep p K N (Ideal.Quotient.mk M t) ⟨t ^ p ^ N, by show ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) ∈ E`. Rewrite using `[ht]`. Conclude with `hE ⟨_, rfl⟩, map_pow _ _ _⟩`. Use the proof step `(by`.

Introduce and unpack `_ ⟨y, hy, rfl⟩ hb`. Use `hq y hy y.2 ?_` and prove the remaining obligations. Rewrite using `[← ht]`. Use `(hmem (y ^ p - t ^ p ^ N)).1 (by rw [map_sub, map_pow, map_pow, hb, sub_self])` as an intermediate fact. Conclude with `this)`.

Use the proof step `(fun j => Ideal.Quotient.mk M (d' j))`. Use the proof step `(fun j hj => ⟨d' j, by show (d' j : Ω) ∈ E`. Rewrite using `[hd' j hj]`. Conclude with `(hd j hj).1, rfl⟩)`. Use the proof step `(by`.

Establish `e : ((∑ j ∈ Finset.range (p ^ N), d' j * t ^ j : integralClosure (O0 p) Ω) : Ω) = ∑ j ∈ Finset.range (p ^ N), d j * T.qq N ^ j`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun j hj => by rw [hd' j (Finset.mem_range.1 hj)]`. Use `(hmem _).2 (e ▸ hs)` as an intermediate fact. Simplify `this)` using `only [map_sum, map_mul, map_pow]`.

Introduce `j hj`. Rewrite using `[← hd' j hj]`. Conclude with `(hmem _).1 (key j hj)`.
-/
theorem residue_indep : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ E : Subfield Ω, Set.range (algebraMap (O0 p) Ω) ⊆ (E : Set Ω) →
  (∀ y ∈ E, IsInt p y →
    ¬ ∃ m : ℕ, 0 < m ∧ IsInt p ((y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m / (p : Ω))) →
  ∀ (T : Tower p Ω) (N : ℕ) (d : ℕ → Ω), (∀ j < p ^ N, d j ∈ E ∧ IsInt p (d j)) →
  (∃ m : ℕ, 0 < m ∧ IsInt p ((∑ j ∈ Finset.range (p ^ N), d j * T.qq N ^ j) ^ m / (p : Ω))) →
  ∀ j < p ^ N, ∃ m : ℕ, 0 < m ∧ IsInt p (d j ^ m / (p : Ω)) := by
  intro p hp Ω _ _ h E hE hq T N d hd hs
  classical
  set M := (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical with hM
  have hmem : ∀ x : integralClosure (O0 p) Ω, Ideal.Quotient.mk M x = 0 ↔
      ∃ m : ℕ, 0 < m ∧ IsInt p ((x : Ω) ^ m / (p : Ω)) := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, hM, mem_rad_iff h]
  haveI : M.IsMaximal := rad_isMaximal h
  letI : Field (integralClosure (O0 p) Ω ⧸ M) := Ideal.Quotient.field M
  haveI : CharP (integralClosure (O0 p) Ω ⧸ M) p := by
    rw [CharP.charP_iff_prime_eq_zero hp.out, ← map_natCast (Ideal.Quotient.mk M),
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.le_radical (Ideal.mem_span_singleton_self _)
  let K : Subfield (integralClosure (O0 p) Ω ⧸ M) :=
    { (E.toSubring.comap (integralClosure (O0 p) Ω).val.toRingHom).map (Ideal.Quotient.mk M) with
      inv_mem' := by
        rintro _ ⟨y, hy, rfl⟩
        by_cases h0 : Ideal.Quotient.mk M y = 0
        · exact ⟨0, E.zero_mem, by rw [h0, inv_zero, map_zero]⟩
        · obtain ⟨h1, h2⟩ := isInt_inv h (y : Ω) (fun hh => h0 ((hmem y).2 hh))
          refine ⟨⟨_, h2⟩, E.inv_mem hy, ?_⟩
          refine eq_inv_of_mul_eq_one_left ?_
          rw [← map_mul, ← map_one (Ideal.Quotient.mk M)]
          congr 1
          exact Subtype.ext (inv_mul_cancel₀ h1) }
  have hqi : IsIntegral (O0 p) (T.qq N) :=
    IsIntegral.of_pow (pow_pos hp.out.pos N) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  let t : integralClosure (O0 p) Ω := ⟨_, hqi⟩
  have ht : ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) = algebraMap (O0 p) Ω (qO p) := by
    rw [← Basic.qq_pow T N]; rfl
  let d' : ℕ → integralClosure (O0 p) Ω := fun j => if hj : j < p ^ N then ⟨d j, (hd j hj).2⟩ else 0
  have hd' : ∀ j < p ^ N, (d' j : Ω) = d j := fun j hj => by simp only [d', dif_pos hj]
  have key := field_indep p K N (Ideal.Quotient.mk M t)
    ⟨t ^ p ^ N, by
      show ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) ∈ E
      rw [ht]; exact hE ⟨_, rfl⟩, map_pow _ _ _⟩
    (by
      rintro _ ⟨y, hy, rfl⟩ hb
      refine hq y hy y.2 ?_
      rw [← ht]
      have := (hmem (y ^ p - t ^ p ^ N)).1 (by rw [map_sub, map_pow, map_pow, hb, sub_self])
      exact this)
    (fun j => Ideal.Quotient.mk M (d' j))
    (fun j hj => ⟨d' j, by
      show (d' j : Ω) ∈ E
      rw [hd' j hj]; exact (hd j hj).1, rfl⟩)
    (by
      have e : ((∑ j ∈ Finset.range (p ^ N), d' j * t ^ j : integralClosure (O0 p) Ω) : Ω) =
          ∑ j ∈ Finset.range (p ^ N), d j * T.qq N ^ j := by
        push_cast
        exact Finset.sum_congr rfl fun j hj => by rw [hd' j (Finset.mem_range.1 hj)]
      have := (hmem _).2 (e ▸ hs)
      simpa only [map_sum, map_mul, map_pow] using this)
  intro j hj
  rw [← hd' j hj]
  exact (hmem _).1 (key j hj)

end GlobalTheory.K5.ResidueIndep
