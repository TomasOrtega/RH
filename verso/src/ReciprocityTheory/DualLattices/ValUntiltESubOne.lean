import Mathlib
import ReciprocityTheory.DualLattices.CyclicRecursionStatement

noncomputable section

open WittVector Ideal Polynomial

namespace ReciprocityTheory.PGsh

/- English proof (translation)
Establish `hu : ∀ n, IsUnit (Perfection.coeff R p n x)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact h`. Consider the case `succ n ih`.

Establish `h2 : Perfection.coeff R p (n + 1) x ^ p = Perfection.coeff R p n x` using `Perfection.coeff_pow_p' x n`. Rewrite `ih` using `[← h2]`. Conclude with `(isUnit_pow_iff hp.out.ne_zero).mp ih`. Establish `h3 : ∀ n, (hu (n + 1)).unit ^ p = (hu n).unit` using `fun n => Units.ext (by simpa using Perfection.coeff_pow_p' x n)`. Set `y : Perfection R p` to `⟨fun n => ((hu n).unit⁻¹ : Rˣ), fun n => by show (((hu (n + 1)).unit⁻¹ : Rˣ) : R) ^ p = (((hu n).unit⁻¹ : Rˣ) : R)`.

Rewrite using `[← Units.val_pow_eq_pow_val, inv_pow, h3]⟩`. Use `isUnit_iff_exists_inv.mpr ⟨y, Perfection.ext fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_one]`. Conclude with `(hu n).mul_val_inv`.
-/
private lemma perfection_isUnit {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    (x : Perfection R p) (h : IsUnit (Perfection.coeff R p 0 x)) : IsUnit x := by
  have hu : ∀ n, IsUnit (Perfection.coeff R p n x) := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih =>
      have h2 : Perfection.coeff R p (n + 1) x ^ p = Perfection.coeff R p n x :=
        Perfection.coeff_pow_p' x n
      rw [← h2] at ih
      exact (isUnit_pow_iff hp.out.ne_zero).mp ih
  have h3 : ∀ n, (hu (n + 1)).unit ^ p = (hu n).unit := fun n =>
    Units.ext (by simpa using Perfection.coeff_pow_p' x n)
  let y : Perfection R p := ⟨fun n => ((hu n).unit⁻¹ : Rˣ), fun n => by
    show (((hu (n + 1)).unit⁻¹ : Rˣ) : R) ^ p = (((hu n).unit⁻¹ : Rˣ) : R)
    rw [← Units.val_pow_eq_pow_val, inv_pow, h3]⟩
  refine isUnit_iff_exists_inv.mpr ⟨y, Perfection.ext fun n => ?_⟩
  rw [map_mul, map_one]
  exact (hu n).mul_val_inv

/- English proof (translation)
Take `⟨u, hu⟩` from `h`. Conclude with `⟨WittVector.mkUnit (p := p) (a := u) (A := c) (by rw [hu]; rfl), rfl⟩`.
-/
private lemma witt_isUnit {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    [PerfectRing R p] (c : WittVector p R) (h : IsUnit (constantCoeff c)) : IsUnit c := by
  obtain ⟨u, hu⟩ := h
  exact ⟨WittVector.mkUnit (p := p) (a := u) (A := c) (by rw [hu]; rfl), rfl⟩

/- English proof (translation)
Establish `hX : ((Polynomial.X : (ZMod p)[X]) - 1) ^ (p - 1) = ∑ i ∈ Finset.range p, (Polynomial.X : (ZMod p)[X]) ^ i`. Establish `hne : (Polynomial.X : (ZMod p)[X]) - 1 ≠ 0`. Simplify using `using Polynomial.X_sub_C_ne_zero (1 : ZMod p)`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[← pow_succ', Nat.sub_add_cancel hp.out.one_lt.le, sub_pow_char, one_pow, mul_comm, geom_sum_mul]`.

Establish `h` using `congrArg (Polynomial.eval₂ (ZMod.castHom (dvd_refl p) R) x) hX`. Simplify `h` using `[Polynomial.eval₂_finset_sum, Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_one]`.
-/
private lemma sub_one_pow_pred {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    (x : R) : (x - 1) ^ (p - 1) = ∑ i ∈ Finset.range p, x ^ i := by
  have hX : ((Polynomial.X : (ZMod p)[X]) - 1) ^ (p - 1) =
      ∑ i ∈ Finset.range p, (Polynomial.X : (ZMod p)[X]) ^ i := by
    have hne : (Polynomial.X : (ZMod p)[X]) - 1 ≠ 0 := by
      simpa using Polynomial.X_sub_C_ne_zero (1 : ZMod p)
    apply mul_left_cancel₀ hne
    rw [← pow_succ', Nat.sub_add_cancel hp.out.one_lt.le, sub_pow_char, one_pow, mul_comm,
      geom_sum_mul]
  have h := congrArg (Polynomial.eval₂ (ZMod.castHom (dvd_refl p) R) x) hX
  simpa [Polynomial.eval₂_finset_sum, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_one] using h

/- English proof (translation)
Take `⟨i, -, hi⟩ : ∃ i < p, β ^ i = α` from `by first`. Consider the case `exact hβ.eq_pow_of_pow_eq_one hα.pow_eq_one`. Consider the case `exact hβ.eq_pow_of_pow_eq_one hα.pow_eq_one hp.out.pos`. Establish `hvb : v β = 1`. Establish `h : v β ^ p = 1` using `by rw [← map_pow, hβ.pow_eq_one, map_one]`.

Conclude with `(pow_eq_one_iff_of_nonneg (by positivity) hp.out.ne_zero).mp h`. Rewrite using `[← hi, ← geom_sum_mul, map_mul]`. Establish `hs : v (∑ k ∈ Finset.range i, β ^ k) ≤ 1` using `v.map_sum_le fun k _ => by rw [map_pow, hvb, one_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma val_sub_one_le {C : Type*} [Field C] (v : Valuation C NNReal) {p : ℕ}
    [hp : Fact p.Prime] {α β : C} (hα : IsPrimitiveRoot α p) (hβ : IsPrimitiveRoot β p) :
    v (α - 1) ≤ v (β - 1) := by
  obtain ⟨i, -, hi⟩ : ∃ i < p, β ^ i = α := by
    first
    | exact hβ.eq_pow_of_pow_eq_one hα.pow_eq_one
    | exact hβ.eq_pow_of_pow_eq_one hα.pow_eq_one hp.out.pos
  have hvb : v β = 1 := by
    have h : v β ^ p = 1 := by rw [← map_pow, hβ.pow_eq_one, map_one]
    exact (pow_eq_one_iff_of_nonneg (by positivity) hp.out.ne_zero).mp h
  rw [← hi, ← geom_sum_mul, map_mul]
  have hs : v (∑ k ∈ Finset.range i, β ^ k) ≤ 1 :=
    v.map_sum_le fun k _ => by rw [map_pow, hvb, one_pow]
  calc v (∑ k ∈ Finset.range i, β ^ k) * v (β - 1) ≤ 1 * v (β - 1) :=
        mul_le_mul_of_nonneg_right hs (by positivity)
    _ = v (β - 1) := one_mul _

/- English proof (translation)
Establish `hcyc` using `Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz`. Establish `h1` using `Polynomial.eval_one_cyclotomic_prime (R := C) (p := p)`. Rewrite `h1` using `[hcyc, Polynomial.eval_prod]`. Simplify using `only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1`. Rewrite using `[← h1, map_prod]`.

Establish `heq : ∀ μ ∈ primitiveRoots p C, v (1 - μ) = v (z - 1)`. Introduce `μ hμ`. Establish `hμ'` using `(mem_primitiveRoots hp.out.pos).mp hμ`. Rewrite using `[← Valuation.map_neg, neg_sub]`. Conclude with `le_antisymm (val_sub_one_le v hμ' hz) (val_sub_one_le v hz hμ')`.

Rewrite using `[Finset.prod_congr rfl heq, Finset.prod_const, hz.card_primitiveRoots, Nat.totient_prime hp.out]`.
-/
private lemma val_prim_root {C : Type*} [Field C] (v : Valuation C NNReal) {p : ℕ}
    [hp : Fact p.Prime] {z : C} (hz : IsPrimitiveRoot z p) :
    v (z - 1) ^ (p - 1) = v (p : C) := by
  have hcyc := Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz
  have h1 := Polynomial.eval_one_cyclotomic_prime (R := C) (p := p)
  rw [hcyc, Polynomial.eval_prod] at h1
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1
  rw [← h1, map_prod]
  have heq : ∀ μ ∈ primitiveRoots p C, v (1 - μ) = v (z - 1) := by
    intro μ hμ
    have hμ' := (mem_primitiveRoots hp.out.pos).mp hμ
    rw [← Valuation.map_neg, neg_sub]
    exact le_antisymm (val_sub_one_le v hμ' hz) (val_sub_one_le v hz hμ')
  rw [Finset.prod_congr rfl heq, Finset.prod_const, hz.card_primitiveRoots, Nat.totient_prime hp.out]

section Ainf

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

/- English proof (translation)
Establish `h1` using `PreTilt.mk_untilt_eq_coeff_zero (x - 1)`. Establish `h2` using `PreTilt.mk_untilt_eq_coeff_zero x`. Establish `h3 : Ideal.Quotient.mk (span {(p : O)}) ((x - 1).untilt - (x.untilt - 1)) = 0`. Rewrite using `[map_sub, h1, map_sub (Ideal.Quotient.mk _), map_one, h2, map_sub, map_one, sub_self]`. Rewrite `h3` using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']`.

Take `⟨t, ht⟩` from `h3`. Conclude with `⟨t, by linear_combination -ht⟩`.
-/
private lemma untilt_sub_one (x : PreTilt O p) :
    ∃ t : O, (x - 1).untilt = x.untilt - 1 + p * t := by
  have h1 := PreTilt.mk_untilt_eq_coeff_zero (x - 1)
  have h2 := PreTilt.mk_untilt_eq_coeff_zero x
  have h3 : Ideal.Quotient.mk (span {(p : O)}) ((x - 1).untilt - (x.untilt - 1)) = 0 := by
    rw [map_sub, h1, map_sub (Ideal.Quotient.mk _), map_one, h2, map_sub, map_one, sub_self]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h3
  obtain ⟨t, ht⟩ := h3
  exact ⟨t, by linear_combination -ht⟩

/- English proof (translation)
Take `⟨t, ht⟩` from `untilt_sub_one x`. Rewrite using `[ht, map_add, map_sub, map_one]`. Establish `hpt : v (algebraMap O C ((p : O) * t)) ≤ v (p : C)`. Rewrite using `[map_mul, map_natCast, map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `Valuation.map_add_eq_of_lt_left v (lt_of_le_of_lt hpt hlt)`.
-/
private lemma val_untilt_sub_one (hv : v.Integers O) (x : PreTilt O p)
    (hlt : v (p : C) < v (algebraMap O C x.untilt - 1)) :
    v (algebraMap O C (x - 1).untilt) = v (algebraMap O C x.untilt - 1) := by
  obtain ⟨t, ht⟩ := untilt_sub_one x
  rw [ht, map_add, map_sub, map_one]
  have hpt : v (algebraMap O C ((p : O) * t)) ≤ v (p : C) := by
    rw [map_mul, map_natCast, map_mul]
    calc v (p : C) * v (algebraMap O C t) ≤ v (p : C) * 1 := mul_le_mul_of_nonneg_left (hv.map_le_one t) (by positivity)
      _ = v (p : C) := mul_one _
  exact Valuation.map_add_eq_of_lt_left v (lt_of_le_of_lt hpt hlt)

/- English proof (translation)
Establish `h1 : v (p : C) ≤ 1`. Establish `h` using `hv.map_le_one (p : O)`. Rewrite `h` using `[map_natCast]`. Then use the resulting hypothesis. Use `lt_of_le_of_ne h1 fun heq => ?_` and prove the remaining obligations. Establish `hp0 : (p : C) ≠ 0` using `fun h0 => by`.

Rewrite `heq` using `[h0, map_zero]`. Conclude with `zero_ne_one heq`. Establish `hu` using `hv.isUnit_of_one (x := (p : O)) (by rw [map_natCast]; exact isUnit_iff_ne_zero.mpr hp0) (by rw [map_natCast]; exact heq)`. Conclude with `(Fact.out : ¬IsUnit (p : O)) hu`.
-/
private lemma val_p_lt_one (hv : v.Integers O) : v (p : C) < 1 := by
  have h1 : v (p : C) ≤ 1 := by
    have h := hv.map_le_one (p : O)
    rwa [map_natCast] at h
  refine lt_of_le_of_ne h1 fun heq => ?_
  have hp0 : (p : C) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at heq
    exact zero_ne_one heq
  have hu := hv.isUnit_of_one (x := (p : O)) (by rw [map_natCast]; exact isUnit_iff_ne_zero.mpr hp0)
    (by rw [map_natCast]; exact heq)
  exact (Fact.out : ¬IsUnit (p : O)) hu

/- English proof (translation)
Establish `hpl : v (p : C) < 1` using `val_p_lt_one hv`. Use `haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)`. Establish `hpow : ∀ (x : PreTilt O p) (n : ℕ), (x ^ n).untilt = x.untilt ^ n`. Introduce `x n`. Use `first`.

Consider the case `exact PreTilt.untilt_pow x n`. Consider the case `exact map_pow _ x n`. Consider the case `simp [PreTilt.untilt_pow]`. Break down `hp.out.eq_two_or_odd' with h2 | hodd` into its components or cases. Substitute `h2 set e' := (frobeniusEquiv (PreTilt O 2) 2).symm e with he'` using the available equality.

Establish `hep : e' ^ 2 = e` using `by first`. Consider the case `exact frobeniusEquiv_symm_pow_p 2 e`. Consider the case `(have h3 := frobenius_apply_frobeniusEquiv_symm (PreTilt O 2) 2 e`. Rewrite using `[frobenius_def] at h3)` and apply the resulting hypothesis. Consider the case `simp [he']`.

Establish `hsub : (e' - 1) ^ 2 = e - 1` using `by rw [sub_pow_char, one_pow, hep]`. Establish `hm1 : e.untilt = -1` using `hζ.eq_neg_one_of_two_right`. Establish `h2ne : (2 : C) ≠ 0`. Introduce `h0`. Apply `hζ.ne_one (by norm_num)` to reduce the goal to its premises.

Rewrite using `[hm1]`. Establish `h5 : algebraMap O C (2 : O) = 0` using `by rw [map_ofNat]; exact h0`. Establish `h6 : (2 : O) = 0` using `hv.hom_inj (h5.trans (map_zero _).symm)`. Take the linear combination `-h6`. Use `set z := algebraMap O C e'.untilt with hz`.

Establish `hz2 : z ^ 2 = -1` using `by rw [hz, ← map_pow, ← hpow, hep, hm1, map_neg, map_one]`. Establish `hvz : v z = 1`. Establish `h7 : v z ^ 2 = 1` using `by rw [← map_pow, hz2, Valuation.map_neg, map_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).mp h7`. Establish `hzz : (z - 1) ^ 2 = -2 * z` using `by linear_combination hz2`.

Establish `hx2 : v (z - 1) ^ 2 = v (2 : C)`. Rewrite using `[← map_pow, hzz, map_mul, hvz, mul_one, Valuation.map_neg]`. Establish `hx0 : v (z - 1) ≠ 0`. Introduce `h0`. Rewrite `hx2` using `[h0]`.

Conclude with `((Valuation.ne_zero_iff v).mpr h2ne) (by rw [← hx2]; simp)`. Rewrite `hpl` using `[Nat.cast_ofNat]`. Establish `hxl : v (z - 1) < 1`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Establish `h9 : 1 ≤ v (z - 1) ^ 2` using `one_le_pow₀ hc`. Rewrite `h9` using `[hx2]`. Conclude with `absurd hpl (not_lt.mpr h9)`. Establish `hlt : v ((2 : ℕ) : C) < v (algebraMap O C e'.untilt - 1)`. Rewrite using `[Nat.cast_ofNat, ← hx2]`.

Use `first`. Consider the case `exact pow_lt_self_of_lt_one₀ (pos_iff_ne_zero.mpr hx0) hxl one_lt_two`. Consider the case `exact pow_lt_self_of_lt_one (pos_iff_ne_zero.mpr hx0) hxl one_lt_two`. Establish `hval` using `val_untilt_sub_one hv e' hlt`. Rewrite using `[← hsub, hpow, map_pow, map_pow, hval, hx2]`.

Simplify using the standard rewrite rules. Establish `hx` using `val_prim_root v (hζ.map_of_injective hv.hom_inj)`. Establish `hne : algebraMap O C e.untilt - 1 ≠ 0`. Introduce `h0`. Apply `hζ.ne_one hp.out.one_lt` to reduce the goal to its premises.

Apply `hv.hom_inj` to reduce the goal to its premises. Rewrite using `[map_one]`. Conclude with `sub_eq_zero.mp h0`. Establish `hx0 : v (algebraMap O C e.untilt - 1) ≠ 0` using `(Valuation.ne_zero_iff v).mpr hne`. Establish `hxl : v (algebraMap O C e.untilt - 1) < 1`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h9 : 1 ≤ v (algebraMap O C e.untilt - 1) ^ (p - 1)` using `one_le_pow₀ hc`. Rewrite `h9` using `[hx]`. Conclude with `absurd hpl (not_lt.mpr h9)`.

Establish `hp3 : 1 < p - 1`. Establish `h10` using `hp.out.two_le`. Take `⟨k, hk⟩` from `hodd`. Use linear arithmetic over natural numbers and integers. Establish `hlt : v (p : C) < v (algebraMap O C e.untilt - 1)`.

Rewrite using `[← hx]`. Use `first`. Consider the case `exact pow_lt_self_of_lt_one₀ (pos_iff_ne_zero.mpr hx0) hxl hp3`. Consider the case `exact pow_lt_self_of_lt_one (pos_iff_ne_zero.mpr hx0) hxl hp3`. Rewrite using `[val_untilt_sub_one hv e hlt, hx]`.
-/
private lemma val_untilt_e_sub_one (hv : v.Integers O) (e : PreTilt O p)
    (hζ : IsPrimitiveRoot e.untilt p) :
    v (algebraMap O C (e - 1).untilt) ^ (p - 1) = v (p : C) := by
  have hpl : v (p : C) < 1 := val_p_lt_one hv
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have hpow : ∀ (x : PreTilt O p) (n : ℕ), (x ^ n).untilt = x.untilt ^ n := by
    intro x n
    first
    | exact PreTilt.untilt_pow x n
    | exact map_pow _ x n
    | simp [PreTilt.untilt_pow]
  rcases hp.out.eq_two_or_odd' with h2 | hodd
  · subst h2
    set e' := (frobeniusEquiv (PreTilt O 2) 2).symm e with he'
    have hep : e' ^ 2 = e := by
      first
      | exact frobeniusEquiv_symm_pow_p 2 e
      | (have h3 := frobenius_apply_frobeniusEquiv_symm (PreTilt O 2) 2 e
         rwa [frobenius_def] at h3)
      | simp [he']
    have hsub : (e' - 1) ^ 2 = e - 1 := by rw [sub_pow_char, one_pow, hep]
    have hm1 : e.untilt = -1 := hζ.eq_neg_one_of_two_right
    have h2ne : (2 : C) ≠ 0 := by
      intro h0
      apply hζ.ne_one (by norm_num)
      rw [hm1]
      have h5 : algebraMap O C (2 : O) = 0 := by rw [map_ofNat]; exact h0
      have h6 : (2 : O) = 0 := hv.hom_inj (h5.trans (map_zero _).symm)
      linear_combination -h6
    set z := algebraMap O C e'.untilt with hz
    have hz2 : z ^ 2 = -1 := by rw [hz, ← map_pow, ← hpow, hep, hm1, map_neg, map_one]
    have hvz : v z = 1 := by
      have h7 : v z ^ 2 = 1 := by rw [← map_pow, hz2, Valuation.map_neg, map_one]
      exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).mp h7
    have hzz : (z - 1) ^ 2 = -2 * z := by linear_combination hz2
    have hx2 : v (z - 1) ^ 2 = v (2 : C) := by
      rw [← map_pow, hzz, map_mul, hvz, mul_one, Valuation.map_neg]
    have hx0 : v (z - 1) ≠ 0 := by
      intro h0
      rw [h0] at hx2
      exact ((Valuation.ne_zero_iff v).mpr h2ne) (by rw [← hx2]; simp)
    rw [Nat.cast_ofNat] at hpl
    have hxl : v (z - 1) < 1 := by
      by_contra hc
      push_neg at hc
      have h9 : 1 ≤ v (z - 1) ^ 2 := one_le_pow₀ hc
      rw [hx2] at h9
      exact absurd hpl (not_lt.mpr h9)
    have hlt : v ((2 : ℕ) : C) < v (algebraMap O C e'.untilt - 1) := by
      rw [Nat.cast_ofNat, ← hx2]
      first
      | exact pow_lt_self_of_lt_one₀ (pos_iff_ne_zero.mpr hx0) hxl one_lt_two
      | exact pow_lt_self_of_lt_one (pos_iff_ne_zero.mpr hx0) hxl one_lt_two
    have hval := val_untilt_sub_one hv e' hlt
    rw [← hsub, hpow, map_pow, map_pow, hval, hx2]
    simp
  · have hx := val_prim_root v (hζ.map_of_injective hv.hom_inj)
    have hne : algebraMap O C e.untilt - 1 ≠ 0 := by
      intro h0
      apply hζ.ne_one hp.out.one_lt
      apply hv.hom_inj
      rw [map_one]
      exact sub_eq_zero.mp h0
    have hx0 : v (algebraMap O C e.untilt - 1) ≠ 0 := (Valuation.ne_zero_iff v).mpr hne
    have hxl : v (algebraMap O C e.untilt - 1) < 1 := by
      by_contra hc
      push_neg at hc
      have h9 : 1 ≤ v (algebraMap O C e.untilt - 1) ^ (p - 1) := one_le_pow₀ hc
      rw [hx] at h9
      exact absurd hpl (not_lt.mpr h9)
    have hp3 : 1 < p - 1 := by
      have h10 := hp.out.two_le
      obtain ⟨k, hk⟩ := hodd
      omega
    have hlt : v (p : C) < v (algebraMap O C e.untilt - 1) := by
      rw [← hx]
      first
      | exact pow_lt_self_of_lt_one₀ (pos_iff_ne_zero.mpr hx0) hxl hp3
      | exact pow_lt_self_of_lt_one (pos_iff_ne_zero.mpr hx0) hxl hp3
    rw [val_untilt_sub_one hv e hlt, hx]

end Ainf

/- English proof (translation)
Introduce `ε hv hζ`. Use `haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)`. Use `set e := (frobeniusEquiv (PreTilt O p) p).symm ε with he`. Establish `hep : e ^ p = ε` using `by first`. Consider the case `exact frobeniusEquiv_symm_pow_p p ε`.

Consider the case `(have h3 := frobenius_apply_frobeniusEquiv_symm (PreTilt O p) p ε`. Rewrite using `[frobenius_def] at h3)` and apply the resulting hypothesis. Consider the case `simp [he]`. Establish `hT : ∀ x : PreTilt O p, fontaineTheta O p (teichmuller p x) = x.untilt`. Introduce `x`.

Use `first`. Consider the case `exact fontaineTheta_teichmuller x`. Consider the case `exact fontaineTheta_teichmuller O p x`. Consider the case `simp [fontaineTheta]`. Establish `h1 : teichmuller p ε - 1 = (∑ i ∈ Finset.range p, teichmuller p e ^ i) * (teichmuller p e - 1)`.

Rewrite using `[geom_sum_mul, ← map_pow, hep]`. Establish `h2 : fontaineTheta O p (teichmuller p e - 1) = e.untilt - 1`. Rewrite using `[map_sub, map_one, hT]`. Establish `hne : algebraMap O C (e.untilt - 1) ≠ 0`. Introduce `h0`.

Apply `hζ.ne_one hp.out.one_lt` to reduce the goal to its premises. Establish `h4` using `hv.hom_inj (h0.trans (map_zero _).symm)`. Conclude with `sub_eq_zero.mp h4`. Establish `h3 : v (algebraMap O C (fontaineTheta O p (teichmuller p e - 1))) ^ (p - 1) = v (p : C)`. Rewrite using `[h2, map_sub, map_one]`.

Conclude with `val_prim_root v (hζ.map_of_injective hv.hom_inj)`. Use `⟨h1, h2, h3, fun pflat hpf => ?_⟩` and prove the remaining obligations. Take `⟨hK1, -, -⟩` from `hK pflat hpf`. Establish `hvp : v (p : C) ≠ 0`. Rewrite using `[← h3, h2]`.

Conclude with `pow_ne_zero _ ((Valuation.ne_zero_iff v).mpr hne)`. Establish `hxi : (∑ i ∈ Finset.range p, teichmuller p e ^ i) ∈ RingHom.ker (fontaineTheta O p)`. Rewrite using `[RingHom.mem_ker, map_sum]`. Simplify using `only [map_pow, hT]`. Conclude with `hζ.geom_sum_eq_zero hp.out.one_lt`.

Rewrite `hxi` using `[hK1]`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.mp hxi`. Establish `hmul : ∀ x y : PreTilt O p, (x * y).untilt = x.untilt * y.untilt`. Introduce `x y`. Use `first`.

Consider the case `exact PreTilt.untilt_mul x y`. Consider the case `exact map_mul _ x y`. Consider the case `simp [PreTilt.untilt_mul]`. Establish `hpow : ∀ (x : PreTilt O p) (n : ℕ), (x ^ n).untilt = x.untilt ^ n`. Introduce `x n`.

Use `first`. Consider the case `exact PreTilt.untilt_pow x n`. Consider the case `exact map_pow _ x n`. Consider the case `simp [PreTilt.untilt_pow]`. Establish `hone : (1 : PreTilt O p).untilt = 1`.

Establish `h5` using `hpow (1 : PreTilt O p) 0`. Rewrite `h5` using `[pow_zero, pow_zero]`. Then use the resulting hypothesis. Establish `hct : ∀ x : PreTilt O p, WittVector.constantCoeff (teichmuller p x) = x` using `fun x => WittVector.teichmuller_coeff_zero p x`. Establish `hc` using `congrArg WittVector.constantCoeff ha`. Rewrite `hc` using `[map_mul, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub, hct, map_sum]`.

Simplify using `only [map_pow, hct] at hc`. Establish `hc2 : WittVector.constantCoeff a * ((-1) * pflat) = (e - 1) ^ (p - 1)`. Rewrite using `[sub_one_pow_pred, ← hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hw` using `congrArg (fun x : PreTilt O p => v (algebraMap O C x.untilt)) hc2`.

Simplify using `only [hmul, hpow, map_mul, map_pow] at hw`. Rewrite `hw` using `[val_untilt_e_sub_one hv e hζ, hpf, map_natCast]`. Establish `hm1 : v (algebraMap O C ((-1 : PreTilt O p).untilt)) = 1`. Establish `h5 : ((-1 : PreTilt O p).untilt) ^ 2 = 1`. Rewrite using `[← hpow, neg_one_sq, hone]`.

Establish `h6 : v (algebraMap O C ((-1 : PreTilt O p).untilt)) ^ 2 = 1`. Rewrite using `[← map_pow, ← map_pow, h5, map_one, map_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).mp h6`. Rewrite `hw` using `[hm1, one_mul]`. Establish `hX : v (algebraMap O C (WittVector.constantCoeff a).untilt) = 1`.

Establish `h7 : v (algebraMap O C (WittVector.constantCoeff a).untilt) * v (p : C) = 1 * v (p : C)`. Rewrite using `[one_mul]`. Conclude with `hw`. Conclude with `mul_right_cancel₀ hvp h7`. Establish `hU : IsUnit (WittVector.constantCoeff a).untilt`.

Use `hv.isUnit_of_one (isUnit_iff_ne_zero.mpr fun h0 => ?_) hX` and prove the remaining obligations. Rewrite `hX` using `[h0, map_zero]`. Conclude with `zero_ne_one hX`. Establish `hunit : IsUnit a`. Apply `witt_isUnit` to reduce the goal to its premises.

Apply `perfection_isUnit` to reduce the goal to its premises. Establish `h8` using `PreTilt.mk_untilt_eq_coeff_zero (WittVector.constantCoeff a)`. Establish `h9 : IsUnit (PreTilt.coeff 0 (WittVector.constantCoeff a))`. Rewrite using `[← h8]`. Conclude with `hU.map _`.

Conclude with `h9`. Use `⟨?_, hunit.unit, by rw [IsUnit.unit_spec, ha]⟩` and prove the remaining obligations. Rewrite using `[hK1, ← ha, Ideal.span_singleton_mul_left_unit hunit]`.
-/
theorem xiNu (p : ℕ) [hp : Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (span {(p : O)}) O] (hK : KerThetaStatement p O) :
    XiNuStatement p C v O := by
  intro ε hv hζ
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  set e := (frobeniusEquiv (PreTilt O p) p).symm ε with he
  have hep : e ^ p = ε := by
    first
    | exact frobeniusEquiv_symm_pow_p p ε
    | (have h3 := frobenius_apply_frobeniusEquiv_symm (PreTilt O p) p ε
       rwa [frobenius_def] at h3)
    | simp [he]
  have hT : ∀ x : PreTilt O p, fontaineTheta O p (teichmuller p x) = x.untilt := by
    intro x
    first
    | exact fontaineTheta_teichmuller x
    | exact fontaineTheta_teichmuller O p x
    | simp [fontaineTheta]
  have h1 : teichmuller p ε - 1 =
      (∑ i ∈ Finset.range p, teichmuller p e ^ i) * (teichmuller p e - 1) := by
    rw [geom_sum_mul, ← map_pow, hep]
  have h2 : fontaineTheta O p (teichmuller p e - 1) = e.untilt - 1 := by
    rw [map_sub, map_one, hT]
  have hne : algebraMap O C (e.untilt - 1) ≠ 0 := by
    intro h0
    apply hζ.ne_one hp.out.one_lt
    have h4 := hv.hom_inj (h0.trans (map_zero _).symm)
    exact sub_eq_zero.mp h4
  have h3 : v (algebraMap O C (fontaineTheta O p (teichmuller p e - 1))) ^ (p - 1) = v (p : C) := by
    rw [h2, map_sub, map_one]
    exact val_prim_root v (hζ.map_of_injective hv.hom_inj)
  refine ⟨h1, h2, h3, fun pflat hpf => ?_⟩
  obtain ⟨hK1, -, -⟩ := hK pflat hpf
  have hvp : v (p : C) ≠ 0 := by
    rw [← h3, h2]
    exact pow_ne_zero _ ((Valuation.ne_zero_iff v).mpr hne)
  have hxi : (∑ i ∈ Finset.range p, teichmuller p e ^ i) ∈ RingHom.ker (fontaineTheta O p) := by
    rw [RingHom.mem_ker, map_sum]
    simp only [map_pow, hT]
    exact hζ.geom_sum_eq_zero hp.out.one_lt
  rw [hK1] at hxi
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hxi
  have hmul : ∀ x y : PreTilt O p, (x * y).untilt = x.untilt * y.untilt := by
    intro x y
    first
    | exact PreTilt.untilt_mul x y
    | exact map_mul _ x y
    | simp [PreTilt.untilt_mul]
  have hpow : ∀ (x : PreTilt O p) (n : ℕ), (x ^ n).untilt = x.untilt ^ n := by
    intro x n
    first
    | exact PreTilt.untilt_pow x n
    | exact map_pow _ x n
    | simp [PreTilt.untilt_pow]
  have hone : (1 : PreTilt O p).untilt = 1 := by
    have h5 := hpow (1 : PreTilt O p) 0
    rwa [pow_zero, pow_zero] at h5
  have hct : ∀ x : PreTilt O p, WittVector.constantCoeff (teichmuller p x) = x := fun x =>
    WittVector.teichmuller_coeff_zero p x
  have hc := congrArg WittVector.constantCoeff ha
  rw [map_mul, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub, hct, map_sum] at hc
  simp only [map_pow, hct] at hc
  have hc2 : WittVector.constantCoeff a * ((-1) * pflat) = (e - 1) ^ (p - 1) := by
    rw [sub_one_pow_pred, ← hc]
    ring
  have hw := congrArg (fun x : PreTilt O p => v (algebraMap O C x.untilt)) hc2
  simp only [hmul, hpow, map_mul, map_pow] at hw
  rw [val_untilt_e_sub_one hv e hζ, hpf, map_natCast] at hw
  have hm1 : v (algebraMap O C ((-1 : PreTilt O p).untilt)) = 1 := by
    have h5 : ((-1 : PreTilt O p).untilt) ^ 2 = 1 := by
      rw [← hpow, neg_one_sq, hone]
    have h6 : v (algebraMap O C ((-1 : PreTilt O p).untilt)) ^ 2 = 1 := by
      rw [← map_pow, ← map_pow, h5, map_one, map_one]
    exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).mp h6
  rw [hm1, one_mul] at hw
  have hX : v (algebraMap O C (WittVector.constantCoeff a).untilt) = 1 := by
    have h7 : v (algebraMap O C (WittVector.constantCoeff a).untilt) * v (p : C) = 1 * v (p : C) := by
      rw [one_mul]
      exact hw
    exact mul_right_cancel₀ hvp h7
  have hU : IsUnit (WittVector.constantCoeff a).untilt := by
    refine hv.isUnit_of_one (isUnit_iff_ne_zero.mpr fun h0 => ?_) hX
    rw [h0, map_zero] at hX
    exact zero_ne_one hX
  have hunit : IsUnit a := by
    apply witt_isUnit
    apply perfection_isUnit
    have h8 := PreTilt.mk_untilt_eq_coeff_zero (WittVector.constantCoeff a)
    have h9 : IsUnit (PreTilt.coeff 0 (WittVector.constantCoeff a)) := by
      rw [← h8]
      exact hU.map _
    exact h9
  refine ⟨?_, hunit.unit, by rw [IsUnit.unit_spec, ha]⟩
  rw [hK1, ← ha, Ideal.span_singleton_mul_left_unit hunit]

end ReciprocityTheory.PGsh
