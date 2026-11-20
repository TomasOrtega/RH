import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameKummerInertiaSurjective

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

section

variable {Ω : Type} [Field Ω] (A : ValuationSubring Ω)

/- English proof (translation)
Establish `: A.valuation x ^ n = 1` using `by rw [← map_pow, h, map_one]`. Conclude with `(pow_eq_one_iff_of_nonneg zero_le' hn).1 this`.
-/
private theorem val_root (x : Ω) {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : A.valuation x = 1 := by
  have : A.valuation x ^ n = 1 := by rw [← map_pow, h, map_one]
  exact (pow_eq_one_iff_of_nonneg zero_le' hn).1 this

/- English proof (translation)
Rewrite using `[← mul_neg_geom_sum, map_mul]`. Establish `: A.valuation (∑ i ∈ Finset.range j, ζ ^ i) ≤ 1` using `Valuation.map_sum_le _ (fun i _ => by rw [map_pow]; exact pow_le_one' hζ i)`. Conclude with `mul_le_of_le_one_right' this`.
-/
private theorem val_one_sub_pow_le {ζ : Ω} (hζ : A.valuation ζ ≤ 1) (j : ℕ) :
    A.valuation (1 - ζ ^ j) ≤ A.valuation (1 - ζ) := by
  rw [← mul_neg_geom_sum, map_mul]
  have : A.valuation (∑ i ∈ Finset.range j, ζ ^ i) ≤ 1 :=
    Valuation.map_sum_le _ (fun i _ => by rw [map_pow]; exact pow_le_one' hζ i)
  exact mul_le_of_le_one_right' this

/- English proof (translation)
Use `haveI : NeZero p := ⟨hp.ne_zero⟩`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Establish `hall : ∀ μ ∈ primitiveRoots p Ω, A.valuation (1 - μ) = A.valuation (1 - ζ)`. Introduce `μ hμ`. Rewrite `hμ` using `[mem_primitiveRoots hp.pos]`.

Establish `hμ1 : A.valuation μ ≤ 1` using `(val_root A μ hp.ne_zero hμ.pow_eq_one).le`. Establish `hζ1 : A.valuation ζ ≤ 1` using `(val_root A ζ hp.ne_zero hζ.pow_eq_one).le`. Take `⟨k, _, hk⟩` from `hμ.eq_pow_of_pow_eq_one hζ.pow_eq_one`. Take `⟨l, _, hl⟩` from `hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[← hl]`. Conclude with `val_one_sub_pow_le A hζ1 l`. Rewrite using `[← hk]`. Conclude with `val_one_sub_pow_le A hμ1 k`. Establish `hprod : ((p : ℕ) : Ω) = ∏ μ ∈ primitiveRoots p Ω, (1 - μ)`.

Establish `h` using `congrArg (Polynomial.eval (1 : Ω)) (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ)`. Rewrite `h` using `[Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_prod]`. Simplify using `using h`. Rewrite using `[hprod, map_prod, Finset.prod_congr rfl hall, Finset.prod_const, hζ.card_primitiveRoots, Nat.totient_prime hp]`.
-/
private theorem val_p {p : ℕ} (hp : p.Prime) {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) :
    A.valuation (1 - ζ) ^ (p - 1) = A.valuation ((p : ℕ) : Ω) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hall : ∀ μ ∈ primitiveRoots p Ω, A.valuation (1 - μ) = A.valuation (1 - ζ) := by
    intro μ hμ
    rw [mem_primitiveRoots hp.pos] at hμ
    have hμ1 : A.valuation μ ≤ 1 := (val_root A μ hp.ne_zero hμ.pow_eq_one).le
    have hζ1 : A.valuation ζ ≤ 1 := (val_root A ζ hp.ne_zero hζ.pow_eq_one).le
    obtain ⟨k, _, hk⟩ := hμ.eq_pow_of_pow_eq_one hζ.pow_eq_one
    obtain ⟨l, _, hl⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    apply le_antisymm
    · rw [← hl]
      exact val_one_sub_pow_le A hζ1 l
    · rw [← hk]
      exact val_one_sub_pow_le A hμ1 k
  have hprod : ((p : ℕ) : Ω) = ∏ μ ∈ primitiveRoots p Ω, (1 - μ) := by
    have h := congrArg (Polynomial.eval (1 : Ω)) (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
    rw [Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_prod] at h
    simpa using h
  rw [hprod, map_prod, Finset.prod_congr rfl hall, Finset.prod_const, hζ.card_primitiveRoots,
    Nat.totient_prime hp]

/- English proof (translation)
Rewrite using `[← geom_sum₂_mul, map_mul]`. Establish `: A.valuation (∑ i ∈ Finset.range e, x ^ i * y ^ (e - 1 - i)) ≤ 1` using `Valuation.map_sum_le _ (fun i _ => by`. Rewrite using `[map_mul, map_pow, map_pow]`. Conclude with `mul_le_one' (pow_le_one' hx _) (pow_le_one' hy _))`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' this) h`.
-/
private theorem val_pow_sub_pow_lt {x y : Ω} (hx : A.valuation x ≤ 1) (hy : A.valuation y ≤ 1)
    (h : A.valuation (x - y) < 1) (e : ℕ) : A.valuation (x ^ e - y ^ e) < 1 := by
  rw [← geom_sum₂_mul, map_mul]
  have : A.valuation (∑ i ∈ Finset.range e, x ^ i * y ^ (e - 1 - i)) ≤ 1 :=
    Valuation.map_sum_le _ (fun i _ => by
      rw [map_mul, map_pow, map_pow]; exact mul_le_one' (pow_le_one' hx _) (pow_le_one' hy _))
  exact lt_of_le_of_lt (mul_le_of_le_one_left' this) h

/- English proof (translation)
Establish `hp1 : 1 ≤ p - 1`. Use `hp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hζ1 : A.valuation ζ = 1` using `val_root A ζ hp.ne_zero hζ.pow_eq_one`. Establish `hμ1 : A.valuation μ = 1` using `val_root A μ (by omega) hμ`.

Establish `hμ0 : μ ≠ 0`. Introduce `h0`. Rewrite `hμ1` using `[h0, map_zero]`. Conclude with `zero_ne_one hμ1`. Establish `hY0 : Y ≠ 0`.

Introduce `h0`. Rewrite `hY` using `[h0, zero_pow (by omega)]`. Conclude with `hp0 hY.symm`. Establish `h4` using `val_p A hp hζ`. Establish `hvYpow : A.valuation Y ^ (p - 1) = A.valuation (1 - ζ) ^ (p - 1)`.

Rewrite using `[← map_pow, hY, h4]`. Establish `hvY : A.valuation Y = A.valuation (1 - ζ)` using `pow_left_injective (by omega) hvYpow`. Establish `hvπ : A.valuation (1 - ζ) < 1`. Assume the negation of the conclusion as `hc`. Establish `h5` using `one_le_pow_of_one_le' (not_lt.mp hc) (p - 1)`.

Rewrite `h5` using `[h4]`. Conclude with `absurd hvp (not_lt.mpr h5)`. Establish `hvY0 : A.valuation Y ≠ 0`. Rewrite using `[Ne, Valuation.zero_iff]`. Conclude with `hY0`.

Establish `hw : A.valuation ((1 - ζ) / Y) = 1`. Rewrite using `[map_div₀, ← hvY, div_self hvY0]`. Establish `hgeom : 1 - ζ ^ i = (1 - ζ) * ∑ k ∈ Finset.range i, ζ ^ k` using `(mul_neg_geom_sum ζ i).symm`. Establish `hfw : f ((1 - ζ) / Y) = (1 - ζ) * (∑ k ∈ Finset.range i, ζ ^ k) / (μ * Y)`. Rewrite using `[map_div₀, map_sub, map_one, hfζ, hfY, hgeom]`.

Establish `hdiff : f ((1 - ζ) / Y) - (1 - ζ) / Y = (1 - ζ) / Y * ((∑ k ∈ Finset.range i, ζ ^ k) - μ) * μ⁻¹`. Rewrite using `[hfw]`. Clear the denominators using the available nonvanishing facts. Establish `h1` using `hf ((1 - ζ) / Y) hw.le`. Rewrite `h1` using `[hdiff, map_mul, map_mul, hw, map_inv₀, hμ1, one_mul, inv_one, mul_one]`.

Establish `h2 : A.valuation ((i : Ω) - ∑ k ∈ Finset.range i, ζ ^ k) < 1`. Establish `hsum : (i : Ω) - ∑ k ∈ Finset.range i, ζ ^ k = ∑ k ∈ Finset.range i, (1 - ζ ^ k)`. Rewrite using `[Finset.sum_sub_distrib]`. Simplify using the standard rewrite rules. Rewrite using `[hsum]`.

Conclude with `lt_of_le_of_lt (Valuation.map_sum_le _ (fun k _ => val_one_sub_pow_le A hζ1.le k)) hvπ`. Establish `h3 : (i : Ω) - μ = ((i : Ω) - ∑ k ∈ Finset.range i, ζ ^ k) + ((∑ k ∈ Finset.range i, ζ ^ k) - μ)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3]`. Conclude with `Valuation.map_add_lt _ h2 h1`.
-/
private theorem val_natCast_sub_lt {p i : ℕ} (hp : p.Prime) {ζ μ Y : Ω} (hζ : IsPrimitiveRoot ζ p)
    (hμ : μ ^ (p - 1) = 1) (hY : Y ^ (p - 1) = ((p : ℕ) : Ω)) (hp0 : ((p : ℕ) : Ω) ≠ 0)
    (hvp : A.valuation ((p : ℕ) : Ω) < 1) (f : Ω →+* Ω)
    (hf : ∀ x, A.valuation x ≤ 1 → A.valuation (f x - x) < 1)
    (hfY : f Y = μ * Y) (hfζ : f ζ = ζ ^ i) : A.valuation ((i : Ω) - μ) < 1 := by
  have hp1 : 1 ≤ p - 1 := by
    have := hp.two_le
    omega
  have hζ1 : A.valuation ζ = 1 := val_root A ζ hp.ne_zero hζ.pow_eq_one
  have hμ1 : A.valuation μ = 1 := val_root A μ (by omega) hμ
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hμ1
    exact zero_ne_one hμ1
  have hY0 : Y ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hY
    exact hp0 hY.symm
  have h4 := val_p A hp hζ
  have hvYpow : A.valuation Y ^ (p - 1) = A.valuation (1 - ζ) ^ (p - 1) := by
    rw [← map_pow, hY, h4]
  have hvY : A.valuation Y = A.valuation (1 - ζ) := pow_left_injective (by omega) hvYpow
  have hvπ : A.valuation (1 - ζ) < 1 := by
    by_contra hc
    have h5 := one_le_pow_of_one_le' (not_lt.mp hc) (p - 1)
    rw [h4] at h5
    exact absurd hvp (not_lt.mpr h5)
  have hvY0 : A.valuation Y ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact hY0
  have hw : A.valuation ((1 - ζ) / Y) = 1 := by
    rw [map_div₀, ← hvY, div_self hvY0]
  have hgeom : 1 - ζ ^ i = (1 - ζ) * ∑ k ∈ Finset.range i, ζ ^ k := (mul_neg_geom_sum ζ i).symm
  have hfw : f ((1 - ζ) / Y) = (1 - ζ) * (∑ k ∈ Finset.range i, ζ ^ k) / (μ * Y) := by
    rw [map_div₀, map_sub, map_one, hfζ, hfY, hgeom]
  have hdiff : f ((1 - ζ) / Y) - (1 - ζ) / Y
      = (1 - ζ) / Y * ((∑ k ∈ Finset.range i, ζ ^ k) - μ) * μ⁻¹ := by
    rw [hfw]
    field_simp
  have h1 := hf ((1 - ζ) / Y) hw.le
  rw [hdiff, map_mul, map_mul, hw, map_inv₀, hμ1, one_mul, inv_one, mul_one] at h1
  have h2 : A.valuation ((i : Ω) - ∑ k ∈ Finset.range i, ζ ^ k) < 1 := by
    have hsum : (i : Ω) - ∑ k ∈ Finset.range i, ζ ^ k = ∑ k ∈ Finset.range i, (1 - ζ ^ k) := by
      rw [Finset.sum_sub_distrib]
      simp
    rw [hsum]
    exact lt_of_le_of_lt (Valuation.map_sum_le _ (fun k _ => val_one_sub_pow_le A hζ1.le k)) hvπ
  have h3 : (i : Ω) - μ = ((i : Ω) - ∑ k ∈ Finset.range i, ζ ^ k) + ((∑ k ∈ Finset.range i, ζ ^ k) - μ) := by
    ring
  rw [h3]
  exact Valuation.map_add_lt _ h2 h1

end

/- English proof (translation)
Unfold `InertiaGen`. Introduce `F Ω _ _ _ _ _ A u hA p _ hpu hpu2 ζ hζ`. Establish `hp : p.Prime` using `Fact.out`. Use `haveI : NeZero p := ⟨hp.ne_zero⟩`. Establish `hm : 0 < p - 1`.

Use `hp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Use `haveI : NeZero (((p - 1 : ℕ)) : Ω) := ⟨by exact_mod_cast hm.ne'⟩`.

Take `⟨Y, hY⟩` from `IsAlgClosed.exists_pow_nat_eq ((p : ℕ) : Ω) hm`. Take `⟨μ, hμ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p - 1)`. Establish `hndvd : ¬ p ∣ p - 1` using `fun h => absurd (Nat.le_of_dvd hm h) (by omega)`. Take `⟨σ, hσ, hσY⟩` from `GlobalTheory.TameKummerInertia.tame_kummer_surj F Ω A u hA p hpu hpu2 (p - 1) hm hndvd Y μ hY hμ.pow_eq_one`. Establish `hσζ : IsPrimitiveRoot (σ ζ) p` using `hζ.map_of_injective σ.injective`.

Take `⟨i, hi_lt, hi⟩` from `hζ.eq_pow_of_pow_eq_one hσζ.pow_eq_one`. Establish `hcop : i.Coprime p` using `(hζ.pow_iff_coprime hp.pos i).mp (hi ▸ hσζ)`. Establish `hi0 : i ≠ 0`. Introduce and unpack `rfl`. Conclude with `hp.ne_one ((Nat.coprime_zero_left p).mp hcop)`.

Establish `hvp : A.valuation ((p : ℕ) : Ω) < 1` using `GlobalTheory.TameCoupledEx.val_g_lt A u hA hpu`. Establish `hp0 : ((p : ℕ) : Ω) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hσ'` using `mem_Ine.mp hσ`. Unfold `Inertia at hσ'`. Establish `h6 : A.valuation ((i : Ω) - μ) < 1` using `val_natCast_sub_lt A hp hζ hμ.pow_eq_one hY hp0 hvp σ.toRingEquiv.toRingHom (fun x hx => hσ'.2 x hx) hσY hi.symm`.

Use `⟨σ, hσ, ZMod.unitOfCoprime i hcop, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[orderOf_eq_iff hm]`. Use `⟨ZMod.units_pow_card_sub_one_eq_one p _, fun k hk hk0 hpow => ?_⟩` and prove the remaining obligations. Establish `hzk : ((i ^ k : ℕ) : ZMod p) = 1`. Establish `h` using `congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) hpow`.

Simplify `h` using `[ZMod.coe_unitOfCoprime]`. Establish `hik : 1 ≤ i ^ k` using `Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hi0)`. Establish `hdvd : p ∣ i ^ k - 1`. Rewrite using `[← ZMod.natCast_eq_zero_iff, Nat.cast_sub hik, hzk, Nat.cast_one, sub_self]`. Take `⟨c, hc⟩` from `hdvd`.

Establish `hv1 : A.valuation ((i : Ω) ^ k - 1) < 1`. Establish `hcast : (i : Ω) ^ k - 1 = ((p : ℕ) : Ω) * (c : Ω)`. Establish `h` using `congrArg (Nat.cast : ℕ → Ω) hc`. Move the coercions through the operations in `[Nat.cast_sub hik] at h`. Conclude with `h`.

Rewrite using `[hcast, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (valuation_natCast_le_one A c)) hvp`. Establish `hμv : A.valuation μ ≤ 1` using `(val_root A μ hm.ne' hμ.pow_eq_one).le`. Establish `h5` using `val_pow_sub_pow_lt A (valuation_natCast_le_one A i) hμv h6 k`. Establish `h7 : A.valuation (μ ^ k - 1) < 1`.

Establish `hrw : μ ^ k - 1 = ((i : Ω) ^ k - 1) + -((i : Ω) ^ k - μ ^ k)` using `by ring`. Rewrite using `[hrw]`. Conclude with `Valuation.map_add_lt _ hv1 (by rw [Valuation.map_neg]; exact h5)`. Establish `hvpm : ¬ A.valuation (((p - 1 : ℕ)) : Ω) < 1`. Introduce `hlt`.

Establish `hone : (1 : Ω) = ((p : ℕ) : Ω) + -(((p - 1 : ℕ)) : Ω)`. Rewrite using `[Nat.cast_sub hp.one_le]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h8` using `Valuation.map_add_lt A.valuation hvp (by rw [Valuation.map_neg]; exact hlt)`.

Rewrite `h8` using `[← hone, map_one]`. Conclude with `lt_irrefl _ h8`. Establish `heq` using `eq_of_pow_eq_one A hvpm (by rw [← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow]) (one_pow _) h7`. Conclude with `hμ.pow_ne_one_of_pos_of_lt hk0.ne' hk heq`. Rewrite using `[ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi_lt]`.

Conclude with `hi.symm`.
-/
theorem inertiaGen : InertiaGen := by
  unfold InertiaGen
  intro F Ω _ _ _ _ _ A u hA p _ hpu hpu2 ζ hζ
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hm : 0 < p - 1 := by
    have := hp.two_le
    omega
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (((p - 1 : ℕ)) : Ω) := ⟨by exact_mod_cast hm.ne'⟩
  obtain ⟨Y, hY⟩ := IsAlgClosed.exists_pow_nat_eq ((p : ℕ) : Ω) hm
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p - 1)
  have hndvd : ¬ p ∣ p - 1 := fun h => absurd (Nat.le_of_dvd hm h) (by omega)
  obtain ⟨σ, hσ, hσY⟩ :=
    GlobalTheory.TameKummerInertia.tame_kummer_surj F Ω A u hA p hpu hpu2 (p - 1) hm hndvd Y μ hY hμ.pow_eq_one
  have hσζ : IsPrimitiveRoot (σ ζ) p := hζ.map_of_injective σ.injective
  obtain ⟨i, hi_lt, hi⟩ := hζ.eq_pow_of_pow_eq_one hσζ.pow_eq_one
  have hcop : i.Coprime p := (hζ.pow_iff_coprime hp.pos i).mp (hi ▸ hσζ)
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hp.ne_one ((Nat.coprime_zero_left p).mp hcop)
  have hvp : A.valuation ((p : ℕ) : Ω) < 1 := GlobalTheory.TameCoupledEx.val_g_lt A u hA hpu
  have hp0 : ((p : ℕ) : Ω) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hσ' := mem_Ine.mp hσ
  unfold Inertia at hσ'
  have h6 : A.valuation ((i : Ω) - μ) < 1 :=
    val_natCast_sub_lt A hp hζ hμ.pow_eq_one hY hp0 hvp σ.toRingEquiv.toRingHom
      (fun x hx => hσ'.2 x hx) hσY hi.symm
  refine ⟨σ, hσ, ZMod.unitOfCoprime i hcop, ?_, ?_⟩
  · rw [orderOf_eq_iff hm]
    refine ⟨ZMod.units_pow_card_sub_one_eq_one p _, fun k hk hk0 hpow => ?_⟩
    have hzk : ((i ^ k : ℕ) : ZMod p) = 1 := by
      have h := congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) hpow
      simpa [ZMod.coe_unitOfCoprime] using h
    have hik : 1 ≤ i ^ k := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hi0)
    have hdvd : p ∣ i ^ k - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hik, hzk, Nat.cast_one, sub_self]
    obtain ⟨c, hc⟩ := hdvd
    have hv1 : A.valuation ((i : Ω) ^ k - 1) < 1 := by
      have hcast : (i : Ω) ^ k - 1 = ((p : ℕ) : Ω) * (c : Ω) := by
        have h := congrArg (Nat.cast : ℕ → Ω) hc
        push_cast [Nat.cast_sub hik] at h
        exact h
      rw [hcast, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (valuation_natCast_le_one A c)) hvp
    have hμv : A.valuation μ ≤ 1 := (val_root A μ hm.ne' hμ.pow_eq_one).le
    have h5 := val_pow_sub_pow_lt A (valuation_natCast_le_one A i) hμv h6 k
    have h7 : A.valuation (μ ^ k - 1) < 1 := by
      have hrw : μ ^ k - 1 = ((i : Ω) ^ k - 1) + -((i : Ω) ^ k - μ ^ k) := by ring
      rw [hrw]
      exact Valuation.map_add_lt _ hv1 (by rw [Valuation.map_neg]; exact h5)
    have hvpm : ¬ A.valuation (((p - 1 : ℕ)) : Ω) < 1 := by
      intro hlt
      have hone : (1 : Ω) = ((p : ℕ) : Ω) + -(((p - 1 : ℕ)) : Ω) := by
        rw [Nat.cast_sub hp.one_le]
        push_cast
        ring
      have h8 := Valuation.map_add_lt A.valuation hvp (by rw [Valuation.map_neg]; exact hlt)
      rw [← hone, map_one] at h8
      exact lt_irrefl _ h8
    have heq := eq_of_pow_eq_one A hvpm
      (by rw [← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow]) (one_pow _) h7
    exact hμ.pow_ne_one_of_pos_of_lt hk0.ne' hk heq
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi_lt]
    exact hi.symm

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
