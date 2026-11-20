import Mathlib
import GroundTheory.FunctionField.PlaceDefs
import GroundTheory.FunctionField.PlaceBasic
import GroundTheory.FunctionField.ValuationAevalSubCoeffZeroLe
import GroundTheory.FunctionField.Divisor
set_option maxSynthPendingDepth 1

namespace GroundTheory.FunctionField

open Module Polynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Use `set p : k[X] := ∑ j : Fin N, monomial (j : ℕ) (g j) with hp`. Establish `hpx : aeval x p = 0`. Rewrite using `[hp, map_sum, ← hg]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial, Algebra.smul_def]`. Establish `hp0 : p = 0`. Assume the negation of the conclusion as `h`. Conclude with `hx ⟨p, h, hpx⟩`.

Establish `h` using `congrArg (fun q : k[X] => q.coeff i) hp0`. Simplify using `only [hp, finsetSum_coeff, coeff_monomial, coeff_zero] at h`. Rewrite `h` using `[Finset.sum_eq_single i]`. Simplify using `using h`. Introduce `j _ hj`.

Rewrite using `[if_neg (fun h' => hj (Fin.ext h'))]`. Introduce `h'`. Conclude with `absurd (Finset.mem_univ i) h'`.
-/
theorem linearIndependent_pow_of_transcendental {x : K} (hx : Transcendental k x) (N : ℕ) :
    LinearIndependent k fun i : Fin N => x ^ (i : ℕ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  set p : k[X] := ∑ j : Fin N, monomial (j : ℕ) (g j) with hp
  have hpx : aeval x p = 0 := by
    rw [hp, map_sum, ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [aeval_monomial, Algebra.smul_def]
  have hp0 : p = 0 := by
    by_contra h
    exact hx ⟨p, h, hpx⟩
  have h := congrArg (fun q : k[X] => q.coeff i) hp0
  simp only [hp, finsetSum_coeff, coeff_monomial, coeff_zero] at h
  rw [Finset.sum_eq_single i] at h
  · simpa using h
  · intro j _ hj
    rw [if_neg (fun h' => hj (Fin.ext h'))]
  · intro h'; exact absurd (Finset.mem_univ i) h'

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`. Conclude with `inv_mem (IntermediateField.mem_adjoin_simple_self k x)`. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`. Use `inv_mem (IntermediateField.mem_adjoin_simple_self k x⁻¹)` as an intermediate fact.

Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis.
-/
theorem adjoin_inv_eq {x : K} :
    IntermediateField.adjoin k {x⁻¹} = IntermediateField.adjoin k {x} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self k x)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have := inv_mem (IntermediateField.mem_adjoin_simple_self k x⁻¹)
    rwa [inv_inv] at this

/- English proof (translation)
Introduce `h` and use `hx (by simpa using IsAlgebraic.inv_iff.2 h)`.
-/
theorem transcendental_inv {x : K} (hx : Transcendental k x) : Transcendental k x⁻¹ :=
  fun h => hx (by simpa using IsAlgebraic.inv_iff.2 h)

variable [IsFunctionField k K]

namespace Divisor

/- English proof (translation)
Distinguish the cases in `hz : z = 0`. Rewrite using `[hz, map_zero]`. Conclude with `zero_le`. Rewrite using `[v.valuation_le_exp_iff hz, poleDivisor_apply]`. Break down `le_total 0 (-v.ord z) with h | h` into its components or cases.

Rewrite using `[max_eq_left h]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[max_eq_right h]`. Use linear arithmetic over natural numbers and integers.
-/
theorem valuation_le_exp_poleDivisor (z : K) (v : Place k K) :
    v.valuation z ≤ WithZero.exp ((poleDivisor z : Divisor k K) v) := by
  by_cases hz : z = 0
  · rw [hz, map_zero]; exact zero_le
  rw [v.valuation_le_exp_iff hz, poleDivisor_apply]
  rcases le_total 0 (-v.ord z) with h | h
  · rw [max_eq_left h]; omega
  · rw [max_eq_right h]; omega

/- English proof (translation)
Use `set S := (zeroDivisor x : Divisor k K).support with hS'`. Establish `hS : ∀ v ∈ S, 0 < v.ord x` using `fun v hv => by`. Establish `h` using `Finsupp.mem_support_iff.1 hv`. Rewrite `h` using `[zeroDivisor_apply]`. Break down `le_or_gt (v.ord x) 0 with h' | h'` into its components or cases.

Rewrite `h` using `[max_eq_right h']`. Conclude with `absurd rfl h`. Conclude with `h'`. Establish `h` using `Place.sum_ord_mul_deg_le hx S hS`. Rewrite using `[deg_eq_sum]`.

Combine the equalities or inequalities in the displayed calculation. Use `push_cast`. Use `Finset.sum_congr rfl fun v hv => ?_` and prove the remaining obligations. Rewrite using `[zeroDivisor_apply, max_eq_left (hS v hv).le, Int.toNat_of_nonneg (hS v hv).le]`. Use `_ ≤ _ := by exact_mod_cast h`.
-/
theorem deg_zeroDivisor_le {x : K} (hx : Transcendental k x) :
    deg (zeroDivisor x : Divisor k K) ≤ finrank (IntermediateField.adjoin k {x}) K := by
  classical
  set S := (zeroDivisor x : Divisor k K).support with hS'
  have hS : ∀ v ∈ S, 0 < v.ord x := fun v hv => by
    have h := Finsupp.mem_support_iff.1 hv
    rw [zeroDivisor_apply] at h
    rcases le_or_gt (v.ord x) 0 with h' | h'
    · rw [max_eq_right h'] at h; exact absurd rfl h
    · exact h'
  have h := Place.sum_ord_mul_deg_le hx S hS
  rw [deg_eq_sum]
  calc ∑ v ∈ S, (zeroDivisor x : Divisor k K) v * (v.deg : ℤ)
      = ((∑ v ∈ S, (v.ord x).toNat * v.deg : ℕ) : ℤ) := by
        push_cast
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [zeroDivisor_apply, max_eq_left (hS v hv).le, Int.toNat_of_nonneg (hS v hv).le]
    _ ≤ _ := by exact_mod_cast h

/- English proof (translation)
Use `finiteDimensional_adjoin hx` as an intermediate fact. Use `set F := IntermediateField.adjoin k {x} with hF`. Use `set n := finrank F K with hn`. Set `b` to `Module.finBasis F K`. Use `set B : Divisor k K := poleDivisor x with hBdef`.

Use `set C : Divisor k K := ∑ j, poleDivisor (b j) with hCdef`. Use `set a : ℤ := (finrank k (algebraicClosure k K) : ℤ) with ha`. Establish `hB : 0 ≤ B` using `poleDivisor_nonneg x`. Establish `hC : 0 ≤ C` using `Finset.sum_nonneg fun j _ => poleDivisor_nonneg _`. Establish `hCj : ∀ j, (poleDivisor (b j) : Divisor k K) ≤ C` using `fun j => Finset.single_le_sum (f := fun j => (poleDivisor (b j) : Divisor k K)) (fun j _ => poleDivisor_nonneg _) (Finset.mem_univ j)`.

Establish `key : ∀ l : ℕ, ((l + 1 : ℤ) * n) ≤ l * deg B + deg C + a`. Introduce `l`. Use `set D : Divisor k K := l • B + C with hD'`. Establish `hD : 0 ≤ D` using `add_nonneg (nsmul_nonneg hB l) hC`. Establish `hmem : ∀ p : Fin (l + 1) × Fin n, x ^ (p.1 : ℕ) * b p.2 ∈ L D`.

Introduce and unpack `⟨i, j⟩ v`. Rewrite using `[map_mul, map_pow]`. Establish `hx'` using `valuation_le_exp_poleDivisor x v`. Establish `hb'` using `(valuation_le_exp_poleDivisor (b j) v).trans (WithZero.exp_le_exp.2 (Finsupp.le_def.1 (hCj j) v))`. Establish `hBv : 0 ≤ B v` using `by simpa using Finsupp.le_def.1 hB v`.

Establish `hil : ((i : ℕ) : ℤ) ≤ l` using `by exact_mod_cast Nat.lt_succ_iff.1 i.2`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.exp_le_exp]`. Simplify using `only [hD', Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]`. Use `mul_le_mul_of_nonneg_right hil hBv` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Set `G : Fin (l + 1) × Fin n → L D` to `fun p => ⟨x ^ (p.1 : ℕ) * b p.2, hmem p⟩`. Establish `hli : LinearIndependent k G`. Apply `LinearIndependent.of_comp (L D).subtype` to reduce the goal to its premises. Establish `hb' : LinearIndependent k fun i : Fin (l + 1) => (IntermediateField.AdjoinSimple.gen k x) ^ (i : ℕ)`.

Apply `LinearIndependent.of_comp F.val.toLinearMap` to reduce the goal to its premises. Establish `h` using `linearIndependent_pow_of_transcendental hx (l + 1)`. Establish `heq : (F.val.toLinearMap ∘ fun i : Fin (l + 1) => (IntermediateField.AdjoinSimple.gen k x) ^ (i : ℕ)) = fun i : Fin (l + 1) => x ^ (i : ℕ)`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Rewrite using `[heq]`. Conclude with `h`. Use `linearIndependent_smul hb' b.linearIndependent using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using `[G, Algebra.smul_def]`.

Establish `hcard` using `hli.fintype_card_le_finrank`. Simplify using `only [Fintype.card_prod, Fintype.card_fin] at hcard`. Establish `hLD` using `finrank_L_le_deg_add hD`. Establish `hdeg : deg D = l * deg B + deg C`. Rewrite using `[hD', map_add, map_nsmul, nsmul_eq_mul]`.

Establish `: ((l + 1 : ℕ) * n : ℕ) ≤ (finrank k (L D) : ℤ)` using `by exact_mod_cast hcard`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`.

Establish `hC0` using `deg_nonneg hC`. Establish `hB0` using `deg_nonneg hB`. Establish `ha0 : 0 ≤ a` using `Int.natCast_nonneg _`. Establish `h` using `key (deg C + a).toNat`. Rewrite `h` using `[Int.toNat_of_nonneg (by omega)]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem finrank_le_deg_poleDivisor {x : K} (hx : Transcendental k x) :
    (finrank (IntermediateField.adjoin k {x}) K : ℤ) ≤ deg (poleDivisor x : Divisor k K) := by
  classical
  have := finiteDimensional_adjoin hx
  set F := IntermediateField.adjoin k {x} with hF
  set n := finrank F K with hn
  let b := Module.finBasis F K
  set B : Divisor k K := poleDivisor x with hBdef
  set C : Divisor k K := ∑ j, poleDivisor (b j) with hCdef
  set a : ℤ := (finrank k (algebraicClosure k K) : ℤ) with ha
  have hB : 0 ≤ B := poleDivisor_nonneg x
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => poleDivisor_nonneg _
  have hCj : ∀ j, (poleDivisor (b j) : Divisor k K) ≤ C := fun j =>
    Finset.single_le_sum (f := fun j => (poleDivisor (b j) : Divisor k K))
      (fun j _ => poleDivisor_nonneg _) (Finset.mem_univ j)
  have key : ∀ l : ℕ, ((l + 1 : ℤ) * n) ≤ l * deg B + deg C + a := by
    intro l
    set D : Divisor k K := l • B + C with hD'
    have hD : 0 ≤ D := add_nonneg (nsmul_nonneg hB l) hC
    have hmem : ∀ p : Fin (l + 1) × Fin n, x ^ (p.1 : ℕ) * b p.2 ∈ L D := by
      rintro ⟨i, j⟩ v
      rw [map_mul, map_pow]
      have hx' := valuation_le_exp_poleDivisor x v
      have hb' := (valuation_le_exp_poleDivisor (b j) v).trans
        (WithZero.exp_le_exp.2 (Finsupp.le_def.1 (hCj j) v))
      have hBv : 0 ≤ B v := by simpa using Finsupp.le_def.1 hB v
      have hil : ((i : ℕ) : ℤ) ≤ l := by exact_mod_cast Nat.lt_succ_iff.1 i.2
      calc v.valuation x ^ (i : ℕ) * v.valuation (b j)
          ≤ WithZero.exp (B v) ^ (i : ℕ) * WithZero.exp (C v) :=
            mul_le_mul' (pow_le_pow_left' hx' _) hb'
        _ ≤ WithZero.exp (D v) := by
            rw [← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.exp_le_exp]
            simp only [hD', Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]
            have := mul_le_mul_of_nonneg_right hil hBv
            linarith
    let G : Fin (l + 1) × Fin n → L D := fun p => ⟨x ^ (p.1 : ℕ) * b p.2, hmem p⟩
    have hli : LinearIndependent k G := by
      apply LinearIndependent.of_comp (L D).subtype
      have hb' : LinearIndependent k fun i : Fin (l + 1) =>
          (IntermediateField.AdjoinSimple.gen k x) ^ (i : ℕ) := by
        apply LinearIndependent.of_comp F.val.toLinearMap
        have h := linearIndependent_pow_of_transcendental hx (l + 1)
        have heq : (F.val.toLinearMap ∘ fun i : Fin (l + 1) =>
            (IntermediateField.AdjoinSimple.gen k x) ^ (i : ℕ)) =
            fun i : Fin (l + 1) => x ^ (i : ℕ) := by
          funext i
          simp
        rw [heq]
        exact h
      convert linearIndependent_smul hb' b.linearIndependent using 1
      funext p
      simp [G, Algebra.smul_def]
    have hcard := hli.fintype_card_le_finrank
    simp only [Fintype.card_prod, Fintype.card_fin] at hcard
    have hLD := finrank_L_le_deg_add hD
    have hdeg : deg D = l * deg B + deg C := by
      rw [hD', map_add, map_nsmul, nsmul_eq_mul]
    have : ((l + 1 : ℕ) * n : ℕ) ≤ (finrank k (L D) : ℤ) := by exact_mod_cast hcard
    push_cast at this
    linarith
  by_contra hlt
  push Not at hlt
  have hC0 := deg_nonneg hC
  have hB0 := deg_nonneg hB
  have ha0 : 0 ≤ a := Int.natCast_nonneg _
  have h := key (deg C + a).toNat
  rw [Int.toNat_of_nonneg (by omega)] at h
  nlinarith

/- English proof (translation)
Use `le_antisymm ?_ (finrank_le_deg_poleDivisor hx)` and prove the remaining obligations. Establish `h` using `deg_zeroDivisor_le (transcendental_inv hx)`. Rewrite `h` using `[zeroDivisor_inv, adjoin_inv_eq]`. Conclude with `h`.
-/
theorem deg_poleDivisor {x : K} (hx : Transcendental k x) :
    deg (poleDivisor x : Divisor k K) = finrank (IntermediateField.adjoin k {x}) K := by
  refine le_antisymm ?_ (finrank_le_deg_poleDivisor hx)
  have h := deg_zeroDivisor_le (transcendental_inv hx)
  rw [zeroDivisor_inv, adjoin_inv_eq] at h
  exact h

/- English proof (translation)
Establish `h` using `deg_poleDivisor (transcendental_inv hx)`. Rewrite `h` using `[poleDivisor_inv, adjoin_inv_eq]`. Conclude with `h`.
-/
theorem deg_zeroDivisor {x : K} (hx : Transcendental k x) :
    deg (zeroDivisor x : Divisor k K) = finrank (IntermediateField.adjoin k {x}) K := by
  have h := deg_poleDivisor (transcendental_inv hx)
  rw [poleDivisor_inv, adjoin_inv_eq] at h
  exact h

/- English proof (translation)
Distinguish the cases in `hx0 : x = 0`. Simplify using `[hx0]`. Distinguish the cases in `halg : IsAlgebraic k x`. Rewrite using `[divisor_eq_zero_of_isAlgebraic halg hx0, map_zero]`. Rewrite using `[← zeroDivisor_sub_poleDivisor, map_sub, deg_zeroDivisor halg, deg_poleDivisor halg, sub_self]`.
-/
theorem deg_divisor (x : K) : deg (divisor x : Divisor k K) = 0 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases halg : IsAlgebraic k x
  · rw [divisor_eq_zero_of_isAlgebraic halg hx0, map_zero]
  rw [← zeroDivisor_sub_poleDivisor, map_sub, deg_zeroDivisor halg, deg_poleDivisor halg,
    sub_self]

/- English proof (translation)
Rewrite using `[eq_bot_iff]`. Introduce `z hz`. Rewrite using `[Submodule.mem_bot]`. Assume the negation of the conclusion as `hz0`. Establish `h` using `deg_nonneg ((mem_L_iff_le hz0).1 hz)`.

Rewrite `h` using `[map_add, deg_divisor, zero_add]`. Use linear arithmetic over natural numbers and integers.
-/
theorem L_eq_bot_of_deg_neg {D : Divisor k K} (hD : deg D < 0) : L D = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Submodule.mem_bot]
  by_contra hz0
  have h := deg_nonneg ((mem_L_iff_le hz0).1 hz)
  rw [map_add, deg_divisor, zero_add] at h
  omega

/- English proof (translation)
Introduce `v`. Rewrite using `[map_mul, v.valuation_eq_exp_neg_ord hy]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← WithZero.exp_add]`. Use `congr 1`.

Simplify using `only [Finsupp.coe_add, Pi.add_apply, divisor_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_mem_L {y : K} (hy : y ≠ 0) {E : Divisor k K} {z : K} (hz : z ∈ L (E + divisor y)) :
    y * z ∈ L E := by
  intro v
  rw [map_mul, v.valuation_eq_exp_neg_ord hy]
  calc WithZero.exp (-v.ord y) * v.valuation z
      ≤ WithZero.exp (-v.ord y) * WithZero.exp ((E + divisor y : Divisor k K) v) :=
        mul_le_mul' le_rfl (hz v)
    _ = WithZero.exp (E v) := by
      rw [← WithZero.exp_add]
      congr 1
      simp only [Finsupp.coe_add, Pi.add_apply, divisor_apply]
      ring

/- English proof (translation)
Establish `hD : (D + divisor x) + divisor x⁻¹ = D` using `by rw [divisor_inv]; abel`. Apply `le_antisymm` to reduce the goal to its premises. Use `LinearMap.finrank_le_finrank_of_injective (f := (LinearMap.mulLeft k x).restrict fun z hz => mul_mem_L hx hz) ?_` and prove the remaining obligations. Introduce `a b h`. Conclude with `Subtype.ext (mul_left_cancel₀ hx (congrArg Subtype.val h))`.

Use `LinearMap.finrank_le_finrank_of_injective (f := (LinearMap.mulLeft k x⁻¹).restrict fun z hz => mul_mem_L (inv_ne_zero hx) (hD.symm ▸ hz)) ?_` and prove the remaining obligations. Introduce `a b h`. Conclude with `Subtype.ext (mul_left_cancel₀ (inv_ne_zero hx) (congrArg Subtype.val h))`.
-/
theorem finrank_L_add_divisor (D : Divisor k K) {x : K} (hx : x ≠ 0) :
    finrank k (L (D + divisor x)) = finrank k (L D) := by
  have hD : (D + divisor x) + divisor x⁻¹ = D := by rw [divisor_inv]; abel
  apply le_antisymm
  · refine LinearMap.finrank_le_finrank_of_injective
      (f := (LinearMap.mulLeft k x).restrict fun z hz => mul_mem_L hx hz) ?_
    intro a b h
    exact Subtype.ext (mul_left_cancel₀ hx (congrArg Subtype.val h))
  · refine LinearMap.finrank_le_finrank_of_injective
      (f := (LinearMap.mulLeft k x⁻¹).restrict fun z hz =>
        mul_mem_L (inv_ne_zero hx) (hD.symm ▸ hz)) ?_
    intro a b h
    exact Subtype.ext (mul_left_cancel₀ (inv_ne_zero hx) (congrArg Subtype.val h))

end Divisor

variable (k K) in

noncomputable abbrev Pic := Divisor k K ⧸ principalDivisors k K

namespace Pic

noncomputable def deg : Pic k K →+ ℤ :=
  QuotientAddGroup.lift (principalDivisors k K) Divisor.deg (by
    intro D hD
    obtain ⟨x, -, rfl⟩ := mem_principalDivisors.1 hD
    simpa [AddMonoidHom.mem_ker] using Divisor.deg_divisor x)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem deg_mk (D : Divisor k K) :
    deg (QuotientAddGroup.mk D : Pic k K) = Divisor.deg D := rfl

/- English proof (translation)
Rewrite `h` using `[QuotientAddGroup.eq]`. Take `⟨x, hx, hxD⟩` from `mem_principalDivisors.1 h`. Establish `hE : E = D + divisor x` using `by rw [hxD]; abel`. Rewrite using `[hE, Divisor.finrank_L_add_divisor D hx]`.
-/
theorem finrank_L_eq_of_mk_eq {D E : Divisor k K}
    (h : (QuotientAddGroup.mk D : Pic k K) = QuotientAddGroup.mk E) :
    finrank k (Divisor.L E) = finrank k (Divisor.L D) := by
  rw [QuotientAddGroup.eq] at h
  obtain ⟨x, hx, hxD⟩ := mem_principalDivisors.1 h
  have hE : E = D + divisor x := by rw [hxD]; abel
  rw [hE, Divisor.finrank_L_add_divisor D hx]

end Pic

variable (k K) in

noncomputable abbrev Pic0 : AddSubgroup (Pic k K) := (Pic.deg (k := k) (K := K)).ker

end GroundTheory.FunctionField
