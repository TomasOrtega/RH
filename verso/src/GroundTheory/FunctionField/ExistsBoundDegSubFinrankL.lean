import Mathlib
import GroundTheory.FunctionField.PlaceDefs
import GroundTheory.FunctionField.PlaceBasic
import GroundTheory.FunctionField.Divisor
import GroundTheory.FunctionField.DivisorDegree
import GroundTheory.FunctionField.Repartition
set_option maxSynthPendingDepth 1

namespace GroundTheory.FunctionField

open Module Repartition

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]

namespace Divisor

/- English proof (translation)
Use `finrank_L_le_of_le h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem deg_sub_finrank_L_mono {D E : Divisor k K} (h : D ≤ E) :
    deg D - (finrank k (L D) : ℤ) ≤ deg E - finrank k (L E) := by
  have := finrank_L_le_of_le h
  linarith

/- English proof (translation)
Take `⟨x, hx, hfin⟩` from `IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)`. Use `set F := IntermediateField.adjoin k {x} with hF`. Use `set n := finrank F K with hn`. Set `b` to `Module.finBasis F K`. Use `set B : Divisor k K := poleDivisor x with hBdef`.

Use `set C : Divisor k K := ∑ j, poleDivisor (b j) with hCdef`. Establish `hB : 0 ≤ B` using `poleDivisor_nonneg x`. Establish `hC : 0 ≤ C` using `Finset.sum_nonneg fun j _ => poleDivisor_nonneg _`. Establish `hCj : ∀ j, (poleDivisor (b j) : Divisor k K) ≤ C` using `fun j => Finset.single_le_sum (f := fun j => (poleDivisor (b j) : Divisor k K)) (fun j _ => poleDivisor_nonneg _) (Finset.mem_univ j)`. Establish `key : ∀ l : ℕ, ((l + 1 : ℤ) * n) ≤ finrank k (L (l • B + C))`.

Introduce `l`. Use `set D : Divisor k K := l • B + C with hD'`. Establish `hmem : ∀ p : Fin (l + 1) × Fin n, x ^ (p.1 : ℕ) * b p.2 ∈ L D`. Introduce and unpack `⟨i, j⟩ v`. Rewrite using `[map_mul, map_pow]`.

Establish `hx'` using `valuation_le_exp_poleDivisor x v`. Establish `hb'` using `(valuation_le_exp_poleDivisor (b j) v).trans (WithZero.exp_le_exp.2 (Finsupp.le_def.1 (hCj j) v))`. Establish `hBv : 0 ≤ B v` using `by simpa using Finsupp.le_def.1 hB v`. Establish `hil : ((i : ℕ) : ℤ) ≤ l` using `by exact_mod_cast Nat.lt_succ_iff.1 i.2`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.exp_le_exp]`. Simplify using `only [hD', Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]`. Use `mul_le_mul_of_nonneg_right hil hBv` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Set `G : Fin (l + 1) × Fin n → L D` to `fun p => ⟨x ^ (p.1 : ℕ) * b p.2, hmem p⟩`.

Establish `hli : LinearIndependent k G`. Apply `LinearIndependent.of_comp (L D).subtype` to reduce the goal to its premises. Establish `hb' : LinearIndependent k fun i : Fin (l + 1) => (IntermediateField.AdjoinSimple.gen k x) ^ (i : ℕ)`. Apply `LinearIndependent.of_comp F.val.toLinearMap` to reduce the goal to its premises. Establish `h` using `linearIndependent_pow_of_transcendental hx (l + 1)`.

Establish `heq : (F.val.toLinearMap ∘ fun i : Fin (l + 1) => (IntermediateField.AdjoinSimple.gen k x) ^ (i : ℕ)) = fun i : Fin (l + 1) => x ^ (i : ℕ)`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[heq]`. Conclude with `h`.

Use `linearIndependent_smul hb' b.linearIndependent using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using `[G, Algebra.smul_def]`. Establish `hcard` using `hli.fintype_card_le_finrank`. Simplify using `only [Fintype.card_prod, Fintype.card_fin] at hcard`.

Establish `: ((l + 1 : ℕ) * n : ℕ) ≤ (finrank k (L D) : ℤ)` using `by exact_mod_cast hcard`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdegB : deg B = n` using `deg_poleDivisor hx`. Establish `hn1 : 0 < n` using `Module.finrank_pos`.

Use `⟨deg C - n, fun D => ?_⟩` and prove the remaining obligations. Use `set A₁ : Divisor k K := D ⊔ 0 with hA₁def`. Establish `hA₁ : 0 ≤ A₁` using `le_sup_right`. Establish `h1` using `deg_sub_finrank_L_mono (le_sup_left : D ≤ A₁)`. Use `set l := (deg A₁).toNat with hldef`.

Establish `hl : (l : ℤ) = deg A₁` using `Int.toNat_of_nonneg (deg_nonneg hA₁)`. Use `set El : Divisor k K := l • B + C with hEl`. Establish `hdegEl : deg El = l * n + deg C`. Rewrite using `[hEl, map_add, map_nsmul, hdegB, nsmul_eq_mul]`. Establish `hkey` using `key l`.

Establish `hle : El - A₁ ≤ El` using `sub_le_self _ hA₁`. Establish `h2` using `finrank_L_le_of_le hle`. Rewrite `h2` using `[map_sub]`. Establish `hpos : 0 < finrank k (L (El - A₁))`. Establish `hn1' : (1 : ℤ) ≤ n` using `by exact_mod_cast hn1`.

Establish `: ((l : ℤ) + 1) * 1 ≤ ((l : ℤ) + 1) * n` using `mul_le_mul_of_nonneg_left hn1' (by positivity)`. Establish `: (0 : ℤ) < finrank k (L (El - A₁))` using `by linarith`. Conclude with `this` after adjusting the coercions. Take `⟨z, hz⟩` from `finrank_pos_iff_exists_ne_zero.1 hpos`. Establish `hz0 : (z : K) ≠ 0` using `fun h => hz (Subtype.ext h)`.

Establish `hzL` using `(mem_L_iff_le hz0).1 z.2`. Use `set D₁ : Divisor k K := A₁ + divisor (z : K)⁻¹ with hD₁`. Establish `hD₁El : D₁ ≤ El`. Rewrite using `[hD₁, divisor_inv, ← sub_eq_add_neg, ← sub_nonneg]`. Establish `: El - (A₁ - divisor (z : K)) = divisor (z : K) + (El - A₁)` using `by abel`.

Rewrite using `[this]`. Conclude with `hzL`. Establish `hlD₁ : finrank k (L D₁) = finrank k (L A₁)` using `finrank_L_add_divisor A₁ (inv_ne_zero hz0)`. Establish `hdegD₁ : deg D₁ = deg A₁` using `by rw [hD₁, map_add, deg_divisor, add_zero]`. Establish `h3` using `deg_sub_finrank_L_mono hD₁El`.

Rewrite `h3` using `[hlD₁, hdegD₁]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_bound_deg_sub_finrank_L :
    ∃ γ : ℤ, ∀ D : Divisor k K, deg D - (finrank k (L D) : ℤ) ≤ γ := by
  classical
  obtain ⟨x, hx, hfin⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  set F := IntermediateField.adjoin k {x} with hF
  set n := finrank F K with hn
  let b := Module.finBasis F K
  set B : Divisor k K := poleDivisor x with hBdef
  set C : Divisor k K := ∑ j, poleDivisor (b j) with hCdef
  have hB : 0 ≤ B := poleDivisor_nonneg x
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => poleDivisor_nonneg _
  have hCj : ∀ j, (poleDivisor (b j) : Divisor k K) ≤ C := fun j =>
    Finset.single_le_sum (f := fun j => (poleDivisor (b j) : Divisor k K))
      (fun j _ => poleDivisor_nonneg _) (Finset.mem_univ j)
  have key : ∀ l : ℕ, ((l + 1 : ℤ) * n) ≤ finrank k (L (l • B + C)) := by
    intro l
    set D : Divisor k K := l • B + C with hD'
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
    have : ((l + 1 : ℕ) * n : ℕ) ≤ (finrank k (L D) : ℤ) := by exact_mod_cast hcard
    push_cast at this
    linarith
  have hdegB : deg B = n := deg_poleDivisor hx
  have hn1 : 0 < n := Module.finrank_pos
  refine ⟨deg C - n, fun D => ?_⟩
  set A₁ : Divisor k K := D ⊔ 0 with hA₁def
  have hA₁ : 0 ≤ A₁ := le_sup_right
  have h1 := deg_sub_finrank_L_mono (le_sup_left : D ≤ A₁)
  set l := (deg A₁).toNat with hldef
  have hl : (l : ℤ) = deg A₁ := Int.toNat_of_nonneg (deg_nonneg hA₁)
  set El : Divisor k K := l • B + C with hEl
  have hdegEl : deg El = l * n + deg C := by
    rw [hEl, map_add, map_nsmul, hdegB, nsmul_eq_mul]
  have hkey := key l
  have hle : El - A₁ ≤ El := sub_le_self _ hA₁
  have h2 := finrank_L_le_of_le hle
  rw [map_sub] at h2
  have hpos : 0 < finrank k (L (El - A₁)) := by
    have hn1' : (1 : ℤ) ≤ n := by exact_mod_cast hn1
    have : ((l : ℤ) + 1) * 1 ≤ ((l : ℤ) + 1) * n := mul_le_mul_of_nonneg_left hn1' (by positivity)
    have : (0 : ℤ) < finrank k (L (El - A₁)) := by linarith
    exact_mod_cast this
  obtain ⟨z, hz⟩ := finrank_pos_iff_exists_ne_zero.1 hpos
  have hz0 : (z : K) ≠ 0 := fun h => hz (Subtype.ext h)
  have hzL := (mem_L_iff_le hz0).1 z.2
  set D₁ : Divisor k K := A₁ + divisor (z : K)⁻¹ with hD₁
  have hD₁El : D₁ ≤ El := by
    rw [hD₁, divisor_inv, ← sub_eq_add_neg, ← sub_nonneg]
    have : El - (A₁ - divisor (z : K)) = divisor (z : K) + (El - A₁) := by abel
    rw [this]
    exact hzL
  have hlD₁ : finrank k (L D₁) = finrank k (L A₁) := finrank_L_add_divisor A₁ (inv_ne_zero hz0)
  have hdegD₁ : deg D₁ = deg A₁ := by rw [hD₁, map_add, deg_divisor, add_zero]
  have h3 := deg_sub_finrank_L_mono hD₁El
  rw [hlD₁, hdegD₁] at h3
  linarith

end Divisor

open Divisor

/- English proof (translation)
Take `⟨γ, hγ⟩` from `exists_bound_deg_sub_finrank_L (k := k) (K := K)`. Use `⟨γ + 1, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨D, rfl⟩`. Use `hγ D` as an intermediate fact. Simplify using `only`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bddAbove_range_deg_add_one_sub :
    BddAbove (Set.range fun D : Divisor k K => deg D + 1 - (finrank k (L D) : ℤ)) := by
  obtain ⟨γ, hγ⟩ := exists_bound_deg_sub_finrank_L (k := k) (K := K)
  refine ⟨γ + 1, ?_⟩
  rintro _ ⟨D, rfl⟩
  have := hγ D
  simp only
  linarith

variable (k K) in

noncomputable def genusInt : ℤ :=
  sSup (Set.range fun D : Divisor k K => deg D + 1 - (finrank k (L D) : ℤ))

/- English proof (translation)
The claim follows from `le_csSup bddAbove_range_deg_add_one_sub ⟨D, rfl⟩`.
-/
theorem le_genusInt (D : Divisor k K) : deg D + 1 - (finrank k (L D) : ℤ) ≤ genusInt k K :=
  le_csSup bddAbove_range_deg_add_one_sub ⟨D, rfl⟩

/- English proof (translation)
Take `⟨D, hD⟩` from `Int.csSup_mem (Set.range_nonempty _) (bddAbove_range_deg_add_one_sub (k := k) (K := K))`. Conclude with `⟨D, hD⟩`.
-/
theorem exists_eq_genusInt : ∃ D : Divisor k K, deg D + 1 - (finrank k (L D) : ℤ) = genusInt k K := by
  obtain ⟨D, hD⟩ := Int.csSup_mem (Set.range_nonempty _) (bddAbove_range_deg_add_one_sub (k := k) (K := K))
  exact ⟨D, hD⟩

/- English proof (translation)
The claim follows from `le_antisymm (le_genusInt E) (by have := deg_sub_finrank_L_mono h; linarith)`.
-/
theorem eq_genusInt_of_le {D E : Divisor k K}
    (hD : deg D + 1 - (finrank k (L D) : ℤ) = genusInt k K) (h : D ≤ E) :
    deg E + 1 - (finrank k (L E) : ℤ) = genusInt k K :=
  le_antisymm (le_genusInt E) (by have := deg_sub_finrank_L_mono h; linarith)

/- English proof (translation)
Rewrite using `[finrank_L_zero, hk, IntermediateField.finrank_bot]`.
-/
theorem finrank_L_zero_eq_one (hk : algebraicClosure k K = ⊥) :
    finrank k (L (0 : Divisor k K)) = 1 := by
  rw [finrank_L_zero, hk, IntermediateField.finrank_bot]

/- English proof (translation)
Establish `h` using `le_genusInt (0 : Divisor k K)`. Rewrite `h` using `[finrank_L_zero_eq_one hk, map_zero]`. Simplify using `using h`.
-/
theorem genusInt_nonneg (hk : algebraicClosure k K = ⊥) : 0 ≤ genusInt k K := by
  have h := le_genusInt (0 : Divisor k K)
  rw [finrank_L_zero_eq_one hk, map_zero] at h
  simpa using h

variable (k K) in

noncomputable def genus : ℕ := (genusInt k K).toNat

/- English proof (translation)
The claim follows from `Int.toNat_of_nonneg (genusInt_nonneg hk)`.
-/
theorem genus_eq_genusInt (hk : algebraicClosure k K = ⊥) : (genus k K : ℤ) = genusInt k K :=
  Int.toNat_of_nonneg (genusInt_nonneg hk)

namespace Divisor

/- English proof (translation)
Use `le_genusInt D` as an intermediate fact. Rewrite `this` using `[← genus_eq_genusInt hk]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem riemann_inequality (hk : algebraicClosure k K = ⊥) (D : Divisor k K) :
    deg D + 1 - (genus k K : ℤ) ≤ finrank k (L D) := by
  have := le_genusInt D
  rw [← genus_eq_genusInt hk] at this
  linarith

/- English proof (translation)
Establish `hsupp : (Function.support fun v : Place k K => max (-v.ord (a v)) 0) ⊆ {v | a v ∉ v.ring}`. Introduce `v hv`. Rewrite `hv` using `[Function.mem_support]`. Use `show a v ∉ v.ring`. Introduce `hmem`.

Apply `hv` to reduce the goal to its premises. Distinguish the cases in `h0 : a v = 0`. Simplify using `[h0]`. Use `(v.ord_nonneg_iff h0).2 hmem` as an intermediate fact. Conclude with `max_eq_right (by omega)`.

Use `⟨Finsupp.ofSupportFinite _ (a.finite_not_mem.subset hsupp), fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.ofSupportFinite_coe]`. Distinguish the cases in `h0 : a v = 0`. Rewrite using `[h0, map_zero]`. Conclude with `zero_le`.

Rewrite using `[v.valuation_eq_exp_neg_ord h0, WithZero.exp_le_exp]`. Conclude with `le_max_left _ _`.
-/
theorem exists_mem_A (a : Repartition k K) : ∃ D : Divisor k K, a ∈ A D := by
  classical
  have hsupp : (Function.support fun v : Place k K => max (-v.ord (a v)) 0) ⊆
      {v | a v ∉ v.ring} := by
    intro v hv
    rw [Function.mem_support] at hv
    show a v ∉ v.ring
    intro hmem
    apply hv
    by_cases h0 : a v = 0
    · simp [h0]
    · have := (v.ord_nonneg_iff h0).2 hmem
      exact max_eq_right (by omega)
  refine ⟨Finsupp.ofSupportFinite _ (a.finite_not_mem.subset hsupp), fun v => ?_⟩
  rw [Finsupp.ofSupportFinite_coe]
  by_cases h0 : a v = 0
  · rw [h0, map_zero]; exact zero_le
  · rw [v.valuation_eq_exp_neg_ord h0, WithZero.exp_le_exp]
    exact le_max_left _ _

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `a _`. Take `⟨Da, ha⟩` from `exists_mem_A a`. Establish `hEE₁ : E ≤ E ⊔ Da` using `le_sup_left`. Establish `hE₁` using `eq_genusInt_of_le hE hEE₁`.

Establish `hrank` using `finrank_relSpace hEE₁`. Use `finiteDimensional_relSpace_of_le hEE₁` as an intermediate fact. Establish `h0 : finrank k (relSpace E (E ⊔ Da)) = 0`. Establish `: (finrank k (relSpace E (E ⊔ Da)) : ℤ) = 0` using `by rw [hrank]; linarith`. Conclude with `this` after adjusting the coercions.

Establish `hbot : relSpace E (E ⊔ Da) = ⊥` using `Submodule.finrank_eq_zero.1 h0`. Establish `haE₁ : a ∈ A (E ⊔ Da)` using `A_mono le_sup_right ha`. Establish `hmem : (A E ⊔ principal k K).mkQ a ∈ relSpace E (E ⊔ Da)` using `Submodule.mem_map_of_mem (Submodule.mem_sup_left haE₁)`. Rewrite `hmem` using `[hbot, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hmem`.
-/
theorem sup_principal_eq_top {E : Divisor k K}
    (hE : deg E + 1 - (finrank k (L E) : ℤ) = genusInt k K) : A E ⊔ principal k K = ⊤ := by
  rw [eq_top_iff]
  intro a _
  obtain ⟨Da, ha⟩ := exists_mem_A a
  have hEE₁ : E ≤ E ⊔ Da := le_sup_left
  have hE₁ := eq_genusInt_of_le hE hEE₁
  have hrank := finrank_relSpace hEE₁
  have := finiteDimensional_relSpace_of_le hEE₁
  have h0 : finrank k (relSpace E (E ⊔ Da)) = 0 := by
    have : (finrank k (relSpace E (E ⊔ Da)) : ℤ) = 0 := by rw [hrank]; linarith
    exact_mod_cast this
  have hbot : relSpace E (E ⊔ Da) = ⊥ := Submodule.finrank_eq_zero.1 h0
  have haE₁ : a ∈ A (E ⊔ Da) := A_mono le_sup_right ha
  have hmem : (A E ⊔ principal k K).mkQ a ∈ relSpace E (E ⊔ Da) :=
    Submodule.mem_map_of_mem (Submodule.mem_sup_left haE₁)
  rw [hbot, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
  exact hmem

/- English proof (translation)
Rewrite using `[relSpace, sup_principal_eq_top (eq_genusInt_of_le hE le_sup_right), Submodule.map_top, Submodule.range_mkQ]`.
-/
theorem relSpace_sup_eq_top (D : Divisor k K) {E : Divisor k K}
    (hE : deg E + 1 - (finrank k (L E) : ℤ) = genusInt k K) : relSpace D (D ⊔ E) = ⊤ := by
  rw [relSpace, sup_principal_eq_top (eq_genusInt_of_le hE le_sup_right), Submodule.map_top,
    Submodule.range_mkQ]

instance finiteDimensional_quotient (D : Divisor k K) :
    FiniteDimensional k (Repartition k K ⧸ (A D ⊔ principal k K)) := by
  obtain ⟨E, hE⟩ := exists_eq_genusInt (k := k) (K := K)
  have h := relSpace_sup_eq_top D hE
  have := finiteDimensional_relSpace_of_le (le_sup_left : D ≤ D ⊔ E)
  rw [h] at this
  exact Module.Finite.equiv Submodule.topEquiv

noncomputable def indexOfSpeciality (D : Divisor k K) : ℕ :=
  finrank k (Repartition k K ⧸ (A D ⊔ principal k K))

/- English proof (translation)
Take `⟨E, hE⟩` from `exists_eq_genusInt (k := k) (K := K)`. Establish `h` using `relSpace_sup_eq_top D hE`. Establish `hr` using `finrank_relSpace (le_sup_left : D ≤ D ⊔ E)`. Rewrite `hr` using `[h, finrank_top]`. Establish `hE'` using `eq_genusInt_of_le hE (le_sup_right : E ≤ D ⊔ E)`.

Unfold `indexOfSpeciality`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem indexOfSpeciality_eq_genusInt (D : Divisor k K) :
    (indexOfSpeciality D : ℤ) = finrank k (L D) - deg D - 1 + genusInt k K := by
  obtain ⟨E, hE⟩ := exists_eq_genusInt (k := k) (K := K)
  have h := relSpace_sup_eq_top D hE
  have hr := finrank_relSpace (le_sup_left : D ≤ D ⊔ E)
  rw [h, finrank_top] at hr
  have hE' := eq_genusInt_of_le hE (le_sup_right : E ≤ D ⊔ E)
  unfold indexOfSpeciality
  linarith

end Divisor

end GroundTheory.FunctionField
