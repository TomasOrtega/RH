import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win
open Polynomial

/- English proof (translation)
Use `haveI : Fact l.Prime := ⟨hl⟩`. Establish `h1 : ¬ b ^ (l ^ (m + 1)) = 1`. Introduce `e`. Establish `: (b ^ l) ^ (l ^ m) = 1` using `by rw [← pow_mul, ← pow_succ']; exact e`. Conclude with `h.pow_ne_one_of_pos_of_lt (pow_ne_zero _ hl.ne_zero) (Nat.pow_lt_pow_right hl.one_lt (Nat.lt_succ_self m)) this`.

Establish `h2 : b ^ (l ^ (m + 1 + 1)) = 1`. Rewrite using `[pow_succ' l (m + 1), pow_mul]`. Conclude with `h.pow_eq_one`. Establish `h3` using `orderOf_eq_prime_pow h1 h2`. Use `IsPrimitiveRoot.orderOf b` as an intermediate fact.

Rewrite `this` using `[h3]`. Then use the resulting hypothesis.
-/
private theorem winlx_up {K : Type} [Field K] {l m : ℕ} (hl : l.Prime) {b : K}
    (h : IsPrimitiveRoot (b ^ l) (l ^ (m + 1))) : IsPrimitiveRoot b (l ^ (m + 2)) := by
  haveI : Fact l.Prime := ⟨hl⟩
  have h1 : ¬ b ^ (l ^ (m + 1)) = 1 := by
    intro e
    have : (b ^ l) ^ (l ^ m) = 1 := by rw [← pow_mul, ← pow_succ']; exact e
    exact h.pow_ne_one_of_pos_of_lt (pow_ne_zero _ hl.ne_zero)
      (Nat.pow_lt_pow_right hl.one_lt (Nat.lt_succ_self m)) this
  have h2 : b ^ (l ^ (m + 1 + 1)) = 1 := by
    rw [pow_succ' l (m + 1), pow_mul]; exact h.pow_eq_one
  have h3 := orderOf_eq_prime_pow h1 h2
  have := IsPrimitiveRoot.orderOf b
  rwa [h3] at this

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `key : ∀ n, ∃ z : K, IsPrimitiveRoot z (l ^ (k + n + 1))`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => exact h`. Consider the case `succ n ih => exact hc (k + n) (by omega) ih`. Take `⟨z, hz⟩` from `key (Module.finrank ℚ K)`. Establish `hpos : 0 < Nat.lcm (l ^ (k + Module.finrank ℚ K + 1)) (l ^ (k + Module.finrank ℚ K + 1))`. Rewrite using `[Nat.lcm_self]`.

Conclude with `pow_pos hl.pos _`. Establish `h1` using `IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) hz hz (Polynomial.cyclotomic.irreducible_rat hpos)`. Rewrite `h1` using `[Nat.lcm_self, Nat.totient_prime_pow_succ hl]`. Establish `h2 : k + Module.finrank ℚ K < l ^ (k + Module.finrank ℚ K)` using `Nat.lt_pow_self hl.one_lt`. Establish `h3 : 1 ≤ l - 1` using `by have := hl.two_le; omega`.

Establish `h4` using `Nat.mul_le_mul_left (l ^ (k + Module.finrank ℚ K)) h3`. Use linear arithmetic over natural numbers and integers.
-/
private theorem winlx_max (K : Type) [Field K] [NumberField K] {l k : ℕ} (hl : l.Prime)
    (h : ∃ z : K, IsPrimitiveRoot z (l ^ (k + 1))) :
    ∃ m, k ≤ m ∧ (∃ z : K, IsPrimitiveRoot z (l ^ (m + 1))) ∧
      ¬ ∃ z : K, IsPrimitiveRoot z (l ^ (m + 2)) := by
  by_contra hc
  push Not at hc
  have key : ∀ n, ∃ z : K, IsPrimitiveRoot z (l ^ (k + n + 1)) := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih => exact hc (k + n) (by omega) ih
  obtain ⟨z, hz⟩ := key (Module.finrank ℚ K)
  have hpos : 0 < Nat.lcm (l ^ (k + Module.finrank ℚ K + 1)) (l ^ (k + Module.finrank ℚ K + 1)) := by
    rw [Nat.lcm_self]; exact pow_pos hl.pos _
  have h1 := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) hz hz (Polynomial.cyclotomic.irreducible_rat hpos)
  rw [Nat.lcm_self, Nat.totient_prime_pow_succ hl] at h1
  have h2 : k + Module.finrank ℚ K < l ^ (k + Module.finrank ℚ K) := Nat.lt_pow_self hl.one_lt
  have h3 : 1 ≤ l - 1 := by have := hl.two_le; omega
  have h4 := Nat.mul_le_mul_left (l ^ (k + Module.finrank ℚ K)) h3
  omega

/- English proof (translation)
Establish `hirr : Irreducible (X ^ l - C z : K[X])` using `X_pow_sub_C_irreducible_of_prime hl (fun b hb => hn ⟨b, winlx_up hl (hb ▸ hz)⟩)`. Use `haveI : Fact (Irreducible (X ^ l - C z : K[X])) := ⟨hirr⟩`. Set `pb` to `AdjoinRoot.powerBasis hirr.ne_zero`. Use `haveI : Module.Finite K (AdjoinRoot (X ^ l - C z : K[X])) := pb.finite`. Use `haveI : NeZero (l ^ (m + 2)) := ⟨pow_ne_zero _ hl.ne_zero⟩`.

Establish `hr : IsPrimitiveRoot (AdjoinRoot.root (X ^ l - C z : K[X])) (l ^ (m + 2))`. Apply `winlx_up hl` to reduce the goal to its premises. Rewrite using `[root_X_pow_sub_C_pow]`. Conclude with `hz.map_of_injective (AdjoinRoot.of (X ^ l - C z : K[X])).injective`. Use `⟨AdjoinRoot (X ^ l - C z : K[X]), inferInstance, NumberField.of_module_finite K _, inferInstance, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[IsCyclotomicExtension.iff_singleton]`. Use `⟨⟨_, hr⟩, fun x => ?_⟩` and prove the remaining obligations. Establish `: x ∈ Algebra.adjoin K {AdjoinRoot.root (X ^ l - C z : K[X])}`. Rewrite using `[AdjoinRoot.adjoinRoot_eq_top]`. Discharge the goal by the elementary cases of `trivial`.

Use `Algebra.adjoin_mono ?_ this` and prove the remaining obligations. Introduce and unpack `_ rfl`. Conclude with `hr.pow_eq_one`. Rewrite using `[pb.finrank, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]`.
-/
private theorem winlx_step (K : Type) [Field K] [NumberField K] {l m : ℕ} (hl : l.Prime)
    {z : K} (hz : IsPrimitiveRoot z (l ^ (m + 1))) (hn : ¬ ∃ z : K, IsPrimitiveRoot z (l ^ (m + 2))) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K'),
      IsCyclotomicExtension {l ^ (m + 2)} K K' ∧ Module.finrank K K' = l := by
  have hirr : Irreducible (X ^ l - C z : K[X]) :=
    X_pow_sub_C_irreducible_of_prime hl (fun b hb => hn ⟨b, winlx_up hl (hb ▸ hz)⟩)
  haveI : Fact (Irreducible (X ^ l - C z : K[X])) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  haveI : Module.Finite K (AdjoinRoot (X ^ l - C z : K[X])) := pb.finite
  haveI : NeZero (l ^ (m + 2)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hr : IsPrimitiveRoot (AdjoinRoot.root (X ^ l - C z : K[X])) (l ^ (m + 2)) := by
    apply winlx_up hl
    rw [root_X_pow_sub_C_pow]
    exact hz.map_of_injective (AdjoinRoot.of (X ^ l - C z : K[X])).injective
  refine ⟨AdjoinRoot (X ^ l - C z : K[X]), inferInstance, NumberField.of_module_finite K _, inferInstance, ?_, ?_⟩
  · rw [IsCyclotomicExtension.iff_singleton]
    refine ⟨⟨_, hr⟩, fun x => ?_⟩
    have : x ∈ Algebra.adjoin K {AdjoinRoot.root (X ^ l - C z : K[X])} := by
      rw [AdjoinRoot.adjoinRoot_eq_top]; trivial
    refine Algebra.adjoin_mono ?_ this
    rintro _ rfl
    exact hr.pow_eq_one
  · rw [pb.finrank, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]

/- English proof (translation)
Introduce `l j hl L _ _ hq`. Establish `hz : ∃ z : L, IsPrimitiveRoot z l`. Take `⟨ζ, hζ⟩` from `hq`. Distinguish the cases in `h2 : l = 2`. Substitute `h2` using the available equality.

Rewrite `hζ` using `[if_pos rfl]`. Conclude with `⟨ζ ^ 2, hζ.pow (by norm_num) (by norm_num)⟩`. Rewrite `hζ` using `[if_neg h2]`. Conclude with `⟨ζ, hζ⟩`. Establish `key : ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L'), (∃ k : ℕ, IsCyclotomicExtension {l ^ (k + 1)} L L') ∧ Module.finrank L L' = l ^ j`.

Proceed by induction on `j with`. Consider the case `zero`. Use `⟨L, inferInstance, inferInstance, inferInstance, ⟨0, ?_⟩, by simp⟩` and prove the remaining obligations. Use `haveI : NeZero (l ^ (0 + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Rewrite using `[IsCyclotomicExtension.iff_singleton]`.

Conclude with `⟨by simpa using hz, fun x => Subalgebra.algebraMap_mem _ x⟩`. Consider the case `succ j ih`. Take `⟨K, _, _, _, ⟨k, hk⟩, hd⟩` from `ih`. Take `⟨m, hkm, ⟨z, hz⟩, hn⟩` from `winlx_max K (k := k) hl (hk.exists_isPrimitiveRoot (Set.mem_singleton _) (pow_ne_zero _ hl.ne_zero))`. Take `⟨K', _, _, _, hc, hd'⟩` from `winlx_step K hl hz hn`.

Use `letI : Algebra L K' := ((algebraMap K K').comp (algebraMap L K)).toAlgebra`. Use `haveI : IsScalarTower L K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Use `⟨K', inferInstance, inferInstance, inferInstance, ⟨m + 1, ?_⟩, ?_⟩` and prove the remaining obligations. Use `haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Establish `h1` using `IsCyclotomicExtension.trans {l ^ (k + 1)} {l ^ (m + 2)} L K K' (algebraMap K K').injective`.

Rewrite `h1` using `[Set.union_comm]`. Conclude with `(IsCyclotomicExtension.iff_union_of_dvd L K' ⟨l ^ (m + 2), Set.mem_singleton _, pow_ne_zero _ hl.ne_zero, pow_dvd_pow _ (by omega)⟩).2 h1`. Rewrite using `[← Module.finrank_mul_finrank L K K', hd, hd', pow_succ]`. Take `⟨L', _, _, _, ⟨k, hk⟩, hd⟩` from `key`. Conclude with `⟨L', inferInstance, inferInstance, inferInstance, ⟨k + 1, hk⟩, hd⟩`.
-/
theorem UpperTheory.V.Win.layerex :
    ∀ (l j : ℕ), l.Prime → ∀ (L : Type) [Field L] [NumberField L], HasMuQ l L →
      ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L'), IsLayer l j L L' := by
  intro l j hl L _ _ hq
  have hz : ∃ z : L, IsPrimitiveRoot z l := by
    obtain ⟨ζ, hζ⟩ := hq
    by_cases h2 : l = 2
    · subst h2
      rw [if_pos rfl] at hζ
      exact ⟨ζ ^ 2, hζ.pow (by norm_num) (by norm_num)⟩
    · rw [if_neg h2] at hζ
      exact ⟨ζ, hζ⟩
  have key : ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L'),
      (∃ k : ℕ, IsCyclotomicExtension {l ^ (k + 1)} L L') ∧ Module.finrank L L' = l ^ j := by
    induction j with
    | zero =>
      refine ⟨L, inferInstance, inferInstance, inferInstance, ⟨0, ?_⟩, by simp⟩
      haveI : NeZero (l ^ (0 + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
      rw [IsCyclotomicExtension.iff_singleton]
      exact ⟨by simpa using hz, fun x => Subalgebra.algebraMap_mem _ x⟩
    | succ j ih =>
      obtain ⟨K, _, _, _, ⟨k, hk⟩, hd⟩ := ih
      obtain ⟨m, hkm, ⟨z, hz⟩, hn⟩ := winlx_max K (k := k) hl
        (hk.exists_isPrimitiveRoot (Set.mem_singleton _) (pow_ne_zero _ hl.ne_zero))
      obtain ⟨K', _, _, _, hc, hd'⟩ := winlx_step K hl hz hn
      letI : Algebra L K' := ((algebraMap K K').comp (algebraMap L K)).toAlgebra
      haveI : IsScalarTower L K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      refine ⟨K', inferInstance, inferInstance, inferInstance, ⟨m + 1, ?_⟩, ?_⟩
      · haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
        have h1 := IsCyclotomicExtension.trans {l ^ (k + 1)} {l ^ (m + 2)} L K K' (algebraMap K K').injective
        rw [Set.union_comm] at h1
        exact (IsCyclotomicExtension.iff_union_of_dvd L K'
          ⟨l ^ (m + 2), Set.mem_singleton _, pow_ne_zero _ hl.ne_zero, pow_dvd_pow _ (by omega)⟩).2 h1
      · rw [← Module.finrank_mul_finrank L K K', hd, hd', pow_succ]
  obtain ⟨L', _, _, _, ⟨k, hk⟩, hd⟩ := key
  exact ⟨L', inferInstance, inferInstance, inferInstance, ⟨k + 1, hk⟩, hd⟩
