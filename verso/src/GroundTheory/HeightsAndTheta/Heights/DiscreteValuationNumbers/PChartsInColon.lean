import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocFiniteCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

open scoped Pointwise

section

variable {A : Type*} [CommRing A] {L : Type*} [Field L] [Algebra A L]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using Submodule.one_le.mp (le_refl (1 : Submodule A L))`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ']`. Conclude with `Submodule.mul_mem_mul (hx i (Finset.mem_insert_self i s)) (ih fun k hk => hx k (Finset.mem_insert_of_mem hk))`.
-/
theorem ChartsInColon.prod_mem_pow {ι : Type*} (M : Submodule A L) (s : Finset ι) (x : ι → L)
    (hx : ∀ i ∈ s, x i ∈ M) : ∏ i ∈ s, x i ∈ M ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Submodule.one_le.mp (le_refl (1 : Submodule A L))
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ']
    exact Submodule.mul_mem_mul (hx i (Finset.mem_insert_self i s))
      (ih fun k hk => hx k (Finset.mem_insert_of_mem hk))

/- English proof (translation)
Use `set I := Submodule.map (Algebra.linearMap A L) (Ideal.span (Set.range a)) with hI`. Establish `hmem : ∀ k, algebraMap A L (a k) ∈ I` using `fun k => Submodule.mem_map_of_mem (f := Algebra.linearMap A L) (Ideal.subset_span ⟨k, rfl⟩)`. Proceed by induction on `hg using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨k, rfl⟩` from `hx`.

Use `⟨1, ?_⟩` and prove the remaining obligations. Simplify `hmem k` using `only [pow_one, div_mul_cancel₀ _ hj]`. Consider the case `algebraMap r`. Conclude with `⟨0, by rw [pow_zero, pow_zero, mul_one]; exact Submodule.algebraMap_mem r⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨m, hm⟩` from `hx`. Take `⟨n, hn⟩` from `hy`. Use `⟨m + n, ?_⟩` and prove the remaining obligations. Establish `h1` using `Submodule.mul_mem_mul hm (Submodule.pow_mem_pow I (hmem j) n)`. Establish `h2` using `Submodule.mul_mem_mul hn (Submodule.pow_mem_pow I (hmem j) m)`.

Rewrite `h1`, `h2` using `[← pow_add]`. Rewrite `h2` using `[add_comm n m]`. Use `add_mem h1 h2 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul x y _ _ hx hy`.

Take `⟨m, hm⟩` from `hx`. Take `⟨n, hn⟩` from `hy`. Use `⟨m + n, ?_⟩` and prove the remaining obligations. Establish `h` using `Submodule.mul_mem_mul hm hn`. Rewrite `h` using `[← pow_add]`.

Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ChartsInColon.exists_mul_pow_mem {J : Type*} (a : J → A) (j : J) (hj : algebraMap A L (a j) ≠ 0)
    {g : L} (hg : g ∈ Algebra.adjoin A (Set.range fun k => algebraMap A L (a k) / algebraMap A L (a j))) :
    ∃ m : ℕ, g * algebraMap A L (a j) ^ m ∈
      (Submodule.map (Algebra.linearMap A L) (Ideal.span (Set.range a))) ^ m := by
  set I := Submodule.map (Algebra.linearMap A L) (Ideal.span (Set.range a)) with hI
  have hmem : ∀ k, algebraMap A L (a k) ∈ I := fun k =>
    Submodule.mem_map_of_mem (f := Algebra.linearMap A L) (Ideal.subset_span ⟨k, rfl⟩)
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    refine ⟨1, ?_⟩
    simpa only [pow_one, div_mul_cancel₀ _ hj] using hmem k
  | algebraMap r =>
    exact ⟨0, by rw [pow_zero, pow_zero, mul_one]; exact Submodule.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    have h1 := Submodule.mul_mem_mul hm (Submodule.pow_mem_pow I (hmem j) n)
    have h2 := Submodule.mul_mem_mul hn (Submodule.pow_mem_pow I (hmem j) m)
    rw [← pow_add] at h1 h2
    rw [add_comm n m] at h2
    convert add_mem h1 h2 using 1
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    have h := Submodule.mul_mem_mul hm hn
    rw [← pow_add] at h
    convert h using 1
    ring

end

/- English proof (translation)
Introduce `A _ L _ _ J _ a f hf`. Unfold `blowUpColon`. Use `set b : J → L := fun k => algebraMap A L (a k) with hb`. Use `set I := Submodule.map (Algebra.linearMap A L) (Ideal.span (Set.range a)) with hI`. Establish `hIspan : I = Submodule.span A (Set.range b)`.

Rewrite using `[hI, Ideal.span, Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Establish `hmem : ∀ k, b k ∈ I` using `fun k => Submodule.mem_map_of_mem (f := Algebra.linearMap A L) (Ideal.subset_span ⟨k, rfl⟩)`. Establish `hex : ∀ j, ∃ m : ℕ, b j ≠ 0 → f * b j ^ m ∈ I ^ m`. Introduce `j`.

Distinguish the cases in `hj : b j = 0`. Conclude with `⟨0, fun h => (h hj).elim⟩`. Take `⟨m, hm⟩` from `ChartsInColon.exists_mul_pow_mem a j hj (hf j hj)`. Conclude with `⟨m, fun _ => hm⟩`. Use `choose m hm using hex`.

Use `set M := ∑ j, m j with hM`. Use `Submodule.mem_iSup_of_mem (Fintype.card J * M + 1) ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_div_iff_forall_mul_mem]`. Introduce `y hy`. Rewrite `hy` using `[hIspan, Submodule.span_pow]`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, rfl⟩` from `Set.mem_pow.mp hx`. Use `choose k hk using fun i => (g i).2`. Establish `hx' : (List.ofFn fun i => (g i : L)).prod = ∏ i, b (k i)`.

Rewrite using `[List.prod_ofFn]`. Conclude with `Finset.prod_congr rfl fun i _ => (hk i).symm`. Rewrite using `[hx']`. Take `⟨j, hj⟩` from `Fintype.exists_lt_card_fiber_of_mul_lt_card (f := k) (n := M) (by rw [Fintype.card_fin]; omega)`. Use `set s := Finset.univ.filter fun i => k i = j with hs`.

Use `set t := Finset.univ.filter fun i => ¬ k i = j with ht`. Establish `hsplit : ∏ i, b (k i) = b j ^ s.card * ∏ i ∈ t, b (k i)`. Rewrite using `[← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => k i = j), ← Finset.prod_const]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]`.

Establish `hcard : s.card + t.card = Fintype.card J * M + 1`. Rewrite using `[hs, ht, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]`. Establish `ht' : ∏ i ∈ t, b (k i) ∈ I ^ t.card` using `ChartsInColon.prod_mem_pow I t _ fun i _ => hmem (k i)`. Rewrite using `[hsplit]`. Distinguish the cases in `hbj : b j = 0`.

Rewrite using `[hbj, zero_pow (by omega), zero_mul, mul_zero]`. Conclude with `zero_mem _`. Establish `hmj : m j ≤ M` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)`. Establish `h1` using `Submodule.mul_mem_mul (Submodule.mul_mem_mul (hm j hbj) (Submodule.pow_mem_pow I (hmem j) (s.card - m j))) ht'`. Rewrite `h1` using `[← pow_add, ← pow_add, Nat.add_sub_cancel' (by omega), hcard]`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Establish `hc : s.card - m j + m j = s.card` using `Nat.sub_add_cancel (by omega)`. Use `conv_lhs => rw [← hc, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => rw [mul_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem ChartsInColon.proof : ChartsInColon.Statement.{u} := by
  classical
  intro A _ L _ _ J _ a f hf
  unfold blowUpColon
  set b : J → L := fun k => algebraMap A L (a k) with hb
  set I := Submodule.map (Algebra.linearMap A L) (Ideal.span (Set.range a)) with hI
  have hIspan : I = Submodule.span A (Set.range b) := by
    rw [hI, Ideal.span, Submodule.map_span, ← Set.range_comp]
    rfl
  have hmem : ∀ k, b k ∈ I := fun k =>
    Submodule.mem_map_of_mem (f := Algebra.linearMap A L) (Ideal.subset_span ⟨k, rfl⟩)
  have hex : ∀ j, ∃ m : ℕ, b j ≠ 0 → f * b j ^ m ∈ I ^ m := by
    intro j
    by_cases hj : b j = 0
    · exact ⟨0, fun h => (h hj).elim⟩
    · obtain ⟨m, hm⟩ := ChartsInColon.exists_mul_pow_mem a j hj (hf j hj)
      exact ⟨m, fun _ => hm⟩
  choose m hm using hex
  set M := ∑ j, m j with hM
  refine Submodule.mem_iSup_of_mem (Fintype.card J * M + 1) ?_
  rw [Submodule.mem_div_iff_forall_mul_mem]
  intro y hy
  rw [hIspan, Submodule.span_pow] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := Set.mem_pow.mp hx
    choose k hk using fun i => (g i).2
    have hx' : (List.ofFn fun i => (g i : L)).prod = ∏ i, b (k i) := by
      rw [List.prod_ofFn]
      exact Finset.prod_congr rfl fun i _ => (hk i).symm
    rw [hx']
    obtain ⟨j, hj⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := k) (n := M)
      (by rw [Fintype.card_fin]; omega)
    set s := Finset.univ.filter fun i => k i = j with hs
    set t := Finset.univ.filter fun i => ¬ k i = j with ht
    have hsplit : ∏ i, b (k i) = b j ^ s.card * ∏ i ∈ t, b (k i) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => k i = j), ← Finset.prod_const]
      congr 1
      exact Finset.prod_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
    have hcard : s.card + t.card = Fintype.card J * M + 1 := by
      rw [hs, ht, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
    have ht' : ∏ i ∈ t, b (k i) ∈ I ^ t.card :=
      ChartsInColon.prod_mem_pow I t _ fun i _ => hmem (k i)
    rw [hsplit]
    by_cases hbj : b j = 0
    · rw [hbj, zero_pow (by omega), zero_mul, mul_zero]
      exact zero_mem _
    · have hmj : m j ≤ M := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have h1 := Submodule.mul_mem_mul
        (Submodule.mul_mem_mul (hm j hbj) (Submodule.pow_mem_pow I (hmem j) (s.card - m j))) ht'
      rw [← pow_add, ← pow_add, Nat.add_sub_cancel' (by omega), hcard] at h1
      convert h1 using 1
      have hc : s.card - m j + m j = s.card := Nat.sub_add_cancel (by omega)
      conv_lhs => rw [← hc, pow_add]
      ring
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

end

end GroundTheory.Heights₂.Heights.NumbersDVR
