import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flag

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

/- English proof (translation)
Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.mp h`. Establish `e : r • y = (r : Ω) * y` using `rfl`. Rewrite using `[← hr, e, mul_div_assoc, div_self hy, mul_one]`. Conclude with `r.2`.
-/
private theorem div_mem_of_mem_span_singleton {R : Subring Ω} {x y : Ω} (hy : y ≠ 0)
    (h : x ∈ Submodule.span R {y}) : x / y ∈ R := by
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp h
  have e : r • y = (r : Ω) * y := rfl
  rw [← hr, e, mul_div_assoc, div_self hy, mul_one]
  exact r.2

/- English proof (translation)
Consider the cases of `n with`. Consider the case `ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast]`. Conclude with `pow_mem hx n`. Consider the case `negSucc n => rw [zpow_negSucc, ← inv_pow]`. Conclude with `pow_mem hxi _`.
-/
private theorem zpow_mem_lemma_2 {R : Subring Ω} {x : Ω} (hx : x ∈ R) (hxi : x⁻¹ ∈ R) (n : ℤ) :
    x ^ n ∈ R := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact pow_mem hx n
  | negSucc n => rw [zpow_negSucc, ← inv_pow]; exact pow_mem hxi _

/- English proof (translation)
Establish `hs0 : ∀ i, s i ≠ 0` using `fun i => (hs i).1`. Use `⟨Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hs0 i), ?_⟩` and prove the remaining obligations. Use `show Submodule.span (regAt ξ p) {t | ∃ s' : I → Ω, (∀ i, (Λ i).IsGenAt p (s' i)) ∧ t = ∏ i, s' i ^ a i} = _`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `t ⟨s', hs', rfl⟩`. Establish `hs'0 : ∀ i, s' i ≠ 0` using `fun i => (hs' i).1`. Establish `hw : ∀ i, s' i / s i ∈ regAt ξ p` using `fun i => by`. Use `div_mem_of_mem_span_singleton (hs0 i) ?_` and prove the remaining obligations. Rewrite using `[← (hs i).2, (hs' i).2]`.

Conclude with `Submodule.mem_span_singleton_self _`. Establish `hwi : ∀ i, (s' i / s i)⁻¹ ∈ regAt ξ p` using `fun i => by`. Rewrite using `[inv_div]`. Use `div_mem_of_mem_span_singleton (hs'0 i) ?_` and prove the remaining obligations. Rewrite using `[← (hs' i).2, (hs i).2]`.

Conclude with `Submodule.mem_span_singleton_self _`. Establish `hc : ∏ i, (s' i / s i) ^ a i ∈ regAt ξ p` using `prod_mem fun i _ => zpow_mem_lemma_2 (hw i) (hwi i) (a i)`. Rewrite using `[SetLike.mem_coe, Submodule.mem_span_singleton]`. Use `⟨⟨_, hc⟩, ?_⟩` and prove the remaining obligations. Use `show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = ∏ i, s' i ^ a i`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_zpow, div_mul_cancel₀ _ (hs0 i)]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Rewrite using `[Set.singleton_subset_iff]`.

Conclude with `⟨s, hs, rfl⟩`.
-/
theorem tens_gen {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  have hs0 : ∀ i, s i ≠ 0 := fun i => (hs i).1
  refine ⟨Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hs0 i), ?_⟩
  show Submodule.span (regAt ξ p) {t | ∃ s' : I → Ω, (∀ i, (Λ i).IsGenAt p (s' i)) ∧ t = ∏ i, s' i ^ a i} = _
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro t ⟨s', hs', rfl⟩
    have hs'0 : ∀ i, s' i ≠ 0 := fun i => (hs' i).1
    have hw : ∀ i, s' i / s i ∈ regAt ξ p := fun i => by
      refine div_mem_of_mem_span_singleton (hs0 i) ?_
      rw [← (hs i).2, (hs' i).2]
      exact Submodule.mem_span_singleton_self _
    have hwi : ∀ i, (s' i / s i)⁻¹ ∈ regAt ξ p := fun i => by
      rw [inv_div]
      refine div_mem_of_mem_span_singleton (hs'0 i) ?_
      rw [← (hs' i).2, (hs i).2]
      exact Submodule.mem_span_singleton_self _
    have hc : ∏ i, (s' i / s i) ^ a i ∈ regAt ξ p :=
      prod_mem fun i _ => zpow_mem_lemma_2 (hw i) (hwi i) (a i)
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨⟨_, hc⟩, ?_⟩
    show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = ∏ i, s' i ^ a i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← mul_zpow, div_mul_cancel₀ _ (hs0 i)]
  · apply Submodule.span_mono
    rw [Set.singleton_subset_iff]
    exact ⟨s, hs, rfl⟩

variable {E : Type} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
Unfold `flagStep`. Establish `hset : {k : Fin r | (k : ℕ) < (i : ℕ) + 1} = {k : Fin r | (k : ℕ) < i} ∪ {i}`. Use extensionality with `k`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Distinguish the cases in `h' : (k : ℕ) = i`. Conclude with `Or.inr (Fin.ext h')`. Conclude with `Or.inl (by omega)`. Introduce and unpack `(h | h)`.

Use linear arithmetic over natural numbers and integers. Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers. Rewrite using `[hset, Set.image_union, Set.image_singleton, Submodule.span_union]`.
-/
theorem step_succ {r : ℕ} (b : Fin r → E) (i : Fin r) : flagStep Ω b (i+1) = flagStep Ω b i ⊔ Submodule.span Ω {b i} := by
  unfold flagStep
  have hset : {k : Fin r | (k : ℕ) < (i : ℕ) + 1} = {k : Fin r | (k : ℕ) < i} ∪ {i} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h
      by_cases h' : (k : ℕ) = i
      · exact Or.inr (Fin.ext h')
      · exact Or.inl (by omega)
    · rintro (h | h)
      · omega
      · subst h
        omega
  rw [hset, Set.image_union, Set.image_singleton, Submodule.span_union]

/- English proof (translation)
Establish `hhi : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j ∈ Submodule.span Ω (b '' {k | (k : ℕ) < n}ᶜ)`. Apply `Submodule.sum_mem` to reduce the goal to its premises. Introduce `j _`. Distinguish the cases in `hj : (j : ℕ) < n`. Simplify using `[hj]`.

Rewrite using `[if_neg hj]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)`. Establish `hlo : ∑ j : Fin r, (if (j : ℕ) < n then g j else 0) • b j ∈ Submodule.span Ω (b '' {k | (k : ℕ) < n})`. Apply `Submodule.sum_mem` to reduce the goal to its premises. Introduce `j _`.

Distinguish the cases in `hj : (j : ℕ) < n`. Rewrite using `[if_pos hj]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)`. Simplify using `[hj]`. Establish `hsplit : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j = ∑ j : Fin r, g j • b j - ∑ j : Fin r, (if (j : ℕ) < n then g j else 0) • b j`.

Rewrite using `[eq_sub_iff_add_eq, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hj : (j : ℕ) < n <;> simp [hj]`. Establish `hzero : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j = 0`. Establish `hmem : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j ∈ Submodule.span Ω (b '' {k | (k : ℕ) < n})`.

Rewrite using `[hsplit]`. Conclude with `Submodule.sub_mem _ hg hlo`. Conclude with `(Submodule.disjoint_def.mp (hli.disjoint_span_image disjoint_compl_right)) _ hmem hhi`. Use `Fintype.linearIndependent_iff.mp hli _ hzero k` as an intermediate fact. Simplify `this` using `[show ¬ (k : ℕ) < n by omega]`.
-/
private theorem eq_zero_of_sum_smul_mem_span_lt {r : ℕ} {b : Fin r → E} (hli : LinearIndependent Ω b) (g : Fin r → Ω)
    (n : ℕ) (hg : ∑ k, g k • b k ∈ Submodule.span Ω (b '' {k | (k : ℕ) < n})) (k : Fin r)
    (hk : n ≤ (k : ℕ)) : g k = 0 := by
  classical
  have hhi : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j ∈
      Submodule.span Ω (b '' {k | (k : ℕ) < n}ᶜ) := by
    apply Submodule.sum_mem
    intro j _
    by_cases hj : (j : ℕ) < n
    · simp [hj]
    · rw [if_neg hj]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  have hlo : ∑ j : Fin r, (if (j : ℕ) < n then g j else 0) • b j ∈
      Submodule.span Ω (b '' {k | (k : ℕ) < n}) := by
    apply Submodule.sum_mem
    intro j _
    by_cases hj : (j : ℕ) < n
    · rw [if_pos hj]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · simp [hj]
  have hsplit : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j =
      ∑ j : Fin r, g j • b j - ∑ j : Fin r, (if (j : ℕ) < n then g j else 0) • b j := by
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : (j : ℕ) < n <;> simp [hj]
  have hzero : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j = 0 := by
    have hmem : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j ∈
        Submodule.span Ω (b '' {k | (k : ℕ) < n}) := by
      rw [hsplit]
      exact Submodule.sub_mem _ hg hlo
    exact (Submodule.disjoint_def.mp (hli.disjoint_span_image disjoint_compl_right)) _ hmem hhi
  have := Fintype.linearIndependent_iff.mp hli _ hzero k
  simpa [show ¬ (k : ℕ) < n by omega] using this

/- English proof (translation)
Take `⟨hli, hLp⟩` from `hb`. Establish `hbi : b i ∈ flagStep Ω b₀ i ⊔ Submodule.span Ω {b₀ i}`. Rewrite using `[← step_succ, ← h]`. Unfold `flagStep`. Conclude with `Submodule.subset_span ⟨i, show (i : ℕ) < (i : ℕ) + 1 by omega, rfl⟩`.

Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.mp hbi`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.mp hz`. Establish `hc : c ≠ 0`. Introduce and unpack `rfl`. Rewrite `hyz` using `[zero_smul, add_zero]`.

Rewrite `hy` using `[← h, hyz]`. Unfold `flagStep at hy`. Conclude with `hli.notMem_span_image (by simp) hy`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Use `show Submodule.span (regAt ξ p) {t | ∃ e ∈ L p, e - t • b₀ i ∈ flagStep Ω b₀ i} = Submodule.span (regAt ξ p) {c}`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `t ⟨e, he, hte⟩`. Rewrite `he` using `[hLp]`. Take `⟨g, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun _).mp he`.

Establish `hsm : ∀ k, g k • b k = (g k : Ω) • b k` using `fun k => rfl`. Establish `hsum : ∑ k, (c * (g k : Ω) - (if k = i then t else 0)) • b k = c • ∑ k, g k • b k - t • b i`. Simplify using `only [hsm, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_smul, Finset.smul_sum]`. Establish `hx : c • (∑ k, g k • b k - t • b₀ i) - t • y ∈ flagStep Ω b₀ i` using `Submodule.sub_mem _ (Submodule.smul_mem _ c hte) (Submodule.smul_mem _ t hy)`. Establish `heq : ∑ k, (c * (g k : Ω) - (if k = i then t else 0)) • b k = c • (∑ k, g k • b k - t • b₀ i) - t • y`.

Rewrite using `[hsum, ← hyz, smul_add, smul_sub, smul_smul, smul_smul, mul_comm t c]`. Normalize the expressions using the abelian group laws. Establish `key : ∑ k, (c * (g k : Ω) - (if k = i then t else 0)) • b k ∈ flagStep Ω b i`. Rewrite using `[h, heq]`. Conclude with `hx`.

Unfold `flagStep at key`. Establish `hci` using `eq_zero_of_sum_smul_mem_span_lt hli _ i key i le_rfl`. Rewrite `hci` using `[if_pos rfl, sub_eq_zero]`. Rewrite using `[SetLike.mem_coe, Submodule.mem_span_singleton]`. Use `⟨g i, ?_⟩` and prove the remaining obligations.

Use `show (g i : Ω) * c = t`. Rewrite using `[mul_comm]`. Conclude with `hci`. Apply `Submodule.span_mono` to reduce the goal to its premises. Rewrite using `[Set.singleton_subset_iff]`.

Use `⟨b i, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hLp]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Rewrite using `[← hyz, add_sub_cancel_right]`. Conclude with `hy`.
-/
theorem gr_gen (L : Lat ξ E) {r : ℕ} (b b₀ : Fin r → E) (p : Cpt ξ) (h : ∀ i, flagStep Ω b i = flagStep Ω b₀ i)
    (hb : L.IsFrameAt b p) (i : Fin r) : ∃ t, (L.gr b₀ i).IsGenAt p t := by
  obtain ⟨hli, hLp⟩ := hb
  have hbi : b i ∈ flagStep Ω b₀ i ⊔ Submodule.span Ω {b₀ i} := by
    rw [← step_succ, ← h]
    unfold flagStep
    exact Submodule.subset_span ⟨i, show (i : ℕ) < (i : ℕ) + 1 by omega, rfl⟩
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hbi
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hyz
    rw [← h, hyz] at hy
    unfold flagStep at hy
    exact hli.notMem_span_image (by simp) hy
  refine ⟨c, hc, ?_⟩
  show Submodule.span (regAt ξ p) {t | ∃ e ∈ L p, e - t • b₀ i ∈ flagStep Ω b₀ i} =
    Submodule.span (regAt ξ p) {c}
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro t ⟨e, he, hte⟩
    rw [hLp] at he
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp he
    have hsm : ∀ k, g k • b k = (g k : Ω) • b k := fun k => rfl
    have hsum : ∑ k, (c * (g k : Ω) - (if k = i then t else 0)) • b k =
        c • ∑ k, g k • b k - t • b i := by
      simp only [hsm, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, mul_smul, Finset.smul_sum]
    have hx : c • (∑ k, g k • b k - t • b₀ i) - t • y ∈ flagStep Ω b₀ i :=
      Submodule.sub_mem _ (Submodule.smul_mem _ c hte) (Submodule.smul_mem _ t hy)
    have heq : ∑ k, (c * (g k : Ω) - (if k = i then t else 0)) • b k =
        c • (∑ k, g k • b k - t • b₀ i) - t • y := by
      rw [hsum, ← hyz, smul_add, smul_sub, smul_smul, smul_smul, mul_comm t c]
      abel
    have key : ∑ k, (c * (g k : Ω) - (if k = i then t else 0)) • b k ∈ flagStep Ω b i := by
      rw [h, heq]
      exact hx
    unfold flagStep at key
    have hci := eq_zero_of_sum_smul_mem_span_lt hli _ i key i le_rfl
    rw [if_pos rfl, sub_eq_zero] at hci
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨g i, ?_⟩
    show (g i : Ω) * c = t
    rw [mul_comm]
    exact hci
  · apply Submodule.span_mono
    rw [Set.singleton_subset_iff]
    refine ⟨b i, ?_, ?_⟩
    · rw [hLp]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [← hyz, add_sub_cancel_right]
      exact hy

/- English proof (translation)
Take `⟨U, hU, b, hflag, hframe⟩` from `h p hp`. Conclude with `gr_gen L b b₀ p hflag (hframe p hp hU) i`.
-/
theorem gr_gen_of_isFlagVBOn {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ} {b₀ : Fin r → E} (h : L.IsFlagVBOn T b₀)
    {p : Cpt ξ} (hp : p ∈ T) (i : Fin r) : ∃ t, (L.gr b₀ i).IsGenAt p t := by
  obtain ⟨U, hU, b, hflag, hframe⟩ := h p hp
  exact gr_gen L b b₀ p hflag (hframe p hp hU) i

end GlobalTheory.CompanionTheory.Ar.Flag
