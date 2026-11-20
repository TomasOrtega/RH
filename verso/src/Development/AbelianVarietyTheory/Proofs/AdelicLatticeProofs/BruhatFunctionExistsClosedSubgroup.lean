import Mathlib
import Formalism.UnipotentAdelicQuotients.BruhatFunctionExistsVariant

universe u

namespace GlobalTheory

open MeasureTheory Pointwise in
/- English proof (translation)
Take `⟨V₀, hV₀c, hV₀n⟩` from `exists_compact_mem_nhds (1 : G)`. Take `⟨V, hVc, hVn, hVinv⟩ : ∃ V : Set G, IsCompact V ∧ V ∈ nhds (1 : G) ∧ V⁻¹ = V` from `⟨V₀ ∩ V₀⁻¹, hV₀c.inter_right hV₀c.inv.isClosed, Filter.inter_mem hV₀n (inv_mem_nhds_one G hV₀n), by rw [Set.inter_inv, inv_inv, Set.inter_comm]⟩`. Establish `hPc : ∀ n : ℕ, IsCompact (V ^ n)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => rw [pow_zero, ← Set.singleton_one]`. Conclude with `isCompact_singleton`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `ih.mul hVc`. Establish `h1V : (1 : G) ∈ interior V` using `mem_interior_iff_mem_nhds.2 hVn`.

Establish `hPint : ∀ n : ℕ, V ^ n ⊆ interior (V ^ (n + 1))`. Introduce `n x hx`. Establish `hx' : x ∈ V ^ n * interior V` using `by simpa using Set.mul_mem_mul hx h1V`. Use `interior_maximal ?_ (isOpen_interior.mul_left) hx'` and prove the remaining obligations. Rewrite using `[pow_succ]`.

Conclude with `Set.mul_subset_mul subset_rfl interior_subset`. Establish `hPinv : ∀ n : ℕ, (V ^ n)⁻¹ = V ^ n` using `fun n => by rw [← inv_pow, hVinv]`. Take `⟨Rel, hRel⟩ : ∃ Rel : G → G → Prop, ∀ y z, Rel y z ↔ ∃ n : ℕ, ∃ a ∈ V ^ n, ∃ h ∈ H, z = a * y * h` from `⟨_, fun _ _ => Iff.rfl⟩`. Establish `hrefl : ∀ y, Rel y y` using `fun y => (hRel y y).2 ⟨0, 1, by simp, 1, H.one_mem, by simp⟩`. Establish `hsymm : ∀ y z, Rel y z → Rel z y`.

Introduce `y z hyz`. Take `⟨n, a, ha, h, hh, rfl⟩` from `(hRel y z).1 hyz`. Use `(hRel _ _).2 ⟨n, a⁻¹, ?_, h⁻¹, H.inv_mem hh, by group⟩` and prove the remaining obligations. Rewrite using `[← hPinv n]`. Conclude with `Set.inv_mem_inv.2 ha`.

Establish `htrans : ∀ y z w, Rel y z → Rel z w → Rel y w`. Introduce `y z w hyz hzw`. Take `⟨n, a, ha, h, hh, rfl⟩` from `(hRel y z).1 hyz`. Take `⟨m, b, hb, k, hk, rfl⟩` from `(hRel _ w).1 hzw`. Use `(hRel _ _).2 ⟨m + n, b * a, ?_, h * k, H.mul_mem hh hk, by group⟩` and prove the remaining obligations.

Rewrite using `[pow_add]`. Conclude with `Set.mul_mem_mul hb ha`. Set `σ : G → G` to `fun y => Classical.epsilon (Rel y)`. Establish `hσ : ∀ y, Rel y (σ y)` using `fun y => Classical.epsilon_spec ⟨y, hrefl y⟩`. Establish `hσeq : ∀ y z, Rel y z → σ z = σ y`.

Introduce `y z hyz`. Express the relevant statement in the definitionally equal form `Classical.epsilon (Rel z) = Classical.epsilon (Rel y)`. Use `congr 1`. Use function extensionality and compare the values at `w`. Conclude with `propext ⟨fun h => htrans _ _ _ hyz h, fun h => htrans _ _ _ (hsymm _ _ hyz) h⟩`.

Set `U : G → ℕ → Set G` to `fun r m => interior (V ^ (m + 1)) * {r} * (H : Set G)`. Establish `hUo : ∀ r m, IsOpen (U r m)` using `fun r m => isOpen_interior.mul_right.mul_right`. Establish `hUrel : ∀ r m z, z ∈ U r m → Rel r z`. Introduce and unpack `r m z ⟨_, ⟨a, ha, _, rfl, rfl⟩, h, hh, rfl⟩`. Conclude with `(hRel _ _).2 ⟨m + 1, a, interior_subset ha, h, hh, rfl⟩`.

Establish `hUH : ∀ r m z, z ∈ U r m → ∀ h ∈ H, z * h ∈ U r m`. Introduce and unpack `r m z ⟨x, hx, k, hk, rfl⟩ h hh`. Conclude with `⟨x, hx, k * h, H.mul_mem hk hh, by rw [mul_assoc]⟩`. Establish `hUsub : ∀ r m, U r m ⊆ V ^ (m + 1) * {r} * (H : Set G)` using `fun r m => Set.mul_subset_mul (Set.mul_subset_mul interior_subset subset_rfl) subset_rfl`. Establish `hexh : ∀ r z, Rel r z → ∃ m, z ∈ U r m`.

Introduce `r z hz`. Take `⟨n, a, ha, h, hh, rfl⟩` from `(hRel r z).1 hz`. Conclude with `⟨n, Set.mul_mem_mul (Set.mul_mem_mul (hPint n ha) rfl) hh⟩`. Set `C : G → ℕ → Set G` to `fun r n => (V ^ (n + 1) * {r}) \ ⋃ k, ⋃ (_ : k < n), U r k`. Set `D : G → ℕ → Set G` to `fun r n => ⋃ k, ⋃ (_ : k < n), V ^ k * {r} * (H : Set G)`.

Establish `hCc : ∀ r n, IsCompact (C r n)` using `fun r n => ((hPc _).mul isCompact_singleton).diff (isOpen_iUnion fun k => isOpen_iUnion fun _ => hUo r k)`. Establish `hDc : ∀ r n, IsClosed (D r n)`. Introduce `r n`. Establish `: D r n = ⋃ k ∈ {k : ℕ | k < n}, V ^ k * {r} * (H : Set G)` using `rfl`. Rewrite using `[this]`.

Conclude with `(Set.finite_lt_nat n).isClosed_biUnion fun k _ => hH.mul_left_of_isCompact ((hPc k).mul isCompact_singleton)`. Establish `hCD : ∀ r n, Disjoint (C r n) (D r n)`. Introduce `r n`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `x ⟨-, hxU⟩ hxD`.

Simplify using `only [D, Set.mem_iUnion] at hxD`. Take `⟨k, hk, hx⟩` from `hxD`. Conclude with `hxU (Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, Set.mul_subset_mul (Set.mul_subset_mul (hPint k) subset_rfl) subset_rfl hx⟩⟩)`. Use `choose φ hφ1 hφ0 hφcs hφI using fun r n => exists_continuous_one_zero_of_isCompact (hCc r n) (hDc r n) (hCD r n)`. Establish `hDU : ∀ r m n, m + 2 ≤ n → U r m ⊆ D r n`.

Introduce `r m n hmn z hz`. Conclude with `Set.mem_iUnion.2 ⟨m + 1, Set.mem_iUnion.2 ⟨by omega, hUsub r m hz⟩⟩`. Establish `hloc : ∀ r m z, z ∈ U r m → ∑ᶠ n, φ r n z = ∑ n ∈ Finset.range (m + 2), φ r n z`. Introduce `r m z hz`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises.

Introduce `n hn`. Assume the negation of the conclusion as `hn'`. Simplify using `only [Finset.coe_range, Set.mem_Iio, not_lt] at hn'`. Conclude with `hn (hφ0 r n (hDU r m n hn' hz))`. Establish `hσU : ∀ y m z, z ∈ U (σ y) m → σ z = σ y` using `fun y m z hz => (hσeq y z (htrans _ _ _ (hσ y) (hUrel _ m z hz)))`.

Establish `hyU : ∀ y, ∃ m, y ∈ U (σ y) m` using `fun y => hexh _ _ (hsymm _ _ (hσ y))`. Establish `hfeq : ∀ y m z, z ∈ U (σ y) m → ∑ᶠ n, φ (σ z) n z = ∑ n ∈ Finset.range (m + 2), φ (σ y) n z`. Introduce `y m z hz`. Rewrite using `[hσU y m z hz]`. Conclude with `hloc _ m z hz`.

Use `⟨fun y => ∑ᶠ n, φ (σ y) n y, ?_, fun y => finsum_nonneg fun n => (hφI _ _ y).1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[continuous_iff_continuousAt]`. Introduce `y`. Take `⟨m, hm⟩` from `hyU y`. Establish `hc : Continuous fun z => ∑ n ∈ Finset.range (m + 2), φ (σ y) n z` using `continuous_finset_sum _ fun n _ => (φ (σ y) n).continuous`.

Use `hc.continuousAt.congr ?_` and prove the remaining obligations. Use `filter_upwards [(hUo _ m).mem_nhds hm] with z hz`. Conclude with `(hfeq y m z hz).symm`. Establish `hloc' : ∀ y, ∃ O Q : Set G, IsOpen O ∧ y ∈ O ∧ (∀ z ∈ O, ∀ h ∈ H, z * h ∈ O) ∧ IsCompact Q ∧ tsupport (fun y => ∑ᶠ n, φ (σ y) n y) ∩ O ⊆ Q`. Introduce `y`.

Take `⟨m, hm⟩` from `hyU y`. Use `⟨U (σ y) m, ⋃ n ∈ Finset.range (m + 2), tsupport (φ (σ y) n), hUo _ m, hm, hUH _ m, (Finset.range (m + 2)).isCompact_biUnion fun n _ => hφcs _ n, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[Set.inter_comm]`. Use `closure_minimal ?_ ((Finset.range (m + 2)).isCompact_biUnion fun n _ => hφcs _ n).isClosed ((hUo _ m).inter_closure hx)` and prove the remaining obligations.

Introduce and unpack `z ⟨hzU, hz⟩`. Rewrite `hz` using `[Function.mem_support, hfeq y m z hzU]`. Take `⟨n, hn, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hz`. Conclude with `Set.mem_biUnion hn (subset_tsupport _ hne)`. Use `choose O Q hOo hyO hOH hQc hOQ using hloc'`.

Introduce `K hK`. Take `⟨t, ht⟩` from `hK.elim_finite_subcover (fun y : K => O y) (fun y => hOo y) fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyO y⟩`. Use `((t.isCompact_biUnion fun i _ => hQc i)).of_isClosed_subset ((isClosed_tsupport _).inter (hH.mul_left_of_isCompact hK)) ?_` and prove the remaining obligations. Introduce and unpack `x ⟨hxs, _, hk, h, hh, rfl⟩`. Take `⟨i, hi, hkO⟩` from `Set.mem_iUnion₂.1 (ht hk)`.

Conclude with `Set.mem_biUnion hi (hOQ i ⟨hxs, hOH i _ hkO h hh⟩)`. Introduce `y set r := σ y with hr`. Establish `hex : ∃ m, y ∈ U r m` using `hyU y`. Set `m` to `Nat.find hex`. Establish `hm : y ∈ U r m` using `Nat.find_spec hex`.

Take `⟨_, ⟨a, ha, _, rfl, rfl⟩, h, hh, hya⟩` from `hm`. Use `⟨⟨h, hh⟩⁻¹, ?_⟩` and prove the remaining obligations. Establish `hz : y * ((⟨h, hh⟩ : H)⁻¹ : H) = a * r`. Rewrite using `[← hya]`. Simplify using the standard rewrite rules.

Rewrite using `[hz]`. Establish `hzU : a * r ∈ U r m` using `⟨a * r, Set.mul_mem_mul ha rfl, 1, H.one_mem, mul_one _⟩`. Establish `hzC : a * r ∈ C r m`. Use `⟨Set.mul_mem_mul (interior_subset ha) rfl, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_iUnion]`.

Introduce and unpack `⟨k, hk, hkU⟩`. Conclude with `Nat.find_min hex hk (hya ▸ hUH r k _ hkU h hh)`. Express the relevant statement in the definitionally equal form `∑ᶠ n, φ (σ (a * r)) n (a * r) ≠ 0`. Rewrite using `[hfeq y m _ hzU]`. Use `(lt_of_lt_of_le ?_ (Finset.single_le_sum (fun n _ => (hφI _ n _).1) (Finset.mem_range.2 (by omega : m < m + 2)))).ne'` and prove the remaining obligations.

Rewrite using `[hφ1 _ m hzC]`. Evaluate the numerical expressions.
-/
private lemma exists_nonneg_continuous_ne_zero_on_cosets {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ f : G → ℝ, Continuous f ∧ (∀ x, 0 ≤ f x) ∧
      (∀ K : Set G, IsCompact K → IsCompact (tsupport f ∩ (K * (H : Set G)))) ∧
      ∀ x, ∃ h : H, f (x * h) ≠ 0 := by

  obtain ⟨V₀, hV₀c, hV₀n⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨V, hVc, hVn, hVinv⟩ : ∃ V : Set G, IsCompact V ∧ V ∈ nhds (1 : G) ∧ V⁻¹ = V :=
    ⟨V₀ ∩ V₀⁻¹, hV₀c.inter_right hV₀c.inv.isClosed, Filter.inter_mem hV₀n (inv_mem_nhds_one G hV₀n),
      by rw [Set.inter_inv, inv_inv, Set.inter_comm]⟩
  have hPc : ∀ n : ℕ, IsCompact (V ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, ← Set.singleton_one]; exact isCompact_singleton
    | succ n ih => rw [pow_succ]; exact ih.mul hVc
  have h1V : (1 : G) ∈ interior V := mem_interior_iff_mem_nhds.2 hVn
  have hPint : ∀ n : ℕ, V ^ n ⊆ interior (V ^ (n + 1)) := by
    intro n x hx
    have hx' : x ∈ V ^ n * interior V := by simpa using Set.mul_mem_mul hx h1V
    refine interior_maximal ?_ (isOpen_interior.mul_left) hx'
    rw [pow_succ]
    exact Set.mul_subset_mul subset_rfl interior_subset
  have hPinv : ∀ n : ℕ, (V ^ n)⁻¹ = V ^ n := fun n => by rw [← inv_pow, hVinv]

  obtain ⟨Rel, hRel⟩ : ∃ Rel : G → G → Prop, ∀ y z,
      Rel y z ↔ ∃ n : ℕ, ∃ a ∈ V ^ n, ∃ h ∈ H, z = a * y * h := ⟨_, fun _ _ => Iff.rfl⟩
  have hrefl : ∀ y, Rel y y := fun y =>
    (hRel y y).2 ⟨0, 1, by simp, 1, H.one_mem, by simp⟩
  have hsymm : ∀ y z, Rel y z → Rel z y := by
    intro y z hyz
    obtain ⟨n, a, ha, h, hh, rfl⟩ := (hRel y z).1 hyz
    refine (hRel _ _).2 ⟨n, a⁻¹, ?_, h⁻¹, H.inv_mem hh, by group⟩
    rw [← hPinv n]
    exact Set.inv_mem_inv.2 ha
  have htrans : ∀ y z w, Rel y z → Rel z w → Rel y w := by
    intro y z w hyz hzw
    obtain ⟨n, a, ha, h, hh, rfl⟩ := (hRel y z).1 hyz
    obtain ⟨m, b, hb, k, hk, rfl⟩ := (hRel _ w).1 hzw
    refine (hRel _ _).2 ⟨m + n, b * a, ?_, h * k, H.mul_mem hh hk, by group⟩
    rw [pow_add]
    exact Set.mul_mem_mul hb ha

  let σ : G → G := fun y => Classical.epsilon (Rel y)
  have hσ : ∀ y, Rel y (σ y) := fun y => Classical.epsilon_spec ⟨y, hrefl y⟩
  have hσeq : ∀ y z, Rel y z → σ z = σ y := by
    intro y z hyz
    change Classical.epsilon (Rel z) = Classical.epsilon (Rel y)
    congr 1
    funext w
    exact propext ⟨fun h => htrans _ _ _ hyz h, fun h => htrans _ _ _ (hsymm _ _ hyz) h⟩

  let U : G → ℕ → Set G := fun r m => interior (V ^ (m + 1)) * {r} * (H : Set G)
  have hUo : ∀ r m, IsOpen (U r m) := fun r m => isOpen_interior.mul_right.mul_right
  have hUrel : ∀ r m z, z ∈ U r m → Rel r z := by
    rintro r m z ⟨_, ⟨a, ha, _, rfl, rfl⟩, h, hh, rfl⟩
    exact (hRel _ _).2 ⟨m + 1, a, interior_subset ha, h, hh, rfl⟩
  have hUH : ∀ r m z, z ∈ U r m → ∀ h ∈ H, z * h ∈ U r m := by
    rintro r m z ⟨x, hx, k, hk, rfl⟩ h hh
    exact ⟨x, hx, k * h, H.mul_mem hk hh, by rw [mul_assoc]⟩
  have hUsub : ∀ r m, U r m ⊆ V ^ (m + 1) * {r} * (H : Set G) := fun r m =>
    Set.mul_subset_mul (Set.mul_subset_mul interior_subset subset_rfl) subset_rfl
  have hexh : ∀ r z, Rel r z → ∃ m, z ∈ U r m := by
    intro r z hz
    obtain ⟨n, a, ha, h, hh, rfl⟩ := (hRel r z).1 hz
    exact ⟨n, Set.mul_mem_mul (Set.mul_mem_mul (hPint n ha) rfl) hh⟩

  let C : G → ℕ → Set G := fun r n => (V ^ (n + 1) * {r}) \ ⋃ k, ⋃ (_ : k < n), U r k
  let D : G → ℕ → Set G := fun r n => ⋃ k, ⋃ (_ : k < n), V ^ k * {r} * (H : Set G)
  have hCc : ∀ r n, IsCompact (C r n) := fun r n =>
    ((hPc _).mul isCompact_singleton).diff (isOpen_iUnion fun k => isOpen_iUnion fun _ => hUo r k)
  have hDc : ∀ r n, IsClosed (D r n) := by
    intro r n
    have : D r n = ⋃ k ∈ {k : ℕ | k < n}, V ^ k * {r} * (H : Set G) := rfl
    rw [this]
    exact (Set.finite_lt_nat n).isClosed_biUnion fun k _ =>
      hH.mul_left_of_isCompact ((hPc k).mul isCompact_singleton)
  have hCD : ∀ r n, Disjoint (C r n) (D r n) := by
    intro r n
    rw [Set.disjoint_left]
    rintro x ⟨-, hxU⟩ hxD
    simp only [D, Set.mem_iUnion] at hxD
    obtain ⟨k, hk, hx⟩ := hxD
    exact hxU (Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk,
      Set.mul_subset_mul (Set.mul_subset_mul (hPint k) subset_rfl) subset_rfl hx⟩⟩)
  choose φ hφ1 hφ0 hφcs hφI using fun r n =>
    exists_continuous_one_zero_of_isCompact (hCc r n) (hDc r n) (hCD r n)

  have hDU : ∀ r m n, m + 2 ≤ n → U r m ⊆ D r n := by
    intro r m n hmn z hz
    exact Set.mem_iUnion.2 ⟨m + 1, Set.mem_iUnion.2 ⟨by omega, hUsub r m hz⟩⟩
  have hloc : ∀ r m z, z ∈ U r m →
      ∑ᶠ n, φ r n z = ∑ n ∈ Finset.range (m + 2), φ r n z := by
    intro r m z hz
    apply finsum_eq_sum_of_support_subset
    intro n hn
    by_contra hn'
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hn'
    exact hn (hφ0 r n (hDU r m n hn' hz))
  have hσU : ∀ y m z, z ∈ U (σ y) m → σ z = σ y := fun y m z hz =>
    (hσeq y z (htrans _ _ _ (hσ y) (hUrel _ m z hz)))
  have hyU : ∀ y, ∃ m, y ∈ U (σ y) m := fun y => hexh _ _ (hsymm _ _ (hσ y))
  have hfeq : ∀ y m z, z ∈ U (σ y) m →
      ∑ᶠ n, φ (σ z) n z = ∑ n ∈ Finset.range (m + 2), φ (σ y) n z := by
    intro y m z hz
    rw [hσU y m z hz]
    exact hloc _ m z hz
  refine ⟨fun y => ∑ᶠ n, φ (σ y) n y, ?_, fun y => finsum_nonneg fun n => (hφI _ _ y).1, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro y
    obtain ⟨m, hm⟩ := hyU y
    have hc : Continuous fun z => ∑ n ∈ Finset.range (m + 2), φ (σ y) n z :=
      continuous_finset_sum _ fun n _ => (φ (σ y) n).continuous
    refine hc.continuousAt.congr ?_
    filter_upwards [(hUo _ m).mem_nhds hm] with z hz
    exact (hfeq y m z hz).symm
  ·
    have hloc' : ∀ y, ∃ O Q : Set G, IsOpen O ∧ y ∈ O ∧ (∀ z ∈ O, ∀ h ∈ H, z * h ∈ O) ∧
        IsCompact Q ∧ tsupport (fun y => ∑ᶠ n, φ (σ y) n y) ∩ O ⊆ Q := by
      intro y
      obtain ⟨m, hm⟩ := hyU y
      refine ⟨U (σ y) m, ⋃ n ∈ Finset.range (m + 2), tsupport (φ (σ y) n), hUo _ m, hm,
        hUH _ m, (Finset.range (m + 2)).isCompact_biUnion fun n _ => hφcs _ n, ?_⟩
      intro x hx
      rw [Set.inter_comm] at hx
      refine closure_minimal ?_ ((Finset.range (m + 2)).isCompact_biUnion
        fun n _ => hφcs _ n).isClosed ((hUo _ m).inter_closure hx)
      rintro z ⟨hzU, hz⟩
      rw [Function.mem_support, hfeq y m z hzU] at hz
      obtain ⟨n, hn, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
      exact Set.mem_biUnion hn (subset_tsupport _ hne)
    choose O Q hOo hyO hOH hQc hOQ using hloc'
    intro K hK
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : K => O y) (fun y => hOo y)
      fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyO y⟩
    refine ((t.isCompact_biUnion fun i _ => hQc i)).of_isClosed_subset
      ((isClosed_tsupport _).inter (hH.mul_left_of_isCompact hK)) ?_
    rintro x ⟨hxs, _, hk, h, hh, rfl⟩
    obtain ⟨i, hi, hkO⟩ := Set.mem_iUnion₂.1 (ht hk)
    exact Set.mem_biUnion hi (hOQ i ⟨hxs, hOH i _ hkO h hh⟩)
  · intro y
    set r := σ y with hr
    have hex : ∃ m, y ∈ U r m := hyU y
    classical
    let m := Nat.find hex
    have hm : y ∈ U r m := Nat.find_spec hex
    obtain ⟨_, ⟨a, ha, _, rfl, rfl⟩, h, hh, hya⟩ := hm
    refine ⟨⟨h, hh⟩⁻¹, ?_⟩
    have hz : y * ((⟨h, hh⟩ : H)⁻¹ : H) = a * r := by
      rw [← hya]; simp
    rw [hz]
    have hzU : a * r ∈ U r m := ⟨a * r, Set.mul_mem_mul ha rfl, 1, H.one_mem, mul_one _⟩
    have hzC : a * r ∈ C r m := by
      refine ⟨Set.mul_mem_mul (interior_subset ha) rfl, ?_⟩
      simp only [Set.mem_iUnion]
      rintro ⟨k, hk, hkU⟩
      exact Nat.find_min hex hk (hya ▸ hUH r k _ hkU h hh)
    change ∑ᶠ n, φ (σ (a * r)) n (a * r) ≠ 0
    rw [hfeq y m _ hzU]
    refine (lt_of_lt_of_le ?_ (Finset.single_le_sum (fun n _ => (hφI _ n _).1)
      (Finset.mem_range.2 (by omega : m < m + 2)))).ne'
    rw [hφ1 _ m hzC]
    norm_num

open MeasureTheory Pointwise in
/- English proof (translation)
Establish `hemb : Topology.IsClosedEmbedding ((↑) : H → G)` using `hH.isClosedEmbedding_subtypeVal`. Establish `hsupp : ∀ K : Set G, IsCompact K → ∃ S : Set H, IsCompact S ∧ ∀ x ∈ K, ∀ h : H, h ∉ S → f (x * h) = 0`. Introduce `K hK`. Use `⟨(↑) ⁻¹' (K⁻¹ * (tsupport f ∩ (K * (H : Set G)))), hemb.isCompact_preimage (hK.inv.mul (hfK K hK)), ?_⟩` and prove the remaining obligations. Introduce `x hx h hS`.

Assume the negation of the conclusion as `hne`. Apply `hS` to reduce the goal to its premises. Use `⟨x⁻¹, by simpa using hx, x * h, ⟨subset_tsupport _ hne, x, hx, h, h.2, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hcont_h : ∀ x, Continuous fun h : H => f (x * h)` using `fun x => hf.comp (continuous_const.mul continuous_subtype_val)`.

Establish `hcs : ∀ x, HasCompactSupport fun h : H => f (x * h)`. Introduce `x`. Take `⟨S, hS, hSf⟩` from `hsupp {x} isCompact_singleton`. Conclude with `HasCompactSupport.intro hS fun h hh => hSf x rfl h hh`. Use `set F : G → ℝ := fun x => ∫ h : H, f (x * h) ∂μ with hFdef`.

Establish `hFpos : ∀ x, 0 < F x`. Introduce `x`. Take `⟨h, hh⟩` from `hpos x`. Conclude with `(hcont_h x).integral_pos_of_hasCompactSupport_nonneg_nonzero (hcs x) (fun h => hf0 _) hh`. Establish `hFinv : ∀ x (h : H), F (x * h) = F x`.

Introduce `x h`. Simplify using `only [hFdef]`. Use `integral_mul_left_eq_self (μ := μ) (fun k : H => f (x * k)) h` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`.

Use extensionality with `k`. Simplify using `[mul_assoc]`. Establish `hFcont : Continuous F`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `x₀`.

Take `⟨K, hK, hKn⟩` from `exists_compact_mem_nhds x₀`. Take `⟨S, hS, hSf⟩` from `hsupp K hK`. Establish `hc : ContinuousOn F K` using `continuousOn_integral_of_compact_support (f := fun x (h : H) => f (x * h)) hS (hf.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))).continuousOn fun x h hx hh => hSf x hx h hh`. Conclude with `hc.continuousAt hKn`. Use `⟨fun x => f x / F x, hf.div hFcont fun x => (hFpos x).ne', fun x => div_nonneg (hf0 x) (hFpos x).le, ?_, ?_⟩` and prove the remaining obligations.

Introduce `K hK`. Establish `hsub : tsupport (fun x => f x / F x) ⊆ tsupport f`. Apply `closure_mono` to reduce the goal to its premises. Introduce `x hx`. Simplify using `only [Function.mem_support] at hx ⊢`.

Introduce `h0`. Simplify using `[h0] at hx`. Use `((hfK K hK).inter_right (isClosed_tsupport (fun x => f x / F x))).of_isClosed_subset ((isClosed_tsupport _).inter (hH.mul_left_of_isCompact hK)) ?_` and prove the remaining obligations. Introduce and unpack `y ⟨hy1, hy2⟩`. Conclude with `⟨⟨hsub hy1, hy2⟩, hy1⟩`.

Introduce `x`. Simplify using `only [hFinv]`. Rewrite using `[integral_div]`. Conclude with `div_self (hFpos x).ne'`.
-/
private lemma exists_bruhat_function_of_positive_on_cosets {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (μ : Measure H) [μ.IsHaarMeasure]
    (f : G → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hfK : ∀ K : Set G, IsCompact K → IsCompact (tsupport f ∩ (K * (H : Set G))))
    (hpos : ∀ x, ∃ h : H, f (x * h) ≠ 0) :
    ∃ β : G → ℝ, Continuous β ∧ (∀ x, 0 ≤ β x) ∧
      (∀ K : Set G, IsCompact K → IsCompact (tsupport β ∩ (K * (H : Set G)))) ∧
      ∀ x, ∫ h : H, β (x * h) ∂μ = 1 := by
  have hemb : Topology.IsClosedEmbedding ((↑) : H → G) := hH.isClosedEmbedding_subtypeVal

  have hsupp : ∀ K : Set G, IsCompact K → ∃ S : Set H, IsCompact S ∧
      ∀ x ∈ K, ∀ h : H, h ∉ S → f (x * h) = 0 := by
    intro K hK
    refine ⟨(↑) ⁻¹' (K⁻¹ * (tsupport f ∩ (K * (H : Set G)))),
      hemb.isCompact_preimage (hK.inv.mul (hfK K hK)), ?_⟩
    intro x hx h hS
    by_contra hne
    apply hS
    refine ⟨x⁻¹, by simpa using hx, x * h, ⟨subset_tsupport _ hne, x, hx, h, h.2, rfl⟩, ?_⟩
    simp
  have hcont_h : ∀ x, Continuous fun h : H => f (x * h) :=
    fun x => hf.comp (continuous_const.mul continuous_subtype_val)
  have hcs : ∀ x, HasCompactSupport fun h : H => f (x * h) := by
    intro x
    obtain ⟨S, hS, hSf⟩ := hsupp {x} isCompact_singleton
    exact HasCompactSupport.intro hS fun h hh => hSf x rfl h hh
  set F : G → ℝ := fun x => ∫ h : H, f (x * h) ∂μ with hFdef
  have hFpos : ∀ x, 0 < F x := by
    intro x
    obtain ⟨h, hh⟩ := hpos x
    exact (hcont_h x).integral_pos_of_hasCompactSupport_nonneg_nonzero (hcs x)
      (fun h => hf0 _) hh
  have hFinv : ∀ x (h : H), F (x * h) = F x := by
    intro x h
    simp only [hFdef]
    have := integral_mul_left_eq_self (μ := μ) (fun k : H => f (x * k)) h
    rw [← this]
    congr 1
    ext k
    simp [mul_assoc]
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x₀
    obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds x₀
    obtain ⟨S, hS, hSf⟩ := hsupp K hK
    have hc : ContinuousOn F K :=
      continuousOn_integral_of_compact_support (f := fun x (h : H) => f (x * h)) hS
        (hf.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))).continuousOn
        fun x h hx hh => hSf x hx h hh
    exact hc.continuousAt hKn
  refine ⟨fun x => f x / F x, hf.div hFcont fun x => (hFpos x).ne',
    fun x => div_nonneg (hf0 x) (hFpos x).le, ?_, ?_⟩
  · intro K hK
    have hsub : tsupport (fun x => f x / F x) ⊆ tsupport f := by
      apply closure_mono
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h0
      simp [h0] at hx
    refine ((hfK K hK).inter_right (isClosed_tsupport (fun x => f x / F x))).of_isClosed_subset
      ((isClosed_tsupport _).inter (hH.mul_left_of_isCompact hK)) ?_
    rintro y ⟨hy1, hy2⟩
    exact ⟨⟨hsub hy1, hy2⟩, hy1⟩
  · intro x
    simp only [hFinv]
    rw [integral_div]
    exact div_self (hFpos x).ne'

open MeasureTheory Pointwise in

/- English proof (translation)
Unfold `_root_.HeckeCharacterZeroLocus.BruhatFunctionExistsVariant`. Introduce `G _ _ _ _ _ _ _ H hH μ _`. Take `⟨f, hf, hf0, hfK, hpos⟩` from `exists_nonneg_continuous_ne_zero_on_cosets H hH`. Conclude with `exists_bruhat_function_of_positive_on_cosets H hH μ f hf hf0 hfK hpos`.
-/
theorem _root_.GlobalTheory.bruhatFunctionExists_closedSubgroup : _root_.HeckeCharacterZeroLocus.BruhatFunctionExistsVariant.{u} := by
  unfold _root_.HeckeCharacterZeroLocus.BruhatFunctionExistsVariant
  intro G _ _ _ _ _ _ _ H hH μ _
  obtain ⟨f, hf, hf0, hfK, hpos⟩ := exists_nonneg_continuous_ne_zero_on_cosets H hH
  exact exists_bruhat_function_of_positive_on_cosets H hH μ f hf hf0 hfK hpos

end GlobalTheory
