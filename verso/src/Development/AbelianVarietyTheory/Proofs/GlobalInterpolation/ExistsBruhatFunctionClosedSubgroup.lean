import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory

open MeasureTheory Topology in
open scoped ENNReal Pointwise in
/- English proof (translation)
Use `haveI : LocallyCompactSpace T' := hj.locallyCompactSpace`. Use `haveI : SecondCountableTopology T' := hj.isEmbedding.secondCountableTopology`. Use `haveI : T2Space T' := hj.isEmbedding.t2Space`. Establish `hjm : Measurable j` using `hj.continuous.measurable`. Set `E` to `CompactExhaustion.choice T`.

Take `⟨A, hA⟩ : ∃ A : ℕ → Set T, ∀ n x, x ∈ A n ↔ ∃ s : T', x * j s ∈ E n` from `⟨fun n => {x | ∃ s : T', x * j s ∈ E n}, fun _ _ => Iff.rfl⟩`. Establish `hA_mono : ∀ {m n}, m ≤ n → A m ⊆ A n` using `fun hmn x hx => by`. Take `⟨s, hs⟩` from `(hA _ x).1 hx`. Conclude with `(hA _ x).2 ⟨s, E.subset hmn hs⟩`. Establish `hA_mul : ∀ n x (s : T'), x * j s ∈ A n ↔ x ∈ A n`.

Introduce `n x s`. Rewrite using `[hA, hA]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s', hs'⟩`. Conclude with `⟨s * s', by simpa [mul_assoc] using hs'⟩`.

Introduce and unpack `⟨s', hs'⟩`. Conclude with `⟨s⁻¹ * s', by simpa [mul_assoc] using hs'⟩`. Establish `hE_A : ∀ n, E n ⊆ A n` using `fun n x hx => (hA n x).2 ⟨1, by simpa using hx⟩`. Establish `hA_meas : ∀ n, MeasurableSet (A n)`. Introduce `n`.

Establish `hAn : A n = E n * Set.range j`. Use extensionality with `x`. Rewrite using `[hA, Set.mem_mul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs⟩`.

Conclude with `⟨_, hs, j s⁻¹, ⟨s⁻¹, rfl⟩, by simp [mul_assoc]⟩`. Introduce and unpack `⟨k, hk, _, ⟨s, rfl⟩, rfl⟩`. Conclude with `⟨s⁻¹, by simpa [mul_assoc] using hk⟩`. Rewrite using `[hAn]`. Conclude with `(hj.isClosed_range.mul_left_of_isCompact (E.isCompact n)).measurableSet`.

Establish `hex : ∀ x, ∃ n, x ∈ A n` using `fun x => ⟨E.find x, hE_A _ (E.mem_find x)⟩`. Choose the witnesses or unpack the hypotheses as in `⟨N, hNm, hN⟩ : ∃ N : T → ℕ, Measurable N ∧ ∀ x n, N x ≤ n ↔ x ∈ A n := by`. Use `⟨fun x => Nat.find (hex x), measurable_find hex hA_meas, fun x n => ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.find_le_iff]`. Conclude with `⟨fun ⟨m, hm, hx⟩ => hA_mono hm hx, fun hx => ⟨n, le_rfl, hx⟩⟩`.

Establish `hN_mem : ∀ x, x ∈ A (N x)` using `fun x => (hN x _).1 le_rfl`. Establish `hN_mul : ∀ x (s : T'), N (x * j s) = N x` using `fun x s => le_antisymm ((hN _ _).2 ((hA_mul _ _ _).2 (hN_mem x))) ((hN _ _).2 ((hA_mul _ _ _).1 (hN_mem _)))`. Take `⟨S, hS⟩ : ∃ S : Set T, ∀ x, x ∈ S ↔ x ∈ E (N x + 1)` from `⟨{x | x ∈ E (N x + 1)}, fun _ => Iff.rfl⟩`. Establish `hS_meas : MeasurableSet S`. Establish `hSU : S = ⋃ n, N ⁻¹' {n} ∩ E (n + 1)`.

Use extensionality with `x`. Rewrite using `[hS]`. Simplify using `only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]`. Conclude with `⟨fun hx => ⟨_, rfl, hx⟩, by rintro ⟨n, rfl, hx⟩; exact hx⟩`. Rewrite using `[hSU]`.

Conclude with `MeasurableSet.iUnion fun n => (hNm (measurableSet_singleton n)).inter (E.isCompact _).isClosed.measurableSet`. Choose the witnesses or unpack the hypotheses as in `⟨ψ, hψm, hψle, hψS, hψ1⟩ : ∃ ψ : T → ℝ≥0∞, Measurable ψ ∧ (∀ x, ψ x ≤ 1) ∧ (∀ x, ψ x ≠ 0 → x ∈ S) ∧ (∀ x, x ∈ S → ψ x = 1) := by`. Use `⟨S.indicator fun _ => 1, measurable_const.indicator hS_meas, fun x => ?_, fun x hx => ?_, fun x hx => Set.indicator_of_mem hx _⟩` and prove the remaining obligations. Apply the tactic sequence `by_cases hx : x ∈ S <;> simp [hx]`. Assume the negation of the conclusion as `hxS`.

Conclude with `hx (by simp [hxS])`. Take `⟨F, hFm, hF⟩ : ∃ F : T → ℝ≥0∞, Measurable F ∧ ∀ x, F x = ∫⁻ s, ψ (x * j s) ∂ν` from `⟨fun x => ∫⁻ s, ψ (x * j s) ∂ν, (hψm.comp (measurable_fst.mul (hjm.comp measurable_snd))).lintegral_prod_right', fun _ => rfl⟩`. Establish `hF_mul : ∀ x (s : T'), F (x * j s) = F x`. Introduce `x s`. Rewrite using `[hF, hF]`.

Simplify `lintegral_mul_left_eq_self (μ := ν) (fun t => ψ (x * j t)) s` using `[mul_assoc]`. Establish `hF_pos : ∀ n, ∃ c : ℝ≥0∞, 0 < c ∧ ∀ x, N x = n → c ≤ F x`. Introduce `n`. Take `⟨V, hV, hKV⟩` from `compact_open_separated_mul_right (E.isCompact n) isOpen_interior (E.subset_interior_succ n)`. Establish `hVo : IsOpen (j ⁻¹' interior V)` using `isOpen_interior.preimage hj.continuous`.

Establish `hV1 : (1 : T') ∈ j ⁻¹' interior V`. Simplify using `using mem_interior_iff_mem_nhds.2 hV`. Use `⟨ν (j ⁻¹' interior V), hVo.measure_pos ν ⟨1, hV1⟩, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨s₀, hs₀⟩` from `(hA n x).1 (hx ▸ hN_mem x)`. Combine the equalities or inequalities in the displayed calculation.

Use `lintegral_mono fun s => ?_` and prove the remaining obligations. Distinguish the cases in `hs : s ∈ j ⁻¹' interior V`. Rewrite using `[Set.indicator_of_mem hs, Pi.one_apply, hψ1]`. Rewrite using `[hS, hN_mul, hN_mul, hx]`. Conclude with `interior_subset (hKV (Set.mul_mem_mul hs₀ (interior_subset hs)))`.

Simplify using `[hs]`. Use `_ = F x := by rw [← hF, hF_mul]`. Use `choose c hc_pos hc using hF_pos`. Establish `hF_ne : ∀ x, F x ≠ 0` using `fun x => ((hc_pos (N x)).trans_le (hc _ x rfl)).ne'`. Establish `hF_fin : ∀ x, F x ≠ ⊤`.

Introduce `x`. Establish `hK : IsCompact ((fun s : T' => x * j s) ⁻¹' E (N x + 1))` using `((Homeomorph.mulLeft x).isClosedEmbedding.comp hj).isCompact_preimage (E.isCompact _)`. Use `(lt_of_le_of_lt ?_ (hK.measure_lt_top (μ := ν))).ne` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun s => ?_` and prove the remaining obligations.

Distinguish the cases in `hs : s ∈ (fun s : T' => x * j s) ⁻¹' E (N x + 1)`. Rewrite using `[Set.indicator_of_mem hs]`. Conclude with `hψle _`. Rewrite using `[Set.indicator_of_notMem hs]`. Use `le_of_eq (by_contra fun hψs => ?_)` and prove the remaining obligations.

Establish `hmem` using `(hS _).1 (hψS _ hψs)`. Rewrite `hmem` using `[hN_mul]`. Conclude with `hs hmem`. Use `_ = ν ((fun s : T' => x * j s) ⁻¹' E (N x + 1)) := lintegral_indicator_one hK.isClosed.measurableSet`. Use `⟨fun x => ψ x * (F x)⁻¹, hψm.mul hFm.inv, fun g => ?_, fun K hK => ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Repeatedly rewrite using `[hF_mul]`. Use `_ = (∫⁻ s, ψ (g * j s) ∂ν) * (F g)⁻¹ := lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (hF_ne g))`. Use `_ = 1 := by rw [← hF, ENNReal.mul_inv_cancel (hF_ne g) (hF_fin g)]`. Take `⟨M, hM⟩` from `E.exists_superset_of_isCompact hK`.

Use `⟨E (M + 1), ∑ n ∈ Finset.range (M + 1), (c n)⁻¹, E.isCompact _, ENNReal.sum_lt_top.2 fun n _ => ENNReal.inv_lt_top.2 (hc_pos n), fun k hk s => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `hNk : N k ≤ M` using `(hN k M).2 (hE_A M (hM hk))`. Combine the equalities or inequalities in the displayed calculation. Introduce `hne`. Establish `hNk : N k ≤ M` using `(hN k M).2 (hE_A M (hM hk))`.

Establish `hmem` using `(hS _).1 (hψS _ (left_ne_zero_of_mul hne))`. Rewrite `hmem` using `[hN_mul]`. Conclude with `E.subset (Nat.succ_le_succ hNk) hmem`.
-/
private theorem exists_normalized_weight_of_closedEmbedding
    {T T' : Type} [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T]
    [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [MeasurableSpace T'] [BorelSpace T']
    (j : T' →* T) (hj : IsClosedEmbedding j) (ν : Measure T') [ν.IsHaarMeasure] :
    ∃ φ : T → ℝ≥0∞, Measurable φ ∧ (∀ g, ∫⁻ s, φ (g * j s) ∂ν = 1) ∧
      ∀ K : Set T, IsCompact K → ∃ (K' : Set T) (C : ℝ≥0∞), IsCompact K' ∧ C < ⊤ ∧
        ∀ k ∈ K, ∀ s : T', φ (k * j s) ≤ C ∧ (φ (k * j s) ≠ 0 → k * j s ∈ K') := by
  classical
  haveI : LocallyCompactSpace T' := hj.locallyCompactSpace
  haveI : SecondCountableTopology T' := hj.isEmbedding.secondCountableTopology
  haveI : T2Space T' := hj.isEmbedding.t2Space
  have hjm : Measurable j := hj.continuous.measurable
  let E := CompactExhaustion.choice T
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Set T, ∀ n x, x ∈ A n ↔ ∃ s : T', x * j s ∈ E n :=
    ⟨fun n => {x | ∃ s : T', x * j s ∈ E n}, fun _ _ => Iff.rfl⟩
  have hA_mono : ∀ {m n}, m ≤ n → A m ⊆ A n := fun hmn x hx => by
    obtain ⟨s, hs⟩ := (hA _ x).1 hx
    exact (hA _ x).2 ⟨s, E.subset hmn hs⟩
  have hA_mul : ∀ n x (s : T'), x * j s ∈ A n ↔ x ∈ A n := by
    intro n x s
    rw [hA, hA]
    constructor
    · rintro ⟨s', hs'⟩
      exact ⟨s * s', by simpa [mul_assoc] using hs'⟩
    · rintro ⟨s', hs'⟩
      exact ⟨s⁻¹ * s', by simpa [mul_assoc] using hs'⟩
  have hE_A : ∀ n, E n ⊆ A n := fun n x hx => (hA n x).2 ⟨1, by simpa using hx⟩
  have hA_meas : ∀ n, MeasurableSet (A n) := by
    intro n
    have hAn : A n = E n * Set.range j := by
      ext x
      rw [hA, Set.mem_mul]
      constructor
      · rintro ⟨s, hs⟩
        exact ⟨_, hs, j s⁻¹, ⟨s⁻¹, rfl⟩, by simp [mul_assoc]⟩
      · rintro ⟨k, hk, _, ⟨s, rfl⟩, rfl⟩
        exact ⟨s⁻¹, by simpa [mul_assoc] using hk⟩
    rw [hAn]
    exact (hj.isClosed_range.mul_left_of_isCompact (E.isCompact n)).measurableSet
  have hex : ∀ x, ∃ n, x ∈ A n := fun x => ⟨E.find x, hE_A _ (E.mem_find x)⟩
  obtain ⟨N, hNm, hN⟩ : ∃ N : T → ℕ, Measurable N ∧ ∀ x n, N x ≤ n ↔ x ∈ A n := by
    refine ⟨fun x => Nat.find (hex x), measurable_find hex hA_meas, fun x n => ?_⟩
    rw [Nat.find_le_iff]
    exact ⟨fun ⟨m, hm, hx⟩ => hA_mono hm hx, fun hx => ⟨n, le_rfl, hx⟩⟩
  have hN_mem : ∀ x, x ∈ A (N x) := fun x => (hN x _).1 le_rfl
  have hN_mul : ∀ x (s : T'), N (x * j s) = N x := fun x s =>
    le_antisymm ((hN _ _).2 ((hA_mul _ _ _).2 (hN_mem x)))
      ((hN _ _).2 ((hA_mul _ _ _).1 (hN_mem _)))
  obtain ⟨S, hS⟩ : ∃ S : Set T, ∀ x, x ∈ S ↔ x ∈ E (N x + 1) :=
    ⟨{x | x ∈ E (N x + 1)}, fun _ => Iff.rfl⟩
  have hS_meas : MeasurableSet S := by
    have hSU : S = ⋃ n, N ⁻¹' {n} ∩ E (n + 1) := by
      ext x
      rw [hS]
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hx => ⟨_, rfl, hx⟩, by rintro ⟨n, rfl, hx⟩; exact hx⟩
    rw [hSU]
    exact MeasurableSet.iUnion fun n =>
      (hNm (measurableSet_singleton n)).inter (E.isCompact _).isClosed.measurableSet
  obtain ⟨ψ, hψm, hψle, hψS, hψ1⟩ : ∃ ψ : T → ℝ≥0∞, Measurable ψ ∧ (∀ x, ψ x ≤ 1) ∧
      (∀ x, ψ x ≠ 0 → x ∈ S) ∧ (∀ x, x ∈ S → ψ x = 1) := by
    refine ⟨S.indicator fun _ => 1, measurable_const.indicator hS_meas, fun x => ?_,
      fun x hx => ?_, fun x hx => Set.indicator_of_mem hx _⟩
    · by_cases hx : x ∈ S <;> simp [hx]
    · by_contra hxS
      exact hx (by simp [hxS])
  obtain ⟨F, hFm, hF⟩ : ∃ F : T → ℝ≥0∞, Measurable F ∧ ∀ x, F x = ∫⁻ s, ψ (x * j s) ∂ν :=
    ⟨fun x => ∫⁻ s, ψ (x * j s) ∂ν,
      (hψm.comp (measurable_fst.mul (hjm.comp measurable_snd))).lintegral_prod_right',
      fun _ => rfl⟩
  have hF_mul : ∀ x (s : T'), F (x * j s) = F x := by
    intro x s
    rw [hF, hF]
    simpa [mul_assoc] using lintegral_mul_left_eq_self (μ := ν) (fun t => ψ (x * j t)) s
  have hF_pos : ∀ n, ∃ c : ℝ≥0∞, 0 < c ∧ ∀ x, N x = n → c ≤ F x := by
    intro n
    obtain ⟨V, hV, hKV⟩ :=
      compact_open_separated_mul_right (E.isCompact n) isOpen_interior (E.subset_interior_succ n)
    have hVo : IsOpen (j ⁻¹' interior V) := isOpen_interior.preimage hj.continuous
    have hV1 : (1 : T') ∈ j ⁻¹' interior V := by
      simpa using mem_interior_iff_mem_nhds.2 hV
    refine ⟨ν (j ⁻¹' interior V), hVo.measure_pos ν ⟨1, hV1⟩, fun x hx => ?_⟩
    obtain ⟨s₀, hs₀⟩ := (hA n x).1 (hx ▸ hN_mem x)
    calc ν (j ⁻¹' interior V) = ∫⁻ s, (j ⁻¹' interior V).indicator 1 s ∂ν :=
          (lintegral_indicator_one hVo.measurableSet).symm
      _ ≤ ∫⁻ s, ψ (x * j s₀ * j s) ∂ν := by
          refine lintegral_mono fun s => ?_
          by_cases hs : s ∈ j ⁻¹' interior V
          · rw [Set.indicator_of_mem hs, Pi.one_apply, hψ1]
            rw [hS, hN_mul, hN_mul, hx]
            exact interior_subset (hKV (Set.mul_mem_mul hs₀ (interior_subset hs)))
          · simp [hs]
      _ = F x := by rw [← hF, hF_mul]
  choose c hc_pos hc using hF_pos
  have hF_ne : ∀ x, F x ≠ 0 := fun x => ((hc_pos (N x)).trans_le (hc _ x rfl)).ne'
  have hF_fin : ∀ x, F x ≠ ⊤ := by
    intro x
    have hK : IsCompact ((fun s : T' => x * j s) ⁻¹' E (N x + 1)) :=
      ((Homeomorph.mulLeft x).isClosedEmbedding.comp hj).isCompact_preimage (E.isCompact _)
    refine (lt_of_le_of_lt ?_ (hK.measure_lt_top (μ := ν))).ne
    calc F x = ∫⁻ s, ψ (x * j s) ∂ν := hF x
      _ ≤ ∫⁻ s, ((fun s : T' => x * j s) ⁻¹' E (N x + 1)).indicator 1 s ∂ν := by
          refine lintegral_mono fun s => ?_
          by_cases hs : s ∈ (fun s : T' => x * j s) ⁻¹' E (N x + 1)
          · rw [Set.indicator_of_mem hs]
            exact hψle _
          · rw [Set.indicator_of_notMem hs]
            refine le_of_eq (by_contra fun hψs => ?_)
            have hmem := (hS _).1 (hψS _ hψs)
            rw [hN_mul] at hmem
            exact hs hmem
      _ = ν ((fun s : T' => x * j s) ⁻¹' E (N x + 1)) :=
          lintegral_indicator_one hK.isClosed.measurableSet
  refine ⟨fun x => ψ x * (F x)⁻¹, hψm.mul hFm.inv, fun g => ?_, fun K hK => ?_⟩
  · calc ∫⁻ s, ψ (g * j s) * (F (g * j s))⁻¹ ∂ν = ∫⁻ s, ψ (g * j s) * (F g)⁻¹ ∂ν := by
          simp_rw [hF_mul]
      _ = (∫⁻ s, ψ (g * j s) ∂ν) * (F g)⁻¹ :=
          lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (hF_ne g))
      _ = 1 := by rw [← hF, ENNReal.mul_inv_cancel (hF_ne g) (hF_fin g)]
  · obtain ⟨M, hM⟩ := E.exists_superset_of_isCompact hK
    refine ⟨E (M + 1), ∑ n ∈ Finset.range (M + 1), (c n)⁻¹, E.isCompact _,
      ENNReal.sum_lt_top.2 fun n _ => ENNReal.inv_lt_top.2 (hc_pos n), fun k hk s => ⟨?_, ?_⟩⟩
    · have hNk : N k ≤ M := (hN k M).2 (hE_A M (hM hk))
      calc ψ (k * j s) * (F (k * j s))⁻¹ ≤ 1 * (c (N k))⁻¹ :=
            mul_le_mul' (hψle _) (ENNReal.inv_le_inv.2 (hc _ _ (hN_mul k s)))
        _ = (c (N k))⁻¹ := one_mul _
        _ ≤ ∑ n ∈ Finset.range (M + 1), (c n)⁻¹ :=
            Finset.single_le_sum (f := fun n => (c n)⁻¹) (fun _ _ => bot_le)
              (Finset.mem_range.2 (Nat.lt_succ_of_le hNk))
    · intro hne
      have hNk : N k ≤ M := (hN k M).2 (hE_A M (hM hk))
      have hmem := (hS _).1 (hψS _ (left_ne_zero_of_mul hne))
      rw [hN_mul] at hmem
      exact E.subset (Nat.succ_le_succ hNk) hmem

open MeasureTheory in
open scoped ENNReal in

/- English proof (translation)
Take `⟨φ, hφm, hφ, hφK⟩` from `exists_normalized_weight_of_closedEmbedding H.subtype hH.isClosedEmbedding_subtypeVal ν`. Conclude with `⟨φ, hφm, hφ, hφK⟩`.
-/
theorem _root_.GlobalTheory.exists_bruhat_function_closed_subgroup
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
    (hH : IsClosed (H : Set G)) (ν : Measure H) [ν.IsHaarMeasure] :
    ∃ φ : G → ℝ≥0∞, Measurable φ ∧ (∀ g : G, ∫⁻ h : H, φ (g * h) ∂ν = 1) ∧
      ∀ K : Set G, IsCompact K → ∃ (K' : Set G) (C : ℝ≥0∞), IsCompact K' ∧ C < ⊤ ∧
        ∀ k ∈ K, ∀ h : H, φ (k * h) ≤ C ∧ (φ (k * h) ≠ 0 → k * h ∈ K') := by
  obtain ⟨φ, hφm, hφ, hφK⟩ :=
    exists_normalized_weight_of_closedEmbedding H.subtype hH.isClosedEmbedding_subtypeVal ν
  exact ⟨φ, hφm, hφ, hφK⟩

end GlobalTheory
