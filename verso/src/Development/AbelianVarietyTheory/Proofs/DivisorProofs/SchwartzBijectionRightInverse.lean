import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace

open Filter Topology
open scoped SchwartzMap Pointwise

namespace GlobalTheory
namespace FrechetOpenMapping

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul ℂ E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]

/- English proof (translation)
Conclude with `tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)`.
-/
theorem tendsto_inv_nat_complex : Tendsto (fun n : ℕ => ((n : ℂ))⁻¹) atTop (𝓝 0) := by
  exact tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨W, hW, hWU⟩ : ∃ W ∈ 𝓝 (0 : E), ∀ a ∈ W, ∀ b ∈ W, a - b ∈ U := by`. Establish `: Tendsto (fun p : E × E => p.1 - p.2) (𝓝 (0, 0)) (𝓝 0)`. Conclude with `(continuous_fst.sub continuous_snd).tendsto' _ _ (by simp)`. Take `⟨A, hA, B, hB, hAB⟩` from `mem_nhds_prod_iff.1 (this hU)`. Conclude with `⟨A ∩ B, inter_mem hA hB, fun a ha b hb => hAB (Set.mk_mem_prod ha.1 hb.2)⟩`.

Use `set A := closure (T '' W) with hAdef`. Establish `hcov : ⋃ n : ℕ, ((n + 1 : ℕ) : ℂ) • A = Set.univ`. Use `Set.eq_univ_of_forall fun y => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hT y`. Establish `ht : Tendsto (fun n : ℕ => ((n : ℂ))⁻¹ • x) atTop (𝓝 0)`.

Simplify using `using tendsto_inv_nat_complex.smul_const x`. Take `⟨N, hN⟩` from `eventually_atTop.1 (ht hW)`. Establish `hmem` using `hN (N + 1) (Nat.le_succ N)`. Use `Set.mem_iUnion.2 ⟨N, ?_⟩` and prove the remaining obligations. Establish `hne : ((N + 1 : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero N`.

Use `⟨T (((N + 1 : ℕ) : ℂ)⁻¹ • x), subset_closure ⟨_, hmem, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [map_smul, smul_smul, mul_inv_cancel₀ hne, one_smul]`. Establish `hcl : ∀ n : ℕ, IsClosed (((n + 1 : ℕ) : ℂ) • A)` using `fun n => isClosed_closure.smul_of_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)`. Use `haveI : Nonempty F := ⟨0⟩`. Take `⟨n, y, hy⟩` from `nonempty_interior_of_iUnion_of_closed hcl hcov`.

Establish `hne : ((n + 1 : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero n`. Rewrite `hy` using `[interior_smul₀ hne]`. Take `⟨y, hy, -⟩` from `hy`. Establish `hnb : {z : F | y + z ∈ interior A} ∈ 𝓝 (0 : F)`. Establish `hc : Continuous fun z : F => y + z` using `continuous_const.add continuous_id`.

Conclude with `hc.continuousAt.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hy)`. Use `mem_of_superset hnb fun z hz => ?_` and prove the remaining obligations. Establish `h1 : y + z ∈ closure (T '' W)` using `interior_subset hz`. Establish `h2 : y ∈ closure (T '' W)` using `interior_subset hy`. Use `map_mem_closure₂ (f := fun a b : F => a - b) (u := T '' U) (continuous_fst.sub continuous_snd) h1 h2 (by` as an intermediate fact.

Introduce and unpack `_ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩`. Conclude with `⟨a - b, hWU a ha b hb, map_sub T a b⟩)`. Simplify using `using this`.
-/
theorem closure_image_mem_nhds [BaireSpace F] (T : E →L[ℂ] F) (hT : Function.Surjective T)
    {U : Set E} (hU : U ∈ 𝓝 (0 : E)) : closure (T '' U) ∈ 𝓝 (0 : F) := by
  obtain ⟨W, hW, hWU⟩ : ∃ W ∈ 𝓝 (0 : E), ∀ a ∈ W, ∀ b ∈ W, a - b ∈ U := by
    have : Tendsto (fun p : E × E => p.1 - p.2) (𝓝 (0, 0)) (𝓝 0) := by
      exact (continuous_fst.sub continuous_snd).tendsto' _ _ (by simp)
    obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 (this hU)
    exact ⟨A ∩ B, inter_mem hA hB, fun a ha b hb => hAB (Set.mk_mem_prod ha.1 hb.2)⟩
  set A := closure (T '' W) with hAdef
  have hcov : ⋃ n : ℕ, ((n + 1 : ℕ) : ℂ) • A = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨x, rfl⟩ := hT y
    have ht : Tendsto (fun n : ℕ => ((n : ℂ))⁻¹ • x) atTop (𝓝 0) := by
      simpa using tendsto_inv_nat_complex.smul_const x
    obtain ⟨N, hN⟩ := eventually_atTop.1 (ht hW)
    have hmem := hN (N + 1) (Nat.le_succ N)
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    have hne : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    refine ⟨T (((N + 1 : ℕ) : ℂ)⁻¹ • x), subset_closure ⟨_, hmem, rfl⟩, ?_⟩
    simp only [map_smul, smul_smul, mul_inv_cancel₀ hne, one_smul]
  have hcl : ∀ n : ℕ, IsClosed (((n + 1 : ℕ) : ℂ) • A) := fun n =>
    isClosed_closure.smul_of_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)
  haveI : Nonempty F := ⟨0⟩
  obtain ⟨n, y, hy⟩ := nonempty_interior_of_iUnion_of_closed hcl hcov
  have hne : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [interior_smul₀ hne] at hy
  obtain ⟨y, hy, -⟩ := hy
  have hnb : {z : F | y + z ∈ interior A} ∈ 𝓝 (0 : F) := by
    have hc : Continuous fun z : F => y + z := continuous_const.add continuous_id
    exact hc.continuousAt.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hy)
  refine mem_of_superset hnb fun z hz => ?_
  have h1 : y + z ∈ closure (T '' W) := interior_subset hz
  have h2 : y ∈ closure (T '' W) := interior_subset hy
  have := map_mem_closure₂ (f := fun a b : F => a - b) (u := T '' U)
    (continuous_fst.sub continuous_snd) h1 h2 (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact ⟨a - b, hWU a ha b hb, map_sub T a b⟩)
  simpa using this

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro m`. Simplify using `using h0 m`. Consider the case `succ n ih`.

Introduce `m`. Rewrite using `[Finset.sum_eq_sum_Ico_succ_bot (by omega), show m + (n + 1) = m + 1 + n by omega]`. Conclude with `hadd m _ (hx m) _ (ih (m + 1))`.
-/
theorem sum_Ico_mem {U : ℕ → Set E} (h0 : ∀ k, (0 : E) ∈ U k)
    (hadd : ∀ k, ∀ a ∈ U (k + 1), ∀ b ∈ U (k + 1), a + b ∈ U k) {x : ℕ → E}
    (hx : ∀ j, x j ∈ U (j + 1)) : ∀ n m, ∑ j ∈ Finset.Ico m (m + n), x j ∈ U m := by
  intro n
  induction n with
  | zero => intro m; simpa using h0 m
  | succ n ih =>
    intro m
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), show m + (n + 1) = m + 1 + n by omega]
    exact hadd m _ (hx m) _ (ih (m + 1))

/- English proof (translation)
Take `⟨B, hB⟩` from `(𝓝 (0 : E)).exists_antitone_basis`. Set `half : Set E → Set E` to `fun S => if hS : S ∈ 𝓝 (0 : E) then Classical.choose (exists_nhds_zero_half hS) ∩ -Classical.choose (exists_nhds_zero_half hS) else Set.univ`. Establish `hhalf : ∀ S ∈ 𝓝 (0 : E), half S ∈ 𝓝 (0 : E) ∧ (∀ v ∈ half S, ∀ w ∈ half S, v + w ∈ S) ∧ ∀ v ∈ half S, -v ∈ half S`. Introduce `S hS`. Take `⟨h1, h2⟩` from `Classical.choose_spec (exists_nhds_zero_half hS)`.

Simplify using `only [half, dif_pos hS]`. Use `⟨inter_mem h1 (neg_mem_nhds_zero E h1), fun v hv w hw => h2 v hv.1 w hw.1, ?_⟩` and prove the remaining obligations. Introduce and unpack `v ⟨hv1, hv2⟩`. Conclude with `⟨hv2, by simpa using hv1⟩`. Set `U : ℕ → Set E` to `fun n => Nat.rec U₀ (fun k Uk => half Uk ∩ (B k ∩ -B k)) n`.

Establish `hU : ∀ k, U k ∈ 𝓝 (0 : E)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact h`. Consider the case `succ k ih => exact inter_mem (hhalf _ ih).1 (inter_mem (hB.mem k) (neg_mem_nhds_zero E (hB.mem k)))`.

Use `⟨U, rfl, hU, fun k a ha b hb => (hhalf _ (hU k)).2.1 a ha.1 b hb.1, ?_, fun N hN => ?_⟩` and prove the remaining obligations. Introduce and unpack `k a ⟨ha1, ha2, ha3⟩`. Conclude with `⟨(hhalf _ (hU k)).2.2 a ha1, by simpa using ha3, by simpa using ha2⟩`. Take `⟨k, -, hk⟩` from `hB.toHasBasis.mem_iff.1 hN`. Conclude with `⟨k + 1, fun a ha => hk ha.2.1⟩`.
-/
theorem exists_halving [(𝓝 (0 : E)).IsCountablyGenerated] {U₀ : Set E} (h : U₀ ∈ 𝓝 (0 : E)) :
    ∃ U : ℕ → Set E, U 0 = U₀ ∧ (∀ k, U k ∈ 𝓝 (0 : E)) ∧
      (∀ k, ∀ a ∈ U (k + 1), ∀ b ∈ U (k + 1), a + b ∈ U k) ∧
      (∀ k, ∀ a ∈ U (k + 1), -a ∈ U (k + 1)) ∧ ∀ N ∈ 𝓝 (0 : E), ∃ k, U k ⊆ N := by
  classical
  obtain ⟨B, hB⟩ := (𝓝 (0 : E)).exists_antitone_basis
  let half : Set E → Set E := fun S =>
    if hS : S ∈ 𝓝 (0 : E) then Classical.choose (exists_nhds_zero_half hS) ∩
      -Classical.choose (exists_nhds_zero_half hS) else Set.univ
  have hhalf : ∀ S ∈ 𝓝 (0 : E), half S ∈ 𝓝 (0 : E) ∧ (∀ v ∈ half S, ∀ w ∈ half S, v + w ∈ S) ∧
      ∀ v ∈ half S, -v ∈ half S := by
    intro S hS
    obtain ⟨h1, h2⟩ := Classical.choose_spec (exists_nhds_zero_half hS)
    simp only [half, dif_pos hS]
    refine ⟨inter_mem h1 (neg_mem_nhds_zero E h1), fun v hv w hw => h2 v hv.1 w hw.1, ?_⟩
    rintro v ⟨hv1, hv2⟩
    exact ⟨hv2, by simpa using hv1⟩
  let U : ℕ → Set E := fun n => Nat.rec U₀ (fun k Uk => half Uk ∩ (B k ∩ -B k)) n
  have hU : ∀ k, U k ∈ 𝓝 (0 : E) := by
    intro k
    induction k with
    | zero => exact h
    | succ k ih => exact inter_mem (hhalf _ ih).1 (inter_mem (hB.mem k) (neg_mem_nhds_zero E (hB.mem k)))
  refine ⟨U, rfl, hU, fun k a ha b hb => (hhalf _ (hU k)).2.1 a ha.1 b hb.1, ?_, fun N hN => ?_⟩
  · rintro k a ⟨ha1, ha2, ha3⟩
    exact ⟨(hhalf _ (hU k)).2.2 a ha1, by simpa using ha3, by simpa using ha2⟩
  · obtain ⟨k, -, hk⟩ := hB.toHasBasis.mem_iff.1 hN
    exact ⟨k + 1, fun a ha => hk ha.2.1⟩

/- English proof (translation)
Take `⟨U, rfl, hU, hadd, hneg, hbas⟩` from `exists_halving h`. Establish `h0 : ∀ k, (0 : E) ∈ U k` using `fun k => mem_of_mem_nhds (hU k)`. Establish `hanti : ∀ k, U (k + 1) ⊆ U k` using `fun k a ha => by simpa using hadd k a ha 0 (h0 _)`. Establish `hmono : ∀ k l, k ≤ l → U l ⊆ U k`. Introduce `k l hkl`.

Proceed by induction on `hkl with`. Consider the case `refl => exact le_rfl`. Consider the case `step _ ih => exact (hanti _).trans ih`. Set `V : ℕ → Set F` to `fun k => closure (T '' U k)`. Establish `hVn : ∀ k, V k ∈ 𝓝 (0 : F)` using `fun k => closure_image_mem_nhds T hT (hU k)`.

Establish `pick : ∀ k, ∀ r ∈ V k, ∃ x ∈ U k, r - T x ∈ V (k + 1)`. Introduce `k r hr`. Establish `hnb : {w : F | r - w ∈ V (k + 1)} ∈ 𝓝 r`. Establish `hc : Continuous fun w : F => r - w` using `continuous_const.sub continuous_id`. Conclude with `hc.continuousAt.preimage_mem_nhds (by simpa using hVn (k + 1))`.

Take `⟨_, hw, ⟨x, hx, rfl⟩⟩` from `mem_closure_iff_nhds.1 hr _ hnb`. Conclude with `⟨x, hx, hw⟩`. Use `mem_of_superset (hVn 2) fun y hy => ?_` and prove the remaining obligations. Set `step : ℕ → F → E` to `fun k r => if hr : r ∈ V k then Classical.choose (pick k r hr) else 0`. Establish `hstep : ∀ k r, r ∈ V k → step k r ∈ U k ∧ r - T (step k r) ∈ V (k + 1)`.

Introduce `k r hr`. Simplify using `only [step, dif_pos hr]`. Conclude with `Classical.choose_spec (pick k r hr)`. Set `r : ℕ → F` to `fun n => Nat.rec y (fun n rn => rn - T (step (n + 2) rn)) n`. Establish `hr : ∀ n, r n ∈ V (n + 2)`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact hy`. Consider the case `succ n ih => exact (hstep _ _ ih).2`. Set `x : ℕ → E` to `fun n => step (n + 2) (r n)`.

Establish `hx : ∀ n, x n ∈ U (n + 2)` using `fun n => (hstep _ _ (hr n)).1`. Set `s : ℕ → E` to `fun n => ∑ j ∈ Finset.range n, x j`. Establish `hrs : ∀ n, r n = y - T (s n)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp [r, s]`. Consider the case `succ n ih => show r n - T (x n) = _`. Rewrite using `[ih]`. Simplify using `only [s, Finset.sum_range_succ, map_add]`. Normalize the expressions using the abelian group laws.

Establish `htail : ∀ n m, ∑ j ∈ Finset.Ico m (m + n), x j ∈ U (m + 1)` using `sum_Ico_mem (U := fun k => U (k + 1)) (fun k => h0 _) (fun k => hadd (k + 1)) hx`. Establish `hdiff : ∀ m n, m ≤ n → s n - s m ∈ U (m + 1)`. Introduce `m n hmn`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Use `htail d m` as an intermediate fact.

Rewrite `this` using `[Finset.sum_Ico_eq_sub _ hmn]`. Then use the resulting hypothesis. Establish `hs1 : ∀ n, s n ∈ U 1` using `fun n => by simpa [s] using hdiff 0 n (Nat.zero_le n)`. Establish `hcau : CauchySeq s`. Rewrite using `[cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff]`. Introduce `N hN`.

Take `⟨k, hk⟩` from `hbas N hN`. Use `mem_map.2 (mem_atTop_sets.2 ⟨(k, k), fun p hp => hk ?_⟩)` and prove the remaining obligations. Take `⟨hp1, hp2⟩` from `hp`. Use `show s p.2 - s p.1 ∈ U k`. Break down `le_total p.1 p.2 with hle | hle` into its components or cases.

Conclude with `hmono k (p.1 + 1) (by simp at hp1; omega) (hdiff _ _ hle)`. Use `hneg p.2 _ (hdiff _ _ hle)` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Conclude with `hmono k (p.2 + 1) (by simp at hp2; omega) this`. Take `⟨z, hz⟩` from `cauchySeq_tendsto_of_complete hcau`.

Establish `hzU : z ∈ closure (U 1)` using `mem_closure_of_tendsto hz (Eventually.of_forall hs1)`. Establish `hz0 : z ∈ U 0`. Establish `hnb : {q : E | z - q ∈ U 1} ∈ 𝓝 z` using `(continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU 1)`. Take `⟨q, hq, hq1⟩` from `mem_closure_iff_nhds.1 hzU _ hnb`. Simplify using `using hadd 0 _ hq _ hq1`.

Use `⟨z, hz0, ?_⟩` and prove the remaining obligations. Establish `h1 : Tendsto (fun n => T (s n)) atTop (𝓝 (T z))` using `(T.continuous.tendsto z).comp hz`. Establish `h2 : Tendsto r atTop (𝓝 0)`. Introduce `N hN`. Take `⟨N', ⟨hN', hN'c⟩, hN'N⟩` from `(closed_nhds_basis (0 : F)).mem_iff.1 hN`.

Establish `hpre : T ⁻¹' N' ∈ 𝓝 (0 : E)` using `T.continuous.continuousAt.preimage_mem_nhds (by simpa using hN')`. Take `⟨k, hk⟩` from `hbas _ hpre`. Use `mem_map.2 (mem_atTop_sets.2 ⟨k, fun n hn => hN'N ?_⟩)` and prove the remaining obligations. Establish `hsub : V (n + 2) ⊆ N'` using `closure_minimal (by`. Introduce and unpack `_ ⟨a, ha, rfl⟩`.

Conclude with `hk (hmono k (n + 2) (by omega) ha)) hN'c`. Conclude with `hsub (hr n)`. Establish `h3 : Tendsto (fun n => T (s n)) atTop (𝓝 y)`. Use `(tendsto_const_nhds (x := y)).sub h2` as an intermediate fact. Simplify using `only [sub_zero] at this`.

Use `this.congr fun n => ?_` and prove the remaining obligations. Rewrite using `[hrs n]`. Normalize the expressions using the abelian group laws. Conclude with `tendsto_nhds_unique h1 h3`.
-/
theorem image_mem_nhds [CompleteSpace E] [(𝓝 (0 : E)).IsCountablyGenerated] [T2Space F] [BaireSpace F]
    (T : E →L[ℂ] F) (hT : Function.Surjective T) {U₀ : Set E} (h : U₀ ∈ 𝓝 (0 : E)) :
    T '' U₀ ∈ 𝓝 (0 : F) := by
  classical
  obtain ⟨U, rfl, hU, hadd, hneg, hbas⟩ := exists_halving h
  have h0 : ∀ k, (0 : E) ∈ U k := fun k => mem_of_mem_nhds (hU k)
  have hanti : ∀ k, U (k + 1) ⊆ U k := fun k a ha => by simpa using hadd k a ha 0 (h0 _)
  have hmono : ∀ k l, k ≤ l → U l ⊆ U k := by
    intro k l hkl
    induction hkl with
    | refl => exact le_rfl
    | step _ ih => exact (hanti _).trans ih
  let V : ℕ → Set F := fun k => closure (T '' U k)
  have hVn : ∀ k, V k ∈ 𝓝 (0 : F) := fun k => closure_image_mem_nhds T hT (hU k)
  have pick : ∀ k, ∀ r ∈ V k, ∃ x ∈ U k, r - T x ∈ V (k + 1) := by
    intro k r hr
    have hnb : {w : F | r - w ∈ V (k + 1)} ∈ 𝓝 r := by
      have hc : Continuous fun w : F => r - w := continuous_const.sub continuous_id
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hVn (k + 1))
    obtain ⟨_, hw, ⟨x, hx, rfl⟩⟩ := mem_closure_iff_nhds.1 hr _ hnb
    exact ⟨x, hx, hw⟩
  refine mem_of_superset (hVn 2) fun y hy => ?_
  let step : ℕ → F → E := fun k r => if hr : r ∈ V k then Classical.choose (pick k r hr) else 0
  have hstep : ∀ k r, r ∈ V k → step k r ∈ U k ∧ r - T (step k r) ∈ V (k + 1) := by
    intro k r hr
    simp only [step, dif_pos hr]
    exact Classical.choose_spec (pick k r hr)
  let r : ℕ → F := fun n => Nat.rec y (fun n rn => rn - T (step (n + 2) rn)) n
  have hr : ∀ n, r n ∈ V (n + 2) := by
    intro n
    induction n with
    | zero => exact hy
    | succ n ih => exact (hstep _ _ ih).2
  let x : ℕ → E := fun n => step (n + 2) (r n)
  have hx : ∀ n, x n ∈ U (n + 2) := fun n => (hstep _ _ (hr n)).1
  let s : ℕ → E := fun n => ∑ j ∈ Finset.range n, x j
  have hrs : ∀ n, r n = y - T (s n) := by
    intro n
    induction n with
    | zero => simp [r, s]
    | succ n ih =>
      show r n - T (x n) = _
      rw [ih]
      simp only [s, Finset.sum_range_succ, map_add]
      abel
  have htail : ∀ n m, ∑ j ∈ Finset.Ico m (m + n), x j ∈ U (m + 1) :=
    sum_Ico_mem (U := fun k => U (k + 1)) (fun k => h0 _) (fun k => hadd (k + 1)) hx
  have hdiff : ∀ m n, m ≤ n → s n - s m ∈ U (m + 1) := by
    intro m n hmn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have := htail d m
    rwa [Finset.sum_Ico_eq_sub _ hmn] at this
  have hs1 : ∀ n, s n ∈ U 1 := fun n => by simpa [s] using hdiff 0 n (Nat.zero_le n)
  have hcau : CauchySeq s := by
    rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff]
    intro N hN
    obtain ⟨k, hk⟩ := hbas N hN
    refine mem_map.2 (mem_atTop_sets.2 ⟨(k, k), fun p hp => hk ?_⟩)
    obtain ⟨hp1, hp2⟩ := hp
    show s p.2 - s p.1 ∈ U k
    rcases le_total p.1 p.2 with hle | hle
    · exact hmono k (p.1 + 1) (by simp at hp1; omega) (hdiff _ _ hle)
    · have := hneg p.2 _ (hdiff _ _ hle)
      rw [neg_sub] at this
      exact hmono k (p.2 + 1) (by simp at hp2; omega) this
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcau
  have hzU : z ∈ closure (U 1) := mem_closure_of_tendsto hz (Eventually.of_forall hs1)
  have hz0 : z ∈ U 0 := by
    have hnb : {q : E | z - q ∈ U 1} ∈ 𝓝 z :=
      (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU 1)
    obtain ⟨q, hq, hq1⟩ := mem_closure_iff_nhds.1 hzU _ hnb
    simpa using hadd 0 _ hq _ hq1
  refine ⟨z, hz0, ?_⟩
  have h1 : Tendsto (fun n => T (s n)) atTop (𝓝 (T z)) := (T.continuous.tendsto z).comp hz
  have h2 : Tendsto r atTop (𝓝 0) := by
    intro N hN
    obtain ⟨N', ⟨hN', hN'c⟩, hN'N⟩ := (closed_nhds_basis (0 : F)).mem_iff.1 hN
    have hpre : T ⁻¹' N' ∈ 𝓝 (0 : E) :=
      T.continuous.continuousAt.preimage_mem_nhds (by simpa using hN')
    obtain ⟨k, hk⟩ := hbas _ hpre
    refine mem_map.2 (mem_atTop_sets.2 ⟨k, fun n hn => hN'N ?_⟩)
    have hsub : V (n + 2) ⊆ N' := closure_minimal (by
      rintro _ ⟨a, ha, rfl⟩
      exact hk (hmono k (n + 2) (by omega) ha)) hN'c
    exact hsub (hr n)
  have h3 : Tendsto (fun n => T (s n)) atTop (𝓝 y) := by
    have := (tendsto_const_nhds (x := y)).sub h2
    simp only [sub_zero] at this
    refine this.congr fun n => ?_
    rw [hrs n]
    abel
  exact tendsto_nhds_unique h1 h3

/- English proof (translation)
Set `e` to `LinearEquiv.ofBijective (T : E →ₗ[ℂ] F) hT`. Establish `hc : Continuous e.symm`. Use `continuous_of_continuousAt_zero e.symm ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_zero]`. Introduce `U hU`.

Rewrite using `[mem_map]`. Use `mem_of_superset (image_mem_nhds T hT.2 hU) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `show e.symm (e x) ∈ U`. Rewrite using `[e.symm_apply_apply]`.

Conclude with `hx`. Conclude with `⟨⟨e.symm.toLinearMap, hc⟩, fun f => e.apply_symm_apply f⟩`.
-/
theorem exists_inverse [CompleteSpace E] [(𝓝 (0 : E)).IsCountablyGenerated] [T2Space F]
    [BaireSpace F] (T : E →L[ℂ] F) (hT : Function.Bijective T) :
    ∃ S : F →L[ℂ] E, ∀ f, T (S f) = f := by
  let e := LinearEquiv.ofBijective (T : E →ₗ[ℂ] F) hT
  have hc : Continuous e.symm := by
    refine continuous_of_continuousAt_zero e.symm ?_
    rw [ContinuousAt, map_zero]
    intro U hU
    rw [mem_map]
    refine mem_of_superset (image_mem_nhds T hT.2 hU) ?_
    rintro _ ⟨x, hx, rfl⟩
    show e.symm (e x) ∈ U
    rw [e.symm_apply_apply]
    exact hx
  exact ⟨⟨e.symm.toLinearMap, hc⟩, fun f => e.apply_symm_apply f⟩

/- English proof (translation)
Use `haveI := IsUniformAddGroup.uniformity_countably_generated (α := X)`. Use `letI := UniformSpace.pseudoMetricSpace X`. Use `infer_instance`.
-/
theorem baireSpace_of_complete (X : Type*) [UniformSpace X] [AddGroup X] [IsUniformAddGroup X]
    [(𝓝 (0 : X)).IsCountablyGenerated] [CompleteSpace X] : BaireSpace X := by
  haveI := IsUniformAddGroup.uniformity_countably_generated (α := X)
  letI := UniformSpace.pseudoMetricSpace X
  infer_instance

/- English proof (translation)
Introduce `V W _ _ _ _ T hT`. Use `haveI : BaireSpace (SchwartzMap W ℂ) := baireSpace_of_complete _`. Conclude with `exists_inverse T hT`.
-/
theorem schwartz_exists_inverse : ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap W ℂ),
    Function.Bijective T → ∃ S : SchwartzMap W ℂ →L[ℂ] SchwartzMap V ℂ, ∀ f, T (S f) = f := by
  intro V W _ _ _ _ T hT
  haveI : BaireSpace (SchwartzMap W ℂ) := baireSpace_of_complete _
  exact exists_inverse T hT

end FrechetOpenMapping
end GlobalTheory
