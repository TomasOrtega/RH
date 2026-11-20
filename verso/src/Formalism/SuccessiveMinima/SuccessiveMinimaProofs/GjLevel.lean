import Formalism.SuccessiveMinima.DefsMink

open MeasureTheory Set
open scoped Pointwise ENNReal

noncomputable section

namespace Formalism.FN

/- English proof (translation)
Establish `h : boxJ n j = ⋂ i : Fin n, ⋂ (_ : (i : ℕ) < j), ({u : Fin n → ℝ | 0 ≤ u i} ∩ {u | u i < 1})`. Use extensionality with `u`. Simplify using `[boxJ]`. Rewrite using `[h]`. Conclude with `MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => (measurableSet_le measurable_const (measurable_pi_apply i)).inter (measurableSet_lt (measurable_pi_apply i) measurable_const)`.
-/
lemma measurableSet_boxJ (n j : ℕ) : MeasurableSet (boxJ n j) := by
  have h : boxJ n j = ⋂ i : Fin n, ⋂ (_ : (i : ℕ) < j),
      ({u : Fin n → ℝ | 0 ≤ u i} ∩ {u | u i < 1}) := by
    ext u; simp [boxJ]
  rw [h]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    (measurableSet_le measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const)

/- English proof (translation)
Introduce `n j A hj hA hinj`. Take `⟨jj, hjj⟩ : ∃ jj : Fin n, (jj : ℕ) = j` from `⟨⟨j, hj⟩, rfl⟩`. Set `ej : Fin n → ℝ` to `Pi.single jj 1`. Establish `ej_apply : ∀ i, ej i = if i = jj then 1 else 0` using `fun i => by simp [ej, Pi.single_apply]`. Establish `hcoord : ∀ (y : Fin n → ℝ) (m : ℤ) (i : Fin n), (y + (m : ℝ) • ej) i = if i = jj then y i + m else y i`.

Introduce `y m i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, ej_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> ring`. Set `S : Set (Fin n → ℝ)` to `boxJ n j ∩ (A + latJ n j)`. Set `P : ℤ → Set (Fin n → ℝ)` to `fun m => S ∩ {x | ⌊x jj⌋ = m}`.

Set `Q : ℤ → Set (Fin n → ℝ)` to `fun m => (fun y => y + (m : ℝ) • ej) ⁻¹' P m`. Establish `hSm : MeasurableSet S` using `(measurableSet_boxJ n j).inter (hA.add_right (t := latJ n j)).measurableSet`. Establish `hPm : ∀ m, MeasurableSet (P m)` using `fun m => hSm.inter ((Int.measurable_floor.comp (measurable_pi_apply jj)) (measurableSet_singleton m))`. Establish `hQm : ∀ m, MeasurableSet (Q m)` using `fun m => (measurable_id.add_const _) (hPm m)`. Establish `hvol : ∀ m, volume (Q m) = volume (P m)` using `fun m => measure_preimage_add_right volume _ (P m)`.

Establish `hsub : ∀ m, Q m ⊆ boxJ n (j + 1) ∩ (A + latJ n (j + 1))`. Introduce `m y hy`. Take `⟨⟨hbox, hAk⟩, hfl⟩` from `hy`. Establish `hfl' : ⌊(y + (m : ℝ) • ej) jj⌋ = m` using `hfl`. Rewrite `hfl'` using `[hcoord, if_pos rfl, Int.floor_add_intCast]`.

Establish `h0 : ⌊y jj⌋ = 0` using `by omega`. Establish `hyj` using `Int.floor_eq_zero_iff.1 h0`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Distinguish the cases in `hij : i = jj`.

Substitute `hij` using the available equality. Conclude with `⟨hyj.1, hyj.2⟩`. Establish `hlt : (i : ℕ) < j` using `lt_of_le_of_ne (Nat.lt_succ_iff.1 hi) (fun h => hij (Fin.ext (h.trans hjj.symm)))`. Establish `hb : 0 ≤ (y + (m : ℝ) • ej) i ∧ (y + (m : ℝ) • ej) i < 1` using `hbox i hlt`. Rewrite `hb` using `[hcoord, if_neg hij]`.

Conclude with `hb`. Take `⟨a, ha, k, hk, hak0⟩` from `hAk`. Establish `hak : a + k = y + (m : ℝ) • ej` using `hak0`. Use `Set.mem_add.2 ⟨a, ha, k - (m : ℝ) • ej, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `i`.

Take `⟨z, hz⟩` from `hk.1 i`. Use `⟨z - (if i = jj then m else 0), ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.sub_apply, Pi.smul_apply, ej_apply, smul_eq_mul, hz]`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`. Introduce `i hi`.

Establish `hne : i ≠ jj` using `fun h => by rw [h, hjj] at hi; omega`. Simplify using `[hk.2 i (by omega), ej_apply, hne]`. Rewrite using `[← add_sub_assoc, hak, add_sub_cancel_right]`. Establish `hdisj : Pairwise (Function.onFun Disjoint Q)`. Introduce `m m' hmm'`.

Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce `y hy hy'`. Take `⟨⟨_, hAk⟩, _⟩` from `hy`. Take `⟨⟨_, hAk'⟩, _⟩` from `hy'`. Take `⟨a, ha, k, hk, hak0⟩` from `hAk`.

Take `⟨a', ha', k', hk', hak0'⟩` from `hAk'`. Establish `hak : a + k = y + (m : ℝ) • ej` using `hak0`. Establish `hak' : a' + k' = y + (m' : ℝ) • ej` using `hak0'`. Establish `hint : ∀ i, ∃ z : ℤ, a i - a' i = z`. Introduce `i`.

Take `⟨z, hz⟩` from `hk.1 i`. Take `⟨z', hz'⟩` from `hk'.1 i`. Establish `e1` using `congrFun hak i`. Establish `e2` using `congrFun hak' i`. Rewrite `e1`, `e2` using `[Pi.add_apply, hcoord]`.

Use `split_ifs at e1 e2`. Conclude with `⟨m - m' - z + z', by push_cast; linarith⟩`. Conclude with `⟨-z + z', by push_cast; linarith⟩`. Establish `hjeq` using `hinj a ha a' ha' hint jj hjj.ge`. Establish `hk0 : k jj = 0` using `hk.2 jj hjj.ge`.

Establish `hk0' : k' jj = 0` using `hk'.2 jj hjj.ge`. Establish `e1` using `congrFun hak jj`. Establish `e2` using `congrFun hak' jj`. Rewrite `e1` using `[Pi.add_apply, hcoord, if_pos rfl, hk0, add_zero]`. Rewrite `e2` using `[Pi.add_apply, hcoord, if_pos rfl, hk0', add_zero]`.

Apply `hmm'` to reduce the goal to its premises. Conclude with `(by linarith : (m : ℝ) = m')` after adjusting the coercions. Establish `hcover : S ⊆ ⋃ m : ℤ, P m` using `fun x hx => Set.mem_iUnion.2 ⟨⌊x jj⌋, hx, rfl⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem partialBoxVolumeMonotoneStep : GjLevel := by
  intro n j A hj hA hinj
  obtain ⟨jj, hjj⟩ : ∃ jj : Fin n, (jj : ℕ) = j := ⟨⟨j, hj⟩, rfl⟩
  let ej : Fin n → ℝ := Pi.single jj 1
  have ej_apply : ∀ i, ej i = if i = jj then 1 else 0 := fun i => by simp [ej, Pi.single_apply]
  have hcoord : ∀ (y : Fin n → ℝ) (m : ℤ) (i : Fin n),
      (y + (m : ℝ) • ej) i = if i = jj then y i + m else y i := by
    intro y m i
    simp only [Pi.add_apply, Pi.smul_apply, ej_apply, smul_eq_mul]
    split_ifs <;> ring

  let S : Set (Fin n → ℝ) := boxJ n j ∩ (A + latJ n j)
  let P : ℤ → Set (Fin n → ℝ) := fun m => S ∩ {x | ⌊x jj⌋ = m}
  let Q : ℤ → Set (Fin n → ℝ) := fun m => (fun y => y + (m : ℝ) • ej) ⁻¹' P m
  have hSm : MeasurableSet S := (measurableSet_boxJ n j).inter (hA.add_right (t := latJ n j)).measurableSet
  have hPm : ∀ m, MeasurableSet (P m) := fun m =>
    hSm.inter ((Int.measurable_floor.comp (measurable_pi_apply jj)) (measurableSet_singleton m))
  have hQm : ∀ m, MeasurableSet (Q m) := fun m => (measurable_id.add_const _) (hPm m)
  have hvol : ∀ m, volume (Q m) = volume (P m) := fun m =>
    measure_preimage_add_right volume _ (P m)
  have hsub : ∀ m, Q m ⊆ boxJ n (j + 1) ∩ (A + latJ n (j + 1)) := by
    intro m y hy
    obtain ⟨⟨hbox, hAk⟩, hfl⟩ := hy
    have hfl' : ⌊(y + (m : ℝ) • ej) jj⌋ = m := hfl
    rw [hcoord, if_pos rfl, Int.floor_add_intCast] at hfl'
    have h0 : ⌊y jj⌋ = 0 := by omega
    have hyj := Int.floor_eq_zero_iff.1 h0
    refine ⟨?_, ?_⟩
    · intro i hi
      by_cases hij : i = jj
      · subst hij; exact ⟨hyj.1, hyj.2⟩
      · have hlt : (i : ℕ) < j :=
          lt_of_le_of_ne (Nat.lt_succ_iff.1 hi) (fun h => hij (Fin.ext (h.trans hjj.symm)))
        have hb : 0 ≤ (y + (m : ℝ) • ej) i ∧ (y + (m : ℝ) • ej) i < 1 := hbox i hlt
        rw [hcoord, if_neg hij] at hb
        exact hb
    · obtain ⟨a, ha, k, hk, hak0⟩ := hAk
      have hak : a + k = y + (m : ℝ) • ej := hak0
      refine Set.mem_add.2 ⟨a, ha, k - (m : ℝ) • ej, ⟨?_, ?_⟩, ?_⟩
      · intro i
        obtain ⟨z, hz⟩ := hk.1 i
        refine ⟨z - (if i = jj then m else 0), ?_⟩
        simp only [Pi.sub_apply, Pi.smul_apply, ej_apply, smul_eq_mul, hz]
        split_ifs <;> push_cast <;> ring
      · intro i hi
        have hne : i ≠ jj := fun h => by rw [h, hjj] at hi; omega
        simp [hk.2 i (by omega), ej_apply, hne]
      · rw [← add_sub_assoc, hak, add_sub_cancel_right]
  have hdisj : Pairwise (Function.onFun Disjoint Q) := by
    intro m m' hmm'
    rw [Function.onFun, Set.disjoint_left]
    intro y hy hy'
    obtain ⟨⟨_, hAk⟩, _⟩ := hy
    obtain ⟨⟨_, hAk'⟩, _⟩ := hy'
    obtain ⟨a, ha, k, hk, hak0⟩ := hAk
    obtain ⟨a', ha', k', hk', hak0'⟩ := hAk'
    have hak : a + k = y + (m : ℝ) • ej := hak0
    have hak' : a' + k' = y + (m' : ℝ) • ej := hak0'
    have hint : ∀ i, ∃ z : ℤ, a i - a' i = z := by
      intro i
      obtain ⟨z, hz⟩ := hk.1 i
      obtain ⟨z', hz'⟩ := hk'.1 i
      have e1 := congrFun hak i
      have e2 := congrFun hak' i
      rw [Pi.add_apply, hcoord] at e1 e2
      split_ifs at e1 e2
      · exact ⟨m - m' - z + z', by push_cast; linarith⟩
      · exact ⟨-z + z', by push_cast; linarith⟩
    have hjeq := hinj a ha a' ha' hint jj hjj.ge
    have hk0 : k jj = 0 := hk.2 jj hjj.ge
    have hk0' : k' jj = 0 := hk'.2 jj hjj.ge
    have e1 := congrFun hak jj
    have e2 := congrFun hak' jj
    rw [Pi.add_apply, hcoord, if_pos rfl, hk0, add_zero] at e1
    rw [Pi.add_apply, hcoord, if_pos rfl, hk0', add_zero] at e2
    apply hmm'
    exact_mod_cast (by linarith : (m : ℝ) = m')
  have hcover : S ⊆ ⋃ m : ℤ, P m := fun x hx => Set.mem_iUnion.2 ⟨⌊x jj⌋, hx, rfl⟩
  calc Gj n j A = volume S := rfl
    _ ≤ volume (⋃ m : ℤ, P m) := measure_mono hcover
    _ ≤ ∑' m, volume (P m) := measure_iUnion_le _
    _ = ∑' m, volume (Q m) := tsum_congr fun m => (hvol m).symm
    _ = volume (⋃ m, Q m) := (measure_iUnion hdisj hQm).symm
    _ ≤ volume (boxJ n (j + 1) ∩ (A + latJ n (j + 1))) := measure_mono (Set.iUnion_subset hsub)
    _ = Gj n (j + 1) A := rfl

end Formalism.FN
