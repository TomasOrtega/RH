import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

/- English proof (translation)
Introduce `ι _ E _ d T hmono m c hc`. Unfold `_root_.GlobalTheory.DI.InTot at hc`. Take `⟨h0, hmem, hzero⟩` from `hc`. Establish `hδ0 : _root_.GlobalTheory.DI.delta c ∅ = 0`. Unfold `_root_.GlobalTheory.DI.delta`.

Simplify using the standard rewrite rules. Establish `hδmem : ∀ (q : ℕ) (t : Finset ι), q + t.card = m + 1 → _root_.GlobalTheory.DI.delta c t ∈ T q t`. Introduce `q t hqt`. Unfold `_root_.GlobalTheory.DI.delta`. Use `AddSubgroup.sum_mem _ fun i hi => AddSubgroup.zsmul_mem _ ?_ _` and prove the remaining obligations.

Establish `hcard : (t.erase i).card = t.card - 1` using `Finset.card_erase_of_mem hi`. Establish `hpos : 0 < t.card` using `Finset.card_pos.mpr ⟨i, hi⟩`. Establish `hq : q + (t.erase i).card = m` using `by omega`. Break down `(t.erase i).eq_empty_or_nonempty with he | hne` into its components or cases. Rewrite using `[he, h0]`.

Conclude with `zero_mem _`. Conclude with `hmono q _ _ hne (Finset.erase_subset i t) (hmem q _ hq)`. Establish `hδz : ∀ t : Finset ι, m + 1 < t.card → _root_.GlobalTheory.DI.delta c t = 0`. Introduce `t ht`. Unfold `_root_.GlobalTheory.DI.delta`.

Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Establish `hcard : (t.erase i).card = t.card - 1` using `Finset.card_erase_of_mem hi`. Rewrite using `[hzero _ (by omega), smul_zero]`. Use `⟨⟨hδ0, hδmem, hδz⟩, fun hd => ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Unfold `_root_.GlobalTheory.DI.Dtot`.

Simplify using `[hδ0, h0]`. Introduce `q t hqt`. Unfold `_root_.GlobalTheory.DI.Dtot`. Use `add_mem (hδmem q t hqt) (AddSubgroup.zsmul_mem _ ?_ _)` and prove the remaining obligations. Break down `q with _ | q` into its components or cases.

Rewrite using `[hzero t (by omega), map_zero]; exact zero_mem _`. Conclude with `hd q t _ (hmem q t (by omega))`. Introduce `t ht`. Unfold `_root_.GlobalTheory.DI.Dtot`. Rewrite using `[hδz t ht, hzero t (by omega), map_zero, smul_zero, add_zero]`.
-/
theorem _root_.GlobalTheory.DI.inTot_delta_Dtot : ∀ {ι : Type} [LinearOrder ι] {E : Type}
    [AddCommGroup E] (d : E →+ E)
    (T : ℕ → Finset ι → AddSubgroup E), (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) →
    ∀ m c, _root_.GlobalTheory.DI.InTot T m c → _root_.GlobalTheory.DI.InTot T (m + 1)
        (_root_.GlobalTheory.DI.delta c) ∧
      ((∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) →
        _root_.GlobalTheory.DI.InTot T (m + 1) (_root_.GlobalTheory.DI.Dtot d c)) := by
  intro ι _ E _ d T hmono m c hc
  unfold _root_.GlobalTheory.DI.InTot at hc
  obtain ⟨h0, hmem, hzero⟩ := hc
  have hδ0 : _root_.GlobalTheory.DI.delta c ∅ = 0 := by
    unfold _root_.GlobalTheory.DI.delta; simp
  have hδmem : ∀ (q : ℕ) (t : Finset ι), q + t.card = m + 1 →
      _root_.GlobalTheory.DI.delta c t ∈ T q t := by
    intro q t hqt
    unfold _root_.GlobalTheory.DI.delta
    refine AddSubgroup.sum_mem _ fun i hi => AddSubgroup.zsmul_mem _ ?_ _
    have hcard : (t.erase i).card = t.card - 1 := Finset.card_erase_of_mem hi
    have hpos : 0 < t.card := Finset.card_pos.mpr ⟨i, hi⟩
    have hq : q + (t.erase i).card = m := by omega
    rcases (t.erase i).eq_empty_or_nonempty with he | hne
    · rw [he, h0]; exact zero_mem _
    · exact hmono q _ _ hne (Finset.erase_subset i t) (hmem q _ hq)
  have hδz : ∀ t : Finset ι, m + 1 < t.card → _root_.GlobalTheory.DI.delta c t = 0 := by
    intro t ht
    unfold _root_.GlobalTheory.DI.delta
    refine Finset.sum_eq_zero fun i hi => ?_
    have hcard : (t.erase i).card = t.card - 1 := Finset.card_erase_of_mem hi
    rw [hzero _ (by omega), smul_zero]
  refine ⟨⟨hδ0, hδmem, hδz⟩, fun hd => ⟨?_, ?_, ?_⟩⟩
  · unfold _root_.GlobalTheory.DI.Dtot; simp [hδ0, h0]
  · intro q t hqt
    unfold _root_.GlobalTheory.DI.Dtot
    refine add_mem (hδmem q t hqt) (AddSubgroup.zsmul_mem _ ?_ _)
    rcases q with _ | q
    · rw [hzero t (by omega), map_zero]; exact zero_mem _
    · exact hd q t _ (hmem q t (by omega))
  · intro t ht
    unfold _root_.GlobalTheory.DI.Dtot
    rw [hδz t ht, hzero t (by omega), map_zero, smul_zero, add_zero]

end GlobalTheory.DI
