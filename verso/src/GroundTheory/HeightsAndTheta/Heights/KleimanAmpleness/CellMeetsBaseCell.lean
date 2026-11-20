import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreLast
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerBis
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraBis
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

variable {S : Type} [CommRing S] {K : Type} {ι : K → Type} {Ω : Type} [Field Ω] [Algebra S Ω]

/- English proof (translation)
Unfold `cellSec`. Rewrite using `[if_pos hI']`. Use `split_ifs with hI`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `z ⟨g, t, a, ht, hta, hγ, hg, rfl⟩`.

Use `⟨g, t, a, ?_, hta, hγ, hg, rfl⟩` and prove the remaining obligations. Use `Submonoid.closure_mono ?_ ht` and prove the remaining obligations. Introduce and unpack `f ⟨k, i, hi, rfl⟩`. Conclude with `⟨k, i, h k hi, rfl⟩`. Conclude with `bot_le`.
-/
theorem cellSec_mono [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (γ : K → ℤ) {I I' : ∀ k, Finset (ι k)} (h : ∀ k, I k ⊆ I' k)
    (hI' : CellMeets y I') : cellSec S y γ I ≤ cellSec S y γ I' := by
  classical
  unfold cellSec
  rw [if_pos hI']
  split_ifs with hI
  · refine Submodule.span_mono ?_
    rintro z ⟨g, t, a, ht, hta, hγ, hg, rfl⟩
    refine ⟨g, t, a, ?_, hta, hγ, hg, rfl⟩
    refine Submonoid.closure_mono ?_ ht
    rintro f ⟨k, i, hi, rfl⟩
    exact ⟨k, i, h k hi, rfl⟩
  · exact bot_le

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

/- English proof (translation)
Unfold `baseCell`. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `Finset.subset_union_left`.

Rewrite using `[Function.update_of_ne hk]`.
-/
theorem subset_baseCell (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (J : Finset (Fin (N + 1)))
    (I : ∀ k, Finset (ι k)) (k : K) : I k ⊆ baseCell k₀ e J I k := by
  unfold baseCell
  by_cases hk : k = k₀
  · subst hk; rw [Function.update_self]; exact Finset.subset_union_left
  · rw [Function.update_of_ne hk]

/- English proof (translation)
Unfold `baseCell`. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Rewrite using `[Function.update_self, Function.update_self]`. Conclude with `Finset.union_subset_union (hI k) (Finset.map_subset_map.mpr hJ)`.

Rewrite using `[Function.update_of_ne hk, Function.update_of_ne hk]`. Conclude with `hI k`.
-/
theorem baseCell_mono (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {J J' : Finset (Fin (N + 1))}
    {I I' : ∀ k, Finset (ι k)} (hJ : J ⊆ J') (hI : ∀ k, I k ⊆ I' k) (k : K) :
    baseCell k₀ e J I k ⊆ baseCell k₀ e J' I' k := by
  unfold baseCell
  by_cases hk : k = k₀
  · subst hk; rw [Function.update_self, Function.update_self]
    exact Finset.union_subset_union (hI k) (Finset.map_subset_map.mpr hJ)
  · rw [Function.update_of_ne hk, Function.update_of_ne hk]; exact hI k

/- English proof (translation)
Introduce `k i hi`. Unfold `baseCell at hi`. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Rewrite `hi` using `[Function.update_self, Finset.mem_union]`.

Break down `hi with hi | hi` into its components or cases. Conclude with `hI k i hi`. Take `⟨j, hj, rfl⟩` from `Finset.mem_map.mp hi`. Conclude with `(Kleiman.mem_support _).mp (J.2.2 hj)`. Rewrite `hi` using `[Function.update_of_ne hk]`.

Conclude with `hI k i hi`.
-/
theorem cellMeets_baseCell (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) {I : ∀ k, Finset (ι k)} (hI : CellMeets y I) :
    CellMeets y (baseCell k₀ e J.1 I) := by
  intro k i hi
  unfold baseCell at hi
  by_cases hk : k = k₀
  · subst hk
    rw [Function.update_self, Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact hI k i hi
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      exact (Kleiman.mem_support _).mp (J.2.2 hj)
  · rw [Function.update_of_ne hk] at hi; exact hI k i hi

/- English proof (translation)
Introduce `F _ K _ _ ι _ _ Ω _ _ y k₀ N e hM γ T hT n`. Establish `hM0 : ∀ (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) I, ¬ CellMeets y I → cellSec F y γ (baseCell k₀ e J.1 I) = ⊥` using `fun J I hI => by`. Unfold `cellSec`. Rewrite using `[if_neg fun h => hI fun k i hi => h k i (subset_baseCell k₀ e J.1 I k hi)]`. Establish `hMJ : ∀ (J J' : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) I, J.1 ⊆ J'.1 → cellSec F y γ (baseCell k₀ e J.1 I) ≤ cellSec F y γ (baseCell k₀ e J'.1 I)` using `fun J J' I h => by`.

Distinguish the cases in `hI : CellMeets y I`. Conclude with `cellSec_mono y γ (baseCell_mono k₀ e h fun _ => subset_rfl) (cellMeets_baseCell y k₀ e J' hI)`. Rewrite using `[hM0 J I hI]`. Conclude with `bot_le`. Use `(hD F K ι Ω y N _ T (cellSec F y γ) (fun J I => cellSec F y γ (baseCell k₀ e J.1 I)) hM.1 ?_ (fun I hI => by unfold cellSec; rw [if_neg hI]) hM0 hMJ (fun J I I' h hI' => cellSec_mono y γ (baseCell_mono k₀ e subset_rfl h) (cellMeets_baseCell y k₀ e J hI')) ?_ ?_ n)` and prove the remaining obligations.

Take `⟨i, hi⟩` from `hM.1 k₀`. Conclude with `⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩`. Introduce `I hne hI`. Take `⟨i, hi⟩` from `hne k₀`. Establish `hx : (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (e i) ≠ 0`.

Simplify `hI k₀ i hi` using `[IndefiniteRowSideFullHecke.Kleiman2.blockVec]`. Set `J₀ : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)` to `⟨{e i}, Finset.singleton_nonempty _, Finset.singleton_subset_iff.mpr ((Kleiman.mem_support _).mpr hx)⟩`. Establish `hadd : ∀ J : Finset (Fin (N + 1)), baseCell k₀ e ({e i} ∪ J) I = baseCell k₀ e J I`. Introduce `J`. Unfold `baseCell`.

Use `congr 1`. Rewrite using `[Finset.map_union, ← Finset.union_assoc, Finset.map_singleton]`. Use `congr 1`. Conclude with `Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr (by simpa using hi))`. Establish `h₀ : baseCell k₀ e J₀.1 I = I`.

Use `hadd ∅` as an intermediate fact. Rewrite `this` using `[Finset.union_empty]`. Rewrite using `[show J₀.1 = {e i} from rfl, this]`. Unfold `baseCell`. Simplify using the standard rewrite rules.

Use `hC F Ω N _ (fun J => cellSec F y γ (baseCell k₀ e J.1 I)) J₀ (Finset.card_singleton _) (fun J J' h => hMJ J J' I h) (fun J J' h => by show cellSec F y γ (baseCell k₀ e J'.1 I) = _` as an intermediate fact. Rewrite using `[h]`. Conclude with `congrArg _ (hadd J.1))`. Simplify `this` using `only [h₀]`. Introduce `J`.

Establish `h` using `hR F K ι Ω y k₀ N e hM γ J`. Rewrite `h` using `[← hT J, ← Submodule.coe_restrictScalars F, Submodule.span_eq]`. Then use the resulting hypothesis.
-/
theorem ModelCechRefine.proof (hC : CechContract.Statement) (hR : ModelRowExact.Statement)
    (hD : DoubleCech.Statement) : ModelCechRefine.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ N e hM γ T hT n
  have hM0 : ∀ (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) I, ¬ CellMeets y I →
      cellSec F y γ (baseCell k₀ e J.1 I) = ⊥ := fun J I hI => by
    unfold cellSec
    rw [if_neg fun h => hI fun k i hi => h k i (subset_baseCell k₀ e J.1 I k hi)]
  have hMJ : ∀ (J J' : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) I, J.1 ⊆ J'.1 →
      cellSec F y γ (baseCell k₀ e J.1 I) ≤ cellSec F y γ (baseCell k₀ e J'.1 I) := fun J J' I h => by
    by_cases hI : CellMeets y I
    · exact cellSec_mono y γ (baseCell_mono k₀ e h fun _ => subset_rfl) (cellMeets_baseCell y k₀ e J' hI)
    · rw [hM0 J I hI]; exact bot_le
  refine (hD F K ι Ω y N _ T (cellSec F y γ) (fun J I => cellSec F y γ (baseCell k₀ e J.1 I)) hM.1 ?_
    (fun I hI => by unfold cellSec; rw [if_neg hI]) hM0 hMJ
    (fun J I I' h hI' => cellSec_mono y γ (baseCell_mono k₀ e subset_rfl h) (cellMeets_baseCell y k₀ e J hI'))
    ?_ ?_ n)
  · obtain ⟨i, hi⟩ := hM.1 k₀
    exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
  · intro I hne hI
    obtain ⟨i, hi⟩ := hne k₀
    have hx : (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (e i) ≠ 0 := by
      simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hI k₀ i hi
    let J₀ : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) :=
      ⟨{e i}, Finset.singleton_nonempty _, Finset.singleton_subset_iff.mpr ((Kleiman.mem_support _).mpr hx)⟩
    have hadd : ∀ J : Finset (Fin (N + 1)), baseCell k₀ e ({e i} ∪ J) I = baseCell k₀ e J I := by
      intro J
      unfold baseCell
      congr 1
      rw [Finset.map_union, ← Finset.union_assoc, Finset.map_singleton]
      congr 1
      exact Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr (by simpa using hi))
    have h₀ : baseCell k₀ e J₀.1 I = I := by
      have := hadd ∅
      rw [Finset.union_empty] at this
      rw [show J₀.1 = {e i} from rfl, this]
      unfold baseCell
      simp
    have := hC F Ω N _ (fun J => cellSec F y γ (baseCell k₀ e J.1 I)) J₀ (Finset.card_singleton _)
      (fun J J' h => hMJ J J' I h) (fun J J' h => by
        show cellSec F y γ (baseCell k₀ e J'.1 I) = _
        rw [h]; exact congrArg _ (hadd J.1))
    simpa only [h₀] using this
  · intro J
    have h := hR F K ι Ω y k₀ N e hM γ J
    rwa [← hT J, ← Submodule.coe_restrictScalars F, Submodule.span_eq] at h

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
