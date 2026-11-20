import Formalism.GaloisIrreducibility.Statement

namespace Formalism.GaloisIrreducibility

open Classical

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using hx`. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply']`.

Conclude with `hO.1 _ ih`.
-/
lemma orbit_iterate_mem {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O)
    {x : α} (hx : x ∈ O) : ∀ n : ℕ, f^[n] x ∈ O := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hO.1 _ ih

/- English proof (translation)
Apply `Finset.Subset.antisymm` to reduce the goal to its premises. Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.mp hy`. Conclude with `hO.1 x hx`. Introduce `y hy`.

Take `⟨n, hn⟩` from `hO.2 (f y) (hO.1 y hy) y hy`. Rewrite `hn` using `[← Function.iterate_succ_apply, Function.iterate_succ_apply']`. Conclude with `Finset.mem_image.mpr ⟨f^[n] y, orbit_iterate_mem hO hy n, hn⟩`.
-/
lemma orbit_image_eq {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O) :
    O.image f = O := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hO.1 x hx
  · intro y hy
    obtain ⟨n, hn⟩ := hO.2 (f y) (hO.1 y hy) y hy
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply'] at hn
    exact Finset.mem_image.mpr ⟨f^[n] y, orbit_iterate_mem hO hy n, hn⟩

/- English proof (translation)
Establish `hinj : Set.InjOn f O`. Rewrite using `[← Finset.card_image_iff, orbit_image_eq hO]`. Rewrite using `[← Finset.image_val_of_injOn hinj, orbit_image_eq hO]`.
-/
lemma orbit_map_eq {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O) :
    O.val.map f = O.val := by
  have hinj : Set.InjOn f O := by
    rw [← Finset.card_image_iff, orbit_image_eq hO]
  rw [← Finset.image_val_of_injOn hinj, orbit_image_eq hO]

/- English proof (translation)
Rewrite using `[Multiset.le_iff_subset O.nodup]`. Introduce `y hy`. Take `⟨n, rfl⟩` from `hO.2 x hxO y (Finset.mem_val.mp hy)`. Use `clear hy`. Proceed by induction on `n with`.

Consider the case `zero => simpa using hxM`. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply', ← hM]`. Conclude with `Multiset.mem_map_of_mem f ih`.
-/
lemma orbit_le {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O) {M' : Multiset α}
    (hM : M'.map f = M') {x : α} (hxO : x ∈ O) (hxM : x ∈ M') : O.val ≤ M' := by
  rw [Multiset.le_iff_subset O.nodup]
  intro y hy
  obtain ⟨n, rfl⟩ := hO.2 x hxO y (Finset.mem_val.mp hy)
  clear hy
  induction n with
  | zero => simpa using hxM
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← hM]
    exact Multiset.mem_map_of_mem f ih

/- English proof (translation)
Proceed by induction on `I using Finset.strongInduction with`. Consider the case `H I ih`. Introduce `M' hO hle hM`. Distinguish the cases in `h0 : M' = 0`. Conclude with `⟨∅, Finset.empty_subset _, by simp [h0]⟩`.

Take `⟨x, hx⟩` from `Multiset.exists_mem_of_ne_zero h0`. Establish `hxs : x ∈ ∑ i ∈ I, (O i).val` using `Multiset.mem_of_le hle hx`. Rewrite `hxs` using `[Multiset.mem_sum]`. Take `⟨i0, hi0, hxi⟩` from `hxs`. Establish `hle0 : (O i0).val ≤ M'` using `orbit_le (hO i0 hi0) hM (Finset.mem_val.mp hxi) hx`.

Take `⟨M'', rfl⟩ : ∃ M'', M' = (O i0).val + M''` from `⟨M' - (O i0).val, (add_tsub_cancel_of_le hle0).symm⟩`. Establish `hM'' : M''.map f = M''`. Rewrite `hM` using `[Multiset.map_add, orbit_map_eq (hO i0 hi0)]`. Conclude with `add_left_cancel hM`. Establish `hle'' : M'' ≤ ∑ i ∈ I.erase i0, (O i).val`.

Rewrite `hle` using `[← Finset.add_sum_erase I _ hi0]`. Conclude with `(add_le_add_iff_left _).mp hle`. Take `⟨J, hJ, hc⟩` from `ih (I.erase i0) (Finset.erase_ssubset hi0) M'' (fun i hi => hO i (Finset.mem_of_mem_erase hi)) hle'' hM''`. Use `⟨insert i0 J, Finset.insert_subset hi0 (hJ.trans (Finset.erase_subset _ _)), ?_⟩` and prove the remaining obligations. Establish `hnot : i0 ∉ J` using `fun h => by simpa using hJ h`.

Rewrite using `[Finset.sum_insert hnot, Multiset.card_add, hc, Finset.card_val]`.
-/
theorem invariant_multiset_orbit_sum {α ι : Type} (f : α → α) (O : ι → Finset α) (I : Finset ι) :
    ∀ (M' : Multiset α), (∀ i ∈ I, IsOrbit f (O i)) → M' ≤ ∑ i ∈ I, (O i).val →
      M'.map f = M' → ∃ J ⊆ I, M'.card = ∑ i ∈ J, (O i).card := by
  induction I using Finset.strongInduction with
  | H I ih =>
  intro M' hO hle hM
  by_cases h0 : M' = 0
  · exact ⟨∅, Finset.empty_subset _, by simp [h0]⟩
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero h0
  have hxs : x ∈ ∑ i ∈ I, (O i).val := Multiset.mem_of_le hle hx
  rw [Multiset.mem_sum] at hxs
  obtain ⟨i0, hi0, hxi⟩ := hxs
  have hle0 : (O i0).val ≤ M' := orbit_le (hO i0 hi0) hM (Finset.mem_val.mp hxi) hx
  obtain ⟨M'', rfl⟩ : ∃ M'', M' = (O i0).val + M'' :=
    ⟨M' - (O i0).val, (add_tsub_cancel_of_le hle0).symm⟩
  have hM'' : M''.map f = M'' := by
    rw [Multiset.map_add, orbit_map_eq (hO i0 hi0)] at hM
    exact add_left_cancel hM
  have hle'' : M'' ≤ ∑ i ∈ I.erase i0, (O i).val := by
    rw [← Finset.add_sum_erase I _ hi0] at hle
    exact (add_le_add_iff_left _).mp hle
  obtain ⟨J, hJ, hc⟩ := ih (I.erase i0) (Finset.erase_ssubset hi0) M''
    (fun i hi => hO i (Finset.mem_of_mem_erase hi)) hle'' hM''
  refine ⟨insert i0 J, Finset.insert_subset hi0 (hJ.trans (Finset.erase_subset _ _)), ?_⟩
  have hnot : i0 ∉ J := fun h => by simpa using hJ h
  rw [Finset.sum_insert hnot, Multiset.card_add, hc, Finset.card_val]

/- English proof (translation)
Introduce `α ι f O I M' hO hle hM`. Conclude with `invariant_multiset_orbit_sum f O I M' hO hle hM`.
-/
theorem orbit_subset_sum : OrbitSubSum := by
  intro α ι f O I M' hO hle hM
  exact invariant_multiset_orbit_sum f O I M' hO hle hM

end Formalism.GaloisIrreducibility
