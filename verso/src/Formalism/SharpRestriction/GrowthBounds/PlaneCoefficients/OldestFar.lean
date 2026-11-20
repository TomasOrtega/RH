import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.ValSCongrSupp

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks.Ar

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Geo

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ}

/- English proof (translation)
Use `set s := (Fr.LLset j).sort (· ≤ ·) with hs`. Establish `hlen : s.length = (Fr.LLset j).card` using `Finset.length_sort _`. Establish `hpw : s.Pairwise (· ≤ ·)` using `Finset.pairwise_sort _ _`. Establish `hnd : s.Nodup` using `Finset.sort_nodup _ _`. Establish `hl' : l < s.length` using `by omega`.

Establish `hget : llPos Fr j l = s[l]`. Unfold `llPos`. Rewrite using `[← hs, List.getD_eq_getElem _ _ hl']`. Establish `hsub : (Fr.LLset j).filter (· ≤ llPos Fr j l) ⊆ (s.take (l + 1)).toFinset`. Introduce `x hx`.

Rewrite `hx` using `[Finset.mem_filter]`. Establish `hxs : x ∈ s` using `by rw [hs, Finset.mem_sort]; exact hx.1`. Take `⟨k, hk, rfl⟩` from `List.getElem_of_mem hxs`. Rewrite using `[List.mem_toFinset]`. Establish `hkl : k ≤ l`.

Assume the negation of the conclusion as `hc`. Establish `h1 : s[l] ≤ s[k]` using `List.pairwise_iff_getElem.mp hpw l k hl' hk (by omega)`. Establish `h2 : s[k] ≤ s[l]` using `by rw [← hget]; exact hx.2`. Establish `h3 : s[k] = s[l]` using `le_antisymm h2 h1`. Use `(List.Nodup.getElem_inj_iff hnd).mp h3` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[List.mem_iff_getElem]`. Conclude with `⟨k, by simp; omega, by simp⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem filt_card (j : ℤ) (l : ℕ) (_hl : l < (Fr.LLset j).card) :
    ((Fr.LLset j).filter (· ≤ llPos Fr j l)).card ≤ l + 1 := by
  classical
  set s := (Fr.LLset j).sort (· ≤ ·) with hs
  have hlen : s.length = (Fr.LLset j).card := Finset.length_sort _
  have hpw : s.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hnd : s.Nodup := Finset.sort_nodup _ _
  have hl' : l < s.length := by omega
  have hget : llPos Fr j l = s[l] := by
    unfold llPos
    rw [← hs, List.getD_eq_getElem _ _ hl']
  have hsub : (Fr.LLset j).filter (· ≤ llPos Fr j l) ⊆ (s.take (l + 1)).toFinset := by
    intro x hx
    rw [Finset.mem_filter] at hx
    have hxs : x ∈ s := by rw [hs, Finset.mem_sort]; exact hx.1
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hxs
    rw [List.mem_toFinset]
    have hkl : k ≤ l := by
      by_contra hc
      have h1 : s[l] ≤ s[k] := List.pairwise_iff_getElem.mp hpw l k hl' hk (by omega)
      have h2 : s[k] ≤ s[l] := by rw [← hget]; exact hx.2
      have h3 : s[k] = s[l] := le_antisymm h2 h1
      have := (List.Nodup.getElem_inj_iff hnd).mp h3
      omega
    rw [List.mem_iff_getElem]
    exact ⟨k, by simp; omega, by simp⟩
  calc ((Fr.LLset j).filter (· ≤ llPos Fr j l)).card ≤ (s.take (l + 1)).toFinset.card :=
        Finset.card_le_card hsub
    _ ≤ (s.take (l + 1)).length := List.toFinset_card_le _
    _ ≤ l + 1 := by simp

/- English proof (translation)
Take `⟨-, -, hinc, hsep, hmem, -, hLL, -, -⟩` from `hV`. Establish `hcard : 0 < (Fr.LLset j).card` using `by have := (hLL j).1; omega`. Establish `hx : llPos Fr j 0 ∈ Fr.LLset j`. Unfold `llPos`. Rewrite using `[List.getD_eq_getElem _ _ (by rw [Finset.length_sort]; exact hcard)]`.

Conclude with `(Finset.mem_sort _).mp (List.getElem_mem _)`. Establish `hf` using `filt_card (Fr := Fr) j 0 hcard`. Establish `hmin : ∀ z ∈ Fr.LLset j, ¬ z < llPos Fr j 0`. Introduce `z hz hzx`. Establish `hsub : ({z, llPos Fr j 0} : Finset ℤ) ⊆ (Fr.LLset j).filter (· ≤ llPos Fr j 0)`.

Introduce `w hw`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hw`. Break down `hw with rfl | rfl` into its components or cases. Conclude with `Finset.mem_filter.mpr ⟨hz, hzx.le⟩`. Conclude with `Finset.mem_filter.mpr ⟨hx, le_rfl⟩`.

Establish `h2` using `Finset.card_le_card hsub`. Rewrite `h2` using `[Finset.card_pair hzx.ne]`. Use linear arithmetic over natural numbers and integers. Establish `hgap` using `((hLL j).2.1 _ hx (Or.inl (le_trans hf (by omega)))).2`. Establish `hmono : ∀ k : ℤ, ∀ i, i < r → Fr.fr k 0 ≤ Fr.fr k i`.

Introduce `k i`. Proceed by induction on `i with`. Consider the case `zero => intro _`. Conclude with `le_rfl`. Consider the case `succ i ih => intro hi; exact (ih (by omega)).trans (hinc k i hi).le`.

Establish `hxI` using `hx`. Unfold `Frames.LLset at hxI`. Rewrite `hxI` using `[Finset.mem_filter, Finset.mem_Ioo]`. Establish `hsep' : Fr.fr (j - 1) (r - 1) < Fr.fr j 0`. Establish `h` using `hsep (j - 1)`.

Rewrite `h` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `hyl : Fr.fr (j - 1) (r - 1) ∈ Fr.letters j`. Unfold `Frames.letters`. Rewrite using `[Finset.mem_filter, Finset.mem_Icc]`. Conclude with `⟨⟨hmono _ _ (by omega), hsep'.le.trans (hmono _ _ (by omega))⟩, (hmem (j - 1) (r - 1) (by omega)).1⟩`.

Establish `hfin` using `hgap _ hyl hxI.1.1 ?_`. Use linear arithmetic over natural numbers and integers. Introduce `z hz hzx`. Assume the negation of the conclusion as `hzy`. Use `push_neg at hzy`.

Unfold `Frames.letters at hz`. Rewrite `hz` using `[Finset.mem_filter, Finset.mem_Icc]`. Apply `hmin z _ hzx` to reduce the goal to its premises. Unfold `Frames.LLset`. Rewrite using `[Finset.mem_filter, Finset.mem_Ioo]`.

Conclude with `⟨⟨hzy, hzx.trans hxI.1.2⟩, hz.2⟩`.
-/
theorem first_gap (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) : Fr.fr (j - 1) (r - 1) + L₁ < llPos Fr j 0 := by
  classical
  obtain ⟨-, -, hinc, hsep, hmem, -, hLL, -, -⟩ := hV
  have hcard : 0 < (Fr.LLset j).card := by have := (hLL j).1; omega
  have hx : llPos Fr j 0 ∈ Fr.LLset j := by
    unfold llPos
    rw [List.getD_eq_getElem _ _ (by rw [Finset.length_sort]; exact hcard)]
    exact (Finset.mem_sort _).mp (List.getElem_mem _)
  have hf := filt_card (Fr := Fr) j 0 hcard
  have hmin : ∀ z ∈ Fr.LLset j, ¬ z < llPos Fr j 0 := by
    intro z hz hzx
    have hsub : ({z, llPos Fr j 0} : Finset ℤ) ⊆ (Fr.LLset j).filter (· ≤ llPos Fr j 0) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hz, hzx.le⟩
      · exact Finset.mem_filter.mpr ⟨hx, le_rfl⟩
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_pair hzx.ne] at h2
    omega
  have hgap := ((hLL j).2.1 _ hx (Or.inl (le_trans hf (by omega)))).2
  have hmono : ∀ k : ℤ, ∀ i, i < r → Fr.fr k 0 ≤ Fr.fr k i := by
    intro k i
    induction i with
    | zero => intro _; exact le_rfl
    | succ i ih => intro hi; exact (ih (by omega)).trans (hinc k i hi).le
  have hxI := hx
  unfold Frames.LLset at hxI
  rw [Finset.mem_filter, Finset.mem_Ioo] at hxI
  have hsep' : Fr.fr (j - 1) (r - 1) < Fr.fr j 0 := by
    have h := hsep (j - 1)
    rwa [sub_add_cancel] at h
  have hyl : Fr.fr (j - 1) (r - 1) ∈ Fr.letters j := by
    unfold Frames.letters
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hmono _ _ (by omega), hsep'.le.trans (hmono _ _ (by omega))⟩, (hmem (j - 1) (r - 1) (by omega)).1⟩
  have hfin := hgap _ hyl hxI.1.1 ?_
  · omega
  intro z hz hzx
  by_contra hzy
  push_neg at hzy
  unfold Frames.letters at hz
  rw [Finset.mem_filter, Finset.mem_Icc] at hz
  apply hmin z _ hzx
  unfold Frames.LLset
  rw [Finset.mem_filter, Finset.mem_Ioo]
  exact ⟨⟨hzy, hzx.trans hxI.1.2⟩, hz.2⟩

/- English proof (translation)
Unfold `llPos`. Rewrite using `[List.getD_eq_getElem _ _ (by rw [Finset.length_sort]; exact hl)]`. Conclude with `(Finset.mem_sort _).mp (List.getElem_mem _)`.
-/
private theorem llPos_mem_LLset (j : ℤ) (l : ℕ) (hl : l < (Fr.LLset j).card) :
    llPos Fr j l ∈ Fr.LLset j := by
  unfold llPos
  rw [List.getD_eq_getElem _ _ (by rw [Finset.length_sort]; exact hl)]
  exact (Finset.mem_sort _).mp (List.getElem_mem _)

/- English proof (translation)
Unfold `llPos at h`. Rewrite `h` using `[List.getD_eq_getElem _ _ (by rw [Finset.length_sort]; exact ha), List.getD_eq_getElem _ _ (by rw [Finset.length_sort]; exact hb)]`. Conclude with `(List.Nodup.getElem_inj_iff (Finset.sort_nodup _ _)).mp h`.
-/
private theorem llPos_injOn (j : ℤ) (a b : ℕ) (ha : a < (Fr.LLset j).card)
    (hb : b < (Fr.LLset j).card) (h : llPos Fr j a = llPos Fr j b) : a = b := by
  unfold llPos at h
  rw [List.getD_eq_getElem _ _ (by rw [Finset.length_sort]; exact ha),
    List.getD_eq_getElem _ _ (by rw [Finset.length_sort]; exact hb)] at h
  exact (List.Nodup.getElem_inj_iff (Finset.sort_nodup _ _)).mp h

/- English proof (translation)
Introduce `z hz`. Assume the negation of the conclusion as `hzx`. Use `push_neg at hzx`. Establish `hx` using `llPos_mem_LLset (Fr := Fr) j 0 hc`. Establish `hf` using `filt_card (Fr := Fr) j 0 hc`.

Establish `hsub : ({z, llPos Fr j 0} : Finset ℤ) ⊆ (Fr.LLset j).filter (· ≤ llPos Fr j 0)`. Introduce `w hw`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hw`. Break down `hw with rfl | rfl` into its components or cases. Conclude with `Finset.mem_filter.mpr ⟨hz, hzx.le⟩`.

Conclude with `Finset.mem_filter.mpr ⟨hx, le_rfl⟩`. Establish `h2` using `Finset.card_le_card hsub`. Rewrite `h2` using `[Finset.card_pair hzx.ne]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem llPos_zero_le_of_mem (j : ℤ) (hc : 0 < (Fr.LLset j).card) :
    ∀ z ∈ Fr.LLset j, llPos Fr j 0 ≤ z := by
  classical
  intro z hz
  by_contra hzx
  push_neg at hzx
  have hx := llPos_mem_LLset (Fr := Fr) j 0 hc
  have hf := filt_card (Fr := Fr) j 0 hc
  have hsub : ({z, llPos Fr j 0} : Finset ℤ) ⊆ (Fr.LLset j).filter (· ≤ llPos Fr j 0) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hz, hzx.le⟩
    · exact Finset.mem_filter.mpr ⟨hx, le_rfl⟩
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_pair hzx.ne] at h2
  omega

/- English proof (translation)
Use `set s := S.sort (· ≤ ·) with hs`. Establish `hlen : s.length = S.card` using `Finset.length_sort _`. Establish `hSk : k ≤ S.card` using `h.trans (Finset.card_filter_le _ _)`. Establish `hpw : s.Pairwise (· ≤ ·)` using `Finset.pairwise_sort _ _`. Establish `hi : s.length - k < s.length` using `by omega`.

Rewrite using `[List.getD_eq_getElem _ _ hi]`. Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Establish `hsub : S.filter (c < ·) ⊆ (s.drop (s.length - k + 1)).toFinset`. Introduce `z hz`.

Rewrite `hz` using `[Finset.mem_filter]`. Establish `hzs : z ∈ s` using `by rw [hs, Finset.mem_sort]; exact hz.1`. Take `⟨m, hm, rfl⟩` from `List.getElem_of_mem hzs`. Rewrite using `[List.mem_toFinset]`. Establish `hmk : s.length - k < m`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h1 : s[m] ≤ s[s.length - k]`. Break down `hc.lt_or_eq with hlt | heq` into its components or cases. Conclude with `List.pairwise_iff_getElem.mp hpw m _ hm hi hlt`.

Simplify using `[heq]`. Conclude with `absurd hz.2 (not_lt.mpr (h1.trans hle))`. Rewrite using `[List.mem_iff_getElem]`. Use `⟨m - (s.length - k + 1), by simp; omega, ?_⟩` and prove the remaining obligations. Simplify using `only [List.getElem_drop]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `h2` using `(Finset.card_le_card hsub).trans (List.toFinset_card_le _)`. Simplify using `at h2`. Use linear arithmetic over natural numbers and integers.
-/
private theorem lt_sort_getD_of_le_card_filter_gt (S : Finset ℤ) (c : ℤ) (k : ℕ) (hk : 1 ≤ k)
    (h : k ≤ (S.filter (c < ·)).card) :
    c < (S.sort (· ≤ ·)).getD ((S.sort (· ≤ ·)).length - k) 0 := by
  classical
  set s := S.sort (· ≤ ·) with hs
  have hlen : s.length = S.card := Finset.length_sort _
  have hSk : k ≤ S.card := h.trans (Finset.card_filter_le _ _)
  have hpw : s.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hi : s.length - k < s.length := by omega
  rw [List.getD_eq_getElem _ _ hi]
  by_contra hle
  push_neg at hle
  have hsub : S.filter (c < ·) ⊆ (s.drop (s.length - k + 1)).toFinset := by
    intro z hz
    rw [Finset.mem_filter] at hz
    have hzs : z ∈ s := by rw [hs, Finset.mem_sort]; exact hz.1
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hzs
    rw [List.mem_toFinset]
    have hmk : s.length - k < m := by
      by_contra hc
      push_neg at hc
      have h1 : s[m] ≤ s[s.length - k] := by
        rcases hc.lt_or_eq with hlt | heq
        · exact List.pairwise_iff_getElem.mp hpw m _ hm hi hlt
        · simp [heq]
      exact absurd hz.2 (not_lt.mpr (h1.trans hle))
    rw [List.mem_iff_getElem]
    refine ⟨m - (s.length - k + 1), by simp; omega, ?_⟩
    simp only [List.getElem_drop]
    congr 1
    omega
  have h2 := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  simp at h2
  omega

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => exact le_rfl`. Consider the case `succ i ih => exact (ih (by omega)).trans (hV.2.2.1 k i hi).le`.
-/
private theorem fr_zero_le_fr_of_valid (hV : Fr.Valid L₁ N₁) (k : ℤ) (i : ℕ) (hi : i < r) :
    Fr.fr k 0 ≤ Fr.fr k i := by
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact (ih (by omega)).trans (hV.2.2.1 k i hi).le

/- English proof (translation)
Establish `hfg` using `first_gap hV hr j`. Establish `hcard : r ≤ (Fr.LLset j).card` using `(hV.2.2.2.2.2.2.1 j).1`. Establish `hsep' : Fr.fr (j - 1) (r - 1) < Fr.fr j 0`. Establish `h` using `hV.2.2.2.1 (j - 1)`. Rewrite `h` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Simplify using `only [Frames.oldest]`. Apply `lt_sort_getD_of_le_card_filter_gt _ _ r hr` to reduce the goal to its premises. Establish `hsub : (Finset.range r).image (llPos Fr j) ⊆ ({z ∈ Fr.letters j | Even z ∧ z < Fr.fr j i}).filter (Fr.fr (j - 1) (r - 1) + L₁ < ·)`. Introduce `z hz`. Rewrite `hz` using `[Finset.mem_image]`.

Take `⟨l, hl, rfl⟩` from `hz`. Rewrite `hl` using `[Finset.mem_range]`. Establish `hm` using `llPos_mem_LLset (Fr := Fr) j l (by omega)`. Establish `hev` using `((hV.2.2.2.2.2.2.1 j).2.1 _ hm (Or.inl (le_trans (filt_card (Fr := Fr) j l (by omega)) (by omega)))).1`. Establish `h0` using `llPos_zero_le_of_mem (Fr := Fr) j (by omega) _ hm`.

Establish `hmI` using `hm`. Unfold `Frames.LLset at hmI`. Rewrite `hmI` using `[Finset.mem_filter, Finset.mem_Ioo]`. Establish `hm1` using `fr_zero_le_fr_of_valid hV (j - 1) (r - 1) (by omega)`. Establish `hm2` using `fr_zero_le_fr_of_valid hV j (r - 1) (by omega)`.

Establish `hm3` using `fr_zero_le_fr_of_valid hV j i hi`. Rewrite using `[Finset.mem_filter, Finset.mem_filter]`. Use `⟨⟨?_, hev, by omega⟩, by omega⟩` and prove the remaining obligations. Unfold `Frames.letters`. Rewrite using `[Finset.mem_filter, Finset.mem_Icc]`.

Conclude with `⟨⟨by omega, by omega⟩, hmI.2⟩`. Use `le_trans ?_ (Finset.card_le_card hsub)` and prove the remaining obligations. Rewrite using `[Finset.card_image_of_injOn, Finset.card_range]`. Introduce `a ha b hb hab`. Conclude with `llPos_injOn (Fr := Fr) j a b (by simp at ha; omega) (by simp at hb; omega) hab`.
-/
theorem oldest_far (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (i : ℕ) (hi : i < r) :
    Fr.fr (j - 1) (r - 1) + L₁ < Fr.oldest j (Fr.fr j i) := by
  classical
  have hfg := first_gap hV hr j
  have hcard : r ≤ (Fr.LLset j).card := (hV.2.2.2.2.2.2.1 j).1
  have hsep' : Fr.fr (j - 1) (r - 1) < Fr.fr j 0 := by
    have h := hV.2.2.2.1 (j - 1)
    rwa [sub_add_cancel] at h
  dsimp only [Frames.oldest]
  apply lt_sort_getD_of_le_card_filter_gt _ _ r hr
  have hsub : (Finset.range r).image (llPos Fr j) ⊆
      ({z ∈ Fr.letters j | Even z ∧ z < Fr.fr j i}).filter (Fr.fr (j - 1) (r - 1) + L₁ < ·) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨l, hl, rfl⟩ := hz
    rw [Finset.mem_range] at hl
    have hm := llPos_mem_LLset (Fr := Fr) j l (by omega)
    have hev := ((hV.2.2.2.2.2.2.1 j).2.1 _ hm
      (Or.inl (le_trans (filt_card (Fr := Fr) j l (by omega)) (by omega)))).1
    have h0 := llPos_zero_le_of_mem (Fr := Fr) j (by omega) _ hm
    have hmI := hm
    unfold Frames.LLset at hmI
    rw [Finset.mem_filter, Finset.mem_Ioo] at hmI
    have hm1 := fr_zero_le_fr_of_valid hV (j - 1) (r - 1) (by omega)
    have hm2 := fr_zero_le_fr_of_valid hV j (r - 1) (by omega)
    have hm3 := fr_zero_le_fr_of_valid hV j i hi
    rw [Finset.mem_filter, Finset.mem_filter]
    refine ⟨⟨?_, hev, by omega⟩, by omega⟩
    unfold Frames.letters
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hmI.2⟩
  refine le_trans ?_ (Finset.card_le_card hsub)
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  exact llPos_injOn (Fr := Fr) j a b (by simp at ha; omega) (by simp at hb; omega) hab

end Geo

section Deg

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (hk : m + 1 = r + K) {J : ℕ} [NeZero J]
  (nL : ZMod J → ℕ) {L₁ N₁ : ℕ}

/- English proof (translation)
Use `set t := posOf n' (posTL Fr x) with ht`. Use `set P := lowP Fr p x with hP`. Use `set mo := l.mapDomain (castV hk) + ga with hmo`. Establish `hB` using `hb x`. Simplify using `only at hB`.

Rewrite `hB` using `[← hP, ← ht]`. Establish `hsplit : ∑ c : Fin (r + K), rho (x, c) = ∑ a : Fin r, rho (x, Fin.castAdd K a) + ∑ b : Fin K, rho (x, Fin.natAdd r b)` using `Fin.sum_univ_add _`. Establish `htop : topDeg ga t = ∑ a : Fin r, ga (TestSideWords.plVar Fr hk nL x a)`. Unfold `topDeg`. Rewrite using `[Fintype.sum_equiv (finCongr hk) (fun c => ga (t, c)) (fun c => ga (t, Fin.cast hk.symm c)) (by intro c; simp)]`.

Rewrite using `[Fin.sum_univ_add]`. Establish `hz : ∑ b : Fin K, ga (t, Fin.cast hk.symm (Fin.natAdd r b)) = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Assume the negation of the conclusion as `hne`.

Establish `h1` using `(hga _ hne).1`. Simplify using `at h1`. Rewrite using `[hz, add_zero]`. Both sides reduce to the same expression. Establish `hM : multideg (plMon Fr p hk nL mo) x = ∑ a : Fin r, mo (TestSideWords.plVar Fr hk nL x a) / P`.

Unfold `multideg plMon`. Simplify using `[hP]`. Establish `hle : ∑ a : Fin r, ga (TestSideWords.plVar Fr hk nL x a) ≤ P * ∑ a : Fin r, mo (TestSideWords.plVar Fr hk nL x a) / P + ∑ a : Fin r, rho (x, Fin.castAdd K a)`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `a _`. Rewrite using `[← hlow.1 x a, Nat.div_add_mod, hmo, Finsupp.add_apply]`. Conclude with `Nat.le_add_left _ _`. Rewrite using `[hM, Nat.mul_sub]`. Rewrite `hB` using `[Nat.mul_add]`.

Generalize the expression as in `P * dPl x = A at *`. Generalize the expression as in `P * dNo x = B at *`. Generalize the expression as in `P * ∑ a : Fin r, mo (TestSideWords.plVar Fr hk nL x a) / P = C at *`. Use linear arithmetic over natural numbers and integers.
-/
theorem deg_le (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card)
    (d : Fin n' → ℕ) (l : Fin n' × Fin (r + K) →₀ ℕ) (hl : IsLabel p Fr l) (ga : TV n' (m + 1) →₀ ℕ)
    (hga : PlaneEven r ga) (dPl dNo : TL J nL r → ℕ) (rho : TL J nL r × Fin (r + K) → ℕ)
    (hb : BlockDeg Fr p nL (fun t => d t + topDeg ga t) rho dPl dNo)
    (hlow : InLow Fr p hk nL rho (l.mapDomain (castV hk) + ga)) (x : TL J nL r) :
    lowP Fr p x * (dPl x - multideg (plMon Fr p hk nL (l.mapDomain (castV hk) + ga)) x) ≤
      d (posOf n' (posTL Fr x)) := by
  classical
  set t := posOf n' (posTL Fr x) with ht
  set P := lowP Fr p x with hP
  set mo := l.mapDomain (castV hk) + ga with hmo
  have hB := hb x
  simp only at hB
  rw [← hP, ← ht] at hB
  have hsplit : ∑ c : Fin (r + K), rho (x, c) =
      ∑ a : Fin r, rho (x, Fin.castAdd K a) + ∑ b : Fin K, rho (x, Fin.natAdd r b) :=
    Fin.sum_univ_add _
  have htop : topDeg ga t = ∑ a : Fin r, ga (TestSideWords.plVar Fr hk nL x a) := by
    unfold topDeg
    rw [Fintype.sum_equiv (finCongr hk) (fun c => ga (t, c))
      (fun c => ga (t, Fin.cast hk.symm c)) (by intro c; simp)]
    rw [Fin.sum_univ_add]
    have hz : ∑ b : Fin K, ga (t, Fin.cast hk.symm (Fin.natAdd r b)) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      by_contra hne
      have h1 := (hga _ hne).1
      simp at h1
    rw [hz, add_zero]
    rfl
  have hM : multideg (plMon Fr p hk nL mo) x = ∑ a : Fin r, mo (TestSideWords.plVar Fr hk nL x a) / P := by
    unfold multideg plMon
    simp [hP]
  have hle : ∑ a : Fin r, ga (TestSideWords.plVar Fr hk nL x a) ≤
      P * ∑ a : Fin r, mo (TestSideWords.plVar Fr hk nL x a) / P + ∑ a : Fin r, rho (x, Fin.castAdd K a) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a _
    rw [← hlow.1 x a, Nat.div_add_mod, hmo, Finsupp.add_apply]
    exact Nat.le_add_left _ _
  rw [hM, Nat.mul_sub]
  rw [Nat.mul_add] at hB
  generalize P * dPl x = A at *
  generalize P * dNo x = B at *
  generalize P * ∑ a : Fin r, mo (TestSideWords.plVar Fr hk nL x a) / P = C at *
  omega

end Deg

end Formalism.MainNotions.PairMembershipBlocks.Ar
