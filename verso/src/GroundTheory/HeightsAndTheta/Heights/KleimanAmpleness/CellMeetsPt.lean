import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

namespace CellZeroConst

variable {K : Type} [Fintype K] {ι : K → Type}

def pt (c : ∀ k, ι k) : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 :=
  ⟨fun k => {c k}, fun _ => Finset.singleton_nonempty _, by simp⟩

/- English proof (translation)
Establish `h1 : ∀ k, (c.1 k).card = 1`. Introduce `k`. Establish `hk : (c.1 k).card - 1 = 0` using `(Finset.sum_eq_zero_iff.mp c.2.2) k (Finset.mem_univ _)`. Use `(c.2.1 k).card_pos` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `choose d hd using fun k => Finset.card_eq_one.mp (h1 k)`. Conclude with `⟨d, Subtype.ext (funext hd)⟩`.
-/
theorem exists_pt (c : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0) : ∃ d : ∀ k, ι k, c = pt d := by
  have h1 : ∀ k, (c.1 k).card = 1 := by
    intro k
    have hk : (c.1 k).card - 1 = 0 := (Finset.sum_eq_zero_iff.mp c.2.2) k (Finset.mem_univ _)
    have := (c.2.1 k).card_pos
    omega
  choose d hd using fun k => Finset.card_eq_one.mp (h1 k)
  exact ⟨d, Subtype.ext (funext hd)⟩

/- English proof (translation)
Simplify using `[CellMeets, pt]`.
-/
theorem cellMeets_pt {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    CellMeets y (pt c).1 ↔ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  simp [CellMeets, pt]

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

/- English proof (translation)
Establish `hne : i ≠ i'` using `hii.ne`. Take `⟨J, hJk, hJl⟩ : ∃ J : ∀ l, Finset (ι l), J k = {i, i'} ∧ ∀ l, l ≠ k → J l = {d l}` from `⟨Function.update (fun l => {d l}) k {i, i'}, by simp, fun l hl => by simp [hl]⟩`. Establish `hJ1 : (∀ l, (J l).Nonempty) ∧ ∑ l, ((J l).card - 1) = 0 + 1`. Use `⟨fun l => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hl : l = k`.

Substitute `hl` using the available equality. Simplify using `[hJk]`. Simplify using `[hJl l hl]`. Rewrite using `[Finset.sum_eq_single k (fun l _ hl => by simp [hJl l hl]) (by simp)]`. Simplify using `[hJk, Finset.card_pair hne]`.

Establish `hm : CellMeets y J`. Introduce `l j hj`. Distinguish the cases in `hl : l = k`. Substitute `hl` using the available equality. Rewrite `hj` using `[hJk]`.

Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hj`. Apply the tactic sequence `rcases hj with rfl | rfl <;> assumption`. Rewrite `hj` using `[hJl l hl, Finset.mem_singleton]`. Substitute `hj` using the available equality. Conclude with `hd l hl`.

Establish `hface : ∀ a b : ι k, J k = {a, b} → a ≠ b → Function.update J k ((J k).erase a) = (pt (Function.update d k b)).1`. Introduce `a b hab habn`. Use function extensionality and compare the values at `l`. Distinguish the cases in `hl : l = k`. Substitute `hl` using the available equality.

Simplify using `[pt, hab, habn]`. Simplify using `[pt, hl, hJl l hl]`. Establish `hfa` using `hface i i' hJk hne`. Establish `hfb` using `hface i' i (by rw [hJk, Finset.pair_comm]) hne.symm`. Establish `hlow : ∑ l ∈ Finset.univ.filter (· < k), ((J l).card - 1) = 0` using `Finset.sum_eq_zero fun l hl => by`.

Rewrite using `[hJl l (ne_of_lt (Finset.mem_filter.mp hl).2)]`. Simplify using the standard rewrite rules. Establish `hsa : faceSign J k i = 1`. Unfold `faceSign`. Rewrite using `[hlow, hJk]`.

Simplify using `[Finset.filter_insert, Finset.filter_singleton, not_lt_of_gt hii]`. Establish `hsb : faceSign J k i' = -1`. Unfold `faceSign`. Rewrite using `[hlow, hJk]`. Simplify using `[Finset.filter_insert, Finset.filter_singleton, hii]`.

Establish `h0 : cellD S y 0 s ⟨J, hJ1⟩ = 0` using `by rw [hs]; rfl`. Unfold `cellD at h0`. Use `erw [LinearMap.pi_apply] at h0`. Use `erw [if_pos (show CellMeets y J from hm)] at h0`. Rewrite `h0` using `[LinearMap.sum_apply, Finset.sum_eq_single k]`.

Use `rotate_left`. Introduce `l _ hl`. Rewrite using `[LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations. Rewrite using `[dif_neg]`.

Both sides reduce to the same expression. Introduce and unpack `⟨hn, -⟩`. Establish `h2` using `hn l`. Rewrite `h2` using `[Function.update_self]`. Express the relevant statement in the definitionally equal form `j ∈ J l at hj`.

Rewrite `hj` using `[hJl l hl, Finset.mem_singleton]`. Substitute `hj` using the available equality. Express the relevant statement in the definitionally equal form `((J l).erase (d l)).Nonempty at h2`. Rewrite `h2` using `[hJl l hl]`. Simplify using `at h2`.

Simplify using the standard rewrite rules. Rewrite `h0` using `[LinearMap.sum_apply, Finset.sum_eq_add i i' hne]`. Use `rotate_left`. Introduce `j hj hj2`. Express the relevant statement in the definitionally equal form `j ∈ J k at hj`.

Rewrite `hj` using `[hJk]`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hj`. Break down `hj with rfl | rfl` into its components or cases. Conclude with `absurd rfl hj2.1`. Conclude with `absurd rfl hj2.2`.

Introduce `h; exact absurd (show i ∈ J k by rw [hJk]; simp) h`. Introduce `h; exact absurd (show i' ∈ J k by rw [hJk]; simp) h`. Rewrite `h0` using `[dif_pos (hfa ▸ (pt (Function.update d k i')).2), dif_pos (hfb ▸ (pt (Function.update d k i)).2)]`. Simplify using `only [LinearMap.smul_apply] at h0`. Use `erw [LinearMap.proj_apply, LinearMap.proj_apply] at h0`.

Establish `e1 : ∀ h, s ⟨Function.update J k ((J k).erase i), h⟩ = s (pt (Function.update d k i'))` using `fun _ => congrArg s (Subtype.ext hfa)`. Establish `e2 : ∀ h, s ⟨Function.update J k ((J k).erase i'), h⟩ = s (pt (Function.update d k i))` using `fun _ => congrArg s (Subtype.ext hfb)`. Rewrite `h0` using `[hsa, hsb, e1, e2, one_smul, neg_smul, one_smul]`. Take the linear combination `-h0`.
-/
theorem edge (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 → Ω) (hs : cellD S y 0 s = 0) (d : ∀ k, ι k) (k : K)
    {i i' : ι k} (hii : i < i') (hd : ∀ l, l ≠ k → y ⟨l, d l⟩ ≠ 0) (hi : y ⟨k, i⟩ ≠ 0)
    (hi' : y ⟨k, i'⟩ ≠ 0) :
    s (pt (Function.update d k i)) = s (pt (Function.update d k i')) := by
  classical
  have hne : i ≠ i' := hii.ne
  obtain ⟨J, hJk, hJl⟩ : ∃ J : ∀ l, Finset (ι l), J k = {i, i'} ∧ ∀ l, l ≠ k → J l = {d l} :=
    ⟨Function.update (fun l => {d l}) k {i, i'}, by simp, fun l hl => by simp [hl]⟩
  have hJ1 : (∀ l, (J l).Nonempty) ∧ ∑ l, ((J l).card - 1) = 0 + 1 := by
    refine ⟨fun l => ?_, ?_⟩
    · by_cases hl : l = k
      · subst hl; simp [hJk]
      · simp [hJl l hl]
    · rw [Finset.sum_eq_single k (fun l _ hl => by simp [hJl l hl]) (by simp)]
      simp [hJk, Finset.card_pair hne]
  have hm : CellMeets y J := by
    intro l j hj
    by_cases hl : l = k
    · subst hl
      rw [hJk] at hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> assumption
    · rw [hJl l hl, Finset.mem_singleton] at hj
      subst hj
      exact hd l hl

  have hface : ∀ a b : ι k, J k = {a, b} → a ≠ b →
      Function.update J k ((J k).erase a) = (pt (Function.update d k b)).1 := by
    intro a b hab habn
    funext l
    by_cases hl : l = k
    · subst hl
      simp [pt, hab, habn]
    · simp [pt, hl, hJl l hl]
  have hfa := hface i i' hJk hne
  have hfb := hface i' i (by rw [hJk, Finset.pair_comm]) hne.symm
  have hlow : ∑ l ∈ Finset.univ.filter (· < k), ((J l).card - 1) = 0 :=
    Finset.sum_eq_zero fun l hl => by
      rw [hJl l (ne_of_lt (Finset.mem_filter.mp hl).2)]
      simp
  have hsa : faceSign J k i = 1 := by
    unfold faceSign
    rw [hlow, hJk]
    simp [Finset.filter_insert, Finset.filter_singleton, not_lt_of_gt hii]
  have hsb : faceSign J k i' = -1 := by
    unfold faceSign
    rw [hlow, hJk]
    simp [Finset.filter_insert, Finset.filter_singleton, hii]
  have h0 : cellD S y 0 s ⟨J, hJ1⟩ = 0 := by rw [hs]; rfl
  unfold cellD at h0
  erw [LinearMap.pi_apply] at h0
  erw [if_pos (show CellMeets y J from hm)] at h0
  rw [LinearMap.sum_apply, Finset.sum_eq_single k] at h0
  rotate_left
  · intro l _ hl
    rw [LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [dif_neg]
    · rfl
    rintro ⟨hn, -⟩
    have h2 := hn l
    rw [Function.update_self] at h2
    change j ∈ J l at hj
    rw [hJl l hl, Finset.mem_singleton] at hj
    subst hj
    change ((J l).erase (d l)).Nonempty at h2
    rw [hJl l hl] at h2
    simp at h2
  · simp
  rw [LinearMap.sum_apply, Finset.sum_eq_add i i' hne] at h0
  rotate_left
  · intro j hj hj2
    change j ∈ J k at hj
    rw [hJk] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact absurd rfl hj2.1
    · exact absurd rfl hj2.2
  · intro h; exact absurd (show i ∈ J k by rw [hJk]; simp) h
  · intro h; exact absurd (show i' ∈ J k by rw [hJk]; simp) h
  rw [dif_pos (hfa ▸ (pt (Function.update d k i')).2), dif_pos (hfb ▸ (pt (Function.update d k i)).2)] at h0
  simp only [LinearMap.smul_apply] at h0
  erw [LinearMap.proj_apply, LinearMap.proj_apply] at h0
  have e1 : ∀ h, s ⟨Function.update J k ((J k).erase i), h⟩ = s (pt (Function.update d k i')) :=
    fun _ => congrArg s (Subtype.ext hfa)
  have e2 : ∀ h, s ⟨Function.update J k ((J k).erase i'), h⟩ = s (pt (Function.update d k i)) :=
    fun _ => congrArg s (Subtype.ext hfb)
  rw [hsa, hsb, e1, e2, one_smul, neg_smul, one_smul] at h0
  linear_combination -h0

/- English proof (translation)
Establish `hdl : ∀ l, l ≠ k → y ⟨l, d l⟩ ≠ 0` using `fun l _ => hd l`. Break down `lt_trichotomy (d k) j with h | h | h` into its components or cases. Use `edge S y s hs d k h hdl (hd k) hj` as an intermediate fact. Rewrite `this` using `[Function.update_eq_self]`. Then use the resulting hypothesis. Rewrite using `[← h, Function.update_eq_self]`.

Use `edge S y s hs d k h hdl hj (hd k)` as an intermediate fact. Rewrite `this` using `[Function.update_eq_self]`. Conclude with `this.symm`.
-/
theorem step (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 → Ω) (hs : cellD S y 0 s = 0) (d : ∀ k, ι k)
    (hd : ∀ l, y ⟨l, d l⟩ ≠ 0) (k : K) (j : ι k) (hj : y ⟨k, j⟩ ≠ 0) :
    s (pt d) = s (pt (Function.update d k j)) := by
  classical
  have hdl : ∀ l, l ≠ k → y ⟨l, d l⟩ ≠ 0 := fun l _ => hd l
  rcases lt_trichotomy (d k) j with h | h | h
  · have := edge S y s hs d k h hdl (hd k) hj
    rwa [Function.update_eq_self] at this
  · rw [← h, Function.update_eq_self]
  · have := edge S y s hs d k h hdl hj (hd k)
    rw [Function.update_eq_self] at this
    exact this.symm

/- English proof (translation)
Establish `key : ∀ T : Finset K, s (pt d) = s (pt (fun l => if l ∈ T then d' l else d l))`. Introduce `T`. Use `Finset.induction_on T ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `a T ha ih`.

Rewrite using `[ih]`. Establish `hmeet : ∀ l, y ⟨l, (fun l => if l ∈ T then d' l else d l) l⟩ ≠ 0` using `fun l => by dsimp only split_ifs`. Conclude with `hd' l`. Conclude with `hd l`. Rewrite using `[step S y s hs _ hmeet a (d' a) (hd' a)]`.

Use `congr 2`. Use function extensionality and compare the values at `l`. Distinguish the cases in `hl : l = a`. Substitute `hl` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hl]`. Simplify using `using key Finset.univ`.
-/
theorem chain (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 → Ω) (hs : cellD S y 0 s = 0) (d d' : ∀ k, ι k)
    (hd : ∀ l, y ⟨l, d l⟩ ≠ 0) (hd' : ∀ l, y ⟨l, d' l⟩ ≠ 0) :
    s (pt d) = s (pt d') := by
  classical
  have key : ∀ T : Finset K, s (pt d) = s (pt (fun l => if l ∈ T then d' l else d l)) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · simp
    · intro a T ha ih
      rw [ih]
      have hmeet : ∀ l, y ⟨l, (fun l => if l ∈ T then d' l else d l) l⟩ ≠ 0 := fun l => by
        dsimp only
        split_ifs
        · exact hd' l
        · exact hd l
      rw [step S y s hs _ hmeet a (d' a) (hd' a)]
      congr 2
      funext l
      by_cases hl : l = a
      · subst hl
        simp
      · simp [hl]
  simpa using key Finset.univ

end CellZeroConst

/- English proof (translation)
Introduce `S _ K _ _ ι _ _ Ω _ _ y s hs c c' hc hc'`. Take `⟨d, rfl⟩` from `CellZeroConst.exists_pt c`. Take `⟨d', rfl⟩` from `CellZeroConst.exists_pt c'`. Rewrite `hc`, `hc'` using `[CellZeroConst.cellMeets_pt]`. Conclude with `CellZeroConst.chain S y s hs d d' hc hc'`.
-/
theorem CellZeroConst.proof : CellZeroConst.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y s hs c c' hc hc'
  obtain ⟨d, rfl⟩ := CellZeroConst.exists_pt c
  obtain ⟨d', rfl⟩ := CellZeroConst.exists_pt c'
  rw [CellZeroConst.cellMeets_pt] at hc hc'
  exact CellZeroConst.chain S y s hs d d' hc hc'

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
