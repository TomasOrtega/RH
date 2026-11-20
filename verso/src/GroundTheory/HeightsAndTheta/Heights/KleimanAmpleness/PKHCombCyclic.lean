import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHCombCyclicSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHCombContractSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

namespace KHCombCyclic

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

abbrev FaceOK (J : ∀ k, Finset (ι k)) (n : ℕ) (G : ∀ k, Finset (ι k)) : Prop :=
  ((∀ l, (G l).Nonempty) ∧ ∑ l, ((G l).card - 1) = n) ∧ ∀ l, J l ⊆ G l

open Classical in

/- English proof (translation)
Simplify using `only [combD, LinearMap.pi_apply, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i))`. Rewrite using `[dif_pos h, dif_pos h]`. Both sides reduce to the same expression.

Rewrite using `[dif_neg h, dif_neg h]`. Both sides reduce to the same expression.
-/
theorem combD_apply (J : ∀ k, Finset (ι k)) (n : ℕ) (f : CombC S J n) (I : CombCell ι J (n + 1)) :
    combD S J n f I = ∑ k, ∑ i ∈ I.1.1 k,
      if h : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)) then
        (KH.faceSign I.1.1 k i : ℤ) • f ⟨⟨Function.update I.1.1 k ((I.1.1 k).erase i), h.1⟩, h.2⟩
      else 0 := by
  simp only [combD, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  by_cases h : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i))
  · rw [dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h]; rfl

/- English proof (translation)
The claim follows from `Subtype.ext (Subtype.ext h)`.
-/
theorem cell_ext {J : ∀ k, Finset (ι k)} {n : ℕ} {I₁ I₂ : CombCell ι J n} (h : I₁.1.1 = I₂.1.1) : I₁ = I₂ :=
  Subtype.ext (Subtype.ext h)

/- English proof (translation)
Establish `hcard : ∀ m, (G m).card = (G' m).card` using `fun m => by`. Distinguish the cases in `hm : m = k`. Rewrite using `[hm]`. Conclude with `hc`. Rewrite using `[ho m hm]`.

Establish `hsub : ∀ m, J m ⊆ G m ↔ J m ⊆ G' m` using `fun m => by`. Distinguish the cases in `hm : m = k`. Rewrite using `[hm, hJ]`. Simplify using the standard rewrite rules. Rewrite using `[ho m hm]`.

Simplify using `only [FaceOK, ← Finset.card_pos, hcard, hsub]`.
-/
theorem faceOK_congr {J : ∀ k, Finset (ι k)} {n : ℕ} {k : K} (hJ : J k = ∅) {G G' : ∀ k, Finset (ι k)}
    (hc : (G k).card = (G' k).card) (ho : ∀ m, m ≠ k → G m = G' m) : FaceOK J n G ↔ FaceOK J n G' := by
  have hcard : ∀ m, (G m).card = (G' m).card := fun m => by
    by_cases hm : m = k
    · rw [hm]; exact hc
    · rw [ho m hm]
  have hsub : ∀ m, J m ⊆ G m ↔ J m ⊆ G' m := fun m => by
    by_cases hm : m = k
    · rw [hm, hJ]; simp
    · rw [ho m hm]
  simp only [FaceOK, ← Finset.card_pos, hcard, hsub]

/- English proof (translation)
Introduce `h'` and use `by have := h'.1.1 l rw [Function.update_self, ← Finset.card_pos, Finset.card_erase_of_mem hi, h] at this exact lt_irrefl 0 this`.
-/
theorem not_faceOK_of_card_one {J : ∀ k, Finset (ι k)} {n : ℕ} (A : ∀ k, Finset (ι k)) (l : K) {i : ι l}
    (hi : i ∈ A l) (h : (A l).card = 1) : ¬ FaceOK J n (Function.update A l ((A l).erase i)) := fun h' => by
  have := h'.1.1 l
  rw [Function.update_self, ← Finset.card_pos, Finset.card_erase_of_mem hi, h] at this
  exact lt_irrefl 0 this

/- English proof (translation)
Establish `h1 : ((A k).filter (· < a)).card = 0`. Rewrite using `[Finset.card_eq_zero, he]`. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]`. Introduce and unpack `(rfl | rfl)`.

Conclude with `lt_irrefl _`. Conclude with `not_lt.mpr hab.le`. Establish `h2 : ((A k).filter (· < b)).card = 1`. Rewrite using `[Finset.card_eq_one]`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Rewrite using `[he]`. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨rfl | rfl, h⟩`.

Both sides reduce to the same expression. Conclude with `absurd h (lt_irrefl _)`. Introduce and unpack `rfl`. Conclude with `⟨Or.inl rfl, hab⟩`. Unfold `KH.faceSign`.

Rewrite using `[h1, h2, pow_add, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem faceSign_pair (A : ∀ k, Finset (ι k)) (k : K) {a b : ι k} (hab : a < b) (he : A k = {a, b}) :
    KH.faceSign A k b = - KH.faceSign A k a := by
  have h1 : ((A k).filter (· < a)).card = 0 := by
    rw [Finset.card_eq_zero, he]
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
    rintro (rfl | rfl)
    · exact lt_irrefl _
    · exact not_lt.mpr hab.le
  have h2 : ((A k).filter (· < b)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨a, ?_⟩
    rw [he]
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · rfl
      · exact absurd h (lt_irrefl _)
    · rintro rfl
      exact ⟨Or.inl rfl, hab⟩
  unfold KH.faceSign
  rw [h1, h2, pow_add, pow_add]
  ring

/- English proof (translation)
Establish `hs : ∑ m ∈ Finset.univ.filter (· < l), ((Function.update A k v m).card - 1) = ∑ m ∈ Finset.univ.filter (· < l), ((A m).card - 1)`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Distinguish the cases in `hm : m = k`. Rewrite using `[hm, Function.update_self, hv, hA]`. Rewrite using `[Function.update_of_ne hm]`.

Unfold `KH.faceSign`. Rewrite using `[Function.update_of_ne hl, hs]`.
-/
theorem faceSign_update_one (A : ∀ k, Finset (ι k)) {k l : K} (hl : l ≠ k) (i : ι l) (v : Finset (ι k))
    (hA : (A k).card = 1) (hv : v.card = 1) :
    KH.faceSign (Function.update A k v) l i = KH.faceSign A l i := by
  have hs : ∑ m ∈ Finset.univ.filter (· < l), ((Function.update A k v m).card - 1) =
      ∑ m ∈ Finset.univ.filter (· < l), ((A m).card - 1) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : m = k
    · rw [hm, Function.update_self, hv, hA]
    · rw [Function.update_of_ne hm]
  unfold KH.faceSign
  rw [Function.update_of_ne hl, hs]

open Classical in

/- English proof (translation)
Take `⟨a, b, hab, he⟩` from `Finset.card_eq_two.mp h2`. Establish `ha : a ∈ I.1.1 k` using `by rw [he]; simp`. Establish `hb : b ∈ I.1.1 k` using `by rw [he]; simp`. Establish `hiff : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase a)) ↔ FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase b))` using `faceOK_congr hJ (by rw [Function.update_self, Function.update_self, Finset.card_erase_of_mem ha, Finset.card_erase_of_mem hb]) (fun m hm => by rw [Function.update_of_ne hm, Function.update_of_ne hm])`. Set `t : ι k → S` to `fun i => if h : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)) then (KH.faceSign I.1.1 k i : ℤ) • f ⟨⟨_, h.1⟩, h.2⟩ else 0`.

Use `show ∑ i ∈ I.1.1 k, t i = 0`. Rewrite using `[he, Finset.sum_pair hab]`. Distinguish the cases in `hOK : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase a))`. Establish `hOK'` using `hiff.mp hOK`. Simplify using `only [t]`.

Rewrite using `[dif_pos hOK, dif_pos hOK', hf b hb a ha hOK' hOK]`. Break down `lt_or_gt_of_ne hab with h | h` into its components or cases. Rewrite using `[faceSign_pair I.1.1 k h he, neg_smul, add_neg_cancel]`. Rewrite using `[faceSign_pair I.1.1 k h (he.trans (Finset.pair_comm a b)), neg_smul, neg_add_cancel]`. Simplify using `only [t]`.

Rewrite using `[dif_neg hOK, dif_neg (fun h => hOK (hiff.mpr h)), add_zero]`.
-/
theorem block_pair (J : ∀ k, Finset (ι k)) (n : ℕ) (f : CombC S J n) (I : CombCell ι J (n + 1)) (k : K)
    (hJ : J k = ∅) (h2 : (I.1.1 k).card = 2)
    (hf : ∀ i ∈ I.1.1 k, ∀ j ∈ I.1.1 k,
      ∀ (hi : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)))
        (hj : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase j))),
      f ⟨⟨_, hi.1⟩, hi.2⟩ = f ⟨⟨_, hj.1⟩, hj.2⟩) :
    ∑ i ∈ I.1.1 k, (if h : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)) then
        (KH.faceSign I.1.1 k i : ℤ) • f ⟨⟨_, h.1⟩, h.2⟩ else 0) = 0 := by
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp h2
  have ha : a ∈ I.1.1 k := by rw [he]; simp
  have hb : b ∈ I.1.1 k := by rw [he]; simp
  have hiff : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase a)) ↔
      FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase b)) :=
    faceOK_congr hJ (by rw [Function.update_self, Function.update_self, Finset.card_erase_of_mem ha,
      Finset.card_erase_of_mem hb]) (fun m hm => by rw [Function.update_of_ne hm, Function.update_of_ne hm])
  let t : ι k → S := fun i => if h : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)) then
      (KH.faceSign I.1.1 k i : ℤ) • f ⟨⟨_, h.1⟩, h.2⟩ else 0
  show ∑ i ∈ I.1.1 k, t i = 0
  rw [he, Finset.sum_pair hab]
  by_cases hOK : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase a))
  · have hOK' := hiff.mp hOK
    simp only [t]
    rw [dif_pos hOK, dif_pos hOK', hf b hb a ha hOK' hOK]
    rcases lt_or_gt_of_ne hab with h | h
    · rw [faceSign_pair I.1.1 k h he, neg_smul, add_neg_cancel]
    · rw [faceSign_pair I.1.1 k h (he.trans (Finset.pair_comm a b)), neg_smul, neg_add_cancel]
  · simp only [t]
    rw [dif_neg hOK, dif_neg (fun h => hOK (hiff.mpr h)), add_zero]

open Classical in

/- English proof (translation)
Use function extensionality and compare the values at `I`. Rewrite using `[combD_apply, Pi.zero_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Break down `hJ k with hk | hk` into its components or cases. Distinguish the cases in `hc : (I.1.1 k).card = 2 ∧ ∀ m, m ≠ k → J m = ∅ → (I.1.1 m).card = 1`.

Establish `key : ∀ i ∈ I.1.1 k, ∀ hi' : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)), singOne S J n ⟨⟨_, hi'.1⟩, hi'.2⟩ = 1`. Introduce `i hi hi'`. Simplify using `only [singOne]`. Rewrite using `[if_pos]`. Introduce `m hm`.

Distinguish the cases in `hmk : m = k`. Rewrite using `[hmk, Function.update_self, Finset.card_erase_of_mem hi, hc.1]`. Rewrite using `[Function.update_of_ne hmk]`. Conclude with `hc.2 m hmk hm`. Use `block_pair J n _ I k hk hc.1 fun i hi j hj hi' hj' => ?_` and prove the remaining obligations.

Rewrite using `[key i hi hi', key j hj hj']`. Use `Finset.sum_eq_zero fun i hi => ?_ split_ifs with h` and prove the remaining obligations. Establish `h0 : singOne S J n ⟨⟨_, h.1⟩, h.2⟩ = 0`. Simplify using `only [singOne]`. Rewrite using `[if_neg]`.

Introduce `hall`. Apply `hc` to reduce the goal to its premises. Establish `hpos : 0 < (I.1.1 k).card` using `Finset.card_pos.mpr ⟨i, hi⟩`. Establish `hkk` using `hall k hk`. Rewrite `hkk` using `[Function.update_self, Finset.card_erase_of_mem hi]`.

Use `⟨by omega, fun m hm hJm => ?_⟩` and prove the remaining obligations. Use `hall m hJm` as an intermediate fact. Rewrite `this` using `[Function.update_of_ne hm]`. Then use the resulting hypothesis. Rewrite using `[h0, smul_zero]`. Both sides reduce to the same expression.

Use `Finset.sum_eq_zero fun i hi => dif_neg fun h => ?_` and prove the remaining obligations. Establish `hiJ : i ∈ J k` using `by rw [hk]; exact Finset.mem_univ i`. Use `h.2 k hiJ` as an intermediate fact. Rewrite `this` using `[Function.update_self]`. Conclude with `Finset.notMem_erase i _ this`.
-/
theorem singOne_cocycle (J : ∀ k, Finset (ι k)) (n : ℕ) (hJ : ∀ k, J k = ∅ ∨ J k = Finset.univ) :
    combD S J n (singOne S J n) = 0 := by
  funext I
  rw [combD_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases hJ k with hk | hk
  · by_cases hc : (I.1.1 k).card = 2 ∧ ∀ m, m ≠ k → J m = ∅ → (I.1.1 m).card = 1
    · have key : ∀ i ∈ I.1.1 k, ∀ hi' : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)),
          singOne S J n ⟨⟨_, hi'.1⟩, hi'.2⟩ = 1 := by
        intro i hi hi'
        simp only [singOne]
        rw [if_pos]
        intro m hm
        by_cases hmk : m = k
        · rw [hmk, Function.update_self, Finset.card_erase_of_mem hi, hc.1]
        · rw [Function.update_of_ne hmk]
          exact hc.2 m hmk hm
      refine block_pair J n _ I k hk hc.1 fun i hi j hj hi' hj' => ?_
      rw [key i hi hi', key j hj hj']
    · refine Finset.sum_eq_zero fun i hi => ?_
      split_ifs with h
      · have h0 : singOne S J n ⟨⟨_, h.1⟩, h.2⟩ = 0 := by
          simp only [singOne]
          rw [if_neg]
          intro hall
          apply hc
          have hpos : 0 < (I.1.1 k).card := Finset.card_pos.mpr ⟨i, hi⟩
          have hkk := hall k hk
          rw [Function.update_self, Finset.card_erase_of_mem hi] at hkk
          refine ⟨by omega, fun m hm hJm => ?_⟩
          have := hall m hJm
          rwa [Function.update_of_ne hm] at this
        rw [h0, smul_zero]
      · rfl
  · refine Finset.sum_eq_zero fun i hi => dif_neg fun h => ?_
    have hiJ : i ∈ J k := by rw [hk]; exact Finset.mem_univ i
    have := h.2 k hiJ
    rw [Function.update_self] at this
    exact Finset.notMem_erase i _ this

open Classical in

/- English proof (translation)
Use function extensionality and compare the values at `I`. Rewrite using `[Pi.zero_apply, combD_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]`. Establish `hz : ∀ l, ∀ i ∈ I.1.1 l, ((Function.update I.1.1 l ((I.1.1 l).erase i)) k).card ≠ 1 → (if h : FaceOK J n (Function.update I.1.1 l ((I.1.1 l).erase i)) then (KH.faceSign I.1.1 l i : ℤ) • g ⟨⟨_, h.1⟩, h.2⟩ else 0) = 0`. Introduce `l i _ hne`. Use `split_ifs with h`.

Rewrite using `[hg0 ⟨⟨_, h.1⟩, h.2⟩ hne, smul_zero]`. Both sides reduce to the same expression. Distinguish the cases in `h1 : (I.1.1 k).card = 1`. Establish `hOK : FaceOK J (n + 1) (Function.update I.1.1 k {i₀})` using `(faceOK_congr hJ (by rw [Function.update_self, Finset.card_singleton, h1]) (fun m hm => (Function.update_of_ne hm _ _).symm)).mp ⟨I.1.2, I.2⟩`. Take `⟨I', hI'⟩ : ∃ I' : CombCell ι J (n + 1), I'.1.1 = Function.update I.1.1 k {i₀}` from `⟨⟨⟨_, hOK.1⟩, hOK.2⟩, rfl⟩`.

Establish `hφI'` using `congrFun hφ I'`. Rewrite `hφI'` using `[Pi.zero_apply, combD_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]`. Use `Eq.trans ?_ hφI'` and prove the remaining obligations. Establish `hI'k : (I'.1.1 k).card = 1` using `by rw [hI', Function.update_self, Finset.card_singleton]`. Use `congr 1`.

Rewrite using `[Finset.sum_eq_zero fun i hi => dif_neg (not_faceOK_of_card_one _ k hi h1), Finset.sum_eq_zero fun i hi => dif_neg (not_faceOK_of_card_one _ k hi hI'k)]`. Use `Finset.sum_congr rfl fun l hlm => ?_` and prove the remaining obligations. Establish `hl : l ≠ k` using `Finset.ne_of_mem_erase hlm`. Establish `hset : I.1.1 l = I'.1.1 l` using `by rw [hI', Function.update_of_ne hl]`. Use `Finset.sum_congr hset fun i hi => ?_` and prove the remaining obligations.

Establish `hF' : Function.update I'.1.1 l ((I'.1.1 l).erase i) = Function.update (Function.update I.1.1 l ((I.1.1 l).erase i)) k {i₀}`. Rewrite using `[← hset, hI', Function.update_comm (Ne.symm hl)]`. Establish `hFk : ((Function.update I.1.1 l ((I.1.1 l).erase i)) k).card = 1`. Rewrite using `[Function.update_of_ne (Ne.symm hl), h1]`. Establish `hiff : FaceOK J n (Function.update I.1.1 l ((I.1.1 l).erase i)) ↔ FaceOK J n (Function.update I'.1.1 l ((I'.1.1 l).erase i))`.

Rewrite using `[hF']`. Conclude with `faceOK_congr hJ (by rw [Function.update_self, Finset.card_singleton, hFk]) (fun m hm => (Function.update_of_ne hm _ _).symm)`. Establish `hsign : KH.faceSign I'.1.1 l i = KH.faceSign I.1.1 l i`. Rewrite using `[hI']`. Conclude with `faceSign_update_one I.1.1 hl i {i₀} h1 (Finset.card_singleton i₀)`.

Distinguish the cases in `hc : FaceOK J n (Function.update I.1.1 l ((I.1.1 l).erase i))`. Rewrite using `[dif_pos hc, dif_pos (hiff.mp hc), hsign]`. Take `⟨I'', hk'', ho'', hgI⟩` from `hg1 ⟨⟨_, hc.1⟩, hc.2⟩ hFk`. Rewrite using `[hgI]`. Use `congr 1`.

Use `congrArg φ (cell_ext ?_)` and prove the remaining obligations. Use `show I''.1.1 = Function.update I'.1.1 l ((I'.1.1 l).erase i)`. Rewrite using `[hF', Function.eq_update_iff]`. Conclude with `⟨hk'', fun m hm => ho'' m hm⟩`. Rewrite using `[dif_neg hc, dif_neg (fun h => hc (hiff.mpr h))]`.

Distinguish the cases in `h2 : (I.1.1 k).card = 2`. Rewrite using `[Finset.sum_eq_zero fun l hlm => Finset.sum_eq_zero fun i hi => hz l i hi (by`. Rewrite using `[Function.update_of_ne (Ne.symm (Finset.ne_of_mem_erase hlm)), h2]`. Use the proof step `omega), add_zero]`. Establish `hrep : ∀ i ∈ I.1.1 k, ∀ Ii : CombCell ι J n, Ii.1.1 k = {i₀} → (∀ m, m ≠ k → Ii.1.1 m = Function.update I.1.1 k ((I.1.1 k).erase i) m) → Ii.1.1 = Function.update I.1.1 k {i₀}` using `fun i _ Ii hk ho => by`.

Rewrite using `[Function.eq_update_iff]`. Conclude with `⟨hk, fun m hm => (ho m hm).trans (Function.update_of_ne hm _ _)⟩`. Establish `hcard : ∀ i ∈ I.1.1 k, ((Function.update I.1.1 k ((I.1.1 k).erase i)) k).card = 1` using `fun i hi => by`. Rewrite using `[Function.update_self, Finset.card_erase_of_mem hi, h2]`. Use `block_pair J n g I k hJ h2 fun i hi j hj hi' hj' => ?_` and prove the remaining obligations.

Take `⟨Ii, hki, hoi, hgi⟩` from `hg1 ⟨⟨_, hi'.1⟩, hi'.2⟩ (hcard i hi)`. Take `⟨Ij, hkj, hoj, hgj⟩` from `hg1 ⟨⟨_, hj'.1⟩, hj'.2⟩ (hcard j hj)`. Rewrite using `[hgi, hgj]`. Conclude with `congrArg φ (cell_ext ((hrep i hi Ii hki hoi).trans (hrep j hj Ij hkj hoj).symm))`. Rewrite using `[Finset.sum_eq_zero fun i hi => hz k i hi (by`.

Rewrite using `[Function.update_self, Finset.card_erase_of_mem hi]`. Use `Finset.card_pos.mpr ⟨i, hi⟩` as an intermediate fact. Use the proof step `omega),`. Use the proof step `Finset.sum_eq_zero fun l hlm => Finset.sum_eq_zero fun i hi => hz l i hi (by`. Rewrite using `[Function.update_of_ne (Ne.symm (Finset.ne_of_mem_erase hlm))]`.

Conclude with `h1), add_zero]`.
-/
theorem contract_cocycle (J : ∀ k, Finset (ι k)) (n : ℕ) (k : K) (i₀ : ι k) (hJ : J k = ∅)
    (φ g : CombC S J n) (hφ : combD S J n φ = 0)
    (hg1 : ∀ I : CombCell ι J n, (I.1.1 k).card = 1 →
      ∃ I' : CombCell ι J n, I'.1.1 k = {i₀} ∧ (∀ l, l ≠ k → I'.1.1 l = I.1.1 l) ∧ g I = φ I')
    (hg0 : ∀ I : CombCell ι J n, (I.1.1 k).card ≠ 1 → g I = 0) :
    combD S J n g = 0 := by
  funext I
  rw [Pi.zero_apply, combD_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have hz : ∀ l, ∀ i ∈ I.1.1 l, ((Function.update I.1.1 l ((I.1.1 l).erase i)) k).card ≠ 1 →
      (if h : FaceOK J n (Function.update I.1.1 l ((I.1.1 l).erase i)) then
        (KH.faceSign I.1.1 l i : ℤ) • g ⟨⟨_, h.1⟩, h.2⟩ else 0) = 0 := by
    intro l i _ hne
    split_ifs with h
    · rw [hg0 ⟨⟨_, h.1⟩, h.2⟩ hne, smul_zero]
    · rfl
  by_cases h1 : (I.1.1 k).card = 1
  · have hOK : FaceOK J (n + 1) (Function.update I.1.1 k {i₀}) :=
      (faceOK_congr hJ (by rw [Function.update_self, Finset.card_singleton, h1])
        (fun m hm => (Function.update_of_ne hm _ _).symm)).mp ⟨I.1.2, I.2⟩
    obtain ⟨I', hI'⟩ : ∃ I' : CombCell ι J (n + 1), I'.1.1 = Function.update I.1.1 k {i₀} :=
      ⟨⟨⟨_, hOK.1⟩, hOK.2⟩, rfl⟩
    have hφI' := congrFun hφ I'
    rw [Pi.zero_apply, combD_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hφI'
    refine Eq.trans ?_ hφI'
    have hI'k : (I'.1.1 k).card = 1 := by rw [hI', Function.update_self, Finset.card_singleton]
    congr 1
    · rw [Finset.sum_eq_zero fun i hi => dif_neg (not_faceOK_of_card_one _ k hi h1),
        Finset.sum_eq_zero fun i hi => dif_neg (not_faceOK_of_card_one _ k hi hI'k)]
    refine Finset.sum_congr rfl fun l hlm => ?_
    have hl : l ≠ k := Finset.ne_of_mem_erase hlm
    have hset : I.1.1 l = I'.1.1 l := by rw [hI', Function.update_of_ne hl]
    refine Finset.sum_congr hset fun i hi => ?_
    have hF' : Function.update I'.1.1 l ((I'.1.1 l).erase i) =
        Function.update (Function.update I.1.1 l ((I.1.1 l).erase i)) k {i₀} := by
      rw [← hset, hI', Function.update_comm (Ne.symm hl)]
    have hFk : ((Function.update I.1.1 l ((I.1.1 l).erase i)) k).card = 1 := by
      rw [Function.update_of_ne (Ne.symm hl), h1]
    have hiff : FaceOK J n (Function.update I.1.1 l ((I.1.1 l).erase i)) ↔
        FaceOK J n (Function.update I'.1.1 l ((I'.1.1 l).erase i)) := by
      rw [hF']
      exact faceOK_congr hJ (by rw [Function.update_self, Finset.card_singleton, hFk])
        (fun m hm => (Function.update_of_ne hm _ _).symm)
    have hsign : KH.faceSign I'.1.1 l i = KH.faceSign I.1.1 l i := by
      rw [hI']
      exact faceSign_update_one I.1.1 hl i {i₀} h1 (Finset.card_singleton i₀)
    by_cases hc : FaceOK J n (Function.update I.1.1 l ((I.1.1 l).erase i))
    · rw [dif_pos hc, dif_pos (hiff.mp hc), hsign]
      obtain ⟨I'', hk'', ho'', hgI⟩ := hg1 ⟨⟨_, hc.1⟩, hc.2⟩ hFk
      rw [hgI]
      congr 1
      refine congrArg φ (cell_ext ?_)
      show I''.1.1 = Function.update I'.1.1 l ((I'.1.1 l).erase i)
      rw [hF', Function.eq_update_iff]
      exact ⟨hk'', fun m hm => ho'' m hm⟩
    · rw [dif_neg hc, dif_neg (fun h => hc (hiff.mpr h))]
  · by_cases h2 : (I.1.1 k).card = 2
    · rw [Finset.sum_eq_zero fun l hlm => Finset.sum_eq_zero fun i hi => hz l i hi (by
        rw [Function.update_of_ne (Ne.symm (Finset.ne_of_mem_erase hlm)), h2]; omega), add_zero]
      have hrep : ∀ i ∈ I.1.1 k, ∀ Ii : CombCell ι J n, Ii.1.1 k = {i₀} →
          (∀ m, m ≠ k → Ii.1.1 m = Function.update I.1.1 k ((I.1.1 k).erase i) m) →
          Ii.1.1 = Function.update I.1.1 k {i₀} := fun i _ Ii hk ho => by
        rw [Function.eq_update_iff]
        exact ⟨hk, fun m hm => (ho m hm).trans (Function.update_of_ne hm _ _)⟩
      have hcard : ∀ i ∈ I.1.1 k, ((Function.update I.1.1 k ((I.1.1 k).erase i)) k).card = 1 := fun i hi => by
        rw [Function.update_self, Finset.card_erase_of_mem hi, h2]
      refine block_pair J n g I k hJ h2 fun i hi j hj hi' hj' => ?_
      obtain ⟨Ii, hki, hoi, hgi⟩ := hg1 ⟨⟨_, hi'.1⟩, hi'.2⟩ (hcard i hi)
      obtain ⟨Ij, hkj, hoj, hgj⟩ := hg1 ⟨⟨_, hj'.1⟩, hj'.2⟩ (hcard j hj)
      rw [hgi, hgj]
      exact congrArg φ (cell_ext ((hrep i hi Ii hki hoi).trans (hrep j hj Ij hkj hoj).symm))
    · rw [Finset.sum_eq_zero fun i hi => hz k i hi (by
          rw [Function.update_self, Finset.card_erase_of_mem hi]
          have := Finset.card_pos.mpr ⟨i, hi⟩
          omega),
        Finset.sum_eq_zero fun l hlm => Finset.sum_eq_zero fun i hi => hz l i hi (by
          rw [Function.update_of_ne (Ne.symm (Finset.ne_of_mem_erase hlm))]; exact h1), add_zero]

/- English proof (translation)
Distinguish the cases in `hcell : Nonempty (CombCell ι J n)`. Use `swap`. Use `⟨0, ?_⟩` and prove the remaining obligations. Establish `: f - (0 : S) • singOne S J n = 0` using `funext fun I => (hcell ⟨I⟩).elim`. Rewrite using `[this]`.

Conclude with `Submodule.zero_mem _`. Take `⟨I₀⟩` from `hcell`. Set `i₀ : ∀ k, ι k` to `fun k => (I₀.1.2.1 k).choose`. Establish `key : ∀ T : Finset K, (∀ k ∈ T, J k = ∅) → ∃ φ : CombC S J n, combD S J n φ = 0 ∧ f - φ ∈ combB S J n ∧ ∀ I : CombCell ι J n, ((∀ k ∈ T, (I.1.1 k).card = 1) → ∃ I' : CombCell ι J n, (∀ k ∈ T, I'.1.1 k = {i₀ k}) ∧ (∀ l, l ∉ T → I'.1.1 l = I.1.1 l) ∧ φ I = f I') ∧ (¬ (∀ k ∈ T, (I.1 …`. Introduce `T`.

Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Introduce `_`. Use `⟨f, hf, by rw [sub_self]; exact Submodule.zero_mem _, fun I => ⟨fun _ => ⟨I, fun k hk => absurd hk (Finset.notMem_empty k), fun _ _ => rfl, rfl⟩, fun h => absurd (fun k hk => absurd hk (Finset.notMem_empty k)) h⟩⟩` and prove the remaining obligations. Consider the case `insert k T hk ih`.

Introduce `hT`. Take `⟨φ, hφ, hfφ, hφI⟩` from `ih fun m hm => hT m (Finset.mem_insert_of_mem hm)`. Establish `hJk : J k = ∅` using `hT k (Finset.mem_insert_self k T)`. Take `⟨g, hφg, hg⟩` from `hC S K ι J n k (i₀ k) (by rw [hJk]; exact Finset.notMem_empty _) φ hφ`. Use `⟨g, contract_cocycle J n k (i₀ k) hJk φ g hφ (fun I h1 => (hg I).1 ⟨hJk, h1⟩) (fun I h1 => (hg I).2 fun h => h1 h.2), ?_, fun I => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Use `Submodule.add_mem _ hfφ hφg` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Introduce `hI`. Take `⟨I₁, hI₁k, hI₁o, hgI⟩` from `(hg I).1 ⟨hJk, hI k (Finset.mem_insert_self k T)⟩`. Establish `hne : ∀ m ∈ T, m ≠ k` using `fun m hm h => hk (h ▸ hm)`.

Establish `hI₁T : ∀ m ∈ T, (I₁.1.1 m).card = 1` using `fun m hm => by`. Rewrite using `[hI₁o m (hne m hm)]`. Conclude with `hI m (Finset.mem_insert_of_mem hm)`. Take `⟨I', hI'T, hI'o, hφI₁⟩` from `(hφI I₁).1 hI₁T`. Use `⟨I', fun m hm => ?_, fun l hl => ?_, hgI.trans hφI₁⟩` and prove the remaining obligations.

Break down `Finset.mem_insert.mp hm with h | hm` into its components or cases. Rewrite using `[h, hI'o k hk, hI₁k]`. Conclude with `hI'T m hm`. Establish `hlk : l ≠ k` using `fun h => hl (by rw [h]; exact Finset.mem_insert_self k T)`. Rewrite using `[hI'o l (fun h => hl (Finset.mem_insert_of_mem h)), hI₁o l hlk]`.

Introduce `hI`. Distinguish the cases in `h1 : (I.1.1 k).card = 1`. Take `⟨I₁, hI₁k, hI₁o, hgI⟩` from `(hg I).1 ⟨hJk, h1⟩`. Rewrite using `[hgI]`. Use `(hφI I₁).2 fun hall => hI fun m hm => ?_` and prove the remaining obligations.

Break down `Finset.mem_insert.mp hm with h | hm` into its components or cases. Rewrite using `[h]`. Conclude with `h1`. Rewrite using `[← hI₁o m (fun h => hk (h ▸ hm))]`. Conclude with `hall m hm`.

Conclude with `(hg I).2 fun h => h1 h.2`. Take `⟨E, hE⟩ : ∃ E : Finset K, ∀ k, k ∈ E ↔ J k = ∅` from `⟨Finset.univ.filter fun k => J k = ∅, fun k => by simp⟩`. Take `⟨φ, -, hfφ, hφI⟩` from `key E fun k hk => (hE k).mp hk`. Establish `hval : ∀ I₁ I₂ : CombCell ι J n, (∀ k ∈ E, (I₁.1.1 k).card = 1) → (∀ k ∈ E, (I₂.1.1 k).card = 1) → φ I₁ = φ I₂`. Introduce `I₁ I₂ h₁ h₂`.

Take `⟨I₁', hk₁, ho₁, hφ₁⟩` from `(hφI I₁).1 h₁`. Take `⟨I₂', hk₂, ho₂, hφ₂⟩` from `(hφI I₂).1 h₂`. Establish `huniv : ∀ I : CombCell ι J n, ∀ l, l ∉ E → I.1.1 l = Finset.univ` using `fun I l hl => by`. Establish `hJl : J l = Finset.univ` using `(hJ l).resolve_left fun h => hl ((hE l).mpr h)`. Use `I.2 l` as an intermediate fact.

Rewrite `this` using `[hJl]`. Conclude with `Finset.univ_subset_iff.mp this`. Rewrite using `[hφ₁, hφ₂]`. Use `congrArg f (cell_ext (funext fun l => ?_))` and prove the remaining obligations. Distinguish the cases in `hl : l ∈ E`.

Rewrite using `[hk₁ l hl, hk₂ l hl]`. Rewrite using `[ho₁ l hl, ho₂ l hl, huniv I₁ l hl, huniv I₂ l hl]`. Use `⟨if h : ∃ I : CombCell ι J n, ∀ k ∈ E, (I.1.1 k).card = 1 then φ h.choose else 0, ?_⟩` and prove the remaining obligations. Establish `hφs : φ = (if h : ∃ I : CombCell ι J n, ∀ k ∈ E, (I.1.1 k).card = 1 then φ h.choose else 0) • singOne S J n`. Use function extensionality and compare the values at `I`.

Simplify using `only [Pi.smul_apply, singOne, smul_eq_mul]`. Distinguish the cases in `hI : ∀ k ∈ E, (I.1.1 k).card = 1`. Establish `h : ∃ I : CombCell ι J n, ∀ k ∈ E, (I.1.1 k).card = 1` using `⟨I, hI⟩`. Rewrite using `[dif_pos h, if_pos (fun k hk => hI k ((hE k).mpr hk)), mul_one]`. Conclude with `hval I h.choose hI h.choose_spec`.

Rewrite using `[if_neg (fun h => hI fun k hk => h k ((hE k).mp hk)), mul_zero]`. Conclude with `(hφI I).2 hI`. Rewrite using `[← hφs]`. Conclude with `hfφ`.
-/
theorem cyclic_cohom (hC : KHCombContract.Statement) (J : ∀ k, Finset (ι k)) (n : ℕ)
    (hJ : ∀ k, J k = ∅ ∨ J k = Finset.univ) (f : CombC S J n) (hf : combD S J n f = 0) :
    ∃ s : S, f - s • singOne S J n ∈ combB S J n := by
  classical
  by_cases hcell : Nonempty (CombCell ι J n)
  swap
  · refine ⟨0, ?_⟩
    have : f - (0 : S) • singOne S J n = 0 := funext fun I => (hcell ⟨I⟩).elim
    rw [this]
    exact Submodule.zero_mem _
  obtain ⟨I₀⟩ := hcell
  let i₀ : ∀ k, ι k := fun k => (I₀.1.2.1 k).choose
  have key : ∀ T : Finset K, (∀ k ∈ T, J k = ∅) → ∃ φ : CombC S J n, combD S J n φ = 0 ∧
      f - φ ∈ combB S J n ∧ ∀ I : CombCell ι J n,
        ((∀ k ∈ T, (I.1.1 k).card = 1) → ∃ I' : CombCell ι J n, (∀ k ∈ T, I'.1.1 k = {i₀ k}) ∧
          (∀ l, l ∉ T → I'.1.1 l = I.1.1 l) ∧ φ I = f I') ∧
        (¬ (∀ k ∈ T, (I.1.1 k).card = 1) → φ I = 0) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨f, hf, by rw [sub_self]; exact Submodule.zero_mem _, fun I => ⟨fun _ => ⟨I, fun k hk =>
        absurd hk (Finset.notMem_empty k), fun _ _ => rfl, rfl⟩, fun h => absurd (fun k hk =>
        absurd hk (Finset.notMem_empty k)) h⟩⟩
    | insert k T hk ih =>
      intro hT
      obtain ⟨φ, hφ, hfφ, hφI⟩ := ih fun m hm => hT m (Finset.mem_insert_of_mem hm)
      have hJk : J k = ∅ := hT k (Finset.mem_insert_self k T)
      obtain ⟨g, hφg, hg⟩ := hC S K ι J n k (i₀ k) (by rw [hJk]; exact Finset.notMem_empty _) φ hφ
      refine ⟨g, contract_cocycle J n k (i₀ k) hJk φ g hφ (fun I h1 => (hg I).1 ⟨hJk, h1⟩)
        (fun I h1 => (hg I).2 fun h => h1 h.2), ?_, fun I => ⟨?_, ?_⟩⟩
      · have := Submodule.add_mem _ hfφ hφg
        rwa [sub_add_sub_cancel] at this
      · intro hI
        obtain ⟨I₁, hI₁k, hI₁o, hgI⟩ := (hg I).1 ⟨hJk, hI k (Finset.mem_insert_self k T)⟩
        have hne : ∀ m ∈ T, m ≠ k := fun m hm h => hk (h ▸ hm)
        have hI₁T : ∀ m ∈ T, (I₁.1.1 m).card = 1 := fun m hm => by
          rw [hI₁o m (hne m hm)]
          exact hI m (Finset.mem_insert_of_mem hm)
        obtain ⟨I', hI'T, hI'o, hφI₁⟩ := (hφI I₁).1 hI₁T
        refine ⟨I', fun m hm => ?_, fun l hl => ?_, hgI.trans hφI₁⟩
        · rcases Finset.mem_insert.mp hm with h | hm
          · rw [h, hI'o k hk, hI₁k]
          · exact hI'T m hm
        · have hlk : l ≠ k := fun h => hl (by rw [h]; exact Finset.mem_insert_self k T)
          rw [hI'o l (fun h => hl (Finset.mem_insert_of_mem h)), hI₁o l hlk]
      · intro hI
        by_cases h1 : (I.1.1 k).card = 1
        · obtain ⟨I₁, hI₁k, hI₁o, hgI⟩ := (hg I).1 ⟨hJk, h1⟩
          rw [hgI]
          refine (hφI I₁).2 fun hall => hI fun m hm => ?_
          rcases Finset.mem_insert.mp hm with h | hm
          · rw [h]; exact h1
          · rw [← hI₁o m (fun h => hk (h ▸ hm))]
            exact hall m hm
        · exact (hg I).2 fun h => h1 h.2
  obtain ⟨E, hE⟩ : ∃ E : Finset K, ∀ k, k ∈ E ↔ J k = ∅ :=
    ⟨Finset.univ.filter fun k => J k = ∅, fun k => by simp⟩
  obtain ⟨φ, -, hfφ, hφI⟩ := key E fun k hk => (hE k).mp hk
  have hval : ∀ I₁ I₂ : CombCell ι J n, (∀ k ∈ E, (I₁.1.1 k).card = 1) → (∀ k ∈ E, (I₂.1.1 k).card = 1) →
      φ I₁ = φ I₂ := by
    intro I₁ I₂ h₁ h₂
    obtain ⟨I₁', hk₁, ho₁, hφ₁⟩ := (hφI I₁).1 h₁
    obtain ⟨I₂', hk₂, ho₂, hφ₂⟩ := (hφI I₂).1 h₂
    have huniv : ∀ I : CombCell ι J n, ∀ l, l ∉ E → I.1.1 l = Finset.univ := fun I l hl => by
      have hJl : J l = Finset.univ := (hJ l).resolve_left fun h => hl ((hE l).mpr h)
      have := I.2 l
      rw [hJl] at this
      exact Finset.univ_subset_iff.mp this
    rw [hφ₁, hφ₂]
    refine congrArg f (cell_ext (funext fun l => ?_))
    by_cases hl : l ∈ E
    · rw [hk₁ l hl, hk₂ l hl]
    · rw [ho₁ l hl, ho₂ l hl, huniv I₁ l hl, huniv I₂ l hl]
  refine ⟨if h : ∃ I : CombCell ι J n, ∀ k ∈ E, (I.1.1 k).card = 1 then φ h.choose else 0, ?_⟩
  have hφs : φ = (if h : ∃ I : CombCell ι J n, ∀ k ∈ E, (I.1.1 k).card = 1 then φ h.choose else 0) •
      singOne S J n := by
    funext I
    simp only [Pi.smul_apply, singOne, smul_eq_mul]
    by_cases hI : ∀ k ∈ E, (I.1.1 k).card = 1
    · have h : ∃ I : CombCell ι J n, ∀ k ∈ E, (I.1.1 k).card = 1 := ⟨I, hI⟩
      rw [dif_pos h, if_pos (fun k hk => hI k ((hE k).mpr hk)), mul_one]
      exact hval I h.choose hI h.choose_spec
    · rw [if_neg (fun h => hI fun k hk => h k ((hE k).mp hk)), mul_zero]
      exact (hφI I).2 hI
  rw [← hφs]
  exact hfφ

end KHCombCyclic

/- English proof (translation)
Introduce `S _ K _ _ ι _ _ J n hJ`. Conclude with `⟨KHCombCyclic.singOne_cocycle J n hJ, fun f hf => KHCombCyclic.cyclic_cohom hC J n hJ f hf⟩`.
-/
theorem KHCombCyclic.proof (hC : KHCombContract.Statement) : KHCombCyclic.Statement := by
  intro S _ K _ _ ι _ _ J n hJ
  exact ⟨KHCombCyclic.singOne_cocycle J n hJ, fun f hf => KHCombCyclic.cyclic_cohom hC J n hJ f hf⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
