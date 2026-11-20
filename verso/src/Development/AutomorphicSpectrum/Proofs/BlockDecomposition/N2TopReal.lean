import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ExpansionTerms
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclicStandardTournament

noncomputable section

open Finset
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes

variable {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `c`. Simplify using `only [wtB, Pi.add_apply, Finset.filter_union]`. Rewrite using `[Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h), Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wtB_union {S T : Finset (Fin n × Fin n)} (h : Disjoint S T) : wtB (S ∪ T) = wtB S + wtB T := by
  funext c
  simp only [wtB, Pi.add_apply, Finset.filter_union]
  rw [Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h),
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]
  push_cast
  ring

/- English proof (translation)
Establish `h1 : wtB (S \ T ∪ T) = wtB (S \ T) + wtB T` using `GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_union Finset.sdiff_disjoint`. Rewrite `h1` using `[Finset.sdiff_union_of_subset h]`. Rewrite using `[h1, add_sub_cancel_right]`.
-/
theorem wtB_sdiff {S T : Finset (Fin n × Fin n)} (h : T ⊆ S) : wtB (S \ T) = wtB S - wtB T := by
  have h1 : wtB (S \ T ∪ T) = wtB (S \ T) + wtB T :=
    GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_union Finset.sdiff_disjoint
  rw [Finset.sdiff_union_of_subset h] at h1
  rw [h1, add_sub_cancel_right]

/- English proof (translation)
Use function extensionality and compare the values at `c`. Establish `e1 : (Finset.filter (fun p : Fin n × Fin n => p.1 = c) (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)).card = (univ.filter fun b : Fin n => lev c < lev b).card`. Rewrite using `[GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.card_fst]`. Use `congr 1`. Conclude with `Finset.filter_congr (fun b _ => by simp)`.

Establish `e2 : (Finset.filter (fun p : Fin n × Fin n => p.2 = c) (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)).card = (univ.filter fun b : Fin n => lev b < lev c).card`. Rewrite using `[GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.card_snd]`. Use `congr 1`. Conclude with `Finset.filter_congr (fun b _ => by simp)`. Simplify using `only [wtB, rhoU, e1, e2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem wtB_lev (lev : Fin n → ℕ) :
    wtB (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2) = fun c => 2 * rhoU lev c := by
  funext c
  have e1 : (Finset.filter (fun p : Fin n × Fin n => p.1 = c)
      (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)).card
      = (univ.filter fun b : Fin n => lev c < lev b).card := by
    rw [GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.card_fst]
    congr 1
    exact Finset.filter_congr (fun b _ => by simp)
  have e2 : (Finset.filter (fun p : Fin n × Fin n => p.2 = c)
      (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)).card
      = (univ.filter fun b : Fin n => lev b < lev c).card := by
    rw [GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.card_snd]
    congr 1
    exact Finset.filter_congr (fun b _ => by simp)
  simp only [wtB, rhoU, e1, e2]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `c`. Establish `e1 : (Finset.filter (fun p : Fin n × Fin n => p.1 = c) (univ.filter fun p : Fin n × Fin n => p.1 < p.2)).card = (Finset.Ioi c).card`. Rewrite using `[GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.card_fst]`. Use `congr 1`. Use extensionality with `b`.

Simplify using the standard rewrite rules. Establish `e2 : (Finset.filter (fun p : Fin n × Fin n => p.2 = c) (univ.filter fun p : Fin n × Fin n => p.1 < p.2)).card = (Finset.Iio c).card`. Rewrite using `[GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.card_snd]`. Use `congr 1`. Use extensionality with `b`.

Simplify using the standard rewrite rules. Establish `hc : (c : ℕ) < n` using `c.isLt`. Simplify using `only [wtB, rhoV, e1, e2, Fin.card_Ioi, Fin.card_Iio]`. Rewrite using `[Nat.cast_sub (by omega : (c : ℕ) ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem wtB_pos :
    wtB (univ.filter fun p : Fin n × Fin n => p.1 < p.2) = fun c => 2 * rhoV n c := by
  funext c
  have e1 : (Finset.filter (fun p : Fin n × Fin n => p.1 = c)
      (univ.filter fun p : Fin n × Fin n => p.1 < p.2)).card = (Finset.Ioi c).card := by
    rw [GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.card_fst]
    congr 1
    ext b
    simp
  have e2 : (Finset.filter (fun p : Fin n × Fin n => p.2 = c)
      (univ.filter fun p : Fin n × Fin n => p.1 < p.2)).card = (Finset.Iio c).card := by
    rw [GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.card_snd]
    congr 1
    ext b
    simp
  have hc : (c : ℕ) < n := c.isLt
  simp only [wtB, rhoV, e1, e2, Fin.card_Ioi, Fin.card_Iio]
  rw [Nat.cast_sub (by omega : (c : ℕ) ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  ring

/- English proof (translation)
Substitute `h` using the available equality. Establish `hm : Monotone ((fun a => -y a) ∘ ⇑w)`. Introduce `a b hab`. Use `hz.antitone hab` as an intermediate fact. Simplify using `only [Function.comp_apply] at this ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `key` using `(Tuple.comp_sort_eq_comp_iff_monotone (f := fun a => -y a) (σ := w)).mpr hm`. Use function extensionality and compare the values at `a`. Establish `ha` using `congrFun key a`. Simplify using `only [Function.comp_apply, neg_inj] at ha`.

Simplify using `only [domC, Function.comp_apply]`. Conclude with `ha.symm`.
-/
theorem domC_eq {y z : Fin n → ℝ} (hz : StrictAnti z) {w : Equiv.Perm (Fin n)} (h : z = y ∘ w) : domC y = z := by
  subst h
  have hm : Monotone ((fun a => -y a) ∘ ⇑w) := by
    intro a b hab
    have := hz.antitone hab
    simp only [Function.comp_apply] at this ⊢
    linarith
  have key := (Tuple.comp_sort_eq_comp_iff_monotone (f := fun a => -y a) (σ := w)).mpr hm
  funext a
  have ha := congrFun key a
  simp only [Function.comp_apply, neg_inj] at ha
  simp only [domC, Function.comp_apply]
  exact ha.symm

/- English proof (translation)
Simplify using `[PositivityTheory.RgBcC.RealD.nsq, Formalism.REAL.nsq, Formalism.REAL.dot, sq]`.
-/
theorem nsq_eq (x : Fin n → ℝ) : PositivityTheory.RgBcC.RealD.nsq x = Formalism.REAL.nsq x := by
  simp [PositivityTheory.RgBcC.RealD.nsq, Formalism.REAL.nsq, Formalism.REAL.dot, sq]

/- English proof (translation)
Establish `hmono : Monotone lev`. Unfold `PositivityTheory.RgBcC.RealD.IsLev at hl`. Conclude with `hl.1`. Unfold `PositivityTheory.RgBcC.RealD.IsSecondTypeWeight at h`. Take `⟨B, _hB, hBlev, hanti, w, hw⟩` from `h`.

Establish `hLP : (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2) ⊆ (univ.filter fun p : Fin n × Fin n => p.1 < p.2)`. Introduce `p hp`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢`. Conclude with `hmono.reflect_lt hp`. Establish `hBL : B ⊆ (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)`.

Introduce `p hp`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `hBlev p hp`. Establish `hdisj : Disjoint ((univ.filter fun p : Fin n × Fin n => p.1 < p.2) \ (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)) B` using `Finset.sdiff_disjoint.mono_right hBL`. Establish `hid : muQ lam lev + rhoV n - wtB B = (fun a => 2 * (lam a : ℝ) + 2 * rhoV n a) + rhoV n - wtB (((univ.filter fun p : Fin n × Fin n => p.1 < p.2) \ (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)) ∪ B)`.

Rewrite using `[GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_union hdisj, GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_sdiff hLP, GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_pos, GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_lev]`. Use function extensionality and compare the values at `a`. Simplify using `only [muQ, Pi.add_apply, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdom : domC ((fun a => 2 * (lam a : ℝ) + 2 * rhoV n a) + rhoV n - wtB (((univ.filter fun p : Fin n × Fin n => p.1 < p.2) \ (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)) ∪ B)) = ν + rhoV n` using `GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.domC_eq (w := w) hanti (by rw [hw, hid])`.

Unfold `PositivityTheory.RgBcC.RealD.topTypes`. Rewrite using `[Finset.mem_filter]`. Use `⟨Finset.mem_image.mpr ⟨((univ.filter fun p : Fin n × Fin n => p.1 < p.2) \ (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)) ∪ B, ?_, ?_⟩, hanti⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Introduce `p hp`.

Break down `Finset.mem_union.mp hp with h1 | h1` into its components or cases. Conclude with `(Finset.mem_filter.mp (Finset.mem_sdiff.mp h1).1).2`. Conclude with `hmono.reflect_lt (hBlev p h1)`. Simplify using `only [hdom, add_sub_cancel_right]`.
-/
theorem mem_topTypes {lam : Fin n → ℤ} {lev : Fin n → ℕ} (hl : IsLev lam lev) {ν : Fin n → ℝ}
    (h : IsSecondTypeWeight lam lev ν) : ν ∈ topTypes lam := by
  have hmono : Monotone lev := by
    unfold PositivityTheory.RgBcC.RealD.IsLev at hl
    exact hl.1
  unfold PositivityTheory.RgBcC.RealD.IsSecondTypeWeight at h
  obtain ⟨B, _hB, hBlev, hanti, w, hw⟩ := h
  have hLP : (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)
      ⊆ (univ.filter fun p : Fin n × Fin n => p.1 < p.2) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hmono.reflect_lt hp
  have hBL : B ⊆ (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hBlev p hp
  have hdisj : Disjoint ((univ.filter fun p : Fin n × Fin n => p.1 < p.2) \
      (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)) B :=
    Finset.sdiff_disjoint.mono_right hBL
  have hid : muQ lam lev + rhoV n - wtB B =
      (fun a => 2 * (lam a : ℝ) + 2 * rhoV n a) + rhoV n -
        wtB (((univ.filter fun p : Fin n × Fin n => p.1 < p.2) \
          (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)) ∪ B) := by
    rw [GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_union hdisj, GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_sdiff hLP,
      GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_pos, GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_lev]
    funext a
    simp only [muQ, Pi.add_apply, Pi.sub_apply]
    ring
  have hdom : domC ((fun a => 2 * (lam a : ℝ) + 2 * rhoV n a) + rhoV n -
        wtB (((univ.filter fun p : Fin n × Fin n => p.1 < p.2) \
          (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)) ∪ B)) = ν + rhoV n :=
    GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.domC_eq (w := w) hanti (by rw [hw, hid])
  unfold PositivityTheory.RgBcC.RealD.topTypes
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_image.mpr ⟨((univ.filter fun p : Fin n × Fin n => p.1 < p.2) \
      (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)) ∪ B, ?_, ?_⟩, hanti⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro p hp
    rcases Finset.mem_union.mp hp with h1 | h1
    · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp h1).1).2
    · exact hmono.reflect_lt (hBlev p h1)
  · simp only [hdom, add_sub_cancel_right]

/- English proof (translation)
Unfold `PositivityTheory.RgBcC.RealD.SecondTypeWeightsShorter`. Introduce `m lam hlam lev hl ν h`. Use `⟨GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.mem_topTypes hl h, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.nsq_eq, GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.nsq_eq]`. Conclude with `GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.nsq_lt m lam hlam lev hl ν h`.
-/
theorem n2T : PositivityTheory.RgBcC.RealD.SecondTypeWeightsShorter := by
  unfold PositivityTheory.RgBcC.RealD.SecondTypeWeightsShorter
  intro m lam hlam lev hl ν h
  refine ⟨GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.mem_topTypes hl h, ?_⟩
  rw [GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.nsq_eq, GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.nsq_eq]
  exact GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.nsq_lt m lam hlam lev hl ν h

end GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes
