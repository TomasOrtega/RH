import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff

open GlobalTheory.SeqCx

namespace GlobalTheory.SeqCx.ColDecomp

/- English proof (translation)
Introduce `u v h`. Conclude with `(Prod.mk.inj h).2`.
-/
lemma inj_pair {V W : Type} (l : List V) : Function.Injective (fun w : List W => (l, w)) := by
  intro u v h
  exact (Prod.mk.inj h).2

open Classical in
/- English proof (translation)
Rewrite using `[Finsupp.finset_sum_apply]`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single l]`. Conclude with `Finsupp.mapDomain_apply (inj_pair l) _ _`. Introduce `l' _ hne`.

Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises. Introduce and unpack `⟨w', hw'⟩`. Conclude with `hne (congrArg Prod.fst hw')`. Introduce `hl`. Conclude with `absurd h hl`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `l' hl'`. Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises. Introduce and unpack `⟨w', hw'⟩`. Take `rfl : l' = l` from `congrArg Prod.fst hw'`.

Conclude with `h hl'`.
-/
lemma sum_apply_pair {V W : Type} (T : Finset (List V)) (g : List V → List W →₀ ℤ) (l : List V) (w : List W) :
    (∑ l' ∈ T, Finsupp.mapDomain (fun w => (l', w)) (g l')) (l, w) = if l ∈ T then g l w else 0 := by
  rw [Finsupp.finset_sum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single l]
    · exact Finsupp.mapDomain_apply (inj_pair l) _ _
    · intro l' _ hne
      apply Finsupp.mapDomain_notin_range
      rintro ⟨w', hw'⟩
      exact hne (congrArg Prod.fst hw')
    · intro hl
      exact absurd h hl
  · apply Finset.sum_eq_zero
    intro l' hl'
    apply Finsupp.mapDomain_notin_range
    rintro ⟨w', hw'⟩
    obtain rfl : l' = l := congrArg Prod.fst hw'
    exact h hl'

/- English proof (translation)
Proceed by induction on `c using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add f g hf hg`. Rewrite using `[Finsupp.mapDomain_add, map_add, hf, hg, map_add, Finsupp.mapDomain_add]`. Consider the case `single w k`.

Rewrite using `[Finsupp.mapDomain_single]`. Simplify using `only [vbd, bd, Finsupp.linearCombination_single]`. Rewrite using `[one_smul, Finsupp.mapDomain_smul]`.
-/
lemma vbd_mapDomain {V W : Type} (l : List V) (c : List W →₀ ℤ) :
    vbd V W (Finsupp.mapDomain (fun w => (l, w)) c) = Finsupp.mapDomain (fun w => (l, w)) (bd W c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add, map_add, hf, hg, map_add, Finsupp.mapDomain_add]
  | single w k =>
    rw [Finsupp.mapDomain_single]
    simp only [vbd, bd, Finsupp.linearCombination_single]
    rw [one_smul, Finsupp.mapDomain_smul]

end GlobalTheory.SeqCx.ColDecomp

open GlobalTheory.SeqCx.ColDecomp in

/- English proof (translation)
Introduce `V W D a b hex x hx hvx`. Use `set T : Finset (List V) := x.support.image Prod.fst with hT`. Use `set g : List V → List W →₀ ℤ := fun l => x.curry l with hg`. Establish `hgapp : ∀ l w, g l w = x (l, w)` using `fun l w => Finsupp.curry_apply x l w`. Establish `hsupp : ∀ z ∈ x.support, z ∈ D ∧ z.1.length = a ∧ z.2.length = b` using `fun z hz => hx hz`.

Establish `hdec : x = ∑ l ∈ T, Finsupp.mapDomain (fun w => (l, w)) (g l)`. Use extensionality with `⟨l, w⟩`. Rewrite using `[sum_apply_pair]`. Use `split_ifs with h`. Rewrite using `[hgapp]`.

Assume the negation of the conclusion as `hne`. Conclude with `h (Finset.mem_image.2 ⟨(l, w), Finsupp.mem_support_iff.2 hne, rfl⟩)`. Establish `hvdec : vbd V W x = ∑ l ∈ T, Finsupp.mapDomain (fun w => (l, w)) (bd W (g l))` using `by conv_lhs => rw [hdec]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl (fun l _ => vbd_mapDomain l (g l))`.

Establish `hcyc : ∀ l ∈ T, bd W (g l) = 0`. Introduce `l hl`. Use extensionality with `w`. Use `congrArg (fun f => f (l, w)) hvdec` as an intermediate fact. Simplify using `only [hvx, sum_apply_pair, if_pos hl] at this`.

Simplify using `using this.symm`. Establish `hchain : ∀ l ∈ T, g l ∈ chains {w | (l, w) ∈ D} b`. Introduce `l hl`. Rewrite using `[chains, Finsupp.mem_supported]`. Introduce `w hw`.

Rewrite `hw` using `[Finset.mem_coe, Finsupp.mem_support_iff, hgapp]`. Use `hsupp (l, w) (Finsupp.mem_support_iff.2 hw)` as an intermediate fact. Conclude with `⟨this.1, this.2.2⟩`. Establish `hpre : ∀ l ∈ T, l.length = a ∧ ∃ w, (l, w) ∈ D`. Introduce `l hl`.

Take `⟨z, hz, rfl⟩` from `Finset.mem_image.1 hl`. Use `hsupp z hz` as an intermediate fact. Conclude with `⟨this.2.1, z.2, this.1⟩`. Establish `hy : ∀ l ∈ T, ∃ y ∈ chains {w | (l, w) ∈ D} (b + 1), bd W y = g l`. Introduce `l hl`.

Conclude with `hex l (hpre l hl).1 (hpre l hl).2 (g l) (hchain l hl) (hcyc l hl)`. Use `choose! y hymem hybd using hy`. Use `⟨∑ l ∈ T, Finsupp.mapDomain (fun w => (l, w)) (y l), ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.sum_mem _ (fun l hl => ?_)` and prove the remaining obligations. Rewrite using `[chains2, Finsupp.mem_supported]`.

Introduce `z hz`. Establish `hz'` using `Finsupp.mapDomain_support (Finset.mem_coe.1 hz)`. Take `⟨w, hw, rfl⟩` from `Finset.mem_image.1 hz'`. Establish `hyl` using `hymem l hl`. Rewrite `hyl` using `[chains, Finsupp.mem_supported]`.

Use `hyl (Finset.mem_coe.2 hw)` as an intermediate fact. Conclude with `⟨this.1, (hpre l hl).1, this.2⟩`. Rewrite using `[map_sum, hdec]`. Conclude with `Finset.sum_congr rfl (fun l hl => by rw [vbd_mapDomain, hybd l hl])`.
-/
theorem GlobalTheory.SeqCx.vertical_exact_of_columns : ∀ (V W : Type) (D : Set (List V × List W)) (a b : ℕ), (∀ l : List V, l.length = a → (∃ w, (l, w) ∈ D) → ExactAt {w | (l, w) ∈ D} b) → ∀ x ∈ chains2 D a b, vbd V W x = 0 → ∃ y ∈ chains2 D a (b + 1), vbd V W y = x := by
  classical
  intro V W D a b hex x hx hvx
  set T : Finset (List V) := x.support.image Prod.fst with hT
  set g : List V → List W →₀ ℤ := fun l => x.curry l with hg
  have hgapp : ∀ l w, g l w = x (l, w) := fun l w => Finsupp.curry_apply x l w
  have hsupp : ∀ z ∈ x.support, z ∈ D ∧ z.1.length = a ∧ z.2.length = b := fun z hz => hx hz
  have hdec : x = ∑ l ∈ T, Finsupp.mapDomain (fun w => (l, w)) (g l) := by
    ext ⟨l, w⟩
    rw [sum_apply_pair]
    split_ifs with h
    · rw [hgapp]
    · by_contra hne
      exact h (Finset.mem_image.2 ⟨(l, w), Finsupp.mem_support_iff.2 hne, rfl⟩)
  have hvdec : vbd V W x = ∑ l ∈ T, Finsupp.mapDomain (fun w => (l, w)) (bd W (g l)) := by
    conv_lhs => rw [hdec]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun l _ => vbd_mapDomain l (g l))
  have hcyc : ∀ l ∈ T, bd W (g l) = 0 := by
    intro l hl
    ext w
    have := congrArg (fun f => f (l, w)) hvdec
    simp only [hvx, sum_apply_pair, if_pos hl] at this
    simpa using this.symm
  have hchain : ∀ l ∈ T, g l ∈ chains {w | (l, w) ∈ D} b := by
    intro l hl
    rw [chains, Finsupp.mem_supported]
    intro w hw
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hgapp] at hw
    have := hsupp (l, w) (Finsupp.mem_support_iff.2 hw)
    exact ⟨this.1, this.2.2⟩
  have hpre : ∀ l ∈ T, l.length = a ∧ ∃ w, (l, w) ∈ D := by
    intro l hl
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hl
    have := hsupp z hz
    exact ⟨this.2.1, z.2, this.1⟩
  have hy : ∀ l ∈ T, ∃ y ∈ chains {w | (l, w) ∈ D} (b + 1), bd W y = g l := by
    intro l hl
    exact hex l (hpre l hl).1 (hpre l hl).2 (g l) (hchain l hl) (hcyc l hl)
  choose! y hymem hybd using hy
  refine ⟨∑ l ∈ T, Finsupp.mapDomain (fun w => (l, w)) (y l), ?_, ?_⟩
  · refine Submodule.sum_mem _ (fun l hl => ?_)
    rw [chains2, Finsupp.mem_supported]
    intro z hz
    have hz' := Finsupp.mapDomain_support (Finset.mem_coe.1 hz)
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz'
    have hyl := hymem l hl
    rw [chains, Finsupp.mem_supported] at hyl
    have := hyl (Finset.mem_coe.2 hw)
    exact ⟨this.1, (hpre l hl).1, this.2⟩
  · rw [map_sum, hdec]
    exact Finset.sum_congr rfl (fun l hl => by rw [vbd_mapDomain, hybd l hl])

section
open GlobalTheory.SeqCx
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.SeqCx.vertical_exact_of_columns`.
-/
theorem _root_.GlobalTheory.T.pairSeqVerticalCycle_is_boundary_of_slices_exact : ∀ (V W : Type) (D : Set (List V × List W)) (a b : ℕ), (∀ l : List V, l.length = a → (∃ w, (l, w) ∈ D) → ExactAt {w | (l, w) ∈ D} b) → ∀ x ∈ chains2 D a b, vbd V W x = 0 → ∃ y ∈ chains2 D a (b + 1), vbd V W y = x := by
  first
  | exact @GlobalTheory.SeqCx.vertical_exact_of_columns
end
