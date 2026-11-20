import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductJacquetShuffleCountStatement

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspShuffle

open Zc.Comb

variable {α β : Type*}

/- English proof (translation)
Proceed by induction on `P with`. Consider the case `nil => exact Zc.Comb.Interleave.nil`. Consider the case `cons p P ih`. Consider the cases of `hq : q p with`. Consider the case `true`.

Simplify using `only [List.filter_cons, hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.map_cons]`. Conclude with `Zc.Comb.Interleave.left ih`. Consider the case `false`. Simplify using `only [List.filter_cons, hq, Bool.not_false, Bool.false_eq_true, ↓reduceIte, List.map_cons]`. Conclude with `Zc.Comb.Interleave.right ih`.
-/
theorem interleave_filter (f : β → α) (q : β → Bool) (P : List β) :
    Interleave ((P.filter q).map f) ((P.filter fun p => !q p).map f) (P.map f) := by
  induction P with
  | nil => exact Zc.Comb.Interleave.nil
  | cons p P ih =>
    cases hq : q p with
    | true =>
      simp only [List.filter_cons, hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        List.map_cons]
      exact Zc.Comb.Interleave.left ih
    | false =>
      simp only [List.filter_cons, hq, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
        List.map_cons]
      exact Zc.Comb.Interleave.right ih

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `s P hP`. Establish `hnil : P = []` using `List.eq_nil_iff_forall_not_mem.mpr fun p hp => by`. Use `hP p hp` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Substitute `hnil` using the available equality. Conclude with `Zc.Comb.Shuffle.nil`. Consider the case `succ n ih`. Introduce `s P hP`.

Simplify using `only [List.range'_succ, List.map_cons]`. Use `Zc.Comb.Shuffle.cons (v := (P.filter fun p => !decide (c p = s)).map f) ?_ (GlobalTheory.CompanionTheory.CuspShuffle.interleave_filter f (fun p => decide (c p = s)) P)` and prove the remaining obligations. Establish `h` using `ih (s + 1) (P.filter fun p => !decide (c p = s)) (by`. Introduce `p hp`. Rewrite `hp` using `[List.mem_filter]`.

Establish `h1` using `hP p hp.1`. Establish `hne : c p ≠ s` using `by simpa using hp.2`. Use the proof step `omega)`. Use `h using 1` and compare the differences between its conclusion and the goal. Apply `List.map_congr_left` to reduce the goal to its premises.

Introduce `i hi`. Rewrite `hi` using `[List.mem_range'_1]`. Rewrite using `[List.filter_filter]`. Use `congr 1`. Apply `List.filter_congr` to reduce the goal to its premises.

Introduce `p _`. Distinguish the cases in `hc : c p = i`. Establish `his : i ≠ s` using `by omega`. Simplify using `[hc, his]`. Simplify using `[hc]`.
-/
theorem shuffle_range (f : β → α) (c : β → ℕ) (n : ℕ) : ∀ (s : ℕ) (P : List β),
    (∀ p ∈ P, s ≤ c p ∧ c p < s + n) →
      Shuffle ((List.range' s n).map fun i => (P.filter fun p => c p = i).map f) (P.map f) := by
  induction n with
  | zero =>
    intro s P hP
    have hnil : P = [] := List.eq_nil_iff_forall_not_mem.mpr fun p hp => by
      have := hP p hp
      omega
    subst hnil
    exact Zc.Comb.Shuffle.nil
  | succ n ih =>
    intro s P hP
    simp only [List.range'_succ, List.map_cons]
    refine Zc.Comb.Shuffle.cons (v := (P.filter fun p => !decide (c p = s)).map f) ?_
      (GlobalTheory.CompanionTheory.CuspShuffle.interleave_filter f (fun p => decide (c p = s)) P)
    have h := ih (s + 1) (P.filter fun p => !decide (c p = s)) (by
      intro p hp
      rw [List.mem_filter] at hp
      have h1 := hP p hp.1
      have hne : c p ≠ s := by simpa using hp.2
      omega)
    convert h using 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range'_1] at hi
    rw [List.filter_filter]
    congr 1
    apply List.filter_congr
    intro p _
    by_cases hc : c p = i
    · have his : i ≠ s := by omega
      simp [hc, his]
    · simp [hc]

/- English proof (translation)
Establish `key` using `GlobalTheory.CompanionTheory.CuspShuffle.shuffle_range W.get (fun p => (c p : ℕ)) h 0 (List.finRange W.length) (fun p _ => ⟨Nat.zero_le _, by simpa using (c p).isLt⟩)`. Use `key using 1` and compare the differences between its conclusion and the goal. Apply `List.ext_getElem` to reduce the goal to its premises. Simplify using the standard rewrite rules. Introduce `i h1 h2`.

Rewrite using `[List.getElem_ofFn, List.getElem_map, List.getElem_range', ← hD]`. Unfold `Zc.Cos.sub`. Use `congr 1`. Apply `List.filter_congr` to reduce the goal to its premises. Introduce `p _`.

Simplify using `[Fin.ext_iff]`. Apply the tactic sequence `apply List.ext_getElem <;> simp`.
-/
theorem shuffle_of_colouring {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (D : Fin h → List α)
    (hD : ∀ i, Zc.Cos.sub W c i = D i) : Shuffle (List.ofFn D) W := by
  have key := GlobalTheory.CompanionTheory.CuspShuffle.shuffle_range W.get (fun p => (c p : ℕ)) h 0 (List.finRange W.length)
    (fun p _ => ⟨Nat.zero_le _, by simpa using (c p).isLt⟩)
  convert key using 1
  · apply List.ext_getElem
    · simp
    · intro i h1 h2
      rw [List.getElem_ofFn, List.getElem_map, List.getElem_range', ← hD]
      unfold Zc.Cos.sub
      congr 1
      apply List.filter_congr
      intro p _
      simp [Fin.ext_iff]
  · apply List.ext_getElem <;> simp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Unfold `Zc.Cos.decWord Zc.M.decW`. Apply `List.ext_getElem` to reduce the goal to its premises. Simplify using the standard rewrite rules. Introduce `i h1 h2`. Rewrite using `[List.getElem_reverse, List.getElem_ofFn, List.getElem_ofFn]`.

Use `congr 1`. Use `ext`. Simplify using `only [Fin.val_rev, List.length_ofFn]`. Use linear arithmetic over natural numbers and integers.
-/
theorem decWord_eq_decW (Δ : Segment k) : Zc.Cos.decWord Δ = decW Δ := by
  unfold Zc.Cos.decWord Zc.M.decW
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_reverse, List.getElem_ofFn, List.getElem_ofFn]
    congr 1
    ext
    simp only [Fin.val_rev, List.length_ofFn]
    omega

/- English proof (translation)
Take `⟨hsum, hne⟩` from `hw`. Establish `hmult` using `GlobalTheory.T.segment_product_jacquet_shuffle_count hA hL Δ x hd hΔ w hc`. Establish `hpos : Zc.Cos.jmL w (GlobalTheory.LocGL.prodIrr x hd) ≠ 0`. Unfold `Zc.Cos.jmL`. Rewrite using `[dif_pos hsum]`.

Conclude with `hne`. Rewrite `hpos` using `[hmult]`. Establish `hcard : Zc.Cos.shuffleCount w (fun i => Zc.Cos.decWord (Δ i)) ≠ 0` using `by exact_mod_cast hpos`. Unfold `Zc.Cos.shuffleCount at hcard`. Take `⟨col, hcol⟩` from `Finset.card_ne_zero.mp hcard`.

Establish `hcol' : ∀ i, Zc.Cos.sub w col i = Zc.Cos.decWord (Δ i)` using `by simpa using hcol`. Unfold `Zc.M.InShW`. Use `⟨List.ofFn Δ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.univ_val_map]`. Rewrite using `[List.map_ofFn]`.

Establish `e : (Zc.M.decW ∘ Δ) = fun i => Zc.Cos.decWord (Δ i)`. Use function extensionality and compare the values at `fun i => (GlobalTheory.CompanionTheory.CuspShuffle.decWord_eq_decW (Δ i)).symm`. Rewrite using `[e]`. Conclude with `GlobalTheory.CompanionTheory.CuspShuffle.shuffle_of_colouring w col _ hcol'`.
-/
theorem inShW_of_wd {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hL : LSegJacquet k) {h N : ℕ} (x : Fin h → IrrGL k)
    (hd : ∑ a, (x a).1 = N) (Δ : Fin h → Segment k) (hΔ : ∀ i, IsLSeg (Δ i) (x i).rep) (w : List (IrrGL k))
    (hc : ∀ c ∈ w, c.IsCusp) (hw : Wd (prodIrr x hd) w) : InShW (Finset.univ.val.map Δ) w := by
  obtain ⟨hsum, hne⟩ := hw
  have hmult := GlobalTheory.T.segment_product_jacquet_shuffle_count hA hL Δ x hd hΔ w hc
  have hpos : Zc.Cos.jmL w (GlobalTheory.LocGL.prodIrr x hd) ≠ 0 := by
    unfold Zc.Cos.jmL
    rw [dif_pos hsum]
    exact hne
  rw [hmult] at hpos
  have hcard : Zc.Cos.shuffleCount w (fun i => Zc.Cos.decWord (Δ i)) ≠ 0 := by exact_mod_cast hpos
  unfold Zc.Cos.shuffleCount at hcard
  obtain ⟨col, hcol⟩ := Finset.card_ne_zero.mp hcard
  have hcol' : ∀ i, Zc.Cos.sub w col i = Zc.Cos.decWord (Δ i) := by simpa using hcol
  unfold Zc.M.InShW
  refine ⟨List.ofFn Δ, ?_, ?_⟩
  · rw [Fin.univ_val_map]
  · rw [List.map_ofFn]
    have e : (Zc.M.decW ∘ Δ) = fun i => Zc.Cos.decWord (Δ i) :=
      funext fun i => (GlobalTheory.CompanionTheory.CuspShuffle.decWord_eq_decW (Δ i)).symm
    rw [e]
    exact GlobalTheory.CompanionTheory.CuspShuffle.shuffle_of_colouring w col _ hcol'

end GlobalTheory.CompanionTheory.CuspShuffle

end
