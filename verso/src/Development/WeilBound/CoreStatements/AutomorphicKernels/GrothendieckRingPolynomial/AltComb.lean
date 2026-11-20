import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

noncomputable section

open Zc.Cos

namespace PositivityTheory.Groth.AltC

/- English proof (translation)
Proceed by induction on `hs with`. Consider the case `slnil => rfl`. Consider the case `@cons l m a hs ih`. Establish `ha : a ∉ l` using `fun h => (List.nodup_cons.1 hm).1 (hs.subset h)`. Rewrite using `[List.filter_cons_of_neg (by simpa using ha)]`.

Conclude with `ih (List.nodup_cons.1 hm).2`. Consider the case `@cons_cons l m a hs ih`. Rewrite using `[List.filter_cons_of_pos (by simp)]`. Use `congr 1`. Rewrite using `[← ih (List.nodup_cons.1 hm).2]`.

Apply `List.filter_congr` to reduce the goal to its premises. Introduce `x hx`. Establish `: x ≠ a` using `fun h => (List.nodup_cons.1 hm).1 (h ▸ hx)`. Simplify using `[this, hx]`.
-/
theorem filter_mem_eq_of_sublist {α : Type*} [DecidableEq α] {l m : List α} (hs : l.Sublist m)
    (hm : m.Nodup) : m.filter (fun x => decide (x ∈ l)) = l := by
  induction hs with
  | slnil => rfl
  | @cons l m a hs ih =>
    have ha : a ∉ l := fun h => (List.nodup_cons.1 hm).1 (hs.subset h)
    rw [List.filter_cons_of_neg (by simpa using ha)]
    exact ih (List.nodup_cons.1 hm).2
  | @cons_cons l m a hs ih =>
    rw [List.filter_cons_of_pos (by simp)]
    congr 1
    rw [← ih (List.nodup_cons.1 hm).2]
    apply List.filter_congr
    intro x hx
    have : x ≠ a := fun h => (List.nodup_cons.1 hm).1 (h ▸ hx)
    simp [this, hx]

/- English proof (translation)
Unfold `sub`. Simplify using `[List.mem_map, List.mem_filter, List.mem_finRange]`.
-/
theorem mem_sub {α : Type*} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (i : Fin h) (x : α) :
    x ∈ sub W c i ↔ ∃ p, c p = i ∧ W.get p = x := by
  unfold sub
  simp [List.mem_map, List.mem_filter, List.mem_finRange]

/- English proof (translation)
The claim follows from `(mem_sub W c (c p) _).2 ⟨p, rfl, rfl⟩`.
-/
theorem mem_sub_self {α : Type*} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (p : Fin W.length) :
    W.get p ∈ sub W c (c p) :=
  (mem_sub W c (c p) _).2 ⟨p, rfl, rfl⟩

/- English proof (translation)
Unfold `sub`. Use `(List.filter_sublist (p := fun p => decide (c p = i)) (l := List.finRange W.length)).map W.get` as an intermediate fact. Rewrite `this` using `[← List.ofFn_eq_map, List.ofFn_get]`. Then use the resulting hypothesis.
-/
theorem sub_sublist {α : Type*} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (i : Fin h) :
    (sub W c i).Sublist W := by
  unfold sub
  have := (List.filter_sublist (p := fun p => decide (c p = i)) (l := List.finRange W.length)).map W.get
  rwa [← List.ofFn_eq_map, List.ofFn_get] at this

open Classical in

/- English proof (translation)
Unfold `shuffleCount`. Use `split_ifs with hc`. Rewrite using `[Finset.card_eq_one] choose c0 hc0 using fun p : Fin W.length => (hc.2 (W.get p) (List.get_mem W p)).exists`. Establish `hu : ∀ p y, W.get p ∈ D y → y = c0 p` using `fun p y hy => (hc.2 (W.get p) (List.get_mem W p)).unique hy (hc0 p)`. Use `⟨c0, ?_⟩` and prove the remaining obligations.

Use extensionality with `c`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `hcs`. Use function extensionality and compare the values at `p`.

Use `mem_sub_self W c p` as an intermediate fact. Rewrite `this` using `[hcs (c p)]`. Conclude with `hu p (c p) this`. Introduce `hcc i`. Rewrite using `[hcc]`.

Establish `: sub W c0 i = W.filter (fun x => decide (x ∈ D i))`. Unfold `sub`. Use `conv_rhs => rw [← List.ofFn_get W, List.ofFn_eq_map, List.filter_map]`. Use `congr 1`. Apply `List.filter_congr` to reduce the goal to its premises.

Introduce `p _`. Simplify using `only [Function.comp, decide_eq_decide]`. Conclude with `⟨fun h => h ▸ hc0 p, fun h => (hu p i h).symm⟩`. Rewrite using `[this, filter_mem_eq_of_sublist (hc.1 i) hW]`. Rewrite using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`.

Introduce `c _ hcs`. Apply `hc` to reduce the goal to its premises. Use `⟨fun i => hcs i ▸ sub_sublist W c i, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨p, rfl⟩` from `List.get_of_mem hx`. Use `⟨c p, ?_, fun j hj => ?_⟩` and prove the remaining obligations.

Use `show W.get p ∈ D (c p)`. Rewrite using `[← hcs (c p)]`. Conclude with `mem_sub_self W c p`. Simplify using `only at hj`. Rewrite `hj` using `[← hcs j]`.

Take `⟨q, hq, hqp⟩` from `(mem_sub W c j _).1 hj`. Use `hW.get_inj_iff.1 hqp` as an intermediate fact. Substitute `this` using the available equality. Conclude with `hq.symm`.
-/
theorem shuffleCount_eq {α : Type*} {h : ℕ} (W : List α) (D : Fin h → List α) (hW : W.Nodup) :
    shuffleCount W D = if (∀ i, (D i).Sublist W) ∧ (∀ x ∈ W, ∃! i, x ∈ D i) then 1 else 0 := by
  unfold shuffleCount
  split_ifs with hc
  · rw [Finset.card_eq_one]
    choose c0 hc0 using fun p : Fin W.length => (hc.2 (W.get p) (List.get_mem W p)).exists
    have hu : ∀ p y, W.get p ∈ D y → y = c0 p := fun p y hy =>
      (hc.2 (W.get p) (List.get_mem W p)).unique hy (hc0 p)
    refine ⟨c0, ?_⟩
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hcs
      funext p
      have := mem_sub_self W c p
      rw [hcs (c p)] at this
      exact hu p (c p) this
    · intro hcc i
      rw [hcc]
      have : sub W c0 i = W.filter (fun x => decide (x ∈ D i)) := by
        unfold sub
        conv_rhs => rw [← List.ofFn_get W, List.ofFn_eq_map, List.filter_map]
        congr 1
        apply List.filter_congr
        intro p _
        simp only [Function.comp, decide_eq_decide]
        exact ⟨fun h => h ▸ hc0 p, fun h => (hu p i h).symm⟩
      rw [this, filter_mem_eq_of_sublist (hc.1 i) hW]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c _ hcs
    apply hc
    refine ⟨fun i => hcs i ▸ sub_sublist W c i, fun x hx => ?_⟩
    obtain ⟨p, rfl⟩ := List.get_of_mem hx
    refine ⟨c p, ?_, fun j hj => ?_⟩
    · show W.get p ∈ D (c p)
      rw [← hcs (c p)]; exact mem_sub_self W c p
    simp only at hj
    rw [← hcs j] at hj
    obtain ⟨q, hq, hqp⟩ := (mem_sub W c j _).1 hj
    have := hW.get_inj_iff.1 hqp
    subst this
    exact hq.symm

/- English proof (translation)
Establish `hs : ∀ i, ((E i).map f).Sublist (w.map f) ↔ (E i).Sublist w`. Introduce `i`. Use `⟨fun H => ?_, fun H => H.map f⟩` and prove the remaining obligations. Take `⟨l', hl', he⟩` from `List.sublist_map_iff.1 H`. Rewrite using `[List.map_injective_iff.2 hf he]` and apply the resulting hypothesis.

Simplify using `only [hs, List.forall_mem_map, List.mem_map_of_injective hf]`.
-/
theorem cond_map {β α : Type*} {h : ℕ} (f : β → α) (hf : Function.Injective f) (w : List β)
    (E : Fin h → List β) :
    ((∀ i, ((E i).map f).Sublist (w.map f)) ∧ (∀ x ∈ w.map f, ∃! i, x ∈ (E i).map f)) ↔
      ((∀ i, (E i).Sublist w) ∧ (∀ y ∈ w, ∃! i, y ∈ E i)) := by
  have hs : ∀ i, ((E i).map f).Sublist (w.map f) ↔ (E i).Sublist w := by
    intro i
    refine ⟨fun H => ?_, fun H => H.map f⟩
    obtain ⟨l', hl', he⟩ := List.sublist_map_iff.1 H
    rwa [List.map_injective_iff.2 hf he]
  simp only [hs, List.forall_mem_map, List.mem_map_of_injective hf]

def wN (L : ℕ) (T : Finset ℕ) : List ℕ :=
  ((List.range L).filter (fun x => decide (x ∈ T))).reverse ++ (List.range L).filter (fun x => decide (x ∉ T))

/- English proof (translation)
Unfold `wN`. Apply the tactic sequence `by_cases hx : x ∈ T <;> simp [hx]`.
-/
theorem mem_wN {L x : ℕ} {T : Finset ℕ} : x ∈ wN L T ↔ x < L := by
  unfold wN
  by_cases hx : x ∈ T <;> simp [hx]

/- English proof (translation)
Unfold `wN`. Rewrite using `[List.nodup_append]`. Use `⟨List.nodup_reverse.2 ((List.nodup_range).filter _), (List.nodup_range).filter _, ?_⟩` and prove the remaining obligations. Introduce `a ha c hc hac`. Substitute `hac` using the available equality.

Simplify using `at ha hc`. Conclude with `hc.2 ha.2`.
-/
theorem nodup_wN (L : ℕ) (T : Finset ℕ) : (wN L T).Nodup := by
  unfold wN
  rw [List.nodup_append]
  refine ⟨List.nodup_reverse.2 ((List.nodup_range).filter _), (List.nodup_range).filter _, ?_⟩
  intro a ha c hc hac
  subst hac
  simp at ha hc
  exact hc.2 ha.2

/- English proof (translation)
The claim follows from `List.sublist_of_subperm_of_pairwise (List.subperm_of_subset hl.nodup hs) hl hm`.
-/
theorem sublist_of_lt {l m : List ℕ} (hl : l.Pairwise (· < ·)) (hm : m.Pairwise (· < ·))
    (hs : ∀ x ∈ l, x ∈ m) : l.Sublist m :=
  List.sublist_of_subperm_of_pairwise (List.subperm_of_subset hl.nodup hs) hl hm

/- English proof (translation)
Establish `hA : ((List.range L).filter (fun x => decide (x ∈ T))).Pairwise (· < ·)` using `List.pairwise_lt_range.filter _`. Establish `hB : ((List.range L).filter (fun x => decide (x ∉ T))).Pairwise (· < ·)` using `List.pairwise_lt_range.filter _`. Prove the components needed by the constructor for the conclusion. Introduce `hs x hbx hxl`. Assume the negation of the conclusion as `hxT`.

Take `⟨F1, F2, hE, h1, h2⟩` from `List.sublist_append_iff.1 hs`. Establish `hxE : x ∈ (List.range' b l).reverse`. Simplify using `only [List.mem_reverse, List.mem_range'_1]`. Use linear arithmetic over natural numbers and integers. Establish `hbE : b ∈ (List.range' b l).reverse`.

Simplify using `only [List.mem_reverse, List.mem_range'_1]`. Use linear arithmetic over natural numbers and integers. Establish `hpw : (F1 ++ F2).Pairwise (fun a c => c < a)`. Rewrite using `[← hE]`. Conclude with `List.pairwise_reverse.2 List.pairwise_lt_range'`.

Establish `hx2 : x ∈ F2`. Rewrite `hxE` using `[hE]`. Break down `List.mem_append.1 hxE with h | h` into its components or cases. Use `h1.subset h` as an intermediate fact. Simplify using `at this`.

Conclude with `absurd this.2 hxT`. Conclude with `h`. Establish `hb2 : b ∈ F2`. Rewrite `hbE` using `[hE]`. Break down `List.mem_append.1 hbE with h | h` into its components or cases.

Use `(List.pairwise_append.1 hpw).2.2 b h x hx2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `h`. Establish `hinc : F2.Pairwise (· < ·)` using `hB.sublist h2`. Establish `hdec` using `(List.pairwise_append.1 hpw).2.1`.

Break down `F2 with _ | ⟨y, _ | ⟨z, t⟩⟩` into its components or cases. Simplify using `at hx2`. Simplify using `at hx2 hb2`. Use linear arithmetic over natural numbers and integers. Establish `a1` using `(List.pairwise_cons.1 hinc).1 z (by simp)`.

Establish `a2` using `(List.pairwise_cons.1 hdec).1 z (by simp)`. Use linear arithmetic over natural numbers and integers. Introduce `hT`. Distinguish the cases in `hb : b ∈ T`. Establish `: (List.range' b l).Sublist ((List.range L).filter (fun x => decide (x ∈ T)))`.

Use `sublist_of_lt List.pairwise_lt_range' hA fun x hx => ?_` and prove the remaining obligations. Rewrite `hx` using `[List.mem_range'_1]`. Simplify using `only [List.mem_filter, List.mem_range, decide_eq_true_eq]`. Use `⟨by omega, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_or_lt_of_le hx.1 with h | h` into its components or cases.

Conclude with `h ▸ hb`. Conclude with `hT x h hx.2`. Conclude with `(List.reverse_sublist.2 this).trans (List.sublist_append_left _ _)`. Break down `l with _ | m` into its components or cases. Simplify using the standard rewrite rules.

Rewrite using `[List.range'_succ, List.reverse_cons]`. Establish `: (List.range' (b + 1) m).Sublist ((List.range L).filter (fun x => decide (x ∈ T)))`. Use `sublist_of_lt List.pairwise_lt_range' hA fun x hx => ?_` and prove the remaining obligations. Rewrite `hx` using `[List.mem_range'_1]`. Simplify using `only [List.mem_filter, List.mem_range, decide_eq_true_eq]`.

Conclude with `⟨by omega, hT x (by omega) (by omega)⟩`. Use `(List.reverse_sublist.2 this).append (List.singleton_sublist.2 ?_)` and prove the remaining obligations. Simplify using `only [List.mem_filter, List.mem_range, decide_eq_true_eq]`. Conclude with `⟨by omega, hb⟩`.
-/
theorem run_sublist {L b l : ℕ} {T : Finset ℕ} (hbl : b + l ≤ L) :
    ((List.range' b l).reverse).Sublist (wN L T) ↔ ∀ x, b < x → x < b + l → x ∈ T := by
  have hA : ((List.range L).filter (fun x => decide (x ∈ T))).Pairwise (· < ·) :=
    List.pairwise_lt_range.filter _
  have hB : ((List.range L).filter (fun x => decide (x ∉ T))).Pairwise (· < ·) :=
    List.pairwise_lt_range.filter _
  constructor
  · intro hs x hbx hxl
    by_contra hxT
    obtain ⟨F1, F2, hE, h1, h2⟩ := List.sublist_append_iff.1 hs
    have hxE : x ∈ (List.range' b l).reverse := by
      simp only [List.mem_reverse, List.mem_range'_1]; omega
    have hbE : b ∈ (List.range' b l).reverse := by
      simp only [List.mem_reverse, List.mem_range'_1]; omega
    have hpw : (F1 ++ F2).Pairwise (fun a c => c < a) := by
      rw [← hE]; exact List.pairwise_reverse.2 List.pairwise_lt_range'
    have hx2 : x ∈ F2 := by
      rw [hE] at hxE
      rcases List.mem_append.1 hxE with h | h
      · have := h1.subset h
        simp at this
        exact absurd this.2 hxT
      · exact h
    have hb2 : b ∈ F2 := by
      rw [hE] at hbE
      rcases List.mem_append.1 hbE with h | h
      · have := (List.pairwise_append.1 hpw).2.2 b h x hx2
        omega
      · exact h
    have hinc : F2.Pairwise (· < ·) := hB.sublist h2
    have hdec := (List.pairwise_append.1 hpw).2.1
    rcases F2 with _ | ⟨y, _ | ⟨z, t⟩⟩
    · simp at hx2
    · simp at hx2 hb2
      omega
    · have a1 := (List.pairwise_cons.1 hinc).1 z (by simp)
      have a2 := (List.pairwise_cons.1 hdec).1 z (by simp)
      omega
  · intro hT
    by_cases hb : b ∈ T
    · have : (List.range' b l).Sublist ((List.range L).filter (fun x => decide (x ∈ T))) := by
        refine sublist_of_lt List.pairwise_lt_range' hA fun x hx => ?_
        rw [List.mem_range'_1] at hx
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
        refine ⟨by omega, ?_⟩
        rcases Nat.eq_or_lt_of_le hx.1 with h | h
        · exact h ▸ hb
        · exact hT x h hx.2
      exact (List.reverse_sublist.2 this).trans (List.sublist_append_left _ _)
    · rcases l with _ | m
      · simp
      rw [List.range'_succ, List.reverse_cons]
      have : (List.range' (b + 1) m).Sublist ((List.range L).filter (fun x => decide (x ∈ T))) := by
        refine sublist_of_lt List.pairwise_lt_range' hA fun x hx => ?_
        rw [List.mem_range'_1] at hx
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨by omega, hT x (by omega) (by omega)⟩
      refine (List.reverse_sublist.2 this).append (List.singleton_sublist.2 ?_)
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨by omega, hb⟩

def Cond (L : ℕ) (T : Finset ℕ) {h : ℕ} (b l : Fin h → ℕ) : Prop :=
  (∀ i, ((List.range' (b i) (l i)).reverse).Sublist (wN L T)) ∧
    (∀ x ∈ wN L T, ∃! i, x ∈ (List.range' (b i) (l i)).reverse)

/- English proof (translation)
Establish `hmem : ∀ i x, x ∈ (List.range' (b i) (l i)).reverse ↔ b i ≤ x ∧ x < b i + l i`. Introduce `i x`. Simplify using `[List.mem_range'_1]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Establish `hb : ∀ i, b i + l i ≤ L` using `fun i => by`. Establish `hi` using `hl i`. Use `(h1 i).subset ((hmem i (b i + l i - 1)).2 ⟨by omega, by omega⟩)` as an intermediate fact. Rewrite `this` using `[mem_wN]`. Use linear arithmetic over natural numbers and integers.

Use `⟨hb, fun x hx => ?_, fun i => (run_sublist (hb i)).1 (h1 i)⟩` and prove the remaining obligations. Take `⟨i, hi, hu⟩` from `h2 x (mem_wN.2 hx)`. Conclude with `⟨i, (hmem i x).1 hi, fun j hj => hu j ((hmem j x).2 hj)⟩`. Introduce and unpack `⟨hb, hP, hT⟩`. Use `⟨fun i => (run_sublist (hb i)).2 (hT i), fun x hx => ?_⟩` and prove the remaining obligations.

Take `⟨i, hi, hu⟩` from `hP x (mem_wN.1 hx)`. Conclude with `⟨i, (hmem i x).2 hi, fun j hj => hu j ((hmem j x).1 hj)⟩`.
-/
theorem cond_iff {L : ℕ} {T : Finset ℕ} {h : ℕ} {b l : Fin h → ℕ} (hl : ∀ i, 0 < l i) :
    Cond L T b l ↔ (∀ i, b i + l i ≤ L) ∧ (∀ x < L, ∃! i, b i ≤ x ∧ x < b i + l i) ∧
      (∀ i x, b i < x → x < b i + l i → x ∈ T) := by
  have hmem : ∀ i x, x ∈ (List.range' (b i) (l i)).reverse ↔ b i ≤ x ∧ x < b i + l i := by
    intro i x; simp [List.mem_range'_1]
  constructor
  · rintro ⟨h1, h2⟩
    have hb : ∀ i, b i + l i ≤ L := fun i => by
      have hi := hl i
      have := (h1 i).subset ((hmem i (b i + l i - 1)).2 ⟨by omega, by omega⟩)
      rw [mem_wN] at this
      omega
    refine ⟨hb, fun x hx => ?_, fun i => (run_sublist (hb i)).1 (h1 i)⟩
    obtain ⟨i, hi, hu⟩ := h2 x (mem_wN.2 hx)
    exact ⟨i, (hmem i x).1 hi, fun j hj => hu j ((hmem j x).2 hj)⟩
  · rintro ⟨hb, hP, hT⟩
    refine ⟨fun i => (run_sublist (hb i)).2 (hT i), fun x hx => ?_⟩
    obtain ⟨i, hi, hu⟩ := hP x (mem_wN.1 hx)
    exact ⟨i, (hmem i x).2 hi, fun j hj => hu j ((hmem j x).1 hj)⟩

end PositivityTheory.Groth.AltC

namespace PositivityTheory.Groth.AltC

open Classical in

/- English proof (translation)
Establish `hcond : ∀ S : Finset (Fin L), Cond L (S.map Fin.valEmbedding) b l ↔ (∀ i, b i + l i ≤ L) ∧ (∀ x < L, ∃! i, b i ≤ x ∧ x < b i + l i) ∧ (∀ i x, b i < x → x < b i + l i → ∃ a ∈ S, (a : ℕ) = x)`. Introduce `S`. Rewrite using `[cond_iff hl]`. Simplify using `[Finset.mem_map]`. Distinguish the cases in `hB : (∀ i, b i + l i ≤ L) ∧ (∀ x < L, ∃! i, b i ≤ x ∧ x < b i + l i)`.

Use `swap`. Rewrite using `[if_neg]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `S _`. Rewrite using `[hf, if_neg, mul_zero]`.

Rewrite using `[hcond]`. Conclude with `fun H => hB ⟨H.1, H.2.1⟩`. Introduce and unpack `⟨rfl, hbl⟩`. Apply `hB` to reduce the goal to its premises. Use `⟨fun i => by rw [(hbl i).1, (hbl i).2]; simp, fun x hx => ⟨0, ?_, fun j _ => Subsingleton.elim _ _⟩⟩` and prove the remaining obligations.

Use `show b 0 ≤ x ∧ x < b 0 + l 0`. Rewrite using `[(hbl 0).1, (hbl 0).2]`. Conclude with `⟨Nat.zero_le _, by omega⟩`. Take `⟨hb, hP⟩` from `hB`. Distinguish the cases in `hz : ∃ j, b j ≠ 0`.

Take `⟨j, hj⟩` from `hz`. Rewrite using `[if_neg (by rintro ⟨_, hbl⟩; exact hj (hbl j).1)]`. Establish `hjL : b j < L` using `by have := hb j; have := hl j; omega`. Use `set a : Fin L := ⟨b j, hjL⟩ with ha_def`. Establish `hint : ∀ i x, b i < x → x < b i + l i → x ≠ (a : ℕ)`.

Introduce `i x h1 h2 hx`. Rewrite `hx` using `[ha_def]`. Simplify using `only at hx`. Substitute `hx` using the available equality. Take `⟨k, _, hu⟩` from `hP (b j) hjL`.

Establish `e1` using `hu i ⟨h1.le, h2⟩`. Establish `e2` using `hu j ⟨le_rfl, by have := hl j; omega⟩`. Rewrite `e1` using `[← e2]`. Substitute `e1` using the available equality. Use linear arithmetic over natural numbers and integers.

Establish `hg : ∀ S : Finset (Fin L), (if a ∈ S then S.erase a else insert a S).map Fin.valEmbedding = (if a ∈ S then S.erase a else insert a S).map Fin.valEmbedding` using `fun _ => rfl`. Establish `hc : ∀ S : Finset (Fin L), Cond L ((if a ∈ S then S.erase a else insert a S).map Fin.valEmbedding) b l ↔ Cond L (S.map Fin.valEmbedding) b l`. Introduce `S`. Rewrite using `[hcond, hcond]`. Use `and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun i => forall_congr' fun x => imp_congr_right fun h1 => imp_congr_right fun h2 => ?_` and prove the remaining obligations.

Establish `hxa` using `hint i x h1 h2`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a', ha', rfl⟩`. Use `⟨a', ?_, rfl⟩` and prove the remaining obligations. Use `split_ifs at ha' with haS`.

Conclude with `Finset.mem_of_mem_erase ha'`. Break down `Finset.mem_insert.1 ha' with h | h` into its components or cases. Conclude with `absurd (congrArg Fin.val h) hxa`. Conclude with `h`. Introduce and unpack `⟨a', ha', rfl⟩`.

Use `⟨a', ?_, rfl⟩` and prove the remaining obligations. Establish `: a' ≠ a` using `fun h => hxa (congrArg Fin.val h)`. Use `split_ifs`. Conclude with `Finset.mem_erase.2 ⟨this, ha'⟩`. Conclude with `Finset.mem_insert_of_mem ha'`.

Establish `hcard : ∀ S : Finset (Fin L), (-1 : ℤ) ^ (if a ∈ S then S.erase a else insert a S).card = -(-1) ^ S.card`. Introduce `S`. Use `split_ifs with haS`. Rewrite using `[Finset.card_erase_of_mem haS]`. Establish `: 0 < S.card` using `Finset.card_pos.2 ⟨a, haS⟩`.

Take `⟨n, hn⟩ : ∃ n, S.card = n + 1` from `⟨S.card - 1, by omega⟩`. Rewrite using `[hn, pow_succ]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.card_insert_of_notMem haS, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Use `Finset.sum_involution (fun S _ => if a ∈ S then S.erase a else insert a S) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `S _`. Rewrite using `[hf, hf, hcard, hc]`. Expand and normalize the polynomial expressions, which then agree. Introduce `S _ _ split_ifs with haS`.

Conclude with `fun h => Finset.notMem_erase a S (by rw [h]; exact haS)`. Conclude with `fun h => haS (by rw [← h]; exact Finset.mem_insert_self a S)`. Introduce `S hS`. Rewrite `hS`, the goal using `[hs]`. Introduce `x hx`.

Use `split_ifs at hx`. Conclude with `hS x (Finset.mem_of_mem_erase hx)`. Break down `Finset.mem_insert.1 hx with rfl | h` into its components or cases. Conclude with `hj`. Conclude with `hS x h`.

Introduce `S _`. Distinguish the cases in `haS : a ∈ S`. Simplify using `[haS, Finset.insert_erase]`. Simplify using `[haS]`. Use `push Not at hz`.

Take `⟨i0, _, hu⟩` from `hP 0 hL`. Establish `hall : ∀ i, i = i0` using `fun i => hu i ⟨by rw [hz i], by rw [hz i]; have := hl i; omega⟩`. Establish `hh : h = 1`. Establish `: Fintype.card (Fin h) = 1` using `Fintype.card_eq_one_iff.2 ⟨i0, hall⟩`. Simplify using `using this`.

Substitute `hh` using the available equality. Establish `hlL : ∀ i, l i = L`. Introduce `i`. Rewrite using `[hall i]`. Use `hb i0` as an intermediate fact.

Rewrite `this` using `[hz]`. Assume the negation of the conclusion as `hne`. Take `⟨k, hk, _⟩` from `hP (l i0) (by omega)`. Rewrite `hk` using `[hall k, hz]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[if_pos ⟨rfl, fun i => ⟨hz i, hlL i⟩⟩]`. Take `⟨S0, hS0def⟩ : ∃ S0 : Finset (Fin L), S0 = Finset.univ.filter (fun a : Fin L => (a : ℕ) ≠ 0)` from `⟨_, rfl⟩`. Establish `hS0 : S0 ∈ s` using `(hs S0).2 (fun a ha => by rw [hS0def] at ha; exact (Finset.mem_filter.1 ha).2)`. Rewrite using `[Finset.sum_eq_single_of_mem S0 hS0]`. Rewrite using `[hf, if_pos, mul_one]`.

Use `congr 1`. Take `⟨n, rfl⟩ : ∃ n, L = n + 1` from `⟨L - 1, by omega⟩`. Establish `: S0 = Finset.univ.erase 0`. Use extensionality with `x`. Rewrite using `[hS0def, Finset.mem_filter, Finset.mem_erase]`.

Simplify using `only [Finset.mem_univ, true_and, and_true]`. Conclude with `⟨fun hx h => hx (by rw [h]; rfl), fun hx h => hx (Fin.ext (by simpa using h))⟩`. Rewrite using `[this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]`. Rewrite using `[hcond]`. Use `⟨hb, hP, fun i x h1 h2 => ⟨⟨x, by rw [hz, hlL] at h2; simpa using h2⟩, ?_, rfl⟩⟩` and prove the remaining obligations.

Rewrite `h1` using `[hz]`. Simplify using `[hS0def]`. Use linear arithmetic over natural numbers and integers. Introduce `S hS hne`. Rewrite using `[hf, if_neg, mul_zero]`.

Rewrite using `[hcond]`. Introduce and unpack `⟨_, _, hT⟩`. Apply `hne` to reduce the goal to its premises. Use extensionality with `x`. Simplify using `only [hS0def, Finset.mem_filter, Finset.mem_univ, true_and]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `(hs S).1 hS x hx`. Introduce `hx0`. Take `⟨a', ha', he⟩` from `hT i0 x (by rw [hz]; omega) (by rw [hz, hlL]; simp)`.

Rewrite `ha'` using `[Fin.ext he]`. Then use the resulting hypothesis.
-/
theorem altSumN (L : ℕ) (hL : 0 < L) (s : Finset (Finset (Fin L))) (hs : ∀ S, S ∈ s ↔ ∀ a ∈ S, (a : ℕ) ≠ 0)
    {h : ℕ} (b l : Fin h → ℕ) (hl : ∀ i, 0 < l i) (f : Finset (Fin L) → ℤ)
    (hf : ∀ S, f S = (-1) ^ S.card * if Cond L (S.map Fin.valEmbedding) b l then 1 else 0) :
    ∑ S ∈ s, f S = if h = 1 ∧ ∀ i, b i = 0 ∧ l i = L then (-1) ^ (L - 1) else 0 := by
  have hcond : ∀ S : Finset (Fin L), Cond L (S.map Fin.valEmbedding) b l ↔ (∀ i, b i + l i ≤ L) ∧
      (∀ x < L, ∃! i, b i ≤ x ∧ x < b i + l i) ∧
      (∀ i x, b i < x → x < b i + l i → ∃ a ∈ S, (a : ℕ) = x) := by
    intro S
    rw [cond_iff hl]
    simp [Finset.mem_map]
  by_cases hB : (∀ i, b i + l i ≤ L) ∧ (∀ x < L, ∃! i, b i ≤ x ∧ x < b i + l i)
  swap
  · rw [if_neg]
    · apply Finset.sum_eq_zero
      intro S _
      rw [hf, if_neg, mul_zero]
      rw [hcond]
      exact fun H => hB ⟨H.1, H.2.1⟩
    · rintro ⟨rfl, hbl⟩
      apply hB
      refine ⟨fun i => by rw [(hbl i).1, (hbl i).2]; simp, fun x hx => ⟨0, ?_, fun j _ => Subsingleton.elim _ _⟩⟩
      show b 0 ≤ x ∧ x < b 0 + l 0
      rw [(hbl 0).1, (hbl 0).2]
      exact ⟨Nat.zero_le _, by omega⟩
  obtain ⟨hb, hP⟩ := hB
  by_cases hz : ∃ j, b j ≠ 0
  · obtain ⟨j, hj⟩ := hz
    rw [if_neg (by rintro ⟨_, hbl⟩; exact hj (hbl j).1)]
    have hjL : b j < L := by have := hb j; have := hl j; omega
    set a : Fin L := ⟨b j, hjL⟩ with ha_def
    have hint : ∀ i x, b i < x → x < b i + l i → x ≠ (a : ℕ) := by
      intro i x h1 h2 hx
      rw [ha_def] at hx
      simp only at hx
      subst hx
      obtain ⟨k, _, hu⟩ := hP (b j) hjL
      have e1 := hu i ⟨h1.le, h2⟩
      have e2 := hu j ⟨le_rfl, by have := hl j; omega⟩
      rw [← e2] at e1
      subst e1
      omega
    have hg : ∀ S : Finset (Fin L), (if a ∈ S then S.erase a else insert a S).map Fin.valEmbedding =
        (if a ∈ S then S.erase a else insert a S).map Fin.valEmbedding := fun _ => rfl
    have hc : ∀ S : Finset (Fin L), Cond L ((if a ∈ S then S.erase a else insert a S).map Fin.valEmbedding) b l ↔
        Cond L (S.map Fin.valEmbedding) b l := by
      intro S
      rw [hcond, hcond]
      refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun i => forall_congr' fun x =>
        imp_congr_right fun h1 => imp_congr_right fun h2 => ?_
      have hxa := hint i x h1 h2
      constructor
      · rintro ⟨a', ha', rfl⟩
        refine ⟨a', ?_, rfl⟩
        split_ifs at ha' with haS
        · exact Finset.mem_of_mem_erase ha'
        · rcases Finset.mem_insert.1 ha' with h | h
          · exact absurd (congrArg Fin.val h) hxa
          · exact h
      · rintro ⟨a', ha', rfl⟩
        refine ⟨a', ?_, rfl⟩
        have : a' ≠ a := fun h => hxa (congrArg Fin.val h)
        split_ifs
        · exact Finset.mem_erase.2 ⟨this, ha'⟩
        · exact Finset.mem_insert_of_mem ha'
    have hcard : ∀ S : Finset (Fin L), (-1 : ℤ) ^ (if a ∈ S then S.erase a else insert a S).card =
        -(-1) ^ S.card := by
      intro S
      split_ifs with haS
      · rw [Finset.card_erase_of_mem haS]
        have : 0 < S.card := Finset.card_pos.2 ⟨a, haS⟩
        obtain ⟨n, hn⟩ : ∃ n, S.card = n + 1 := ⟨S.card - 1, by omega⟩
        rw [hn, pow_succ]
        simp
      · rw [Finset.card_insert_of_notMem haS, pow_succ]
        ring
    refine Finset.sum_involution (fun S _ => if a ∈ S then S.erase a else insert a S) ?_ ?_ ?_ ?_
    · intro S _
      rw [hf, hf, hcard, hc]
      ring
    · intro S _ _
      split_ifs with haS
      · exact fun h => Finset.notMem_erase a S (by rw [h]; exact haS)
      · exact fun h => haS (by rw [← h]; exact Finset.mem_insert_self a S)
    · intro S hS
      rw [hs] at hS ⊢
      intro x hx
      split_ifs at hx
      · exact hS x (Finset.mem_of_mem_erase hx)
      · rcases Finset.mem_insert.1 hx with rfl | h
        · exact hj
        · exact hS x h
    · intro S _
      by_cases haS : a ∈ S
      · simp [haS, Finset.insert_erase]
      · simp [haS]
  · push Not at hz
    obtain ⟨i0, _, hu⟩ := hP 0 hL
    have hall : ∀ i, i = i0 := fun i => hu i ⟨by rw [hz i], by rw [hz i]; have := hl i; omega⟩
    have hh : h = 1 := by
      have : Fintype.card (Fin h) = 1 := Fintype.card_eq_one_iff.2 ⟨i0, hall⟩
      simpa using this
    subst hh
    have hlL : ∀ i, l i = L := by
      intro i
      rw [hall i]
      have := hb i0
      rw [hz] at this
      by_contra hne
      obtain ⟨k, hk, _⟩ := hP (l i0) (by omega)
      rw [hall k, hz] at hk
      omega
    rw [if_pos ⟨rfl, fun i => ⟨hz i, hlL i⟩⟩]
    obtain ⟨S0, hS0def⟩ : ∃ S0 : Finset (Fin L), S0 = Finset.univ.filter (fun a : Fin L => (a : ℕ) ≠ 0) := ⟨_, rfl⟩
    have hS0 : S0 ∈ s := (hs S0).2 (fun a ha => by rw [hS0def] at ha; exact (Finset.mem_filter.1 ha).2)
    rw [Finset.sum_eq_single_of_mem S0 hS0]
    · rw [hf, if_pos, mul_one]
      · congr 1
        obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
        have : S0 = Finset.univ.erase 0 := by
          ext x
          rw [hS0def, Finset.mem_filter, Finset.mem_erase]
          simp only [Finset.mem_univ, true_and, and_true]
          exact ⟨fun hx h => hx (by rw [h]; rfl), fun hx h => hx (Fin.ext (by simpa using h))⟩
        rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      · rw [hcond]
        refine ⟨hb, hP, fun i x h1 h2 => ⟨⟨x, by rw [hz, hlL] at h2; simpa using h2⟩, ?_, rfl⟩⟩
        rw [hz] at h1
        simp [hS0def]
        omega
    · intro S hS hne
      rw [hf, if_neg, mul_zero]
      rw [hcond]
      rintro ⟨_, _, hT⟩
      apply hne
      ext x
      simp only [hS0def, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hx
        exact (hs S).1 hS x hx
      · intro hx0
        obtain ⟨a', ha', he⟩ := hT i0 x (by rw [hz]; omega) (by rw [hz, hlL]; simp)
        rwa [Fin.ext he] at ha'

end PositivityTheory.Groth.AltC

end
