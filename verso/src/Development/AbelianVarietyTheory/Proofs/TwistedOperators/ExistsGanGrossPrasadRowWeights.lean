import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional.RowWeights

def Follows (f g : List ℚ) : Prop :=
  f.Pairwise (· > ·) → g.Pairwise (· > ·) ∧ (∀ x ∈ g, ∃ l ∈ f, l - 1 / 2 ≤ x) ∧ ∀ x ∈ g, ∃ h ∈ f, x ≤ h - 1 / 2

/- English proof (translation)
Introduce `hp`. Rewrite `hp` using `[List.pairwise_append]`. Take `⟨p1, p2, p3⟩` from `hp`. Take `⟨a1, a2, a3⟩` from `h p1`. Take `⟨b1, b2, b3⟩` from `h' p2`.

Use `⟨List.pairwise_append.2 ⟨a1, b1, fun x hx y hy => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨l, hl, hlx⟩` from `a2 x hx`. Take `⟨u, hu, huy⟩` from `b3 y hy`. Use `p3 l hl u hu` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Break down `List.mem_append.1 hx with hx | hx` into its components or cases. Take `⟨l, hl, hlx⟩` from `a2 x hx`. Conclude with `⟨l, List.mem_append_left _ hl, hlx⟩`. Take `⟨l, hl, hlx⟩` from `b2 x hx`. Conclude with `⟨l, List.mem_append_right _ hl, hlx⟩`.

Break down `List.mem_append.1 hx with hx | hx` into its components or cases. Take `⟨l, hl, hlx⟩` from `a3 x hx`. Conclude with `⟨l, List.mem_append_left _ hl, hlx⟩`. Take `⟨l, hl, hlx⟩` from `b3 x hx`. Conclude with `⟨l, List.mem_append_right _ hl, hlx⟩`.
-/
theorem Follows.append {f g f' g' : List ℚ} (h : Follows f g) (h' : Follows f' g') : Follows (f ++ f') (g ++ g') := by
  intro hp
  rw [List.pairwise_append] at hp
  obtain ⟨p1, p2, p3⟩ := hp
  obtain ⟨a1, a2, a3⟩ := h p1
  obtain ⟨b1, b2, b3⟩ := h' p2
  refine ⟨List.pairwise_append.2 ⟨a1, b1, fun x hx y hy => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨l, hl, hlx⟩ := a2 x hx
    obtain ⟨u, hu, huy⟩ := b3 y hy
    have := p3 l hl u hu
    linarith
  · rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨l, hl, hlx⟩ := a2 x hx
      exact ⟨l, List.mem_append_left _ hl, hlx⟩
    · obtain ⟨l, hl, hlx⟩ := b2 x hx
      exact ⟨l, List.mem_append_right _ hl, hlx⟩
  · rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨l, hl, hlx⟩ := a3 x hx
      exact ⟨l, List.mem_append_left _ hl, hlx⟩
    · obtain ⟨l, hl, hlx⟩ := b3 x hx
      exact ⟨l, List.mem_append_right _ hl, hlx⟩

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => intro _`. Simplify using the standard rewrite rules. Consider the case `cons a L ih => rw [List.flatMap_cons, List.flatMap_cons]`. Conclude with `(h a).append ih`.
-/
theorem Follows.flatMap {α : Type} {f g : α → List ℚ} (h : ∀ i, Follows (f i) (g i)) (L : List α) :
    Follows (L.flatMap f) (L.flatMap g) := by
  induction L with
  | nil => intro _; simp
  | cons a L ih => rw [List.flatMap_cons, List.flatMap_cons]; exact (h a).append ih

/- English proof (translation)
Simplify using `[block]`.
-/
theorem mem_block {x y : ℚ} {n : ℕ} : y ∈ block x n ↔ ∃ i : ℕ, i < n ∧ x + ((n : ℚ) - 1) / 2 - i = y := by
  simp [block]

/- English proof (translation)
Rewrite using `[block, List.pairwise_map]`. Use `List.pairwise_lt_range.imp fun {a b} hab => ?_` and prove the remaining obligations. Establish `: (a : ℚ) < b` using `by exact_mod_cast hab`. Express the relevant statement in the definitionally equal form `_ < _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem block_pairwise (x : ℚ) (n : ℕ) : (block x n).Pairwise (· > ·) := by
  rw [block, List.pairwise_map]
  refine List.pairwise_lt_range.imp fun {a b} hab => ?_
  have : (a : ℚ) < b := by exact_mod_cast hab
  change _ < _
  linarith

/- English proof (translation)
Establish `h1 : (z : ℚ) < w` using `by linarith`. Establish `h2 : z + 1 ≤ w` using `by exact_mod_cast h1`. Establish `h3 : (z : ℚ) + 1 ≤ w` using `by exact_mod_cast h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem half_le {z w : ℤ} (h : (z : ℚ) + 1 / 2 < w) : (z : ℚ) + 1 / 2 ≤ w - 1 / 2 := by
  have h1 : (z : ℚ) < w := by linarith
  have h2 : z + 1 ≤ w := by exact_mod_cast h1
  have h3 : (z : ℚ) + 1 ≤ w := by exact_mod_cast h2
  linarith

/- English proof (translation)
Take `⟨r, rfl⟩` from `hs`. Take `⟨z, rfl⟩` from `ha`. Introduce `hp`. Rewrite `hp` using `[List.pairwise_append]`. Establish `hbot : (z : ℚ) + 1 / 2 < c - r` using `hp.2.2 _ (mem_block.2 ⟨2 * r, by omega, by push_cast; ring⟩) _ (List.mem_singleton_self _)`.

Establish `htop : ((c : ℚ) + r) ∈ block c (2 * r + 1)` using `mem_block.2 ⟨0, by omega, by push_cast; ring⟩`. Establish `hb : ∀ x ∈ block (c : ℚ) (2 * r + 1 - 1), (c : ℚ) - r ≤ x ∧ x ≤ c + r - 1 / 2`. Introduce `x hx`. Take `⟨i, hi, rfl⟩` from `mem_block.1 hx`. Establish `h1 : ((i + 1 : ℕ) : ℚ) ≤ ((2 * r : ℕ) : ℚ)` using `by exact_mod_cast (by omega : i + 1 ≤ 2 * r)`.

Establish `h2 : (0 : ℚ) ≤ i` using `by positivity`. Rewrite using `[Nat.add_sub_cancel]`. Move the coercions through the operations in `at h1 ⊢`. Apply the tactic sequence `constructor <;> linarith`. Use `⟨List.pairwise_append.2 ⟨block_pairwise _ _, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩, fun x hx => ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩, fun x hx => ⟨_, List.mem_append_left _ htop, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[List.mem_singleton.1 hy]`. Use `(hb x hx).1` as an intermediate fact. Express the relevant statement in the definitionally equal form `_ < _`. Combine the linear equalities and inequalities to obtain the conclusion. Break down `List.mem_append.1 hx with hx | hx` into its components or cases.

Use `(hb x hx).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[List.mem_singleton.1 hx]`. Combine the linear equalities and inequalities to obtain the conclusion. Break down `List.mem_append.1 hx with hx | hx` into its components or cases.

Conclude with `(hb x hx).2`. Rewrite using `[List.mem_singleton.1 hx]`. Establish `h2 : (0 : ℚ) ≤ r` using `by positivity`. Use `half_le (z := z) (w := c + r) (by push_cast; linarith)` as an intermediate fact. Move the coercions through the operations in `at this`.

Conclude with `this`.
-/
theorem follows_block_append (c : ℤ) {s : ℕ} (hs : Odd s) {a : ℚ} (ha : ∃ z : ℤ, a = z + 1 / 2) :
    Follows (block c s ++ [a]) (block c (s - 1) ++ [a]) := by
  obtain ⟨r, rfl⟩ := hs
  obtain ⟨z, rfl⟩ := ha
  intro hp
  rw [List.pairwise_append] at hp
  have hbot : (z : ℚ) + 1 / 2 < c - r :=
    hp.2.2 _ (mem_block.2 ⟨2 * r, by omega, by push_cast; ring⟩) _ (List.mem_singleton_self _)
  have htop : ((c : ℚ) + r) ∈ block c (2 * r + 1) := mem_block.2 ⟨0, by omega, by push_cast; ring⟩
  have hb : ∀ x ∈ block (c : ℚ) (2 * r + 1 - 1), (c : ℚ) - r ≤ x ∧ x ≤ c + r - 1 / 2 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_block.1 hx
    have h1 : ((i + 1 : ℕ) : ℚ) ≤ ((2 * r : ℕ) : ℚ) := by exact_mod_cast (by omega : i + 1 ≤ 2 * r)
    have h2 : (0 : ℚ) ≤ i := by positivity
    rw [Nat.add_sub_cancel]
    push_cast at h1 ⊢
    constructor <;> linarith
  refine ⟨List.pairwise_append.2 ⟨block_pairwise _ _, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩,
    fun x hx => ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩,
    fun x hx => ⟨_, List.mem_append_left _ htop, ?_⟩⟩
  · rw [List.mem_singleton.1 hy]
    have := (hb x hx).1
    change _ < _
    linarith
  · rcases List.mem_append.1 hx with hx | hx
    · have := (hb x hx).1
      linarith
    · rw [List.mem_singleton.1 hx]; linarith
  · rcases List.mem_append.1 hx with hx | hx
    · exact (hb x hx).2
    · rw [List.mem_singleton.1 hx]
      have h2 : (0 : ℚ) ≤ r := by positivity
      have := half_le (z := z) (w := c + r) (by push_cast; linarith)
      push_cast at this
      exact this

/- English proof (translation)
Take `⟨z, rfl⟩` from `hu`. Introduce `hp`. Establish `h : (z : ℚ) + 1 / 2 < v` using `by simpa using hp`. Use `⟨List.pairwise_singleton _ _, fun x hx => ⟨z + 1 / 2, by simp, ?_⟩, fun x hx => ⟨v, by simp, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[List.mem_singleton.1 hx]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[List.mem_singleton.1 hx]`. Conclude with `half_le h`.
-/
theorem follows_pair_singleton (v : ℤ) {u : ℚ} (hu : ∃ z : ℤ, u = z + 1 / 2) : Follows [(v : ℚ), u] [u] := by
  obtain ⟨z, rfl⟩ := hu
  intro hp
  have h : (z : ℚ) + 1 / 2 < v := by simpa using hp
  refine ⟨List.pairwise_singleton _ _, fun x hx => ⟨z + 1 / 2, by simp, ?_⟩, fun x hx => ⟨v, by simp, ?_⟩⟩
  · rw [List.mem_singleton.1 hx]; linarith
  · rw [List.mem_singleton.1 hx]; exact half_le h

/- English proof (translation)
Take `⟨r, rfl⟩` from `ht`. Introduce `hp`. Rewrite `hp` using `[List.pairwise_cons]`. Establish `htop : (-e + r : ℚ) < -b` using `hp.1 _ (mem_block.2 ⟨0, by omega, by push_cast; ring⟩)`. Establish `htop' : (-e + r + 1 : ℚ) ≤ -b`.

Establish `: -e + r + 1 ≤ -b` using `by exact_mod_cast htop`. Conclude with `this` after adjusting the coercions. Establish `hbot : (-e - r : ℚ) ∈ block (-e) (2 * r + 1)` using `mem_block.2 ⟨2 * r, by omega, by push_cast; ring⟩`. Use `⟨block_pairwise _ _, fun x hx => ⟨_, List.mem_cons_of_mem _ hbot, ?_⟩, fun x hx => ⟨_, List.mem_cons_self, ?_⟩⟩` and prove the remaining obligations. Take `⟨i, hi, rfl⟩` from `mem_block.1 hx`.

Establish `h1 : ((i : ℕ) : ℚ) ≤ ((2 * r + 1 : ℕ) : ℚ)` using `by exact_mod_cast (by omega : i ≤ 2 * r + 1)`. Move the coercions through the operations in `at h1 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨i, hi, rfl⟩` from `mem_block.1 hx`. Establish `h2 : (0 : ℚ) ≤ i` using `by positivity`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem follows_cons_block_succ (b e : ℤ) {t : ℕ} (ht : Odd t) :
    Follows ((-b : ℚ) :: block (-e) t) (block (-e) (t + 1)) := by
  obtain ⟨r, rfl⟩ := ht
  intro hp
  rw [List.pairwise_cons] at hp
  have htop : (-e + r : ℚ) < -b := hp.1 _ (mem_block.2 ⟨0, by omega, by push_cast; ring⟩)
  have htop' : (-e + r + 1 : ℚ) ≤ -b := by
    have : -e + r + 1 ≤ -b := by exact_mod_cast htop
    exact_mod_cast this
  have hbot : (-e - r : ℚ) ∈ block (-e) (2 * r + 1) := mem_block.2 ⟨2 * r, by omega, by push_cast; ring⟩
  refine ⟨block_pairwise _ _, fun x hx => ⟨_, List.mem_cons_of_mem _ hbot, ?_⟩, fun x hx => ⟨_, List.mem_cons_self, ?_⟩⟩
  · obtain ⟨i, hi, rfl⟩ := mem_block.1 hx
    have h1 : ((i : ℕ) : ℚ) ≤ ((2 * r + 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : i ≤ 2 * r + 1)
    push_cast at h1 ⊢
    linarith
  · obtain ⟨i, hi, rfl⟩ := mem_block.1 hx
    have h2 : (0 : ℚ) ≤ i := by positivity
    push_cast
    linarith

variable {S : Sizes}

/- English proof (translation)
Establish `h1` using `Follows.flatMap (fun i => follows_block_append (Q.c i) S.s_odd (hQ.a_half i.succ)) (List.finRange S.m)`. Establish `h2` using `Follows.flatMap (fun i => follows_pair_singleton (Q.v i) (hQ.u_half i)) (List.finRange (S.k - 1))`. Establish `h3` using `Follows.flatMap (fun j => follows_cons_block_succ (Q.b j) (Q.e j) S.t_odd) (List.finRange S.m)`. Establish `ho` using `hQ.order`. Rewrite `ho` using `[Entries.orderList, List.cons_append, List.cons_append, List.pairwise_cons]`.

Take `⟨p1, -, p3⟩` from `(h1.append h2).append h3 ho.2`. Rewrite `p1`, `p3` using `[← List.map_eq_flatMap]`. Rewrite using `[Entries.bigPar, Entries.psiPar, List.cons_append, List.cons_append, List.pairwise_cons]`. Use `⟨fun x hx => ?_, p1⟩` and prove the remaining obligations. Take `⟨u, hu, hxu⟩` from `p3 x hx`.

Use `ho.1 u hu` as an intermediate fact. Express the relevant statement in the definitionally equal form `_ < _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bigPar_pairwise (Q : Entries S) (hQ : Q.Good) : Q.bigPar.Pairwise (· > ·) := by
  have h1 := Follows.flatMap (fun i => follows_block_append (Q.c i) S.s_odd (hQ.a_half i.succ)) (List.finRange S.m)
  have h2 := Follows.flatMap (fun i => follows_pair_singleton (Q.v i) (hQ.u_half i)) (List.finRange (S.k - 1))
  have h3 := Follows.flatMap (fun j => follows_cons_block_succ (Q.b j) (Q.e j) S.t_odd) (List.finRange S.m)
  have ho := hQ.order
  rw [Entries.orderList, List.cons_append, List.cons_append, List.pairwise_cons] at ho
  obtain ⟨p1, -, p3⟩ := (h1.append h2).append h3 ho.2
  rw [← List.map_eq_flatMap] at p1 p3
  rw [Entries.bigPar, Entries.psiPar, List.cons_append, List.cons_append, List.pairwise_cons]
  refine ⟨fun x hx => ?_, p1⟩
  obtain ⟨u, hu, hxu⟩ := p3 x hx
  have := ho.1 u hu
  change _ < _
  linarith

/- English proof (translation)
Proceed by induction on `j, hij using Nat.le_induction with`. Consider the case `base => exact le_rfl`. Consider the case `succ j hij ih`. Use `le_trans ?_ (ih (by omega))` and prove the remaining obligations. Establish `h1` using `hw_big Q hQ j (by omega)`.

Establish `h2` using `hw_big Q hQ (j + 1) hj`. Establish `h3 : Q.bigPar[j] > Q.bigPar[j + 1]` using `List.pairwise_iff_getElem.1 (bigPar_pairwise Q hQ) j (j + 1) (by omega) hj (by omega)`. Establish `h4 : (hw Q.bigPar (j + 1) : ℚ) < hw Q.bigPar j + 1`. Rewrite using `[h1, h2]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5 : hw Q.bigPar (j + 1) < hw Q.bigPar j + 1` using `by exact_mod_cast h4`. Use linear arithmetic over natural numbers and integers.
-/
theorem hw_big_anti (Q : Entries S) (hQ : Q.Good) {i j : ℕ} (hij : i ≤ j) (hj : j < Q.bigPar.length) :
    hw Q.bigPar j ≤ hw Q.bigPar i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    refine le_trans ?_ (ih (by omega))
    have h1 := hw_big Q hQ j (by omega)
    have h2 := hw_big Q hQ (j + 1) hj
    have h3 : Q.bigPar[j] > Q.bigPar[j + 1] :=
      List.pairwise_iff_getElem.1 (bigPar_pairwise Q hQ) j (j + 1) (by omega) hj (by omega)
    have h4 : (hw Q.bigPar (j + 1) : ℚ) < hw Q.bigPar j + 1 := by
      rw [h1, h2]; push_cast; linarith
    have h5 : hw Q.bigPar (j + 1) < hw Q.bigPar j + 1 := by exact_mod_cast h4
    omega

/- English proof (translation)
Proceed by induction on `L generalizing j with`. Consider the case `nil => simp at hj`. Consider the case `cons a L ih`. Rewrite using `[List.flatMap_cons]`. Consider the cases of `j with`.

Consider the case `zero => rw [List.getElem?_append_left (by rw [hf]; omega)]; simp`. Consider the case `succ j`. Rewrite using `[List.getElem?_append_right (by rw [hf]; nlinarith), hf, show (j + 1) * n + r - n = j * n + r by rw [add_mul]; omega, ih j (by simpa using hj)]`. Simplify using the standard rewrite rules.
-/
theorem getElem?_flatMap {α β : Type} (f : α → List β) (n : ℕ) (hf : ∀ a, (f a).length = n) (L : List α) (j r : ℕ)
    (hj : j < L.length) (hr : r < n) : (L.flatMap f)[j * n + r]? = (f L[j])[r]? := by
  induction L generalizing j with
  | nil => simp at hj
  | cons a L ih =>
    rw [List.flatMap_cons]
    cases j with
    | zero => rw [List.getElem?_append_left (by rw [hf]; omega)]; simp
    | succ j =>
      rw [List.getElem?_append_right (by rw [hf]; nlinarith), hf,
        show (j + 1) * n + r - n = j * n + r by rw [add_mul]; omega, ih j (by simpa using hj)]
      simp

/- English proof (translation)
Unfold `Sizes.nR`. Use `Nat.mul_le_mul_right (S.t + 1) h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem nR_mono {i j : ℕ} (h : i ≤ j) : S.nR i ≤ S.nR j := by
  unfold Sizes.nR
  have := Nat.mul_le_mul_right (S.t + 1) h
  omega

/- English proof (translation)
Unfold `Sizes.nR`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nR_succ (j : ℕ) : S.nR (j + 1) = S.nR j + (S.t + 1) := by
  unfold Sizes.nR; ring

/- English proof (translation)
Take `⟨r, hr⟩` from `even_nR (S := S) j`. Rewrite using `[hr, show (r + r) / 2 = r by omega]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cast_half (j : ℕ) : ((S.nR j / 2 : ℕ) : ℚ) = (S.nR j : ℚ) / 2 := by
  obtain ⟨r, hr⟩ := even_nR (S := S) j
  rw [hr, show (r + r) / 2 = r by omega]
  push_cast; ring

/- English proof (translation)
Establish `h1 : Q.bigPar[S.nR j + r]? = some (-Q.e j + (S.t : ℚ) / 2 - r)`. Rewrite using `[Entries.bigPar, List.getElem?_append_right (by rw [length_psi]; unfold Sizes.nR; omega), length_psi, show S.nR j + r - S.nR 0 = j * (S.t + 1) + r by unfold Sizes.nR; omega, getElem?_flatMap _ (S.t + 1) (fun a => length_block _ _) _ _ _ (by simp) hr]`. Simplify using `[block, hr]`. Rewrite `h1` using `[List.getElem?_eq_getElem h]`. Conclude with `Option.some.inj h1`.
-/
theorem bigPar_block (Q : Entries S) (j : Fin S.m) (r : ℕ) (hr : r < S.t + 1) (h : S.nR j + r < Q.bigPar.length) :
    Q.bigPar[S.nR j + r] = -Q.e j + (S.t : ℚ) / 2 - r := by
  have h1 : Q.bigPar[S.nR j + r]? = some (-Q.e j + (S.t : ℚ) / 2 - r) := by
    rw [Entries.bigPar, List.getElem?_append_right (by rw [length_psi]; unfold Sizes.nR; omega), length_psi,
      show S.nR j + r - S.nR 0 = j * (S.t + 1) + r by unfold Sizes.nR; omega,
      getElem?_flatMap _ (S.t + 1) (fun a => length_block _ _) _ _ _ (by simp) hr]
    simp [block, hr]
  rw [List.getElem?_eq_getElem h] at h1
  exact Option.some.inj h1

/- English proof (translation)
Establish `hlen : ∀ (j : Fin (S.m + 1)) (i : Fin (S.nR j)), i.1 < Q.bigPar.length` using `fun j i => by`. Rewrite using `[length_big]`. Conclude with `lt_of_lt_of_le i.2 (nR_mono (Nat.lt_succ_iff.1 j.2))`. Use `⟨fun j => ⟨fun i => hw Q.bigPar i + (S.nR S.m / 2 : ℕ) - (S.nR j / 2 : ℕ), fun i i' hi => ?_⟩, fun i => ?_, fun i => ?_, fun j i => ?_⟩` and prove the remaining obligations. Use `hw_big_anti Q hQ (i := i) (j := i') hi (hlen j i') dsimp only` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hi : i.1 < Q.psiPar.length` using `by rw [length_psi]; exact i.2`. Establish `h1` using `hw_big Q hQ i (hlen 0 i)`. Establish `h2` using `hw_psi Q hQ i hi`. Establish `h3 : Q.bigPar[i.1]'(hlen 0 i) = Q.psiPar[i.1]` using `List.getElem_append_left hi`.

Rewrite `h1` using `[h3, length_big]`. Rewrite `h2` using `[length_psi]`. Establish `: ((hw Q.bigPar i + (S.nR S.m / 2 : ℕ) - (S.nR 0 / 2 : ℕ) : ℤ) : ℚ) = hw Q.psiPar i`. Rewrite using `[Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_natCast, cast_half, cast_half, h1, h2]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `this` after adjusting the coercions. Simplify using the standard rewrite rules. Simplify using `only split_ifs with h`. Expand and normalize the polynomial expressions, which then agree. Establish `hi` using `i.2`.

Simplify using `only [Fin.val_succ, Fin.val_castSucc, nR_succ] at hi h`. Take `⟨r, hr⟩ : ∃ r, i.1 = S.nR j + r` from `⟨i.1 - S.nR j, by omega⟩`. Establish `h0` using `hlen j.succ i`. Establish `h1` using `hw_big Q hQ i h0`. Establish `h2 : Q.bigPar[i.1] = -Q.e j + (S.t : ℚ) / 2 - r`.

Rewrite using `[← bigPar_block Q j r (by omega) (hr ▸ h0)]`. Simplify using `only [hr]`. Rewrite `h1` using `[h2, length_big]`. Establish `: ((hw Q.bigPar i + (S.nR S.m / 2 : ℕ) - (S.nR (j + 1) / 2 : ℕ) : ℤ) : ℚ) = ((-Q.e j + (S.nR j / 2 : ℕ) : ℤ) : ℚ)`. Rewrite using `[Int.cast_sub, Int.cast_add, Int.cast_add, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast, cast_half, cast_half, cast_half, h1, nR_succ, hr]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions.
-/
theorem exists_row_weights (S : Sizes) (Q : Entries S) (hQ : Q.Good) :
    ∃ lam : ∀ j : Fin (S.m + 1), DomWeight (S.nR j), (∀ i, (lam 0).w i = hw Q.psiPar i) ∧
      (∀ i, (lam (Fin.last _)).w i = hw Q.bigPar i) ∧
      ∀ j : Fin S.m, StepW (Q.e j - (S.nR j.succ / 2 : ℕ)) (-Q.e j + (S.nR j.castSucc / 2 : ℕ))
        (lam j.castSucc) (lam j.succ) := by
  have hlen : ∀ (j : Fin (S.m + 1)) (i : Fin (S.nR j)), i.1 < Q.bigPar.length := fun j i => by
    rw [length_big]
    exact lt_of_lt_of_le i.2 (nR_mono (Nat.lt_succ_iff.1 j.2))
  refine ⟨fun j => ⟨fun i => hw Q.bigPar i + (S.nR S.m / 2 : ℕ) - (S.nR j / 2 : ℕ), fun i i' hi => ?_⟩,
    fun i => ?_, fun i => ?_, fun j i => ?_⟩
  · have := hw_big_anti Q hQ (i := i) (j := i') hi (hlen j i')
    dsimp only
    omega
  · have hi : i.1 < Q.psiPar.length := by rw [length_psi]; exact i.2
    have h1 := hw_big Q hQ i (hlen 0 i)
    have h2 := hw_psi Q hQ i hi
    have h3 : Q.bigPar[i.1]'(hlen 0 i) = Q.psiPar[i.1] := List.getElem_append_left hi
    rw [h3, length_big] at h1
    rw [length_psi] at h2
    have : ((hw Q.bigPar i + (S.nR S.m / 2 : ℕ) - (S.nR 0 / 2 : ℕ) : ℤ) : ℚ) = hw Q.psiPar i := by
      rw [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_natCast, cast_half, cast_half, h1, h2]
      ring
    exact_mod_cast this
  · simp
  · dsimp only
    split_ifs with h
    · ring
    · have hi := i.2
      simp only [Fin.val_succ, Fin.val_castSucc, nR_succ] at hi h
      obtain ⟨r, hr⟩ : ∃ r, i.1 = S.nR j + r := ⟨i.1 - S.nR j, by omega⟩
      have h0 := hlen j.succ i
      have h1 := hw_big Q hQ i h0
      have h2 : Q.bigPar[i.1] = -Q.e j + (S.t : ℚ) / 2 - r := by
        rw [← bigPar_block Q j r (by omega) (hr ▸ h0)]
        simp only [hr]
      rw [h2, length_big] at h1
      have : ((hw Q.bigPar i + (S.nR S.m / 2 : ℕ) - (S.nR (j + 1) / 2 : ℕ) : ℤ) : ℚ) =
          ((-Q.e j + (S.nR j / 2 : ℕ) : ℤ) : ℚ) := by
        rw [Int.cast_sub, Int.cast_add, Int.cast_add, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast, cast_half,
          cast_half, cast_half, h1, nR_succ, hr]
        push_cast
        ring
      exact_mod_cast this

end GlobalTheory.OneFunctional.RowWeights
