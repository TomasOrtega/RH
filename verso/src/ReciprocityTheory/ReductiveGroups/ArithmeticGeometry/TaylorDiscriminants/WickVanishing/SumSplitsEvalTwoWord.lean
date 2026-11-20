import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.EvalZeroReplicateAppend

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {ι : Type} [DecidableEq ι]

/- English proof (translation)
Proceed by induction on `w generalizing F with`. Consider the case `nil => simp [splits]`. Consider the case `cons l w ih`. Simplify using `only [splits, List.map_append, List.map_map, List.sum_append, Function.comp_def]`. Rewrite using `[ih (fun u => F (l :: u))]`.

Rewrite using `[List.sum_eq_zero (fun x hx => ?_), add_zero]`. Take `⟨p, -, rfl⟩` from `List.mem_map.mp hx`. Simplify using the standard rewrite rules.
-/
private theorem splits_nil_lemma (w : List ι) (F : List ι → k) (c : k) :
    ((splits w).map (fun p => F p.1 * (if p.2 = [] then c else 0))).sum = F w * c := by
  induction w generalizing F with
  | nil => simp [splits]
  | cons l w ih =>
    simp only [splits, List.map_append, List.map_map, List.sum_append, Function.comp_def]
    rw [ih (fun u => F (l :: u))]
    rw [List.sum_eq_zero (fun x hx => ?_), add_zero]
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
    simp

/- English proof (translation)
Apply the tactic sequence `cases t <;> simp [ev1]`.
-/
private theorem ev1_cons_lemma_2 (g : ι → k) (l : ι) (t : List ι) :
    ev1 g (l :: t) = if t = [] then g l else 0 := by
  cases t <;> simp [ev1]

/- English proof (translation)
Simplify using `only [splits, List.map_append, List.map_map, List.sum_append, Function.comp_def, ev1_cons_lemma_2]`. Rewrite using `[splits_nil_lemma w φ (g l)]`.
-/
private theorem t1_cons_lemma_3 (g : ι → k) (l : ι) (w : List ι) (φ : List ι → k) :
    ((splits (l :: w)).map (fun p => φ p.1 * ev1 g p.2)).sum =
      ((splits w).map (fun p => φ (l :: p.1) * ev1 g p.2)).sum + φ w * g l := by
  simp only [splits, List.map_append, List.map_map, List.sum_append, Function.comp_def,
    ev1_cons_lemma_2]
  rw [splits_nil_lemma w φ (g l)]

/- English proof (translation)
Proceed by induction on `n generalizing φ with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[List.replicate_succ, List.cons_append, t1_cons_lemma_3, ih (fun u => φ (y :: u))]`. Consider the cases of `n with`.

Consider the case `zero`. Simplify using the standard rewrite rules. Apply the tactic sequence `try ring`. Consider the case `succ n`. Simplify using `only [Nat.add_sub_cancel, List.replicate_succ, List.cons_append]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem t1_rep_lemma_4 (g : ι → k) (y : ι) (n : ℕ) (w : List ι) (φ : List ι → k) :
    ((splits (List.replicate n y ++ w)).map (fun p => φ p.1 * ev1 g p.2)).sum =
      ((splits w).map (fun p => φ (List.replicate n y ++ p.1) * ev1 g p.2)).sum +
        (n : k) * g y * φ (List.replicate (n - 1) y ++ w) := by
  induction n generalizing φ with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, t1_cons_lemma_3, ih (fun u => φ (y :: u))]
    cases n with
    | zero =>
      simp
      try ring
    | succ n =>
      simp only [Nat.add_sub_cancel, List.replicate_succ, List.cons_append]
      push_cast
      ring

/- English proof (translation)
Simplify using `[word, List.flatMap_cons]`.
-/
private theorem word_cons_lemma_5 (y : ι) (Ls : List ι) (m : ι →₀ ℕ) :
    word (y :: Ls) m = List.replicate (m y) y ++ word Ls m := by
  simp [word, List.flatMap_cons]

/- English proof (translation)
Proceed by induction on `Ls with`. Consider the case `nil => rfl`. Consider the case `cons y Ls ih`. Rewrite using `[word_cons_lemma_5, word_cons_lemma_5, h y (by simp), ih fun z hz => h z (by simp [hz])]`.
-/
private theorem word_congr_lemma_6 (Ls : List ι) (m m' : ι →₀ ℕ) (h : ∀ z ∈ Ls, m z = m' z) :
    word Ls m = word Ls m' := by
  induction Ls with
  | nil => rfl
  | cons y Ls ih =>
    rw [word_cons_lemma_5, word_cons_lemma_5, h y (by simp), ih fun z hz => h z (by simp [hz])]

/- English proof (translation)
Use `revert hnd`. Proceed by induction on `Ls generalizing φ with`. Consider the case `nil`. Introduce `_`. Simplify using `[word, splits, ev1]`.

Consider the case `cons y Ls ih`. Introduce `hnd`. Establish `hy : y ∉ Ls` using `(List.nodup_cons.mp hnd).1`. Establish `hnd' : Ls.Nodup` using `(List.nodup_cons.mp hnd).2`. Rewrite using `[word_cons_lemma_5, t1_rep_lemma_4, ih (fun u => φ (List.replicate (m y) y ++ u)) hnd', List.map_cons, List.sum_cons, add_comm]`.

Use `congr 1`. Establish `e1 : (m - Finsupp.single y 1 : ι →₀ ℕ) y = m y - 1` using `by simp`. Establish `e2 : word Ls (m - Finsupp.single y 1) = word Ls m` using `word_congr_lemma_6 _ _ _ fun z hz => by`. Establish `hyz : y ≠ z` using `fun h => hy (h ▸ hz)`. Simplify using `[Finsupp.single_apply, hyz]`.

Rewrite using `[word_cons_lemma_5, e1, e2]`. Use `congr 1`. Use `List.map_congr_left fun z hz => ?_` and prove the remaining obligations. Establish `hzy : z ≠ y` using `fun h => hy (h ▸ hz)`. Establish `e : (m - Finsupp.single z 1 : ι →₀ ℕ) y = m y` using `by simp [Finsupp.single_apply, hzy]`.

Rewrite using `[word_cons_lemma_5, e]`.
-/
theorem sum_splits_evalOne_word (g : ι → k) (Ls : List ι) (hnd : Ls.Nodup) (m : ι →₀ ℕ) (φ : List ι → k) :
    ((splits (word Ls m)).map (fun p => φ p.1 * ev1 g p.2)).sum =
      (Ls.map (fun y => (m y : k) * g y * φ (word Ls (m - Finsupp.single y 1)))).sum := by
  revert hnd
  induction Ls generalizing φ with
  | nil =>
    intro _
    simp [word, splits, ev1]
  | cons y Ls ih =>
    intro hnd
    have hy : y ∉ Ls := (List.nodup_cons.mp hnd).1
    have hnd' : Ls.Nodup := (List.nodup_cons.mp hnd).2
    rw [word_cons_lemma_5, t1_rep_lemma_4, ih (fun u => φ (List.replicate (m y) y ++ u)) hnd',
      List.map_cons, List.sum_cons, add_comm]
    congr 1
    · have e1 : (m - Finsupp.single y 1 : ι →₀ ℕ) y = m y - 1 := by simp
      have e2 : word Ls (m - Finsupp.single y 1) = word Ls m :=
        word_congr_lemma_6 _ _ _ fun z hz => by
          have hyz : y ≠ z := fun h => hy (h ▸ hz)
          simp [Finsupp.single_apply, hyz]
      rw [word_cons_lemma_5, e1, e2]
    · congr 1
      refine List.map_congr_left fun z hz => ?_
      have hzy : z ≠ y := fun h => hy (h ▸ hz)
      have e : (m - Finsupp.single z 1 : ι →₀ ℕ) y = m y := by simp [Finsupp.single_apply, hzy]
      rw [word_cons_lemma_5, e]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Nat.choose_succ_succ, Nat.choose_one_right, mul_add, ih]`. Consider the cases of `n with`.

Consider the case `zero => simp`. Consider the case `succ n => simp only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, mul_add, ih]
    cases n with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel]; ring

/- English proof (translation)
Apply the tactic sequence `rcases t with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> first | rfl | simp [ev1, ev2]`.
-/
private theorem ev2_cons_lemma_7 (c : ι → ι → k) (l : ι) (t : List ι) :
    ev2 c (l :: t) = ev1 (c l) t := by
  rcases t with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> first | rfl | simp [ev1, ev2]

/- English proof (translation)
Simplify using `only [splits, List.map_append, List.map_map, List.sum_append, Function.comp_def, ev2_cons_lemma_7]`.
-/
private theorem t2_cons_lemma_8 (c : ι → ι → k) (l : ι) (w : List ι) (φ : List ι → k) :
    ((splits (l :: w)).map (fun p => φ p.1 * ev2 c p.2)).sum =
      ((splits w).map (fun p => φ (l :: p.1) * ev2 c p.2)).sum +
        ((splits w).map (fun p => φ p.1 * ev1 (c l) p.2)).sum := by
  simp only [splits, List.map_append, List.map_map, List.sum_append, Function.comp_def,
    ev2_cons_lemma_7]

/- English proof (translation)
Proceed by induction on `n generalizing φ with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[List.replicate_succ, List.cons_append, t2_cons_lemma_8, ih (fun u => φ (y :: u)), t1_rep_lemma_4]`. Break down `n with _ | _ | n` into its components or cases.

Simplify using `[Nat.choose_zero_succ, Nat.choose_succ_self]`. Apply the tactic sequence `simp [Nat.choose_succ_self, Nat.choose_self] try ring`. Establish `e1 : n + 1 + 1 + 1 - 1 = n + 1 + 1` using `by omega`. Establish `e2 : n + 1 + 1 - 1 = n + 1` using `by omega`. Establish `e3 : n + 1 + 1 + 1 - 2 = n + 1` using `by omega`.

Establish `e4 : n + 1 + 1 - 2 = n` using `by omega`. Establish `e5 : (n + 1 + 1 + 1).choose 2 = (n + 1 + 1).choose 2 + (n + 1 + 1)`. Rewrite using `[Nat.choose_succ_succ', Nat.choose_one_right]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, e3, e4, e5]`.

Simplify using `only [List.replicate_succ, List.cons_append]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem t2_rep_lemma_9 (c : ι → ι → k) (y : ι) (n : ℕ) (w : List ι) (φ : List ι → k) :
    ((splits (List.replicate n y ++ w)).map (fun p => φ p.1 * ev2 c p.2)).sum =
      ((splits w).map (fun p => φ (List.replicate n y ++ p.1) * ev2 c p.2)).sum +
        (n : k) * ((splits w).map (fun p => φ (List.replicate (n - 1) y ++ p.1) * ev1 (c y) p.2)).sum +
        (n.choose 2 : k) * c y y * φ (List.replicate (n - 2) y ++ w) := by
  induction n generalizing φ with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, t2_cons_lemma_8, ih (fun u => φ (y :: u)), t1_rep_lemma_4]
    rcases n with _ | _ | n
    · simp [Nat.choose_zero_succ, Nat.choose_succ_self]
    · simp [Nat.choose_succ_self, Nat.choose_self]
      try ring
    · have e1 : n + 1 + 1 + 1 - 1 = n + 1 + 1 := by omega
      have e2 : n + 1 + 1 - 1 = n + 1 := by omega
      have e3 : n + 1 + 1 + 1 - 2 = n + 1 := by omega
      have e4 : n + 1 + 1 - 2 = n := by omega
      have e5 : (n + 1 + 1 + 1).choose 2 = (n + 1 + 1).choose 2 + (n + 1 + 1) := by
        rw [Nat.choose_succ_succ', Nat.choose_one_right]
        ring
      rw [e1, e2, e3, e4, e5]
      simp only [List.replicate_succ, List.cons_append]
      push_cast
      ring

/- English proof (translation)
Use `revert hnd`. Proceed by induction on `Ls generalizing φ with`. Consider the case `nil`. Introduce `_`. Simplify using `[word, splits, ev2]`.

Consider the case `cons y0 Ls ih`. Introduce `hnd`. Establish `hy : y0 ∉ Ls` using `(List.nodup_cons.mp hnd).1`. Establish `hnd' : Ls.Nodup` using `(List.nodup_cons.mp hnd).2`. Establish `hne : ∀ z ∈ Ls, y0 ≠ z` using `fun z hz h => hy (h ▸ hz)`.

Rewrite using `[word_cons_lemma_5, t2_rep_lemma_9, mul_add, mul_add, ih (fun u => φ (List.replicate (m y0) y0 ++ u)) hnd', sum_splits_evalOne_word (c y0) Ls hnd' m (fun u => φ (List.replicate (m y0 - 1) y0 ++ u))]`. Simplify using `only [List.map_cons, List.sum_cons, List.sum_map_add]`. Establish `ha : c y0 y0 * ((m y0 * (m - Finsupp.single y0 1 : ι →₀ ℕ) y0 : ℕ) : k) * φ (word (y0 :: Ls) (m - Finsupp.single y0 1 - Finsupp.single y0 1)) = 2 * (((m y0).choose 2 : ℕ) * c y0 y0 * φ (List.replicate (m y0 - 2) y0 ++ word Ls m))`. Establish `e1 : (m - Finsupp.single y0 1 : ι →₀ ℕ) y0 = m y0 - 1` using `by simp`. Establish `e2 : (m - Finsupp.single y0 1 - Finsupp.single y0 1 : ι →₀ ℕ) y0 = m y0 - 2` using `by first`.

Consider the case `(simp; done)`. Consider the case `(simp; omega)`. Establish `e3 : word Ls (m - Finsupp.single y0 1 - Finsupp.single y0 1) = word Ls m` using `word_congr_lemma_6 _ _ _ fun z hz => by simp [Finsupp.single_apply, hne z hz]`. Rewrite using `[e1, word_cons_lemma_5, e2, e3, ← two_mul_choose_two]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hb1 : (Ls.map (fun y => c y0 y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) y0 : ℕ) : k) * φ (word (y0 :: Ls) (m - Finsupp.single y 1 - Finsupp.single y0 1)))).sum = (m y0 : k) * (Ls.map (fun y => (m y : k) * c y0 y * φ (List.replicate (m y0 - 1) y0 ++ word Ls (m - Finsupp.single …`. Rewrite using `[← List.sum_map_mul_left]`. Use `congr 1`. Use `List.map_congr_left fun y hyL => ?_` and prove the remaining obligations.

Establish `hyy : y0 ≠ y` using `hne y hyL`. Establish `e1 : (m - Finsupp.single y 1 : ι →₀ ℕ) y0 = m y0` using `by simp [Finsupp.single_apply, hyy.symm]`. Establish `e2 : (m - Finsupp.single y 1 - Finsupp.single y0 1 : ι →₀ ℕ) y0 = m y0 - 1`. Simplify using `[Finsupp.single_apply, hyy.symm]`. Establish `e3 : word Ls (m - Finsupp.single y 1 - Finsupp.single y0 1) = word Ls (m - Finsupp.single y 1)` using `word_congr_lemma_6 _ _ _ fun z hz => by simp [Finsupp.single_apply, hne z hz]`.

Rewrite using `[e1, word_cons_lemma_5, e2, e3]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hb2 : (Ls.map (fun x => c x y0 * ((m y0 * (m - Finsupp.single y0 1 : ι →₀ ℕ) x : ℕ) : k) * φ (word (y0 :: Ls) (m - Finsupp.single y0 1 - Finsupp.single x 1)))).sum = (m y0 : k) * (Ls.map (fun y => (m y : k) * c y0 y * φ (List.replicate (m y0 - 1) y0 ++ word Ls (m - Finsupp.single …`. Rewrite using `[← List.sum_map_mul_left]`.

Use `congr 1`. Use `List.map_congr_left fun x hxL => ?_` and prove the remaining obligations. Establish `hxx : y0 ≠ x` using `hne x hxL`. Establish `e1 : (m - Finsupp.single y0 1 : ι →₀ ℕ) x = m x` using `by simp [Finsupp.single_apply, hxx]`. Establish `e2 : (m - Finsupp.single y0 1 - Finsupp.single x 1 : ι →₀ ℕ) y0 = m y0 - 1`.

Simplify using `[Finsupp.single_apply, hxx.symm]`. Establish `e3 : word Ls (m - Finsupp.single y0 1 - Finsupp.single x 1) = word Ls (m - Finsupp.single x 1)` using `word_congr_lemma_6 _ _ _ fun z hz => by simp [Finsupp.single_apply, hne z hz]`. Rewrite using `[e1, word_cons_lemma_5, e2, e3, hc x y0]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hcc : (Ls.map (fun x => (Ls.map (fun y => c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k) * φ (word (y0 :: Ls) (m - Finsupp.single y 1 - Finsupp.single x 1)))).sum)).sum = (Ls.map (fun x => (Ls.map (fun y => c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : …`. Use `congr 1`. Use `List.map_congr_left fun x hxL => ?_` and prove the remaining obligations. Use `congr 1`. Use `List.map_congr_left fun y hyL => ?_` and prove the remaining obligations.

Establish `e : (m - Finsupp.single y 1 - Finsupp.single x 1 : ι →₀ ℕ) y0 = m y0`. Simplify using `[Finsupp.single_apply, (hne y hyL).symm, (hne x hxL).symm]`. Rewrite using `[word_cons_lemma_5, e]`. Take the linear combination `-ha - hb1 - hb2 - hcc`.
-/
theorem sum_splits_evalTwo_word (c : ι → ι → k) (hc : ∀ x y, c x y = c y x) (Ls : List ι) (hnd : Ls.Nodup)
    (m : ι →₀ ℕ) (φ : List ι → k) :
    2 * ((splits (word Ls m)).map (fun p => φ p.1 * ev2 c p.2)).sum =
      (Ls.map (fun x => (Ls.map (fun y => c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k) *
        φ (word Ls (m - Finsupp.single y 1 - Finsupp.single x 1)))).sum)).sum := by
  revert hnd
  induction Ls generalizing φ with
  | nil =>
    intro _
    simp [word, splits, ev2]
  | cons y0 Ls ih =>
    intro hnd
    have hy : y0 ∉ Ls := (List.nodup_cons.mp hnd).1
    have hnd' : Ls.Nodup := (List.nodup_cons.mp hnd).2
    have hne : ∀ z ∈ Ls, y0 ≠ z := fun z hz h => hy (h ▸ hz)
    rw [word_cons_lemma_5, t2_rep_lemma_9, mul_add, mul_add,
      ih (fun u => φ (List.replicate (m y0) y0 ++ u)) hnd',
      sum_splits_evalOne_word (c y0) Ls hnd' m (fun u => φ (List.replicate (m y0 - 1) y0 ++ u))]
    simp only [List.map_cons, List.sum_cons, List.sum_map_add]
    have ha : c y0 y0 * ((m y0 * (m - Finsupp.single y0 1 : ι →₀ ℕ) y0 : ℕ) : k) *
        φ (word (y0 :: Ls) (m - Finsupp.single y0 1 - Finsupp.single y0 1)) =
        2 * (((m y0).choose 2 : ℕ) * c y0 y0 * φ (List.replicate (m y0 - 2) y0 ++ word Ls m)) := by
      have e1 : (m - Finsupp.single y0 1 : ι →₀ ℕ) y0 = m y0 - 1 := by simp
      have e2 : (m - Finsupp.single y0 1 - Finsupp.single y0 1 : ι →₀ ℕ) y0 = m y0 - 2 := by
        first
        | (simp; done)
        | (simp; omega)
      have e3 : word Ls (m - Finsupp.single y0 1 - Finsupp.single y0 1) = word Ls m :=
        word_congr_lemma_6 _ _ _ fun z hz => by simp [Finsupp.single_apply, hne z hz]
      rw [e1, word_cons_lemma_5, e2, e3, ← two_mul_choose_two]
      push_cast
      ring
    have hb1 : (Ls.map (fun y => c y0 y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) y0 : ℕ) : k) *
          φ (word (y0 :: Ls) (m - Finsupp.single y 1 - Finsupp.single y0 1)))).sum =
        (m y0 : k) * (Ls.map (fun y => (m y : k) * c y0 y *
          φ (List.replicate (m y0 - 1) y0 ++ word Ls (m - Finsupp.single y 1)))).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun y hyL => ?_
      have hyy : y0 ≠ y := hne y hyL
      have e1 : (m - Finsupp.single y 1 : ι →₀ ℕ) y0 = m y0 := by simp [Finsupp.single_apply, hyy.symm]
      have e2 : (m - Finsupp.single y 1 - Finsupp.single y0 1 : ι →₀ ℕ) y0 = m y0 - 1 := by
        simp [Finsupp.single_apply, hyy.symm]
      have e3 : word Ls (m - Finsupp.single y 1 - Finsupp.single y0 1) = word Ls (m - Finsupp.single y 1) :=
        word_congr_lemma_6 _ _ _ fun z hz => by simp [Finsupp.single_apply, hne z hz]
      rw [e1, word_cons_lemma_5, e2, e3]
      push_cast
      ring
    have hb2 : (Ls.map (fun x => c x y0 * ((m y0 * (m - Finsupp.single y0 1 : ι →₀ ℕ) x : ℕ) : k) *
          φ (word (y0 :: Ls) (m - Finsupp.single y0 1 - Finsupp.single x 1)))).sum =
        (m y0 : k) * (Ls.map (fun y => (m y : k) * c y0 y *
          φ (List.replicate (m y0 - 1) y0 ++ word Ls (m - Finsupp.single y 1)))).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun x hxL => ?_
      have hxx : y0 ≠ x := hne x hxL
      have e1 : (m - Finsupp.single y0 1 : ι →₀ ℕ) x = m x := by simp [Finsupp.single_apply, hxx]
      have e2 : (m - Finsupp.single y0 1 - Finsupp.single x 1 : ι →₀ ℕ) y0 = m y0 - 1 := by
        simp [Finsupp.single_apply, hxx.symm]
      have e3 : word Ls (m - Finsupp.single y0 1 - Finsupp.single x 1) = word Ls (m - Finsupp.single x 1) :=
        word_congr_lemma_6 _ _ _ fun z hz => by simp [Finsupp.single_apply, hne z hz]
      rw [e1, word_cons_lemma_5, e2, e3, hc x y0]
      push_cast
      ring
    have hcc : (Ls.map (fun x => (Ls.map (fun y => c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k) *
          φ (word (y0 :: Ls) (m - Finsupp.single y 1 - Finsupp.single x 1)))).sum)).sum =
        (Ls.map (fun x => (Ls.map (fun y => c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k) *
          φ (List.replicate (m y0) y0 ++ word Ls (m - Finsupp.single y 1 - Finsupp.single x 1)))).sum)).sum := by
      congr 1
      refine List.map_congr_left fun x hxL => ?_
      congr 1
      refine List.map_congr_left fun y hyL => ?_
      have e : (m - Finsupp.single y 1 - Finsupp.single x 1 : ι →₀ ℕ) y0 = m y0 := by
        simp [Finsupp.single_apply, (hne y hyL).symm, (hne x hxL).symm]
      rw [word_cons_lemma_5, e]
    linear_combination -ha - hb1 - hb2 - hcc

end ReciprocityTheory.ChartRestriction.G.TB.G2
