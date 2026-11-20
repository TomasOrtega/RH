import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv

open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.StrictInterlace

inductive Alt : ℚ → List ℚ → List ℚ → ℚ → Prop
  | nil (x : ℚ) : Alt x [] [] x
  | cons {x s b y : ℚ} {sm bg : List ℚ} : x > s → s > b → Alt b sm bg y → Alt x (s :: sm) (b :: bg) y

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `nil x => simpa using h'`. Consider the case `cons h1 h2 _ ih => exact Alt.cons h1 h2 (ih h')`.
-/
theorem Alt.append {x y z : ℚ} {s b s' b' : List ℚ} (h : Alt x s b y) (h' : Alt y s' b' z) :
    Alt x (s ++ s') (b ++ b') z := by
  induction h with
  | nil x => simpa using h'
  | cons h1 h2 _ ih => exact Alt.cons h1 h2 (ih h')

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `nil x => exact ⟨rfl, fun i h => absurd h (by simp)⟩`. Consider the case `cons h1 h2 _ ih`. Use `⟨by simpa using ih.1, fun i h h' => ?_⟩` and prove the remaining obligations. Consider the cases of `i with`.

Consider the case `zero => exact ⟨h1, h2⟩`. Consider the case `succ i => exact ih.2 i (by simpa using h) (by simpa using h')`.
-/
theorem Alt.interlace {x y : ℚ} {s b : List ℚ} (h : Alt x s b y) : Interlace (x :: b) s := by
  induction h with
  | nil x => exact ⟨rfl, fun i h => absurd h (by simp)⟩
  | cons h1 h2 _ ih =>
    refine ⟨by simpa using ih.1, fun i h h' => ?_⟩
    cases i with
    | zero => exact ⟨h1, h2⟩
    | succ i => exact ih.2 i (by simpa using h) (by simpa using h')

def Above (x : ℚ) (L : List ℚ) : Prop := ∀ z : ℤ, (z : ℚ) ∈ L → x > z

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => intro x _ hx; exact ⟨x, Alt.nil x, by simpa using hx⟩`. Consider the case `cons i l ih`. Introduce `x hp hx`. Rewrite `hp`, `hx` using `[List.flatMap_cons, List.append_assoc]`.

Take `⟨y, h1, h2⟩` from `seg i x _ hp hx`. Take `⟨z, h3, h4⟩` from `ih y (List.pairwise_append.1 hp).2.1 h2`. Conclude with `⟨z, by simpa only [List.flatMap_cons] using h1.append h3, h4⟩`.
-/
theorem alt_flatMap {ι : Type} (f g h : ι → List ℚ)
    (seg : ∀ i x L, (f i ++ L).Pairwise (· > ·) → Above x (f i ++ L) → ∃ y, Alt x (g i) (h i) y ∧ Above y L)
    (l : List ι) (L : List ℚ) : ∀ x, (l.flatMap f ++ L).Pairwise (· > ·) → Above x (l.flatMap f ++ L) →
      ∃ y, Alt x (l.flatMap g) (l.flatMap h) y ∧ Above y L := by
  induction l with
  | nil => intro x _ hx; exact ⟨x, Alt.nil x, by simpa using hx⟩
  | cons i l ih =>
    intro x hp hx
    rw [List.flatMap_cons, List.append_assoc] at hp hx
    obtain ⟨y, h1, h2⟩ := seg i x _ hp hx
    obtain ⟨z, h3, h4⟩ := ih y (List.pairwise_append.1 hp).2.1 h2
    exact ⟨z, by simpa only [List.flatMap_cons] using h1.append h3, h4⟩

/- English proof (translation)
Simplify using `only [block, List.range_succ_eq_map, List.map_cons, List.map_map]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `List.map_congr_left fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [Function.comp]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem block_succ (c : ℚ) (n : ℕ) : block c (n + 1) = (c + n / 2) :: block (c - 1 / 2) n := by
  simp only [block, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · push_cast; ring
  · refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp]
    push_cast; ring

/- English proof (translation)
The claim follows from `List.mem_map.2 ⟨i, List.mem_range.2 hi, hx.symm⟩`.
-/
theorem mem_block (c : ℚ) {n i : ℕ} (hi : i < n) {x : ℚ} (hx : x = c + ((n : ℚ) - 1) / 2 - i) : x ∈ block c n :=
  List.mem_map.2 ⟨i, List.mem_range.2 hi, hx.symm⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `c x h1 h2`. Rewrite using `[block_succ]`. Conclude with `Alt.cons h1 (by simpa using h2) (Alt.nil a)`.

Consider the case `succ n ih`. Introduce `c x h1 h2`. Rewrite using `[block_succ c (n + 1), block_succ c n]`. Move the coercions through the operations in `at h1 h2 ⊢`. Conclude with `Alt.cons h1 (by linarith) (ih _ _ (by linarith) (by linarith))`.
-/
theorem alt_block_upper (n : ℕ) (a : ℚ) : ∀ c x : ℚ, x > c + n / 2 → c - n / 2 > a →
    Alt x (block c (n + 1)) (block c n ++ [a]) a := by
  induction n with
  | zero =>
    intro c x h1 h2
    rw [block_succ]
    exact Alt.cons h1 (by simpa using h2) (Alt.nil a)
  | succ n ih =>
    intro c x h1 h2
    rw [block_succ c (n + 1), block_succ c n]
    push_cast at h1 h2 ⊢
    exact Alt.cons h1 (by linarith) (ih _ _ (by linarith) (by linarith))

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro c`. Simplify `Alt.nil c` using `[block]`. Consider the case `succ n ih`. Introduce `c`.

Rewrite using `[block_succ c n, block_succ (c - 1 / 2) n]`. Establish `e : c - ((n + 1 : ℕ) : ℚ) / 2 = c - 1 / 2 - n / 2` using `by push_cast; ring`. Rewrite using `[e]`. Use `Alt.cons ?_ (by linarith) (ih _)` and prove the remaining obligations. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem alt_block_lower (n : ℕ) : ∀ c : ℚ, Alt (c + n / 2) (block c n) (block (c - 1 / 2) n) (c - n / 2) := by
  induction n with
  | zero => intro c; simpa [block] using Alt.nil c
  | succ n ih =>
    intro c
    rw [block_succ c n, block_succ (c - 1 / 2) n]
    have e : c - ((n + 1 : ℕ) : ℚ) / 2 = c - 1 / 2 - n / 2 := by push_cast; ring
    rw [e]
    refine Alt.cons ?_ (by linarith) (ih _)
    push_cast; linarith

/- English proof (translation)
Take `⟨r, rfl⟩` from `hs`. Take `⟨h1, -, h2⟩` from `List.pairwise_append.1 hp`. Use `⟨a, alt_block_upper (2 * r) a c x ?_ ?_, fun z hz => h2 a (by simp) _ hz⟩` and prove the remaining obligations. Use `hx (c + r) (List.mem_append_left _ (List.mem_append_left _ (mem_block (i := 0) _ (by omega) (by push_cast; ring))))` as an intermediate fact. Move the coercions through the operations in `at this ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(List.pairwise_append.1 h1).2.2 _ (mem_block (i := 2 * r) _ (by omega) (by push_cast; ring)) a (by simp)`.
-/
theorem seg_upper (c : ℤ) (a : ℚ) {s : ℕ} (hs : Odd s) (x : ℚ) (L : List ℚ)
    (hp : (block c s ++ [a] ++ L).Pairwise (· > ·)) (hx : Above x (block c s ++ [a] ++ L)) :
    ∃ y, Alt x (block c s) (block c (s - 1) ++ [a]) y ∧ Above y L := by
  obtain ⟨r, rfl⟩ := hs
  obtain ⟨h1, -, h2⟩ := List.pairwise_append.1 hp
  refine ⟨a, alt_block_upper (2 * r) a c x ?_ ?_, fun z hz => h2 a (by simp) _ hz⟩
  · have := hx (c + r) (List.mem_append_left _ (List.mem_append_left _
      (mem_block (i := 0) _ (by omega) (by push_cast; ring))))
    push_cast at this ⊢; linarith
  · exact (List.pairwise_append.1 h1).2.2 _ (mem_block (i := 2 * r) _ (by omega) (by push_cast; ring)) a (by simp)

/- English proof (translation)
Take `⟨h1, -, h2⟩` from `List.pairwise_append.1 hp`. Conclude with `⟨u, Alt.cons (hx v (by simp)) (by simpa using h1) (Alt.nil u), fun z hz => h2 u (by simp) _ hz⟩`.
-/
theorem seg_middle (v : ℤ) (u : ℚ) (x : ℚ) (L : List ℚ)
    (hp : ([(v : ℚ), u] ++ L).Pairwise (· > ·)) (hx : Above x ([(v : ℚ), u] ++ L)) :
    ∃ y, Alt x [(v : ℚ)] [u] y ∧ Above y L := by
  obtain ⟨h1, -, h2⟩ := List.pairwise_append.1 hp
  exact ⟨u, Alt.cons (hx v (by simp)) (by simpa using h1) (Alt.nil u), fun z hz => h2 u (by simp) _ hz⟩

/- English proof (translation)
Take `⟨r, rfl⟩` from `ht`. Take `⟨h1, -, h2⟩` from `List.pairwise_append.1 hp`. Rewrite using `[block_succ (-e) (2 * r + 1)]`. Use `⟨_, Alt.cons ?_ ?_ (alt_block_lower _ _), fun z hz => ?_⟩` and prove the remaining obligations. Use `hx (-b) (by simp)` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Establish `h3 : (-b : ℚ) > ((-e + r : ℤ) : ℚ)` using `(List.pairwise_cons.1 h1).1 _ (mem_block (i := 0) _ (by omega) (by push_cast; ring))`. Establish `h4 : -e + r < -b` using `by exact_mod_cast h3`. Establish `h5 : ((-e + r + 1 : ℤ) : ℚ) ≤ ((-b : ℤ) : ℚ)` using `by exact_mod_cast h4`. Move the coercions through the operations in `at h5 ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : ((-e - r : ℤ) : ℚ) > z` using `h2 _ (List.mem_cons_of_mem _ (mem_block (i := 2 * r) _ (by omega) (by push_cast; ring))) _ hz`. Establish `h4 : z < -e - r` using `by exact_mod_cast h3`. Establish `h5 : ((z + 1 : ℤ) : ℚ) ≤ ((-e - r : ℤ) : ℚ)` using `by exact_mod_cast h4`. Move the coercions through the operations in `at h5 ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem seg_lower (b e : ℤ) {t : ℕ} (ht : Odd t) (x : ℚ) (L : List ℚ)
    (hp : (((-b : ℚ) :: block (-e) t) ++ L).Pairwise (· > ·)) (hx : Above x (((-b : ℚ) :: block (-e) t) ++ L)) :
    ∃ y, Alt x ((-b : ℚ) :: block (-e) t) (block (-e) (t + 1)) y ∧ Above y L := by
  obtain ⟨r, rfl⟩ := ht
  obtain ⟨h1, -, h2⟩ := List.pairwise_append.1 hp
  rw [block_succ (-e) (2 * r + 1)]
  refine ⟨_, Alt.cons ?_ ?_ (alt_block_lower _ _), fun z hz => ?_⟩
  · have := hx (-b) (by simp)
    exact_mod_cast this
  · have h3 : (-b : ℚ) > ((-e + r : ℤ) : ℚ) :=
      (List.pairwise_cons.1 h1).1 _ (mem_block (i := 0) _ (by omega) (by push_cast; ring))
    have h4 : -e + r < -b := by exact_mod_cast h3
    have h5 : ((-e + r + 1 : ℤ) : ℚ) ≤ ((-b : ℤ) : ℚ) := by exact_mod_cast h4
    push_cast at h5 ⊢; linarith
  · have h3 : ((-e - r : ℤ) : ℚ) > z :=
      h2 _ (List.mem_cons_of_mem _ (mem_block (i := 2 * r) _ (by omega) (by push_cast; ring))) _ hz
    have h4 : z < -e - r := by exact_mod_cast h3
    have h5 : ((z + 1 : ℤ) : ℚ) ≤ ((-e - r : ℤ) : ℚ) := by exact_mod_cast h4
    push_cast at h5 ⊢; linarith

/- English proof (translation)
Establish `ho` using `hQ.order`. Rewrite `ho` using `[Entries.orderList, List.cons_append, List.cons_append, List.append_assoc]`. Take `⟨h0, ho⟩` from `List.pairwise_cons.1 ho`. Take `⟨y1, a1, b1⟩` from `alt_flatMap _ _ _ (fun i => seg_upper (Q.c i) (Q.a i.succ) S.s_odd) _ _ (Q.a 0) ho (fun z hz => h0 _ hz)`. Establish `ho2` using `(List.pairwise_append.1 ho).2.1`.

Take `⟨y2, a2, b2⟩` from `alt_flatMap _ _ _ (fun i => seg_middle (Q.v i) (Q.u i)) _ _ y1 ho2 b1`. Establish `ho3` using `(List.pairwise_append.1 ho2).2.1`. Take `⟨y3, a3, -⟩` from `alt_flatMap _ _ _ (fun i => seg_lower (Q.b i) (Q.e i) S.t_odd) (List.finRange S.m) [] y2 (by simpa only [List.append_nil] using ho3) (by simpa only [List.append_nil] using b2)`. Use `(a1.append (a2.append a3)).interlace` as an intermediate fact. Simplify `this` using `only [Entries.bigPar, Entries.psiPar, Entries.smallPar, Entries.basePar, List.cons_append, List.append_assoc, List.map_eq_flatMap]`.
-/
theorem interlace_big_small (S : Sizes) (Q : Entries S) (hQ : Q.Good) : Interlace Q.bigPar Q.smallPar := by
  have ho := hQ.order
  rw [Entries.orderList, List.cons_append, List.cons_append, List.append_assoc] at ho
  obtain ⟨h0, ho⟩ := List.pairwise_cons.1 ho
  obtain ⟨y1, a1, b1⟩ := alt_flatMap _ _ _ (fun i => seg_upper (Q.c i) (Q.a i.succ) S.s_odd) _ _ (Q.a 0) ho
    (fun z hz => h0 _ hz)
  have ho2 := (List.pairwise_append.1 ho).2.1
  obtain ⟨y2, a2, b2⟩ := alt_flatMap _ _ _ (fun i => seg_middle (Q.v i) (Q.u i)) _ _ y1 ho2 b1
  have ho3 := (List.pairwise_append.1 ho2).2.1
  obtain ⟨y3, a3, -⟩ := alt_flatMap _ _ _ (fun i => seg_lower (Q.b i) (Q.e i) S.t_odd) (List.finRange S.m) [] y2
    (by simpa only [List.append_nil] using ho3) (by simpa only [List.append_nil] using b2)
  have := (a1.append (a2.append a3)).interlace
  simpa only [Entries.bigPar, Entries.psiPar, Entries.smallPar, Entries.basePar, List.cons_append, List.append_assoc,
    List.map_eq_flatMap] using this

end GlobalTheory.StrictInterlace
