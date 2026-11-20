import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMemGLs

noncomputable section

open Matrix Finset
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.GelLevi

open GlobalTheory.CompanionTheory.RCalc (Pw)

section Word

variable {R ι M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [DecidableEq ι]

def wordOp (T : ι → ι → Module.End R M) (w : List (ι × ι)) : Module.End R M :=
  (w.map fun p => T p.1 p.2).prod

def wordWt (blk : ι → ℕ) (w : List (ι × ι)) : ℤ := (w.map fun p => (blk p.2 : ℤ) - blk p.1).sum

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem wordOp_nil (T : ι → ι → Module.End R M) : wordOp T [] = 1 := rfl

/- English proof (translation)
Simplify using `[wordOp]`.
-/
theorem wordOp_cons (T : ι → ι → Module.End R M) (p : ι × ι) (w : List (ι × ι)) :
    wordOp T (p :: w) = T p.1 p.2 * wordOp T w := by
  simp [wordOp]

/- English proof (translation)
Simplify using `[wordOp]`.
-/
theorem wordOp_append (T : ι → ι → Module.End R M) (v w : List (ι × ι)) :
    wordOp T (v ++ w) = wordOp T v * wordOp T w := by
  simp [wordOp]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem wordWt_nil (blk : ι → ℕ) : wordWt blk [] = 0 := rfl

/- English proof (translation)
Simplify using `[wordWt]`.
-/
theorem wordWt_cons (blk : ι → ℕ) (p : ι × ι) (w : List (ι × ι)) :
    wordWt blk (p :: w) = (blk p.2 : ℤ) - blk p.1 + wordWt blk w := by
  simp [wordWt]

/- English proof (translation)
Simplify using `[wordWt]`.
-/
theorem wordWt_append (blk : ι → ℕ) (v w : List (ι × ι)) :
    wordWt blk (v ++ w) = wordWt blk v + wordWt blk w := by
  simp [wordWt]

/- English proof (translation)
Establish `e : T a b * T c d = T c d * T a b + ((if b = c then T a d else 0) - (if d = a then T c b else 0))`. Rewrite using `[← comm]`. Normalize the expressions using the abelian group laws. Simplify using `only [wordOp_append, wordOp_cons]`. Establish `e1 : wordOp T q * (T a b * (T c d * wordOp T t)) = wordOp T q * ((T a b * T c d) * wordOp T t)` using `by simp only [mul_assoc]`.

Rewrite using `[e1, e]`. Apply the tactic sequence `split_ifs <;> simp only [mul_add, add_mul, sub_mul, mul_sub, mul_assoc, zero_mul, mul_zero] <;> abel`.
-/
theorem wordOp_swap (T : ι → ι → Module.End R M)
    (comm : ∀ a b c d, T a b * T c d - T c d * T a b =
      (if b = c then T a d else 0) - (if d = a then T c b else 0))
    (q t : List (ι × ι)) (a b c d : ι) :
    wordOp T (q ++ (a, b) :: (c, d) :: t) = wordOp T (q ++ (c, d) :: (a, b) :: t) +
      (if b = c then wordOp T (q ++ (a, d) :: t) else 0) -
      (if d = a then wordOp T (q ++ (c, b) :: t) else 0) := by
  have e : T a b * T c d = T c d * T a b +
      ((if b = c then T a d else 0) - (if d = a then T c b else 0)) := by
    rw [← comm]; abel
  simp only [wordOp_append, wordOp_cons]
  have e1 : wordOp T q * (T a b * (T c d * wordOp T t)) =
      wordOp T q * ((T a b * T c d) * wordOp T t) := by simp only [mul_assoc]
  rw [e1, e]
  split_ifs <;> simp only [mul_add, add_mul, sub_mul, mul_sub, mul_assoc, zero_mul, mul_zero] <;> abel

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simp [wordWt_nil]`. Consider the case `cons p w ih`. Establish `h1` using `h p (by simp)`. Establish `h2` using `ih fun q hq => h q (by simp [hq])`.

Rewrite using `[wordWt_cons]`. Use linear arithmetic over natural numbers and integers.
-/
theorem wordWt_nonpos (blk : ι → ℕ) (w : List (ι × ι)) (h : ∀ q ∈ w, ¬ blk q.1 < blk q.2) :
    wordWt blk w ≤ 0 := by
  induction w with
  | nil => simp [wordWt_nil]
  | cons p w ih =>
    have h1 := h p (by simp)
    have h2 := ih fun q hq => h q (by simp [hq])
    rw [wordWt_cons]
    omega

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => right`. Simplify using the standard rewrite rules. Consider the case `cons y w ih`. Distinguish the cases in `hy : blk y.1 < blk y.2`.

Conclude with `Or.inl ⟨[], y, w, rfl, hy, by simp⟩`. Break down `ih with ⟨p, x, t, rfl, hx, hp⟩ | h` into its components or cases. Use `Or.inl ⟨y :: p, x, t, rfl, hx, ?_⟩` and prove the remaining obligations. Introduce `q hq`. Break down `List.mem_cons.1 hq with rfl | hq` into its components or cases.

Conclude with `hy`. Conclude with `hp q hq`. Use `right`. Introduce `q hq`. Break down `List.mem_cons.1 hq with rfl | hq` into its components or cases.

Conclude with `hy`. Conclude with `h q hq`.
-/
theorem word_split (blk : ι → ℕ) (w : List (ι × ι)) :
    (∃ p x t, w = p ++ x :: t ∧ blk x.1 < blk x.2 ∧ ∀ q ∈ p, ¬ blk q.1 < blk q.2) ∨
      ∀ q ∈ w, ¬ blk q.1 < blk q.2 := by
  induction w with
  | nil => right; simp
  | cons y w ih =>
    by_cases hy : blk y.1 < blk y.2
    · exact Or.inl ⟨[], y, w, rfl, hy, by simp⟩
    · rcases ih with ⟨p, x, t, rfl, hx, hp⟩ | h
      · refine Or.inl ⟨y :: p, x, t, rfl, hx, ?_⟩
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hy
        · exact hp q hq
      · right
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hy
        · exact h q hq

variable (T : ι → ι → Module.End R M) (blk : ι → ℕ) (F Z : AddSubgroup M)

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simpa [wordOp_nil] using hf`. Consider the case `cons p w ih => rw [wordOp_cons]`. Conclude with `stab _ _ _ ih`.
-/
theorem word_stab (stab : ∀ a b, ∀ x ∈ F, T a b x ∈ F) (w : List (ι × ι)) {f : M} (hf : f ∈ F) :
    wordOp T w f ∈ F := by
  induction w with
  | nil => simpa [wordOp_nil] using hf
  | cons p w ih => rw [wordOp_cons]; exact stab _ _ _ ih

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simpa [wordOp_nil] using hf`. Consider the case `cons p w ih`. Establish `h1` using `h p (by simp)`. Establish `h2 : ∀ q ∈ w, ¬ blk q.1 < blk q.2` using `fun q hq => h q (by simp [hq])`.

Establish `h3` using `wordWt_nonpos blk w h2`. Rewrite `hw` using `[wordWt_cons]`. Rewrite using `[wordOp_cons]`. Conclude with `lev _ _ (by omega) _ (ih h2 (by omega))`.
-/
theorem word_levi (lev : ∀ a b, blk a = blk b → ∀ x ∈ Z, T a b x ∈ Z) (w : List (ι × ι))
    (h : ∀ q ∈ w, ¬ blk q.1 < blk q.2) (hw : 0 ≤ wordWt blk w) {f : M} (hf : f ∈ Z) :
    wordOp T w f ∈ Z := by
  induction w with
  | nil => simpa [wordOp_nil] using hf
  | cons p w ih =>
    have h1 := h p (by simp)
    have h2 : ∀ q ∈ w, ¬ blk q.1 < blk q.2 := fun q hq => h q (by simp [hq])
    have h3 := wordWt_nonpos blk w h2
    rw [wordWt_cons] at hw
    rw [wordOp_cons]
    exact lev _ _ (by omega) _ (ih h2 (by omega))

/- English proof (translation)
Proceed by induction on `p using List.reverseRecOn with`. Consider the case `nil`. Introduce `x t _ hx _ _`. Simplify using `only [List.nil_append, wordOp_cons, Module.End.mul_apply]`. Conclude with `pos _ _ hx _ (word_stab T F stab _ hf)`.

Consider the case `append_singleton q y ih`. Introduce `x t hp hx hl hw`. Take `⟨a, b⟩` from `y`. Take `⟨c, d⟩` from `x`. Establish `e0 : (q ++ [(a, b)]) ++ (c, d) :: t = q ++ (a, b) :: (c, d) :: t` using `by simp`.

Rewrite `hl`, `hw`, the goal using `[e0]`. Rewrite using `[wordOp_swap T comm]`. Simplify using `only [LinearMap.sub_apply, LinearMap.add_apply]`. Establish `hwt : wordWt blk (q ++ (a, b) :: (c, d) :: t) = wordWt blk q + ((blk b : ℤ) - blk a + ((blk d : ℤ) - blk c + wordWt blk t))`. Simplify using `only [wordWt_append, wordWt_cons]`.

Establish `hlen : (q ++ (a, b) :: (c, d) :: t).length = q.length + t.length + 2` using `by simp; omega`. Use `Z.sub_mem (Z.add_mem (ih (c, d) ((a, b) :: t) ?_ hx ?_ ?_) ?_) ?_` and prove the remaining obligations. Conclude with `fun r hr => hp r (by simp [hr])`. Rewrite using `[← hl]`. Simplify using the standard rewrite rules.

Rewrite `hw` using `[hwt]`. Simplify using `only [wordWt_append, wordWt_cons]`. Use linear arithmetic over natural numbers and integers. Use `split_ifs with hbc`. Substitute `hbc` using the available equality.

Use `hk _ ?_ ?_` and prove the remaining obligations. Rewrite using `[← hl, hlen]`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite `hw` using `[hwt]`.

Simplify using `only [wordWt_append, wordWt_cons]`. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Use `split_ifs with had`. Substitute `had` using the available equality.

Use `hk _ ?_ ?_` and prove the remaining obligations. Rewrite using `[← hl, hlen]`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite `hw` using `[hwt]`.

Simplify using `only [wordWt_append, wordWt_cons]`. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.
-/
theorem word_inner (comm : ∀ a b c d, T a b * T c d - T c d * T a b =
      (if b = c then T a d else 0) - (if d = a then T c b else 0))
    (stab : ∀ a b, ∀ x ∈ F, T a b x ∈ F)
    (pos : ∀ a b, blk a < blk b → ∀ x ∈ F, T a b x ∈ Z) {f : M} (hf : f ∈ F) (k : ℕ)
    (hk : ∀ w : List (ι × ι), w.length < k → 0 ≤ wordWt blk w → wordOp T w f ∈ Z)
    (p : List (ι × ι)) : ∀ (x : ι × ι) (t : List (ι × ι)), (∀ q ∈ p, ¬ blk q.1 < blk q.2) →
      blk x.1 < blk x.2 → (p ++ x :: t).length = k → 0 ≤ wordWt blk (p ++ x :: t) →
      wordOp T (p ++ x :: t) f ∈ Z := by
  induction p using List.reverseRecOn with
  | nil =>
    intro x t _ hx _ _
    simp only [List.nil_append, wordOp_cons, Module.End.mul_apply]
    exact pos _ _ hx _ (word_stab T F stab _ hf)
  | append_singleton q y ih =>
    intro x t hp hx hl hw
    obtain ⟨a, b⟩ := y
    obtain ⟨c, d⟩ := x
    have e0 : (q ++ [(a, b)]) ++ (c, d) :: t = q ++ (a, b) :: (c, d) :: t := by simp
    rw [e0] at hl hw ⊢
    rw [wordOp_swap T comm]
    simp only [LinearMap.sub_apply, LinearMap.add_apply]
    have hwt : wordWt blk (q ++ (a, b) :: (c, d) :: t) =
        wordWt blk q + ((blk b : ℤ) - blk a + ((blk d : ℤ) - blk c + wordWt blk t)) := by
      simp only [wordWt_append, wordWt_cons]
    have hlen : (q ++ (a, b) :: (c, d) :: t).length = q.length + t.length + 2 := by
      simp; omega
    refine Z.sub_mem (Z.add_mem (ih (c, d) ((a, b) :: t) ?_ hx ?_ ?_) ?_) ?_
    · exact fun r hr => hp r (by simp [hr])
    · rw [← hl]; simp
    · rw [hwt] at hw
      simp only [wordWt_append, wordWt_cons]
      omega
    · split_ifs with hbc
      · subst hbc
        refine hk _ ?_ ?_
        · rw [← hl, hlen]; simp; omega
        · rw [hwt] at hw
          simp only [wordWt_append, wordWt_cons]
          omega
      · simp
    · split_ifs with had
      · subst had
        refine hk _ ?_ ?_
        · rw [← hl, hlen]; simp; omega
        · rw [hwt] at hw
          simp only [wordWt_append, wordWt_cons]
          omega
      · simp

/- English proof (translation)
Proceed by induction on `hk : w.length using Nat.strong_induction_on generalizing w with`. Consider the case `_ k ih`. Break down `word_split blk w with ⟨p, x, t, rfl, hx, hp⟩ | h` into its components or cases. Conclude with `word_inner T blk F Z comm stab pos hf k (fun w' hl hw' => ih _ hl w' hw' rfl) p x t hp hx hk hw`. Conclude with `word_levi T blk Z lev w h hw hz`.
-/
theorem word_mem (comm : ∀ a b c d, T a b * T c d - T c d * T a b =
      (if b = c then T a d else 0) - (if d = a then T c b else 0))
    (stab : ∀ a b, ∀ x ∈ F, T a b x ∈ F)
    (pos : ∀ a b, blk a < blk b → ∀ x ∈ F, T a b x ∈ Z)
    (lev : ∀ a b, blk a = blk b → ∀ x ∈ Z, T a b x ∈ Z) {f : M} (hf : f ∈ F) (hz : f ∈ Z)
    (w : List (ι × ι)) (hw : 0 ≤ wordWt blk w) : wordOp T w f ∈ Z := by
  induction hk : w.length using Nat.strong_induction_on generalizing w with
  | _ k ih =>
    rcases word_split blk w with ⟨p, x, t, rfl, hx, hp⟩ | h
    · exact word_inner T blk F Z comm stab pos hf k (fun w' hl hw' => ih _ hl w' hw' rfl) p x t hp hx hk hw
    · exact word_levi T blk Z lev w h hw hz

end Word

section Power

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
  (T : Fin n → Fin n → Module.End R M) (blk : Fin n → ℕ) (F Z : AddSubgroup M)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `a b p hp`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using `only [Pw, if_true, Module.End.one_apply]`. Conclude with `word_mem T blk F Z comm stab pos lev hf hz p (by omega)`. Simplify using `only [Pw, if_neg hab, LinearMap.zero_apply, map_zero]`. Conclude with `Z.zero_mem`. Consider the case `succ m ih`.

Introduce `a b p hp`. Simplify using `only [Pw, LinearMap.sum_apply, Module.End.mul_apply, map_sum]`. Use `Z.sum_mem fun c _ => ?_` and prove the remaining obligations. Establish `e : wordOp T p (T a c (Pw T m c b f)) = wordOp T (p ++ [(a, c)]) (Pw T m c b f)`. Simplify using `[wordOp_append, wordOp_cons, wordOp_nil]`.

Rewrite using `[e]`. Use `ih c b _ ?_` and prove the remaining obligations. Simplify using `only [wordWt_append, wordWt_cons, wordWt_nil]`. Use linear arithmetic over natural numbers and integers.
-/
theorem word_Pw (comm : ∀ a b c d, T a b * T c d - T c d * T a b =
      (if b = c then T a d else 0) - (if d = a then T c b else 0))
    (stab : ∀ a b, ∀ x ∈ F, T a b x ∈ F)
    (pos : ∀ a b, blk a < blk b → ∀ x ∈ F, T a b x ∈ Z)
    (lev : ∀ a b, blk a = blk b → ∀ x ∈ Z, T a b x ∈ Z) {f : M} (hf : f ∈ F) (hz : f ∈ Z) (m : ℕ) :
    ∀ (a b : Fin n) (p : List (Fin n × Fin n)), 0 ≤ wordWt blk p + ((blk b : ℤ) - blk a) →
      wordOp T p (Pw T m a b f) ∈ Z := by
  induction m with
  | zero =>
    intro a b p hp
    by_cases hab : a = b
    · subst hab
      simp only [Pw, if_true, Module.End.one_apply]
      exact word_mem T blk F Z comm stab pos lev hf hz p (by omega)
    · simp only [Pw, if_neg hab, LinearMap.zero_apply, map_zero]
      exact Z.zero_mem
  | succ m ih =>
    intro a b p hp
    simp only [Pw, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
    refine Z.sum_mem fun c _ => ?_
    have e : wordOp T p (T a c (Pw T m c b f)) = wordOp T (p ++ [(a, c)]) (Pw T m c b f) := by
      simp [wordOp_append, wordOp_cons, wordOp_nil]
    rw [e]
    refine ih c b _ ?_
    simp only [wordWt_append, wordWt_cons, wordWt_nil]
    omega

/- English proof (translation)
Rewrite using `[LinearMap.sum_apply]`. Use `Z.sum_mem fun a _ => ?_` and prove the remaining obligations. Simplify `word_Pw T blk F Z comm stab pos lev hf hz m a a [] (by simp [wordWt_nil])` using `[wordOp_nil]`.
-/
theorem trace_Pw_mem (comm : ∀ a b c d, T a b * T c d - T c d * T a b =
      (if b = c then T a d else 0) - (if d = a then T c b else 0))
    (stab : ∀ a b, ∀ x ∈ F, T a b x ∈ F)
    (pos : ∀ a b, blk a < blk b → ∀ x ∈ F, T a b x ∈ Z)
    (lev : ∀ a b, blk a = blk b → ∀ x ∈ Z, T a b x ∈ Z) {f : M} (hf : f ∈ F) (hz : f ∈ Z) (m : ℕ) :
    (∑ a, Pw T m a a) f ∈ Z := by
  rw [LinearMap.sum_apply]
  refine Z.sum_mem fun a _ => ?_
  simpa [wordOp_nil] using word_Pw T blk F Z comm stab pos lev hf hz m a a [] (by simp [wordWt_nil])

end Power

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/- English proof (translation)
Rewrite using `[← e.fderiv_eq (𝕜 := ℝ)]`. Conclude with `RCalc.fderiv_comp_clm A hd v`.
-/
theorem fderiv_of_left (A : E →L[ℝ] E) {x : E → F} {g : E} (hd : DifferentiableAt ℝ x (A g))
    (e : (fun y => x (A y)) =ᶠ[nhds g] x) (v : E) : fderiv ℝ x g v = fderiv ℝ x (A g) (A v) := by
  rw [← e.fderiv_eq (𝕜 := ℝ)]
  exact RCalc.fderiv_comp_clm A hd v

/- English proof (translation)
Establish `h1 : (fun t : ℝ => x (g + t • v)) =ᶠ[nhds 0] fun _ => x g` using `e`. Rewrite using `[← hd.lineDeriv_eq_fderiv, lineDeriv, h1.deriv_eq]`. Simplify using the standard rewrite rules.
-/
theorem fderiv_of_line {x : E → F} {g : E} (hd : DifferentiableAt ℝ x g) (v : E)
    (e : ∀ᶠ t : ℝ in nhds 0, x (g + t • v) = x g) : fderiv ℝ x g v = 0 := by
  have h1 : (fun t : ℝ => x (g + t • v)) =ᶠ[nhds 0] fun _ => x g := e
  rw [← hd.lineDeriv_eq_fderiv, lineDeriv, h1.deriv_eq]
  simp

end Calculus

section Analysis

open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/- English proof (translation)
Establish `hT : Matrix.BlockTriangular u blk`. Introduce `i j hij`. Establish `hne : i ≠ j` using `by rintro rfl; exact lt_irrefl _ hij`. Use `hu i j (by omega)` as an intermediate fact. Simplify `this` using `[Matrix.sub_apply, Matrix.one_apply_ne hne]`.

Establish `h1 : u.det = 1`. Rewrite using `[hT.det]`. Use `Finset.prod_eq_one fun k _ => ?_` and prove the remaining obligations. Establish `: u.toSquareBlock blk k = 1`. Use extensionality with `i j`.

Establish `h` using `hu i.1 j.1 (by rw [i.2, j.2]; exact lt_irrefl _)`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify `h` using `[Matrix.toSquareBlock_def, sub_eq_zero]`. Establish `hne : i.1 ≠ j.1` using `fun e => hij (Subtype.ext e)`.

Simplify `h` using `[Matrix.toSquareBlock_def, Matrix.one_apply_ne hne, Matrix.one_apply_ne hij]`. Rewrite using `[this, Matrix.det_one]`. Use `show u.det ≠ 0`. Rewrite using `[h1]`. Conclude with `one_ne_zero`.
-/
theorem nil_mem_GLs (blk : Fin n → ℕ) {u : Mat n} (hu : ∀ a b, ¬ blk a < blk b → (u - 1) a b = 0) : u ∈ GLs n := by
  have hT : Matrix.BlockTriangular u blk := by
    intro i j hij
    have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
    have := hu i j (by omega)
    simpa [Matrix.sub_apply, Matrix.one_apply_ne hne] using this
  have h1 : u.det = 1 := by
    rw [hT.det]
    refine Finset.prod_eq_one fun k _ => ?_
    have : u.toSquareBlock blk k = 1 := by
      ext i j
      have h := hu i.1 j.1 (by rw [i.2, j.2]; exact lt_irrefl _)
      by_cases hij : i = j
      · subst hij
        simpa [Matrix.toSquareBlock_def, sub_eq_zero] using h
      · have hne : i.1 ≠ j.1 := fun e => hij (Subtype.ext e)
        simpa [Matrix.toSquareBlock_def, Matrix.one_apply_ne hne, Matrix.one_apply_ne hij] using h
    rw [this, Matrix.det_one]
  show u.det ≠ 0
  rw [h1]; exact one_ne_zero

/- English proof (translation)
Use `set D : Mat n := diagonal fun a => (blk a : ℂ) with hD`. Establish `hc : g * D = D * g`. Use extensionality with `a b`. Simplify using `only [hD, mul_diagonal, diagonal_mul]`. Distinguish the cases in `h : blk a = blk b`.

Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hb a b h]`. Simplify using the standard rewrite rules. Establish `hu : IsUnit g.det` using `isUnit_iff_ne_zero.2 hg`.

Establish `h1 : g * g⁻¹ = 1` using `mul_nonsing_inv g hu`. Establish `h2 : g⁻¹ * g = 1` using `nonsing_inv_mul g hu`. Establish `hc' : g⁻¹ * D = D * g⁻¹`. Combine the equalities or inequalities in the displayed calculation. Introduce `a b hab`.

Establish `h3` using `congrFun (congrFun hc' a) b`. Simplify using `only [hD, mul_diagonal, diagonal_mul] at h3`. Establish `hne : (blk b : ℂ) - blk a ≠ 0`. Rewrite using `[sub_ne_zero]`. Conclude with `Nat.cast_injective.ne hab.symm`.

Establish `h4 : g⁻¹ a b * ((blk b : ℂ) - blk a) = 0` using `by linear_combination h3`. Conclude with `(mul_eq_zero.1 h4).resolve_right hne`.
-/
theorem inv_block (blk : Fin n → ℕ) {g : Mat n} (hg : g ∈ GLs n) (hb : ∀ a b, blk a ≠ blk b → g a b = 0) :
    ∀ a b, blk a ≠ blk b → g⁻¹ a b = 0 := by
  set D : Mat n := diagonal fun a => (blk a : ℂ) with hD
  have hc : g * D = D * g := by
    ext a b
    simp only [hD, mul_diagonal, diagonal_mul]
    by_cases h : blk a = blk b
    · rw [h]; ring
    · rw [hb a b h]; simp
  have hu : IsUnit g.det := isUnit_iff_ne_zero.2 hg
  have h1 : g * g⁻¹ = 1 := mul_nonsing_inv g hu
  have h2 : g⁻¹ * g = 1 := nonsing_inv_mul g hu
  have hc' : g⁻¹ * D = D * g⁻¹ := by
    calc g⁻¹ * D = g⁻¹ * D * (g * g⁻¹) := by rw [h1, mul_one]
      _ = g⁻¹ * (D * g) * g⁻¹ := by simp only [mul_assoc]
      _ = g⁻¹ * (g * D) * g⁻¹ := by rw [hc]
      _ = D * g⁻¹ := by rw [← mul_assoc g⁻¹ g D, h2, one_mul]
  intro a b hab
  have h3 := congrFun (congrFun hc' a) b
  simp only [hD, mul_diagonal, diagonal_mul] at h3
  have hne : (blk b : ℂ) - blk a ≠ 0 := by
    rw [sub_ne_zero]
    exact Nat.cast_injective.ne hab.symm
  have h4 : g⁻¹ a b * ((blk b : ℂ) - blk a) = 0 := by linear_combination h3
  exact (mul_eq_zero.1 h4).resolve_right hne

/- English proof (translation)
Establish `hd : DifferentiableAt ℝ x (RCalc.mulL u g)` using `RCalc.differentiableAt_of_smooth hx (RCalc.mul_mem_GLs hu hg)`. Establish `e : (fun y => x (RCalc.mulL u y)) =ᶠ[nhds g] x` using `Filter.eventuallyEq_of_mem (RCalc.isOpen_GLs.mem_nhds hg) fun y hy => hinv y hy`. Establish `h` using `fderiv_of_left (RCalc.mulL u) hd e (g * X)`. Establish `e2 : u * g * X = RCalc.mulL u (g * X)` using `mul_assoc u g X`. Use `show fderiv ℝ x (u * g) (u * g * X) = fderiv ℝ x g (g * X)`.

Rewrite using `[e2]`. Conclude with `h.symm`.
-/
theorem Rd_left {x : Mat n → V} (hx : ContDiffOn ℝ ∞ x (GLs n)) {u : Mat n} (hu : u ∈ GLs n)
    (hinv : ∀ g ∈ GLs n, x (u * g) = x g) (X : Mat n) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X x (u * g) = Rd X x g := by
  have hd : DifferentiableAt ℝ x (RCalc.mulL u g) := RCalc.differentiableAt_of_smooth hx (RCalc.mul_mem_GLs hu hg)
  have e : (fun y => x (RCalc.mulL u y)) =ᶠ[nhds g] x :=
    Filter.eventuallyEq_of_mem (RCalc.isOpen_GLs.mem_nhds hg) fun y hy => hinv y hy
  have h := fderiv_of_left (RCalc.mulL u) hd e (g * X)
  have e2 : u * g * X = RCalc.mulL u (g * X) := mul_assoc u g X
  show fderiv ℝ x (u * g) (u * g * X) = fderiv ℝ x g (g * X)
  rw [e2]
  exact h.symm

/- English proof (translation)
Establish `hu : IsUnit g.det` using `isUnit_iff_ne_zero.2 hg`. Use `set Y : Mat n := g * X * g⁻¹ with hYd`. Establish `hY : ∀ a b, ¬ blk a < blk b → Y a b = 0`. Introduce `a b hab`. Simplify using `only [hYd, Matrix.mul_apply]`.

Use `Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Distinguish the cases in `hd : blk d = blk b`. Establish `h0 : (∑ c, g a c * X c d) = 0`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : blk a = blk c`.

Rewrite using `[hX c d (by rw [← hc, hd]; exact hab)]; simp`. Rewrite using `[hb a c hc]`. Simplify using the standard rewrite rules. Rewrite using `[h0]`. Simplify using the standard rewrite rules.

Rewrite using `[inv_block blk hg hb d b hd]`. Simplify using the standard rewrite rules. Establish `hYg : Y * g = g * X`. Rewrite using `[hYd, mul_assoc, nonsing_inv_mul g hu, mul_one]`. Establish `hc : ∀ t : ℝ, x (g + t • (g * X)) = x g`.

Introduce `t`. Establish `e : g + t • (g * X) = (1 + t • Y) * g`. Rewrite using `[add_mul, one_mul, smul_mul_assoc, hYg]`. Rewrite using `[e]`. Use `hinv _ (fun a b hab => ?_) g hg` and prove the remaining obligations.

Simplify using `[hY a b hab]`. Conclude with `fderiv_of_line (RCalc.differentiableAt_of_smooth hx hg) (g * X) (Filter.Eventually.of_forall hc)`.
-/
theorem Rd_nil (blk : Fin n → ℕ) {x : Mat n → V} (hx : ContDiffOn ℝ ∞ x (GLs n))
    (hinv : ∀ u : Mat n, (∀ a b, ¬ blk a < blk b → (u - 1) a b = 0) → ∀ g ∈ GLs n, x (u * g) = x g)
    {g : Mat n} (hg : g ∈ GLs n) (hb : ∀ a b, blk a ≠ blk b → g a b = 0) {X : Mat n}
    (hX : ∀ a b, ¬ blk a < blk b → X a b = 0) : Rd X x g = 0 := by
  have hu : IsUnit g.det := isUnit_iff_ne_zero.2 hg
  set Y : Mat n := g * X * g⁻¹ with hYd
  have hY : ∀ a b, ¬ blk a < blk b → Y a b = 0 := by
    intro a b hab
    simp only [hYd, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun d _ => ?_
    by_cases hd : blk d = blk b
    · have h0 : (∑ c, g a c * X c d) = 0 := by
        refine Finset.sum_eq_zero fun c _ => ?_
        by_cases hc : blk a = blk c
        · rw [hX c d (by rw [← hc, hd]; exact hab)]; simp
        · rw [hb a c hc]; simp
      rw [h0]; simp
    · rw [inv_block blk hg hb d b hd]; simp
  have hYg : Y * g = g * X := by
    rw [hYd, mul_assoc, nonsing_inv_mul g hu, mul_one]
  have hc : ∀ t : ℝ, x (g + t • (g * X)) = x g := by
    intro t
    have e : g + t • (g * X) = (1 + t • Y) * g := by
      rw [add_mul, one_mul, smul_mul_assoc, hYg]
    rw [e]
    refine hinv _ (fun a b hab => ?_) g hg
    simp [hY a b hab]
  exact fderiv_of_line (RCalc.differentiableAt_of_smooth hx hg) (g * X) (Filter.Eventually.of_forall hc)

/- English proof (translation)
Establish `hev : ∀ᶠ t : ℝ in nhds 0, x (g + t • (g * X)) = x g`. Establish `hc : Continuous fun t : ℝ => g + t • (g * X)` using `by fun_prop`. Establish `hm : (fun t : ℝ => g + t • (g * X)) ⁻¹' GLs n ∈ nhds (0 : ℝ)` using `hc.continuousAt.preimage_mem_nhds (by simpa using RCalc.isOpen_GLs.mem_nhds hg)`. Use `filter_upwards [hm] with t ht`. Rewrite using `[hz g hg hb]`.

Use `hz _ ht fun a b hab => ?_` and prove the remaining obligations. Establish `hgX : (g * X) a b = 0`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : blk a = blk c`.

Rewrite using `[hX c b (by rwa [← hc])]; simp`. Rewrite using `[hb a c hc]`. Simplify using the standard rewrite rules. Simplify using `[hb a b hab, hgX]`. Conclude with `fderiv_of_line (RCalc.differentiableAt_of_smooth hx hg) (g * X) hev`.
-/
theorem Rd_levi (blk : Fin n → ℕ) {x : Mat n → V} (hx : ContDiffOn ℝ ∞ x (GLs n))
    (hz : ∀ g ∈ GLs n, (∀ a b, blk a ≠ blk b → g a b = 0) → x g = 0)
    {g : Mat n} (hg : g ∈ GLs n) (hb : ∀ a b, blk a ≠ blk b → g a b = 0) {X : Mat n}
    (hX : ∀ a b, blk a ≠ blk b → X a b = 0) : Rd X x g = 0 := by
  have hev : ∀ᶠ t : ℝ in nhds 0, x (g + t • (g * X)) = x g := by
    have hc : Continuous fun t : ℝ => g + t • (g * X) := by fun_prop
    have hm : (fun t : ℝ => g + t • (g * X)) ⁻¹' GLs n ∈ nhds (0 : ℝ) :=
      hc.continuousAt.preimage_mem_nhds (by simpa using RCalc.isOpen_GLs.mem_nhds hg)
    filter_upwards [hm] with t ht
    rw [hz g hg hb]
    refine hz _ ht fun a b hab => ?_
    have hgX : (g * X) a b = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : blk a = blk c
      · rw [hX c b (by rwa [← hc])]; simp
      · rw [hb a c hc]; simp
    simp [hb a b hab, hgX]
  exact fderiv_of_line (RCalc.differentiableAt_of_smooth hx hg) (g * X) hev

def nilF (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (blk : Fin n → ℕ) : AddSubgroup (RCalc.Sm n V) where
  carrier := {x | ∀ u : Mat n, (∀ a b, ¬ blk a < blk b → (u - 1) a b = 0) → ∀ g ∈ GLs n, x.1 (u * g) = x.1 g}
  add_mem' := fun {x y} hx hy u hu g hg => by
    show x.1 (u * g) + y.1 (u * g) = x.1 g + y.1 g
    rw [hx u hu g hg, hy u hu g hg]
  zero_mem' := fun _ _ _ _ => rfl
  neg_mem' := fun {x} hx u hu g hg => by
    show -x.1 (u * g) = -x.1 g
    rw [hx u hu g hg]

def levZ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (blk : Fin n → ℕ) : AddSubgroup (RCalc.Sm n V) where
  carrier := {x | ∀ g ∈ GLs n, (∀ a b, blk a ≠ blk b → g a b = 0) → x.1 g = 0}
  add_mem' := fun {x y} hx hy g hg hb => by
    show x.1 g + y.1 g = 0
    rw [hx g hg hb, hy g hg hb, add_zero]
  zero_mem' := fun _ _ _ => rfl
  neg_mem' := fun {x} hx g hg hb => by
    show -x.1 g = 0
    rw [hx g hg hb, neg_zero]

/- English proof (translation)
Simplify using `only [Eu, Pi.smul_apply, Pi.add_apply, h1, h2, smul_zero, add_zero]`.
-/
theorem Eu_eq_zero {f : Mat n → V} {g : Mat n} (s : Bool) (a b : Fin n) (h1 : Rd (Matrix.single a b 1) f g = 0)
    (h2 : Rd (Matrix.single a b Complex.I) f g = 0) : Eu s a b f g = 0 := by
  simp only [Eu, Pi.smul_apply, Pi.add_apply, h1, h2, smul_zero, add_zero]

/- English proof (translation)
Introduce `x hx u hu g hg`. Establish `hu'` using `nil_mem_GLs blk hu`. Rewrite using `[RCalc.Tc_apply _ _ _ _ (RCalc.mul_mem_GLs hu' hg), RCalc.Tc_apply _ _ _ _ hg]`. Simplify using `only [Eu, Pi.smul_apply, Pi.add_apply]`. Rewrite using `[Rd_left x.2.1 hu' (hx u hu) _ hg, Rd_left x.2.1 hu' (hx u hu) _ hg]`.
-/
theorem Tc_stab (blk : Fin n → ℕ) (s : Bool) (a b : Fin n) :
    ∀ x ∈ nilF V blk, RCalc.Tc (RCalc.DA n V) s a b x ∈ nilF V blk := by
  intro x hx u hu g hg
  have hu' := nil_mem_GLs blk hu
  rw [RCalc.Tc_apply _ _ _ _ (RCalc.mul_mem_GLs hu' hg), RCalc.Tc_apply _ _ _ _ hg]
  simp only [Eu, Pi.smul_apply, Pi.add_apply]
  rw [Rd_left x.2.1 hu' (hx u hu) _ hg, Rd_left x.2.1 hu' (hx u hu) _ hg]

/- English proof (translation)
Introduce `x hx g hg hb`. Rewrite using `[RCalc.Tc_apply _ _ _ _ hg]`. Establish `hs : ∀ z : ℂ, ∀ c d, ¬ blk c < blk d → (Matrix.single a b z : Mat n) c d = 0`. Introduce `z c d hcd`. Rewrite using `[Matrix.single_apply, if_neg]`.

Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hcd hab`. Conclude with `Eu_eq_zero s a b (Rd_nil blk x.2.1 hx hg hb (hs _)) (Rd_nil blk x.2.1 hx hg hb (hs _))`.
-/
theorem Tc_pos (blk : Fin n → ℕ) (s : Bool) (a b : Fin n) (hab : blk a < blk b) :
    ∀ x ∈ nilF V blk, RCalc.Tc (RCalc.DA n V) s a b x ∈ levZ V blk := by
  intro x hx g hg hb
  rw [RCalc.Tc_apply _ _ _ _ hg]
  have hs : ∀ z : ℂ, ∀ c d, ¬ blk c < blk d → (Matrix.single a b z : Mat n) c d = 0 := by
    intro z c d hcd
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hcd hab
  exact Eu_eq_zero s a b (Rd_nil blk x.2.1 hx hg hb (hs _)) (Rd_nil blk x.2.1 hx hg hb (hs _))

/- English proof (translation)
Introduce `x hx g hg hb`. Rewrite using `[RCalc.Tc_apply _ _ _ _ hg]`. Establish `hs : ∀ z : ℂ, ∀ c d, blk c ≠ blk d → (Matrix.single a b z : Mat n) c d = 0`. Introduce `z c d hcd`. Rewrite using `[Matrix.single_apply, if_neg]`.

Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hcd hab`. Conclude with `Eu_eq_zero s a b (Rd_levi blk x.2.1 hx hg hb (hs _)) (Rd_levi blk x.2.1 hx hg hb (hs _))`.
-/
theorem Tc_lev (blk : Fin n → ℕ) (s : Bool) (a b : Fin n) (hab : blk a = blk b) :
    ∀ x ∈ levZ V blk, RCalc.Tc (RCalc.DA n V) s a b x ∈ levZ V blk := by
  intro x hx g hg hb
  rw [RCalc.Tc_apply _ _ _ _ hg]
  have hs : ∀ z : ℂ, ∀ c d, blk c ≠ blk d → (Matrix.single a b z : Mat n) c d = 0 := by
    intro z c d hcd
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hcd hab
  exact Eu_eq_zero s a b (Rd_levi blk x.2.1 hx hg hb (hs _)) (Rd_levi blk x.2.1 hx hg hb (hs _))

/- English proof (translation)
Introduce `n V _ _ blk f hf hinv hvan s m g hg hb`. Establish `hF : RCalc.res hf ∈ nilF V blk`. Introduce `u hu y hy`. Rewrite using `[RCalc.res_apply hf (RCalc.mul_mem_GLs (nil_mem_GLs blk hu) hy), RCalc.res_apply hf hy]`. Conclude with `hinv u hu y hy`.

Establish `hZ : RCalc.res hf ∈ levZ V blk`. Introduce `y hy hyb`. Rewrite using `[RCalc.res_apply hf hy]`. Conclude with `hvan y hy hyb`. Establish `key` using `trace_Pw_mem (RCalc.Tc (RCalc.DA n V) s) blk (nilF V blk) (levZ V blk) (RCalc.Tc_bracket RCalc.DA_bracket s) (Tc_stab blk s) (fun a b h => Tc_pos blk s a b h) (fun a b h => Tc_lev blk s a b h) hF hZ m`.

Rewrite using `[RCalc.gel_eq s m hf hg]`. Conclude with `key g hg hb`.
-/
theorem gelN : GelN := by
  intro n V _ _ blk f hf hinv hvan s m g hg hb
  have hF : RCalc.res hf ∈ nilF V blk := by
    intro u hu y hy
    rw [RCalc.res_apply hf (RCalc.mul_mem_GLs (nil_mem_GLs blk hu) hy), RCalc.res_apply hf hy]
    exact hinv u hu y hy
  have hZ : RCalc.res hf ∈ levZ V blk := by
    intro y hy hyb
    rw [RCalc.res_apply hf hy]
    exact hvan y hy hyb
  have key := trace_Pw_mem (RCalc.Tc (RCalc.DA n V) s) blk (nilF V blk) (levZ V blk)
    (RCalc.Tc_bracket RCalc.DA_bracket s) (Tc_stab blk s) (fun a b h => Tc_pos blk s a b h)
    (fun a b h => Tc_lev blk s a b h) hF hZ m
  rw [RCalc.gel_eq s m hf hg]
  exact key g hg hb

end Analysis

end GlobalTheory.CompanionTheory.GelLevi
