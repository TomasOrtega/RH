import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfCauchySchwarz
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockEstimatesSumForm

open Finset NumberField
open scoped ComplexConjugate ComplexOrder

namespace Formalism.FourierDecayAlt.P.PBA

open Formalism.FourierDecayAlt

noncomputable section

section pull

/- English proof (translation)
Unfold `TB.PSDOn at hH ⊢`. Conclude with `hH.submatrix (fun x : Y => (⟨g x, hg x x.2⟩ : P))`.
-/
theorem psd_comp {Z X : Type} (P : Finset Z) (H : Z → Z → ℂ) (hH : TB.PSDOn P H) (Y : Finset X) (g : X → Z)
    (hg : ∀ h ∈ Y, g h ∈ P) : TB.PSDOn Y (fun x y => H (g x) (g y)) := by
  unfold TB.PSDOn at hH ⊢
  exact hH.submatrix (fun x : Y => (⟨g x, hg x x.2⟩ : P))

/- English proof (translation)
Establish `h1` using `psd_comp P H hH (Y.disjSum Y) (Sum.elim f g) (by`. Introduce and unpack `(x|x) hx`. Simplify `hx)` using `using hf x (by simpa`. Simplify `hx))` using `using hg x (by simpa`. Establish `hherm` using `((PBA.psd_iff_qf P H).1 hH).1`.

Unfold `KB.BlockPSD`. Unfold `TB.PSDOn at h1 ⊢`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `⟨i, hi⟩ ⟨j, hj⟩`. Apply the tactic sequence `rcases i with x | x <;> rcases j with y | y`.

Both sides reduce to the same expression. Both sides reduce to the same expression. Conclude with `(hherm (f y) (hf y (by simpa using hj)) (g x) (hg x (by simpa using hi))).symm`. Both sides reduce to the same expression.
-/
theorem blockPSD_pull {Z X : Type} (P : Finset Z) (H : Z → Z → ℂ) (hH : TB.PSDOn P H) (Y : Finset X)
    (f g : X → Z) (hf : ∀ h ∈ Y, f h ∈ P) (hg : ∀ h ∈ Y, g h ∈ P) :
    KB.BlockPSD Y Y (fun h h' => H (f h) (f h')) (fun h h' => H (f h) (g h')) (fun h h' => H (g h) (g h')) := by
  have h1 := psd_comp P H hH (Y.disjSum Y) (Sum.elim f g) (by
    rintro (x|x) hx
    · simpa using hf x (by simpa using hx)
    · simpa using hg x (by simpa using hx))
  have hherm := ((PBA.psd_iff_qf P H).1 hH).1
  unfold KB.BlockPSD
  unfold TB.PSDOn at h1 ⊢
  convert h1 using 1
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rcases i with x | x <;> rcases j with y | y
  · rfl
  · rfl
  · exact (hherm (f y) (hf y (by simpa using hj)) (g x) (hg x (by simpa using hi))).symm
  · rfl

/- English proof (translation)
Unfold `KB.BlockPSD at h`. Establish `h1` using `psd_comp _ _ h (Y.disjSum Y) (Sum.map l l) (by`. Introduce and unpack `(x|x) hx`. Simplify `hx)` using `using hl x (by simpa`. Simplify `hx))` using `using hl x (by simpa`.

Unfold `KB.BlockPSD`. Unfold `TB.PSDOn at h1 ⊢`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `⟨i, hi⟩ ⟨j, hj⟩`. Apply the tactic sequence `rcases i with x | x <;> rcases j with y | y <;> rfl`.
-/
theorem blockPSD_comp {α X : Type} (Y₀ : Finset α) (a w b : α → α → ℂ) (h : KB.BlockPSD Y₀ Y₀ a w b)
    (Y : Finset X) (l : X → α) (hl : ∀ x ∈ Y, l x ∈ Y₀) :
    KB.BlockPSD Y Y (fun x y => a (l x) (l y)) (fun x y => w (l x) (l y)) (fun x y => b (l x) (l y)) := by
  unfold KB.BlockPSD at h
  have h1 := psd_comp _ _ h (Y.disjSum Y) (Sum.map l l) (by
    rintro (x|x) hx
    · simpa using hl x (by simpa using hx)
    · simpa using hl x (by simpa using hx))
  unfold KB.BlockPSD
  unfold TB.PSDOn at h1 ⊢
  convert h1 using 1
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rcases i with x | x <;> rcases j with y | y <;> rfl

end pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)

section words

/- English proof (translation)
Unfold `C.Word.cnt`. Conclude with `Finset.le_sup (f := fun v => (w v).length) (Finset.mem_univ v)`.
-/
theorem len_le_cnt (w : C.Word S.f) (v : Fin S.f) : (w v).length ≤ w.cnt := by
  unfold C.Word.cnt
  exact Finset.le_sup (f := fun v => (w v).length) (Finset.mem_univ v)

/- English proof (translation)
Unfold `C.Word.cnt`. Conclude with `Finset.sup_le fun v _ => h v`.
-/
theorem cnt_le {w : C.Word S.f} {n : ℕ} (h : ∀ v, (w v).length ≤ n) : w.cnt ≤ n := by
  unfold C.Word.cnt
  exact Finset.sup_le fun v _ => h v

/- English proof (translation)
Unfold `C.HidaSetting.admitted`. Use `⟨fun v => ?_, fun v => ?_⟩` and prove the remaining obligations. Take `⟨w0, hw⟩` from `h v`. Establish `hA : S.admitted w0.1` using `And.left w0.2`. Establish `hA1` using `(And.left hA) v`.

Rewrite `hA1` using `[hw]`. Conclude with `hA1`. Take `⟨w0, hw⟩` from `h v`. Establish `hA : S.admitted w0.1` using `And.left w0.2`. Establish `hA2` using `(And.right hA) v`.

Rewrite `hA2` using `[hw]`. Conclude with `hA2`.
-/
theorem admissible_of_places {g : C.Word S.f} (h : ∀ v, ∃ w0 : S.W, w0.1 v = g v) : S.admitted g := by
  unfold C.HidaSetting.admitted
  refine ⟨fun v => ?_, fun v => ?_⟩
  · obtain ⟨w0, hw⟩ := h v
    have hA : S.admitted w0.1 := And.left w0.2
    have hA1 := (And.left hA) v
    rw [hw] at hA1
    exact hA1
  · obtain ⟨w0, hw⟩ := h v
    have hA : S.admitted w0.1 := And.left w0.2
    have hA2 := (And.right hA) v
    rw [hw] at hA2
    exact hA2

/- English proof (translation)
Unfold `C.listsUpTo`. Rewrite using `[Finset.mem_biUnion]`. Use `⟨L.length, Finset.mem_range.mpr (Nat.lt_succ_of_le hl), ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_image]`. Use `⟨fun i => L.get i, ?_, List.ofFn_get L⟩` and prove the remaining obligations.

Rewrite using `[Fintype.mem_piFinset]`. Introduce `i`. Rewrite using `[Finset.mem_product]`. Conclude with `⟨Finset.mem_univ _, hT _ (List.mem_iff_get.mpr ⟨i, rfl⟩)⟩`.
-/
theorem mem_listsUpTo {T : Finset ℝ} {n : ℕ} (L : List C.Letter) (hl : L.length ≤ n)
    (hT : ∀ x ∈ L, x.2 ∈ T) : L ∈ C.listsUpTo T n := by
  unfold C.listsUpTo
  rw [Finset.mem_biUnion]
  refine ⟨L.length, Finset.mem_range.mpr (Nat.lt_succ_of_le hl), ?_⟩
  rw [Finset.mem_image]
  refine ⟨fun i => L.get i, ?_, List.ofFn_get L⟩
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_product]
  exact ⟨Finset.mem_univ _, hT _ (List.mem_iff_get.mpr ⟨i, rfl⟩)⟩

/- English proof (translation)
Establish `hA : S.admitted w0.1` using `And.left w0.2`. Establish `hc : w0.1.cnt ≤ S.Ntop` using `And.right w0.2`. Unfold `C.wall`. Rewrite using `[Fintype.mem_piFinset]`. Introduce `v`.

Use `mem_listsUpTo (w0.1 v) ((len_le_cnt S w0.1 v).trans hc) ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨j, hj, rfl⟩` from `List.getElem_of_mem hx`. Establish `h1` using `(And.left hA) v j hj`. Establish `hlen : (w0.1 v).length - j < S.Ntop + 1`.

Use `(len_le_cnt S w0.1 v).trans hc` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hnode : ∀ y, y ∈ S.grid v ((w0.1 v).length - j) ∪ S.grid1 v → y ∈ S.nodes v`. Introduce `y hy`. Unfold `C.HidaSetting.nodes`.

Rewrite `hy`, the goal using `[Finset.mem_union]`. Break down `hy with hy | hy` into its components or cases. Use `left`. Conclude with `Finset.mem_biUnion.mpr ⟨_, Finset.mem_range.mpr hlen, hy⟩`. Use `right`.

Conclude with `hy`. Unfold `C.HidaSetting.pts`. Rewrite using `[Finset.mem_union]`. Distinguish the cases in `hb : ((w0.1 v)[j]'hj).1 = true`. Use `left`.

Rewrite `h1` using `[if_pos hb]`. Conclude with `hnode _ h1`. Use `right`. Rewrite `h1` using `[if_neg hb]`. Conclude with `Finset.mem_image.mpr ⟨_, hnode _ h1, by ring⟩`.
-/
theorem W_mem_wall (w0 : S.W) : w0.1 ∈ C.wall S.pts S.Ntop := by
  have hA : S.admitted w0.1 := And.left w0.2
  have hc : w0.1.cnt ≤ S.Ntop := And.right w0.2
  unfold C.wall
  rw [Fintype.mem_piFinset]
  intro v
  refine mem_listsUpTo (w0.1 v) ((len_le_cnt S w0.1 v).trans hc) ?_
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have h1 := (And.left hA) v j hj
  have hlen : (w0.1 v).length - j < S.Ntop + 1 := by
    have := (len_le_cnt S w0.1 v).trans hc
    omega
  have hnode : ∀ y, y ∈ S.grid v ((w0.1 v).length - j) ∪ S.grid1 v → y ∈ S.nodes v := by
    intro y hy
    unfold C.HidaSetting.nodes
    rw [Finset.mem_union] at hy ⊢
    rcases hy with hy | hy
    · left
      exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_range.mpr hlen, hy⟩
    · right
      exact hy
  unfold C.HidaSetting.pts
  rw [Finset.mem_union]
  by_cases hb : ((w0.1 v)[j]'hj).1 = true
  · left
    rw [if_pos hb] at h1
    exact hnode _ h1
  · right
    rw [if_neg hb] at h1
    exact Finset.mem_image.mpr ⟨_, hnode _ h1, by ring⟩

open Classical in
/- English proof (translation)
Unfold `C.HidaSetting.base C.HidaSetting.mkData`. Simplify using `only`. Rewrite using `[Finset.mem_subtype]`. Conclude with `W_mem_wall S w0`.
-/
theorem W_mem_Wall (w0 : S.W) : w0 ∈ S.base.Wall := by
  unfold C.HidaSetting.base C.HidaSetting.mkData
  dsimp only
  rw [Finset.mem_subtype]
  exact W_mem_wall S w0

/- English proof (translation)
Unfold `TB.Data.Wb`. Rewrite using `[Finset.mem_filter]`. Conclude with `⟨W_mem_Wall S w0, h⟩`.
-/
theorem mem_Wb {w0 : S.W} {n : ℕ} (h : w0.1.cnt ≤ n) : w0 ∈ S.base.Wb n := by
  unfold TB.Data.Wb
  rw [Finset.mem_filter]
  exact ⟨W_mem_Wall S w0, h⟩

def pw (A : Finset (Fin S.f)) (w : S.W) (θ : Fin S.f → List C.Letter → ℝ) (v : Fin S.f) (a : List C.Letter) : ℝ :=
  if v ∈ A then θ v a else if a = w.1 v then 1 else 0

def pθ (A : Finset (Fin S.f)) (w : S.W) (θ : Fin S.f → List C.Letter → ℝ) (w' : S.W) : ℝ :=
  ∏ v, pw S A w θ v (w'.1 v)

def supp (A : Finset (Fin S.f)) (w : S.W) (U : Fin S.f → Finset (List C.Letter)) (v : Fin S.f) :
    Finset (List C.Letter) :=
  if v ∈ A then U v else {w.1 v}

variable {S}

section hyps

variable {A : Finset (Fin S.f)} {w : S.W} {n : ℕ} {U : Fin S.f → Finset (List C.Letter)}
  {θ : Fin S.f → List C.Letter → ℝ}

/- English proof (translation)
Unfold `pw at h`. Unfold `supp`. Use `split_ifs at h ⊢ with h1 h2`. Assume the negation of the conclusion as `ha`. Conclude with `h ((hP v h1).2.1 a ha)`.

Simplify using `[h2]`. Conclude with `absurd rfl h`.
-/
theorem pw_ne_zero (hP : ∀ v ∈ A, TB.IsProb (U v) (θ v)) {v : Fin S.f} {a : List C.Letter}
    (h : pw S A w θ v a ≠ 0) : a ∈ supp S A w U v := by
  unfold pw at h
  unfold supp
  split_ifs at h ⊢ with h1 h2
  · by_contra ha
    exact h ((hP v h1).2.1 a ha)
  · simp [h2]
  · exact absurd rfl h

/- English proof (translation)
Unfold `pw`. Use `split_ifs with h1 h2`. Conclude with `(hP v h1).1 a`. Conclude with `zero_le_one`. Conclude with `le_refl 0`.
-/
theorem pw_nonneg (hP : ∀ v ∈ A, TB.IsProb (U v) (θ v)) (v : Fin S.f) (a : List C.Letter) :
    0 ≤ pw S A w θ v a := by
  unfold pw
  split_ifs with h1 h2
  · exact (hP v h1).1 a
  · exact zero_le_one
  · exact le_refl 0

/- English proof (translation)
Rewrite `hg` using `[Fintype.mem_piFinset]`. Establish `hv : ∀ v, D.AdmAt S v (g v) ∧ (g v).length ≤ n`. Introduce `v`. Establish `hgv` using `hg v`. Unfold `supp at hgv`.

Use `split_ifs at hgv with hA`. Conclude with `hU v hA (g v) hgv`. Rewrite `hgv` using `[Finset.mem_singleton]`. Rewrite using `[hgv]`. Conclude with `⟨Exists.intro w rfl, (len_le_cnt S w.1 v).trans hw⟩`.

Establish `hc : g.cnt ≤ n` using `cnt_le S (fun v => (hv v).2)`. Conclude with `⟨And.intro (admissible_of_places S (fun v => (hv v).1)) (hc.trans hn), hc⟩`.
-/
theorem supp_word (hU : ∀ v ∈ A, ∀ a ∈ U v, D.AdmAt S v a ∧ a.length ≤ n) (hw : w.1.cnt ≤ n) (hn : n ≤ S.Ntop)
    {g : C.Word S.f} (hg : g ∈ Fintype.piFinset (supp S A w U)) : S.AdmN g ∧ g.cnt ≤ n := by
  rw [Fintype.mem_piFinset] at hg
  have hv : ∀ v, D.AdmAt S v (g v) ∧ (g v).length ≤ n := by
    intro v
    have hgv := hg v
    unfold supp at hgv
    split_ifs at hgv with hA
    · exact hU v hA (g v) hgv
    · rw [Finset.mem_singleton] at hgv
      rw [hgv]
      exact ⟨Exists.intro w rfl, (len_le_cnt S w.1 v).trans hw⟩
  have hc : g.cnt ≤ n := cnt_le S (fun v => (hv v).2)
  exact ⟨And.intro (admissible_of_places S (fun v => (hv v).1)) (hc.trans hn), hc⟩

/- English proof (translation)
Establish `e1 : ∀ v, (if v ∈ A then ∑ a ∈ U v, (θ v a : ℂ) * F v a else F v (w.1 v)) = ∑ a ∈ supp S A w U v, (pw S A w θ v a : ℂ) * F v a`. Introduce `v`. Unfold `supp pw`. Distinguish the cases in `hv : v ∈ A`. Simplify using `only [if_pos hv]`.

Simplify using `[hv]`. Simplify using `only [e1]`. Rewrite using `[Finset.prod_univ_sum]`. Establish `e2 : ∀ w' : S.W, (pθ S A w θ w' : ℂ) * ∏ v, F v (w'.1 v) = ∏ v, (pw S A w θ v (w'.1 v) : ℂ) * F v (w'.1 v)`. Introduce `w'`.

Unfold `pθ`. Use `push_cast`. Rewrite using `[← Finset.prod_mul_distrib]`. Simplify using `only [e2]`. Use `Finset.sum_bij_ne_zero (fun w' _ _ => w'.1) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `w' _ h`. Rewrite using `[Fintype.mem_piFinset]`. Introduce `v`. Use `pw_ne_zero hP fun h0 => h ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ v) (by rw [h0]; simp)]`.

Introduce `a _ _ b _ _ h`. Conclude with `Subtype.ext h`. Introduce `g hg h0`. Take `⟨hadm, hcnt⟩` from `supp_word hU hw hn hg`. Conclude with `⟨⟨g, hadm⟩, mem_Wb S hcnt, h0, rfl⟩`.

Introduce `w' _ _`. Both sides reduce to the same expression.
-/
theorem expand (hP : ∀ v ∈ A, TB.IsProb (U v) (θ v))
    (hU : ∀ v ∈ A, ∀ a ∈ U v, D.AdmAt S v a ∧ a.length ≤ n) (hw : w.1.cnt ≤ n) (hn : n ≤ S.Ntop)
    (F : Fin S.f → List C.Letter → ℂ) :
    ∑ w' ∈ S.base.Wb n, (pθ S A w θ w' : ℂ) * ∏ v, F v (w'.1 v) =
      ∏ v, (if v ∈ A then ∑ a ∈ U v, (θ v a : ℂ) * F v a else F v (w.1 v)) := by
  classical
  have e1 : ∀ v, (if v ∈ A then ∑ a ∈ U v, (θ v a : ℂ) * F v a else F v (w.1 v)) =
      ∑ a ∈ supp S A w U v, (pw S A w θ v a : ℂ) * F v a := by
    intro v
    unfold supp pw
    by_cases hv : v ∈ A
    · simp only [if_pos hv]
    · simp [hv]
  simp only [e1]
  rw [Finset.prod_univ_sum]
  have e2 : ∀ w' : S.W, (pθ S A w θ w' : ℂ) * ∏ v, F v (w'.1 v) =
      ∏ v, (pw S A w θ v (w'.1 v) : ℂ) * F v (w'.1 v) := by
    intro w'
    unfold pθ
    push_cast
    rw [← Finset.prod_mul_distrib]
  simp only [e2]
  refine Finset.sum_bij_ne_zero (fun w' _ _ => w'.1) ?_ ?_ ?_ ?_
  · intro w' _ h
    rw [Fintype.mem_piFinset]
    intro v
    refine pw_ne_zero hP fun h0 => h ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (by rw [h0]; simp)]
  · intro a _ _ b _ _ h; exact Subtype.ext h
  · intro g hg h0
    obtain ⟨hadm, hcnt⟩ := supp_word hU hw hn hg
    exact ⟨⟨g, hadm⟩, mem_Wb S hcnt, h0, rfl⟩
  · intro w' _ _
    rfl

/- English proof (translation)
Use `⟨fun w' => Finset.prod_nonneg fun v _ => pw_nonneg hP v _, fun w' hw' => ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Apply `hw'` to reduce the goal to its premises. Establish `hg : w'.1 ∈ Fintype.piFinset (supp S A w U)`. Rewrite using `[Fintype.mem_piFinset]`.

Introduce `v`. Use `pw_ne_zero hP fun h1 => h0 ?_` and prove the remaining obligations. Conclude with `Finset.prod_eq_zero (Finset.mem_univ v) h1`. Conclude with `mem_Wb S (supp_word hU hw hn hg).2`. Use `expand hP hU hw hn (fun _ _ => 1)` as an intermediate fact.

Simplify using `only [mul_one, Finset.prod_const_one] at this`. Establish `e : ∏ v, (if v ∈ A then ∑ a ∈ U v, (θ v a : ℂ) else 1) = 1`. Use `Finset.prod_eq_one fun v _ => ?_` and prove the remaining obligations. Use `split_ifs with hv`. Conclude with `(hP v hv).2.2` after adjusting the coercions.

Both sides reduce to the same expression. Rewrite `this` using `[e]`. Conclude with `this` after adjusting the coercions.
-/
theorem pθ_prob (hP : ∀ v ∈ A, TB.IsProb (U v) (θ v))
    (hU : ∀ v ∈ A, ∀ a ∈ U v, D.AdmAt S v a ∧ a.length ≤ n) (hw : w.1.cnt ≤ n) (hn : n ≤ S.Ntop) :
    TB.IsProb (S.base.Wb n) (pθ S A w θ) := by
  classical
  refine ⟨fun w' => Finset.prod_nonneg fun v _ => pw_nonneg hP v _, fun w' hw' => ?_, ?_⟩
  · by_contra h0
    apply hw'
    have hg : w'.1 ∈ Fintype.piFinset (supp S A w U) := by
      rw [Fintype.mem_piFinset]
      intro v
      refine pw_ne_zero hP fun h1 => h0 ?_
      exact Finset.prod_eq_zero (Finset.mem_univ v) h1
    exact mem_Wb S (supp_word hU hw hn hg).2
  · have := expand hP hU hw hn (fun _ _ => 1)
    simp only [mul_one, Finset.prod_const_one] at this
    have e : ∏ v, (if v ∈ A then ∑ a ∈ U v, (θ v a : ℂ) else 1) = 1 := by
      refine Finset.prod_eq_one fun v _ => ?_
      split_ifs with hv
      · exact_mod_cast (hP v hv).2.2
      · rfl
    rw [e] at this
    exact_mod_cast this

end hyps

end words

end

end Formalism.FourierDecayAlt.P.PBA
