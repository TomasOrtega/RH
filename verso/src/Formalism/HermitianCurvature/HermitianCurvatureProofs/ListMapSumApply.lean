import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemStepsFull

open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def TermClause (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (L : Finset (Fin (r + 2))) (o κ : ℕ) (Θ : DiffOp k r Wp Wq) : Prop :=
  ∀ T ∈ Θ, ∃ (P : Mat k r → ℂ) (a b : Fin (r + 2) → ℕ) (c : ℕ)
      (es : List (Fin nf × List (Mat k r))), U.IsPolyDeg κ P ∧
      (∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) ∧
      T.word.length + (es.map fun e => e.2.length).sum ≤ o ∧ (∀ e ∈ es, ∀ X ∈ e.2, inLie k r X) ∧
      ∀ g ∈ C6.domL D L, T.coef g = (P g * C6.monoM D a b c g) • C6.Epart fib es g

/- English proof (translation)
Introduce `Θ hΘ`. Proceed by induction on `Θ with`. Consider the case `nil => exact ⟨[], by simp, by simp, fun H g _ => by simp [opApply, shape]⟩`. Consider the case `cons T Θ ih`. Take `⟨Lf, h1, h2, h3⟩` from `ih (fun T' hT' => hΘ T' (List.mem_cons_of_mem _ hT'))`.

Take `⟨P, a, b, c, es, ⟨q, hqdeg, hq⟩, hab, hlen, hes, hcoef⟩` from `hΘ T (by simp)`. Use `⟨((⟨q, a, b, c, es⟩ : CT k r nf), T.word) :: Lf, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `e' he'`. Break down `List.mem_cons.1 he' with rfl | he'` into its components or cases. Use `⟨?_, hqdeg, hlen⟩` and prove the remaining obligations.

Unfold `Good`. Use `⟨?_, hes, T.word_lie⟩` and prove the remaining obligations. Introduce `l hl`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Take `⟨ha, hb⟩` from `hab l hcon.1 hcon.2`. Break down `hl with hl | hl` into its components or cases. Conclude with `hl ha`. Conclude with `hl hb`. Conclude with `h1 e' he'`.

Introduce `T' hT'`. Break down `List.mem_cons.1 hT' with rfl | hT'` into its components or cases. Conclude with `⟨_, List.mem_cons_self .., rfl⟩`. Take `⟨e', he', h⟩` from `h2 T' hT'`. Conclude with `⟨e', List.mem_cons_of_mem _ he', h⟩`.

Introduce `H g hg`. Establish `h3'` using `h3 H g hg`. Simplify using `only [opApply, shape, List.map_cons, List.sum_cons] at h3' ⊢`. Rewrite using `[h3', hcoef g hg]`. Use `congr 1`.

Simplify using `only [cv, cvs]`. Rewrite using `[hq g]`. Both sides reduce to the same expression.
-/
theorem toFS (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (L : Finset (Fin (r + 2))) {o κ : ℕ} :
    ∀ Θ : DiffOp k r Wp Wq, TermClause D fib L o κ Θ →
      ∃ Lf : FS k r nf, (∀ e ∈ Lf, Good L e ∧ e.1.q.totalDegree ≤ κ ∧ e.2.length + fo e.1.es ≤ o) ∧
        (∀ T ∈ Θ, ∃ e ∈ Lf, e.2 = T.word) ∧
        ∀ (H : Mat k r → (Wq →L[ℂ] Wp)), ∀ g ∈ C6.domL D L, opApply Θ H g = shape D fib H Lf g := by
  intro Θ hΘ
  induction Θ with
  | nil => exact ⟨[], by simp, by simp, fun H g _ => by simp [opApply, shape]⟩
  | cons T Θ ih =>
    obtain ⟨Lf, h1, h2, h3⟩ := ih (fun T' hT' => hΘ T' (List.mem_cons_of_mem _ hT'))
    obtain ⟨P, a, b, c, es, ⟨q, hqdeg, hq⟩, hab, hlen, hes, hcoef⟩ := hΘ T (by simp)
    refine ⟨((⟨q, a, b, c, es⟩ : CT k r nf), T.word) :: Lf, ?_, ?_, ?_⟩
    · intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · refine ⟨?_, hqdeg, hlen⟩
        unfold Good
        refine ⟨?_, hes, T.word_lie⟩
        intro l hl
        by_contra hcon
        push_neg at hcon
        obtain ⟨ha, hb⟩ := hab l hcon.1 hcon.2
        rcases hl with hl | hl
        · exact hl ha
        · exact hl hb
      · exact h1 e' he'
    · intro T' hT'
      rcases List.mem_cons.1 hT' with rfl | hT'
      · exact ⟨_, List.mem_cons_self .., rfl⟩
      · obtain ⟨e', he', h⟩ := h2 T' hT'
        exact ⟨e', List.mem_cons_of_mem _ he', h⟩
    · intro H g hg
      have h3' := h3 H g hg
      simp only [opApply, shape, List.map_cons, List.sum_cons] at h3' ⊢
      rw [h3', hcoef g hg]
      congr 1
      simp only [cv, cvs]
      rw [hq g]
      rfl

section mk

variable [FiniteDimensional ℂ Wp]

open Classical in

def mkTerm (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (e : CT k r nf × List (Mat k r)) : DTerm k r Wp Wq where
  coef := cv D fib e.1
  coefAdj := fun x => Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.adjH (cv D fib e.1 x)
  word := if ∀ X ∈ e.2, inLie k r X then e.2 else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id := fun x A B => Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.adjH_spec _ A B

/- English proof (translation)
Simplify using `only [mkTerm]`. Rewrite using `[if_pos h]`.
-/
lemma mkTerm_word (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    {e : CT k r nf × List (Mat k r)} (h : ∀ X ∈ e.2, inLie k r X) : (mkTerm D fib e).word = e.2 := by
  dsimp only [mkTerm]
  rw [if_pos h]

/- English proof (translation)
Unfold `opApply shape`. Rewrite using `[List.map_map]`. Use `congr 1`. Use `List.map_congr_left ?_` and prove the remaining obligations. Introduce `e he`.

Simplify using `only [Function.comp_apply]`. Rewrite using `[mkTerm_word D fib (hL e he)]`. Both sides reduce to the same expression.
-/
lemma opApply_mk (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq) (Lf : FS k r nf)
    (hL : ∀ e ∈ Lf, ∀ X ∈ e.2, inLie k r X) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    opApply (Lf.map (mkTerm D fib)) F g = shape D fib F Lf g := by
  unfold opApply shape
  rw [List.map_map]
  congr 1
  refine List.map_congr_left ?_
  intro e he
  simp only [Function.comp_apply]
  rw [mkTerm_word D fib (hL e he)]
  rfl

end mk

def compFS (D : RealPlaceData k r Wp Wq) {nf : ℕ} (L₁ L₂ : FS k r nf) : FS k r nf :=
  L₁.flatMap fun e₁ => (steps D e₁.2 L₂).map fun e => (mulCT e₁.1 e.1, e.2)

/- English proof (translation)
Introduce `e he`. Simplify using `only [compFS, List.mem_flatMap, List.mem_map] at he`. Take `⟨e₁, he₁, e', he', rfl⟩` from `he`. Take `⟨hG₁, hq₁, ho₁⟩` from `h₁ e₁ he₁`. Take `⟨hG₁a, hG₁b, hG₁c⟩` from `hG₁`.

Establish `hG'` using `(good_steps D e₁.2 hG₁c L₂ (fun e he => (h₂ e he).1) e' he').1`. Take `⟨hG'a, hG'b, hG'c⟩` from `hG'`. Take `⟨e₂, he₂, hdeg, hlen⟩` from `bound_steps D e₁.2 L₂ e' he'`. Take `⟨-, hq₂, ho₂⟩` from `h₂ e₂ he₂`. Establish `hfo : ∀ (l₁ l₂ : List (Fin nf × List (Mat k r))), fo (l₁ ++ l₂) = fo l₁ + fo l₂`.

Introduce `l₁ l₂`. Simplify using `[fo, List.map_append, List.sum_append]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `Good`. Use `⟨?_, ?_, hG'c⟩` and prove the remaining obligations.

Introduce `l hl`. Simplify using `only [mulCT, Pi.add_apply] at hl`. Distinguish the cases in `h1 : e₁.1.a l ≠ 0 ∨ e₁.1.b l ≠ 0`. Conclude with `hG₁a l h1`. Apply `hG'a l push_neg at h1` to reduce the goal to its premises.

Break down `hl with hl | hl` into its components or cases. Use `left`. Use linear arithmetic over natural numbers and integers. Use `right`. Use linear arithmetic over natural numbers and integers.

Introduce `x hx Y hY`. Simplify using `only [mulCT, List.mem_append] at hx`. Break down `hx with hx | hx` into its components or cases. Conclude with `hG₁b x hx Y hY`. Conclude with `hG'b x hx Y hY`.

Simplify using `only [mulCT]`. Establish `hmul` using `MvPolynomial.totalDegree_mul e₁.1.q e'.1.q`. Establish `hw : e₁.2.length ≤ o₁` using `by omega`. Use `Nat.mul_le_mul_left (2 * r + 2) hw` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Simplify using `only [mulCT]`. Rewrite using `[hfo]`. Use linear arithmetic over natural numbers and integers.
-/
lemma compFS_bound (D : RealPlaceData k r Wp Wq) {nf : ℕ} {L : Finset (Fin (r + 2))} {o₁ κ₁ o₂ κ₂ : ℕ}
    {L₁ L₂ : FS k r nf}
    (h₁ : ∀ e ∈ L₁, Good L e ∧ e.1.q.totalDegree ≤ κ₁ ∧ e.2.length + fo e.1.es ≤ o₁)
    (h₂ : ∀ e ∈ L₂, Good L e ∧ e.1.q.totalDegree ≤ κ₂ ∧ e.2.length + fo e.1.es ≤ o₂) :
    ∀ e ∈ compFS D L₁ L₂, Good L e ∧ e.1.q.totalDegree ≤ κ₁ + κ₂ + (2 * r + 2) * o₁ ∧
      e.2.length + fo e.1.es ≤ o₁ + o₂ := by
  intro e he
  simp only [compFS, List.mem_flatMap, List.mem_map] at he
  obtain ⟨e₁, he₁, e', he', rfl⟩ := he
  obtain ⟨hG₁, hq₁, ho₁⟩ := h₁ e₁ he₁
  obtain ⟨hG₁a, hG₁b, hG₁c⟩ := hG₁
  have hG' := (good_steps D e₁.2 hG₁c L₂ (fun e he => (h₂ e he).1) e' he').1
  obtain ⟨hG'a, hG'b, hG'c⟩ := hG'
  obtain ⟨e₂, he₂, hdeg, hlen⟩ := bound_steps D e₁.2 L₂ e' he'
  obtain ⟨-, hq₂, ho₂⟩ := h₂ e₂ he₂
  have hfo : ∀ (l₁ l₂ : List (Fin nf × List (Mat k r))), fo (l₁ ++ l₂) = fo l₁ + fo l₂ := by
    intro l₁ l₂
    simp [fo, List.map_append, List.sum_append]
  refine ⟨?_, ?_, ?_⟩
  · unfold Good
    refine ⟨?_, ?_, hG'c⟩
    · intro l hl
      simp only [mulCT, Pi.add_apply] at hl
      by_cases h1 : e₁.1.a l ≠ 0 ∨ e₁.1.b l ≠ 0
      · exact hG₁a l h1
      · apply hG'a l
        push_neg at h1
        rcases hl with hl | hl
        · left; omega
        · right; omega
    · intro x hx Y hY
      simp only [mulCT, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hG₁b x hx Y hY
      · exact hG'b x hx Y hY
  · simp only [mulCT]
    have hmul := MvPolynomial.totalDegree_mul e₁.1.q e'.1.q
    have hw : e₁.2.length ≤ o₁ := by omega
    have := Nat.mul_le_mul_left (2 * r + 2) hw
    omega
  · simp only [mulCT]
    rw [hfo]
    omega

/- English proof (translation)
Rewrite using `[map_list_sum, List.map_map]`. Both sides reduce to the same expression.
-/
lemma list_map_sum_apply {α : Type*} (L : List α) (A : C6.EndH Wp Wq) (f : α → (Wq →L[ℂ] Wp)) :
    A (L.map f).sum = (L.map fun a => A (f a)).sum := by
  rw [map_list_sum, List.map_map]
  rfl

/- English proof (translation)
Introduce `w`. Proceed by induction on `w with`. Consider the case `nil => intro _ H H' hH g hg`. Conclude with `hH g hg`. Consider the case `cons X w ih`.

Introduce `hw H H' hH g hg`. Establish `ih'` using `ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) hH`. Rewrite using `[Rw_cons', Rw_cons', Dx_eq, Dx_eq]`. Apply `Filter.EventuallyEq.deriv_eq` to reduce the goal to its premises. Establish `hGV : g ∈ GV k r` using `((mem_domL D L g).1 hg).1`.

Establish `hV0 : g ∈ V0 D L` using `((mem_domL D L g).1 hg).2`. Use `filter_upwards [crv_ev (x := (false, X)) (isOpen_big_cell_set D L) hV0] with t ht`. Apply `ih'` to reduce the goal to its premises. Rewrite using `[mem_domL]`. Conclude with `⟨crv_mem (x := (false, X)) (hw X (by simp)) hGV t, ht⟩`.
-/
private lemma rw_congr_on_domL (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ {H H' : Mat k r → (Wq →L[ℂ] Wp)},
      (∀ g ∈ C6.domL D L, H g = H' g) → ∀ g ∈ C6.domL D L, Rw w H g = Rw w H' g := by
  intro w
  induction w with
  | nil => intro _ H H' hH g hg; exact hH g hg
  | cons X w ih =>
    intro hw H H' hH g hg
    have ih' := ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) hH
    rw [Rw_cons', Rw_cons', Dx_eq, Dx_eq]
    apply Filter.EventuallyEq.deriv_eq
    have hGV : g ∈ GV k r := ((mem_domL D L g).1 hg).1
    have hV0 : g ∈ V0 D L := ((mem_domL D L g).1 hg).2
    filter_upwards [crv_ev (x := (false, X)) (isOpen_big_cell_set D L) hV0] with t ht
    apply ih'
    rw [mem_domL]
    exact ⟨crv_mem (x := (false, X)) (hw X (by simp)) hGV t, ht⟩

/- English proof (translation)
Use `show (L₁.map fun e => cv D fib e.1 g (Rw e.2 H g)).sum = _`. Unfold `compFS`. Rewrite using `[shape_flatMap']`. Use `congr 1`. Use `List.map_congr_left fun e₁ he₁ => ?_` and prove the remaining obligations.

Take `⟨-, -, hw⟩` from `hg₁ e₁ he₁`. Rewrite using `[rw_congr_on_domL D L e₁.2 hw hH g hg]`. Rewrite using `[expand D fib hfib L hF e₁.2 L₂ hw hg₂ (fun e he => hm e₁ he₁ e he) g hg]`. Unfold `shape`. Rewrite using `[list_map_sum_apply, List.map_map]`.

Use `congr 1`. Use `List.map_congr_left fun e _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, cv_mul, ContinuousLinearMap.mul_apply]`.
-/
theorem comp_identity (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {L₁ L₂ : FS k r nf}
    (hg₁ : ∀ e ∈ L₁, Good L e) (hg₂ : ∀ e ∈ L₂, Good L e) {m : ℕ} (hm : ∀ e₁ ∈ L₁, ∀ e ∈ L₂, e.2.length + e₁.2.length ≤ m)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn (m : ℕ∞) (GV k r) F) {H : Mat k r → (Wq →L[ℂ] Wp)}
    (hH : ∀ g ∈ C6.domL D L, H g = shape D fib F L₂ g) {g : Mat k r} (hg : g ∈ C6.domL D L) :
    shape D fib H L₁ g = shape D fib F (compFS D L₁ L₂) g := by
  show (L₁.map fun e => cv D fib e.1 g (Rw e.2 H g)).sum = _
  unfold compFS
  rw [shape_flatMap']
  congr 1
  refine List.map_congr_left fun e₁ he₁ => ?_
  obtain ⟨-, -, hw⟩ := hg₁ e₁ he₁
  rw [rw_congr_on_domL D L e₁.2 hw hH g hg]
  rw [expand D fib hfib L hF e₁.2 L₂ hw hg₂ (fun e he => hm e₁ he₁ e he) g hg]
  unfold shape
  rw [list_map_sum_apply, List.map_map]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [Function.comp_apply, cv_mul, ContinuousLinearMap.mul_apply]

end Formalism.FourierDecayAlt.P.MinorPolynomials
