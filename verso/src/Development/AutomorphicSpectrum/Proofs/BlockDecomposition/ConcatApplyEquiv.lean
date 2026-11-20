import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegCoarse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) : Fin s → Segment k := fun a =>
  Segment.ofFirst (Δ.first.nu ((∑ b ∈ Finset.univ.filter (fun b => a < b), c b : ℕ) : ℂ)) (Δ.isCusp_first.nu _)
    (c a) (hc a)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem len_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (a : Fin s) :
    (topCut Δ c hc a).len = c a := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, fun _ => rfl⟩`.
-/
theorem isTopCut_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (h : ∑ a, c a = Δ.len) :
    IsTopCut Δ (topCut Δ c hc) :=
  ⟨h, fun _ => rfl⟩

/- English proof (translation)
The claim follows from `funext fun a => Segment.ext_first (by rw [h.2 a]; rfl) rfl`.
-/
theorem eq_topCut {Δ : Segment k} {s : ℕ} {Γ : Fin s → Segment k} (h : IsTopCut Δ Γ) :
    Γ = topCut Δ (fun a => (Γ a).len) (fun a => (Γ a).len_pos) :=
  funext fun a => Segment.ext_first (by rw [h.2 a]; rfl) rfl

/- English proof (translation)
Establish `h1 : ∑ t : Fin a, c (Fin.castLE a.2.le t) = ∑ b ∈ Finset.univ.filter (fun b : Fin s => b < a), c b`. Use `Finset.sum_bij (fun t _ => Fin.castLE a.2.le t) (fun t _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.lt_def.2 t.2⟩) (fun t _ u _ h => Fin.castLE_injective _ h) (fun b hb => ?_) (fun _ _ => rfl)` and prove the remaining obligations. Establish `hb' : (b : ℕ) < a` using `Fin.lt_def.1 (Finset.mem_filter.1 hb).2`. Conclude with `⟨⟨b, hb'⟩, Finset.mem_univ _, rfl⟩`. Rewrite using `[h1]`.

Establish `h2 : ∑ b, c b = ∑ b, ((if b < a then c b else 0) + (if b = a then c b else 0) + (if a < b then c b else 0))`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Break down `lt_trichotomy b a with h | h | h` into its components or cases. Simplify using `[h, h.ne, not_lt.2 h.le]`. Simplify using `[h]`.

Simplify using `[h, h.ne', not_lt.2 h.le]`. Rewrite using `[h2, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter, Finset.filter_eq', if_pos (Finset.mem_univ _), Finset.sum_singleton]`.
-/
theorem sum_split {s : ℕ} (c : Fin s → ℕ) (a : Fin s) :
    ∑ b, c b = (∑ t : Fin a, c (Fin.castLE a.2.le t)) + c a + ∑ b ∈ Finset.univ.filter (fun b => a < b), c b := by
  have h1 : ∑ t : Fin a, c (Fin.castLE a.2.le t) = ∑ b ∈ Finset.univ.filter (fun b : Fin s => b < a), c b := by
    refine Finset.sum_bij (fun t _ => Fin.castLE a.2.le t)
      (fun t _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.lt_def.2 t.2⟩)
      (fun t _ u _ h => Fin.castLE_injective _ h) (fun b hb => ?_) (fun _ _ => rfl)
    have hb' : (b : ℕ) < a := Fin.lt_def.1 (Finset.mem_filter.1 hb).2
    exact ⟨⟨b, hb'⟩, Finset.mem_univ _, rfl⟩
  rw [h1]
  have h2 : ∑ b, c b = ∑ b, ((if b < a then c b else 0) + (if b = a then c b else 0) + (if a < b then c b else 0)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases lt_trichotomy b a with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  rw [h2, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    ← Finset.sum_filter, Finset.filter_eq', if_pos (Finset.mem_univ _), Finset.sum_singleton]

/- English proof (translation)
Use `show dec (topCut Δ c hc (finSigmaFinEquiv.symm i).1) (finSigmaFinEquiv.symm i).2 = dec Δ (Fin.cast h i)`. Break down `hq : finSigmaFinEquiv.symm i with ⟨a, j⟩` into its components or cases. Establish `hi : (i : ℕ) = (∑ t : Fin a, c (Fin.castLE a.2.le t)) + j`. Rewrite using `[← Equiv.apply_symm_apply finSigmaFinEquiv i, hq, finSigmaFinEquiv_apply]`. Establish `hs` using `sum_split c a`.

Establish `hj : (j : ℕ) < c a` using `j.2`. Simplify using `only [dec, Segment.term, topCut, Segment.first_ofFirst, IrrGL.nu_nu]`. Use `congr 1`. Simplify using `only [Fin.val_rev, Fin.val_cast, Segment.len_ofFirst]`. Establish `key : Δ.len - (i + 1) = (∑ b ∈ Finset.univ.filter (fun b => a < b), c b) + (c a - (j + 1))`.

Rewrite using `[← h]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[key]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem concat_dec_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (h : ∑ a, c a = Δ.len)
    (i : Fin (∑ a, c a)) : concat c (fun a => dec (topCut Δ c hc a)) i = dec Δ (Fin.cast h i) := by
  show dec (topCut Δ c hc (finSigmaFinEquiv.symm i).1) (finSigmaFinEquiv.symm i).2 = dec Δ (Fin.cast h i)
  rcases hq : finSigmaFinEquiv.symm i with ⟨a, j⟩
  have hi : (i : ℕ) = (∑ t : Fin a, c (Fin.castLE a.2.le t)) + j := by
    rw [← Equiv.apply_symm_apply finSigmaFinEquiv i, hq, finSigmaFinEquiv_apply]
  have hs := sum_split c a
  have hj : (j : ℕ) < c a := j.2
  simp only [dec, Segment.term, topCut, Segment.first_ofFirst, IrrGL.nu_nu]
  congr 1
  simp only [Fin.val_rev, Fin.val_cast, Segment.len_ofFirst]
  have key : Δ.len - (i + 1) = (∑ b ∈ Finset.univ.filter (fun b => a < b), c b) + (c a - (j + 1)) := by
    rw [← h]; omega
  rw [key]
  push_cast
  ring

/- English proof (translation)
Use function extensionality and compare the values at `a j`. Use `congrFun h (finSigmaFinEquiv ⟨a, j⟩)` as an intermediate fact. Express the relevant statement in the definitionally equal form `(fun p : (b : Fin s) × Fin (c b) => x p.1 p.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨a, j⟩)) = (fun p : (b : Fin s) × Fin (c b) => x' p.1 p.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨a, j⟩)) at this`. Rewrite `this` using `[Equiv.symm_apply_apply]`. Conclude with `this`.
-/
theorem concat_injective {s : ℕ} {c : Fin s → ℕ} {x x' : ∀ a, Fin (c a) → IrrGL k} (h : concat c x = concat c x') :
    x = x' := by
  funext a j
  have := congrFun h (finSigmaFinEquiv ⟨a, j⟩)
  change (fun p : (b : Fin s) × Fin (c b) => x p.1 p.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨a, j⟩)) =
    (fun p : (b : Fin s) × Fin (c b) => x' p.1 p.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨a, j⟩)) at this
  rw [Equiv.symm_apply_apply] at this
  exact this

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(fun q : (b : Fin s) × Fin (c b) => x q.1 q.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv p)) = _`. Rewrite using `[Equiv.symm_apply_apply]`.
-/
theorem concat_apply_equiv {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL k) (p : (a : Fin s) × Fin (c a)) :
    concat c x (finSigmaFinEquiv p) = x p.1 p.2 := by
  change (fun q : (b : Fin s) × Fin (c b) => x q.1 q.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv p)) = _
  rw [Equiv.symm_apply_apply]

/- English proof (translation)
Rewrite using `[← Equiv.sum_comp finSigmaFinEquiv, Fintype.sum_sigma]`. Simplify using `only [concat_apply_equiv]`.
-/
theorem sum_concat {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL k) :
    ∑ i, (concat c x i).1 = ∑ a, ∑ j, (x a j).1 := by
  rw [← Equiv.sum_comp finSigmaFinEquiv, Fintype.sum_sigma]
  simp only [concat_apply_equiv]

/- English proof (translation)
Rewrite using `[← Segment.sum_term_fst]`. Conclude with `Equiv.sum_comp Fin.revPerm (fun a => (Δ.term a).1)`.
-/
theorem sum_dec (Δ : Segment k) : ∑ a, (dec Δ a).1 = Δ.deg := by
  rw [← Segment.sum_term_fst]
  exact Equiv.sum_comp Fin.revPerm (fun a => (Δ.term a).1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem deg_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (a : Fin s) :
    (topCut Δ c hc a).deg = c a * Δ.d := rfl

/- English proof (translation)
Substitute `h` using the available equality. Take `rfl : x = x'` from `funext fun i => by simpa using hx i`. Both sides reduce to the same expression.
-/
theorem jm_reindex {n m N : ℕ} (h : n = m) (x : Fin n → IrrGL k) (x' : Fin m → IrrGL k)
    (hx : ∀ i, x i = x' (Fin.cast h i)) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : jm x hd π = jm x' hd' π := by
  subst h
  obtain rfl : x = x' := funext fun i => by simpa using hx i
  rfl

/- English proof (translation)
Take `⟨n, c⟩` from `x`. Take `⟨n', c'⟩` from `x'`. Establish `e1` using `h.deg_eq`. Establish `e2` using `h'.deg_eq`. Take `rfl : n = n'` from `e1.symm.trans e2`.

Take `⟨φ⟩` from `h.unique h'`. Use `(IrrGL.of_eq_of (π := IrrGL.rep (k := k) ⟨n, c'⟩) (σ := IrrGL.rep (k := k) ⟨n, c⟩) (hs := c'.rep.smooth) (hi := c'.rep.irr) (hs' := c.rep.smooth) (hi' := c.rep.irr)).2 ⟨φ⟩` as an intermediate fact. Rewrite `this` using `[IrrGL.of_rep, IrrGL.of_rep]`. Conclude with `this.symm`.
-/
theorem eq_of_isLSeg {Γ : Segment k} {x x' : IrrGL k} (h : IsLSeg Γ x.rep) (h' : IsLSeg Γ x'.rep) : x = x' := by
  obtain ⟨n, c⟩ := x
  obtain ⟨n', c'⟩ := x'
  have e1 := h.deg_eq
  have e2 := h'.deg_eq
  obtain rfl : n = n' := e1.symm.trans e2
  obtain ⟨φ⟩ := h.unique h'
  have := (IrrGL.of_eq_of (π := IrrGL.rep (k := k) ⟨n, c'⟩) (σ := IrrGL.rep (k := k) ⟨n, c⟩)
    (hs := c'.rep.smooth) (hi := c'.rep.irr) (hs' := c.rep.smooth) (hi' := c.rep.irr)).2 ⟨φ⟩
  rw [IrrGL.of_rep, IrrGL.of_rep] at this
  exact this.symm

end GlobalTheory.CompanionTheory.SegCoarse

end
