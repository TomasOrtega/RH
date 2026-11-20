import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.CechAugRowU
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
universe u v w

noncomputable section

namespace GlobalTheory.CompanionTheory.CechRowExact

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
  {ι : Type} (U : ι → ObjectProperty C)

/- English proof (translation)
Introduce `_ _ φ h a` and use `hU (i a) φ (h a)`.
-/
theorem cosieve_capT (hU : ∀ α, Cosieve (U α)) {n : ℕ} (i : Fin n → ι) : Cosieve (capT U i) :=
  fun _ _ φ h a => hU (i a) φ (h a)

/- English proof (translation)
Introduce `k` and use `by refine Fin.cases ?_ (fun k => ?_) k · exact ha · exact hi k`.
-/
theorem capT_cons {n : ℕ} {a : ι} {i : Fin n → ι} {T : C} (ha : U a T) (hi : capT U i T) :
    capT U (Fin.cons (α := fun _ => ι) a i) T := fun k => by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact ha
  · exact hi k

def liftC (hU : ∀ α, Cosieve (U α)) {n q : ℕ} (i : Fin n → ι) (s : ComposableArrows C q)
    (h : capT U i (s.obj 0)) : ComposableArrows (capT U i).FullSubcategory q :=
  (capT U i).lift s fun k => cosieve_capT U hU i (s.map (homOfLE (Fin.zero_le k))) h

def ev (hU : ∀ α, Cosieve (U α)) {n q : ℕ} (i : Fin n → ι) (x : CH.Cn ((capT U i).ι ⋙ F) q)
    (s : ComposableArrows C q) (h : capT U i (s.obj 0)) : F.obj (s.obj (Fin.last q)) :=
  x (liftC U hU i s h)

variable {F U}

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem ev_congr (hU : ∀ α, Cosieve (U α)) {n q : ℕ} (f : ∀ i : Fin n → ι, CH.Cn ((capT U i).ι ⋙ F) q)
    {i i' : Fin n → ι} (e : i = i') (s : ComposableArrows C q) (h : capT U i (s.obj 0))
    (h' : capT U i' (s.obj 0)) : ev F U hU i (f i) s h = ev F U hU i' (f i') s h' := by
  subst e; rfl

/- English proof (translation)
Establish `e` using `congrFun (congrFun (Cos.d_apply ((cechCC F U).cos q) p f) i) (liftC U hU i s h)`. Use `e.trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_apply, Finset.sum_apply]`. Both sides reduce to the same expression.
-/
theorem ev_d (hU : ∀ α, Cosieve (U α)) {p q : ℕ} (f : ∀ i : Fin (p + 1) → ι, CH.Cn ((capT U i).ι ⋙ F) q)
    (i : Fin (p + 2) → ι) (s : ComposableArrows C q) (h : capT U i (s.obj 0)) :
    ev F U hU i (((cechCC F U).cos q).d p f i) s h =
      ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • ev F U hU (i ∘ k.succAbove) (f (i ∘ k.succAbove)) s (fun a => h _) := by
  have e := congrFun (congrFun (Cos.d_apply ((cechCC F U).cos q) p f) i) (liftC U hU i s h)
  refine e.trans ?_
  rw [Finset.sum_apply, Finset.sum_apply]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[Function.comp]`.
-/
theorem cons_zero {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) :
    (Fin.cons (α := fun _ => ι) a i : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = i := by
  funext k
  simp [Function.comp]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Use `Fin.cases ?_ (fun k => ?_) k` and prove the remaining obligations. Simplify using `[Function.comp]`. Simplify using `[Function.comp]`.
-/
theorem cons_succ {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    (Fin.cons (α := fun _ => ι) a i : Fin (n + 2) → ι) ∘ j.succ.succAbove =
      Fin.cons (α := fun _ => ι) a (i ∘ j.succAbove) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Function.comp]
  · simp [Function.comp]

def hh (hU : ∀ α, Cosieve (U α)) (α : C → ι) (hα : ∀ T, U (α T) T) {p q : ℕ}
    (f : ∀ i : Fin (p + 2) → ι, CH.Cn ((capT U i).ι ⋙ F) q) (i : Fin (p + 1) → ι) :
    CH.Cn ((capT U i).ι ⋙ F) q := fun t =>
  ev F U hU _ (f (Fin.cons (α := fun _ => ι) (α (t.obj 0).obj) i)) (t ⋙ (capT U i).ι)
    (capT_cons U (hα _) (t.obj 0).property)

/- English proof (translation)
Establish `h'` using `capT_cons U (hα (s.obj 0)) h`. Establish `e` using `ev_d hU f _ s h'`. Establish `z : ev F U hU _ (((cechCC F U).cos q).d (p + 1) f (Fin.cons (α` using `fun _ => ι) (α (s.obj 0)) i)) s h' = 0 := by`. Rewrite using `[hf]`. Both sides reduce to the same expression.

Rewrite `e` using `[z, Fin.sum_univ_succ]`. Establish `e0` using `ev_congr hU f (cons_zero (α (s.obj 0)) i) s (fun a => h' _) h`. Establish `e1 : ∀ j : Fin (p + 2), ev F U hU _ (f ((Fin.cons (α` using `fun _ => ι) (α (s.obj 0)) i : Fin (p + 3) → ι) ∘ j.succ.succAbove)) s (fun a => h' _) = ev F U hU _ (f (Fin.cons (α := fun _ => ι) (α (s.obj 0)) (i ∘ j.succAbove))) s (capT_cons U (hα _) fun a => h _) := fun j => ev_congr hU f (cons_succ _ i j) s _ _`. Simplify using `only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib, e0, e1] at e`. Conclude with `(add_neg_eq_zero.1 e.symm)`.
-/
theorem cocycle_eq (hU : ∀ α, Cosieve (U α)) (α : C → ι) (hα : ∀ T, U (α T) T) {p q : ℕ}
    (f : ∀ i : Fin (p + 2) → ι, CH.Cn ((capT U i).ι ⋙ F) q) (hf : ((cechCC F U).cos q).d (p + 1) f = 0)
    (i : Fin (p + 2) → ι) (s : ComposableArrows C q) (h : capT U i (s.obj 0)) :
    ev F U hU i (f i) s h = ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      ev F U hU _ (f (Fin.cons (α := fun _ => ι) (α (s.obj 0)) (i ∘ j.succAbove))) s
        (capT_cons U (hα _) fun a => h _) := by
  have h' := capT_cons U (hα (s.obj 0)) h
  have e := ev_d hU f _ s h'
  have z : ev F U hU _ (((cechCC F U).cos q).d (p + 1) f (Fin.cons (α := fun _ => ι) (α (s.obj 0)) i)) s h' = 0 := by
    rw [hf]; rfl
  rw [z, Fin.sum_univ_succ] at e
  have e0 := ev_congr hU f (cons_zero (α (s.obj 0)) i) s (fun a => h' _) h
  have e1 : ∀ j : Fin (p + 2), ev F U hU _ (f ((Fin.cons (α := fun _ => ι) (α (s.obj 0)) i : Fin (p + 3) → ι) ∘ j.succ.succAbove)) s (fun a => h' _) =
      ev F U hU _ (f (Fin.cons (α := fun _ => ι) (α (s.obj 0)) (i ∘ j.succAbove))) s (capT_cons U (hα _) fun a => h _) :=
    fun j => ev_congr hU f (cons_succ _ i j) s _ _
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, e0, e1] at e
  exact (add_neg_eq_zero.1 e.symm)

/- English proof (translation)
Establish `h'` using `capT_cons U (hα (s.obj 0)) h`. Establish `e` using `ev_d hU f _ s h'`. Establish `z : ev F U hU _ (((cechCC F U).cos q).d 0 f (Fin.cons (α` using `fun _ => ι) (α (s.obj 0)) i)) s h' = 0 := by`. Rewrite using `[hf]`. Both sides reduce to the same expression.

Rewrite `e` using `[z, Fin.sum_univ_two]`. Establish `e0` using `ev_congr hU f (cons_zero (α (s.obj 0)) i) s (fun a => h' _) h`. Establish `e1` using `ev_congr hU f (i := (Fin.cons (α := fun _ => ι) (α (s.obj 0)) i : Fin (0 + 2) → ι) ∘ (1 : Fin (0 + 2)).succAbove) (i' := fun _ => α (s.obj 0)) (funext fun k => by`. Take `rfl : k = 0` from `Subsingleton.elim (α := Fin 1) _ _`. Use the proof step `rfl) s (fun a => h' _) (fun _ => hα _)`.

Simplify using `only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, e0, e1] at e`. Conclude with `(add_neg_eq_zero.1 e.symm)`.
-/
theorem cocycle_zero (hU : ∀ α, Cosieve (U α)) (α : C → ι) (hα : ∀ T, U (α T) T) {q : ℕ}
    (f : ∀ i : Fin (0 + 1) → ι, CH.Cn ((capT U i).ι ⋙ F) q) (hf : ((cechCC F U).cos q).d 0 f = 0)
    (i : Fin (0 + 1) → ι) (s : ComposableArrows C q) (h : capT U i (s.obj 0)) :
    ev F U hU i (f i) s h = ev F U hU _ (f fun _ => α (s.obj 0)) s (fun _ => hα _) := by
  have h' := capT_cons U (hα (s.obj 0)) h
  have e := ev_d hU f _ s h'
  have z : ev F U hU _ (((cechCC F U).cos q).d 0 f (Fin.cons (α := fun _ => ι) (α (s.obj 0)) i)) s h' = 0 := by
    rw [hf]; rfl
  rw [z, Fin.sum_univ_two] at e
  have e0 := ev_congr hU f (cons_zero (α (s.obj 0)) i) s (fun a => h' _) h
  have e1 := ev_congr hU f (i := (Fin.cons (α := fun _ => ι) (α (s.obj 0)) i : Fin (0 + 2) → ι) ∘ (1 : Fin (0 + 2)).succAbove)
    (i' := fun _ => α (s.obj 0)) (funext fun k => by
      obtain rfl : k = 0 := Subsingleton.elim (α := Fin 1) _ _
      rfl) s (fun a => h' _) (fun _ => hα _)
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, e0, e1] at e
  exact (add_neg_eq_zero.1 e.symm)

end GlobalTheory.CompanionTheory.CechRowExact

open GlobalTheory.CompanionTheory.CechRowExact in

/- English proof (translation)
Introduce `R _ C _ F ι U hU hc q`. Use `choose α hα using hc`. Use `⟨(cechAugRowU F U).hε q, fun g hg => ?_, fun f hf => ?_, fun n f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[one_smul]`. Use function extensionality and compare the values at `s`.

Establish `h1` using `congrFun (congrFun hg fun _ => α (s.obj 0)) (liftC U hU _ s fun _ => hα _)`. Conclude with `h1`. Use `⟨fun s => ev F U hU _ (f fun _ => α (s.obj 0)) s (fun _ => hα _), ?_⟩` and prove the remaining obligations. Rewrite using `[one_smul]`. Use function extensionality and compare the values at `i t`.

Conclude with `(cocycle_zero hU α hα f hf i (t ⋙ (capT U i).ι) (t.obj 0).property).symm`. Use `⟨hh hU α hα f, ?_⟩` and prove the remaining obligations. Rewrite using `[one_smul]`. Use function extensionality and compare the values at `i t`. Use `(ev_d hU (hh hU α hα f) i (t ⋙ (capT U i).ι) (t.obj 0).property).trans ?_` and prove the remaining obligations.

Use `Eq.trans ?_ (cocycle_eq hU α hα f hf i (t ⋙ (capT U i).ι) (t.obj 0).property).symm` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem GlobalTheory.CompanionTheory.CechRowExact.cech_rows : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) {ι : Type} (U : ι → ObjectProperty C), (∀ α, Cosieve (U α)) → (∀ T, ∃ α, U α T) → ∀ q, ((cechCC F U).dcx.row q).ResUpTo 1 ((cechAugRowU F U).ε q) := by
  intro R _ C _ F ι U hU hc q
  choose α hα using hc
  refine ⟨(cechAugRowU F U).hε q, fun g hg => ?_, fun f hf => ?_, fun n f hf => ?_⟩
  · rw [one_smul]
    funext s
    have h1 := congrFun (congrFun hg fun _ => α (s.obj 0)) (liftC U hU _ s fun _ => hα _)
    exact h1
  · refine ⟨fun s => ev F U hU _ (f fun _ => α (s.obj 0)) s (fun _ => hα _), ?_⟩
    rw [one_smul]
    funext i t
    exact (cocycle_zero hU α hα f hf i (t ⋙ (capT U i).ι) (t.obj 0).property).symm
  · refine ⟨hh hU α hα f, ?_⟩
    rw [one_smul]
    funext i t
    refine (ev_d hU (hh hU α hα f) i (t ⋙ (capT U i).ι) (t.obj 0).property).trans ?_
    refine Eq.trans ?_ (cocycle_eq hU α hα f hf i (t ⋙ (capT U i).ι) (t.obj 0).property).symm
    rfl
