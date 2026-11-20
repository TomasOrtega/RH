import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.HderEntry
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Rdcalc

noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section SlopeTestRemainingChoices

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/- English proof (translation)
Introduce `x hx`. Establish `h1` using `(UpperTheory.RealTr.rdcalc n V).1 f f' h`. Simplify using `only [Eu, Pi.smul_apply, Pi.add_apply, h1 _ hx]`.
-/
private theorem eu_loc (s : Bool) (a b : Fin n) {f f' : Mat n → V} (h : Set.EqOn f f' (GLs n)) :
    Set.EqOn (Eu s a b f) (Eu s a b f') (GLs n) := by
  intro x hx
  have h1 := (UpperTheory.RealTr.rdcalc n V).1 f f' h
  simp only [Eu, Pi.smul_apply, Pi.add_apply, h1 _ hx]

/- English proof (translation)
Establish `h1` using `((UpperTheory.RealTr.rdcalc n V).2 f h).1`. Conclude with `((h1 _).add ((h1 _).const_smul _)).const_smul _`.
-/
private theorem eu_smo (s : Bool) (a b : Fin n) {f : Mat n → V} (h : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Eu s a b f) (GLs n) := by
  have h1 := ((UpperTheory.RealTr.rdcalc n V).2 f h).1
  exact ((h1 _).add ((h1 _).const_smul _)).const_smul _

/- English proof (translation)
Introduce `g hg`. Establish `hd : DifferentiableAt ℝ f g` using `(h.differentiableOn (by simp)).differentiableAt (((UpperTheory.RealTr.basic n).1).mem_nhds hg)`. Establish `e : fderiv ℝ (fun y => c • f y) g = c • fderiv ℝ f g` using `(hd.hasFDerivAt.const_smul c).fderiv`. Simplify using `only [Rd, e]`. Both sides reduce to the same expression.
-/
private theorem rd_smul (c : ℂ) {f : Mat n → V} (h : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) :
    Set.EqOn (Rd X (fun y => c • f y)) (fun y => c • Rd X f y) (GLs n) := by
  intro g hg
  have hd : DifferentiableAt ℝ f g :=
    (h.differentiableOn (by simp)).differentiableAt (((UpperTheory.RealTr.basic n).1).mem_nhds hg)
  have e : fderiv ℝ (fun y => c • f y) g = c • fderiv ℝ f g := (hd.hasFDerivAt.const_smul c).fderiv
  simp only [Rd, e]
  rfl

/- English proof (translation)
Introduce `x hx`. Simplify using `only [Eu, Pi.smul_apply, Pi.add_apply, rd_smul c h _ hx]`. Rewrite using `[smul_comm _ c, ← smul_add, smul_comm]`.
-/
private theorem eu_smul (s : Bool) (a b : Fin n) (c : ℂ) {f : Mat n → V} (h : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Eu s a b (fun y => c • f y)) (fun y => c • Eu s a b f y) (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, rd_smul c h _ hx]
  rw [smul_comm _ c, ← smul_add, smul_comm]

/- English proof (translation)
Proceed by induction on `m generalizing a b with`. Consider the case `zero`. Introduce `x hx`. Simplify using `only [Epow.eq_1]`. Use `split_ifs`.

Conclude with `h hx`. Both sides reduce to the same expression. Consider the case `succ m ih`. Introduce `x hx`. Simplify using `only [Epow.eq_2, Finset.sum_apply]`.

Conclude with `Finset.sum_congr rfl fun d _ => eu_loc s a d (ih d b) hx`.
-/
private theorem epow_loc (s : Bool) (m : ℕ) (a b : Fin n) {f f' : Mat n → V} (h : Set.EqOn f f' (GLs n)) :
    Set.EqOn (Epow s m a b f) (Epow s m a b f') (GLs n) := by
  induction m generalizing a b with
  | zero =>
    intro x hx
    simp only [Epow.eq_1]
    split_ifs
    · exact h hx
    · rfl
  | succ m ih =>
    intro x hx
    simp only [Epow.eq_2, Finset.sum_apply]
    exact Finset.sum_congr rfl fun d _ => eu_loc s a d (ih d b) hx

/- English proof (translation)
Proceed by induction on `m generalizing a b with`. Consider the case `zero`. Simplify using `only [Epow.eq_1]`. Use `split_ifs`. Conclude with `h`.

Conclude with `contDiffOn_const`. Consider the case `succ m ih`. Simplify using `only [Epow.eq_2]`. Rewrite using `[Finset.sum_fn]`. Conclude with `ContDiffOn.sum fun d _ => eu_smo s a d (ih d b)`.
-/
private theorem epow_smo (s : Bool) (m : ℕ) (a b : Fin n) {f : Mat n → V} (h : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Epow s m a b f) (GLs n) := by
  induction m generalizing a b with
  | zero =>
    simp only [Epow.eq_1]
    split_ifs
    · exact h
    · exact contDiffOn_const
  | succ m ih =>
    simp only [Epow.eq_2]
    rw [Finset.sum_fn]
    exact ContDiffOn.sum fun d _ => eu_smo s a d (ih d b)

/- English proof (translation)
Proceed by induction on `m generalizing a b with`. Consider the case `zero`. Introduce `x hx`. Simplify using `only [Epow.eq_1]`. Apply the tactic sequence `split_ifs <;> simp`.

Consider the case `succ m ih`. Introduce `x hx`. Simplify using `only [Epow.eq_2, Finset.sum_apply, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[eu_loc s a d (ih d b) hx]`.

Conclude with `eu_smul s a d c (epow_smo s m d b h) hx`.
-/
private theorem epow_smul (s : Bool) (m : ℕ) (a b : Fin n) (c : ℂ) {f : Mat n → V}
    (h : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Epow s m a b (fun y => c • f y)) (fun y => c • Epow s m a b f y) (GLs n) := by
  induction m generalizing a b with
  | zero =>
    intro x hx
    simp only [Epow.eq_1]
    split_ifs <;> simp
  | succ m ih =>
    intro x hx
    simp only [Epow.eq_2, Finset.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [eu_loc s a d (ih d b) hx]
    exact eu_smul s a d c (epow_smo s m d b h) hx

/- English proof (translation)
Introduce `g hg`. Simplify using `only [gel, Finset.sum_apply]`. Conclude with `Finset.sum_congr rfl fun a _ => epow_loc s m a a h hg`.
-/
private theorem gel_loc (s : Bool) (m : ℕ) {f f' : Mat n → V} (h : Set.EqOn f f' (GLs n)) :
    Set.EqOn (gel s m f) (gel s m f') (GLs n) := by
  intro g hg
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_loc s m a a h hg

/- English proof (translation)
Introduce `g hg`. Simplify using `only [gel, Finset.sum_apply, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => epow_smul s m a a c h hg`.
-/
private theorem gel_smul (s : Bool) (m : ℕ) (c : ℂ) {f : Mat n → V} (h : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (gel s m (fun y => c • f y)) (fun y => c • gel s m f y) (GLs n) := by
  intro g hg
  simp only [gel, Finset.sum_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => epow_smul s m a a c h hg

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `n V _ _ χ f hf hE c`. Use `⟨fun x hx => ?_, fun w => ?_⟩` and prove the remaining obligations. Simplify using `only [Om, Pi.smul_apply, Pi.add_apply, gel_smul _ _ c hf hx, hE _ _ x hx, cas] module`. Proceed by induction on `w with`. Consider the case `nil`.

Introduce `x hx`. Simplify using `[zOp.eq_1, zVal]`. Consider the case `cons p w ih`. Introduce `x hx`. Simplify using `only [zOp.eq_2]`.

Rewrite using `[gel_loc p.1 p.2 ih hx, gel_smul p.1 p.2 _ hf hx]`. Use `beta_reduce`. Rewrite using `[hE _ _ x hx]`. Simplify using `only [zVal, List.map_cons, List.prod_cons, smul_smul]`. Put the polynomial expressions in normal form.
-/
theorem UpperTheory.RealTr.zEig :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (χ : Inf n) (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → IsEig χ f →
      ∀ c : ℂ, (∀ x ∈ GLs n, Om (fun y => c • f y) x = cas χ • c • f x) ∧
        ∀ (w : List (Bool × ℕ)), ∀ x ∈ GLs n, zOp w (fun y => c • f y) x = (c * zVal w χ) • f x := by
  intro n V _ _ χ f hf hE c
  refine ⟨fun x hx => ?_, fun w => ?_⟩
  · simp only [Om, Pi.smul_apply, Pi.add_apply, gel_smul _ _ c hf hx, hE _ _ x hx, cas]
    module
  · induction w with
    | nil =>
      intro x hx
      simp [zOp.eq_1, zVal]
    | cons p w ih =>
      intro x hx
      simp only [zOp.eq_2]
      rw [gel_loc p.1 p.2 ih hx, gel_smul p.1 p.2 _ hf hx]
      beta_reduce
      rw [hE _ _ x hx]
      simp only [zVal, List.map_cons, List.prod_cons, smul_smul]
      ring_nf
