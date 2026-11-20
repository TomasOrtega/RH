import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DominantRearrangementProperties

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [cf]`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, ((cfBasic n).2.2.2.1 _ _ (c a) y).1, ((cfBasic n).2.2.2.1 (g a) 0 (c a) y).2, ih]`.
-/
private theorem cf_sum_smul {n : ℕ} (s : Finset (Wt n)) (c : Wt n → ℂ) (g : Wt n → FR n) (y : Wt n) :
    cf (∑ x ∈ s, c x • g x) y = ∑ x ∈ s, c x * cf (g x) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cf]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ((cfBasic n).2.2.2.1 _ _ (c a) y).1,
      ((cfBasic n).2.2.2.1 (g a) 0 (c a) y).2, ih]

/- English proof (translation)
Distinguish the cases in `hy : Function.Injective y`. Take `⟨w, hw⟩` from `((rearr n).2.1 y).2.1`. Establish `ha : Antitone (y ∘ ⇑w)` using `hw ▸ ((rearr n).2.1 y).1`. Establish `hs : StrictAnti (y ∘ ⇑w)` using `ha.strictAnti_of_injective (hy.comp w.injective)`. Establish `e` using `h _ hs`.

Rewrite `e` using `[hf w y, hg w y]`. Establish `hne : sg w ≠ 0`. Unfold `sg`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h1 | h1 <;> simp [h1]`. Conclude with `mul_left_cancel₀ hne e`.

Take `⟨a, b, hab, hne⟩` from `Function.not_injective_iff.mp hy`. Establish `hfix : y ∘ ⇑(Equiv.swap a b) = y`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, Equiv.swap_apply_def]`. Use `split_ifs with h1 h2`.

Substitute `h1` using the available equality. Conclude with `hab.symm`. Substitute `h2` using the available equality. Conclude with `hab`. Both sides reduce to the same expression.

Establish `hsg : sg (Equiv.swap a b) = -1`. Simplify using `[sg, Equiv.Perm.sign_swap hne]`. Establish `e1` using `hf (Equiv.swap a b) y`. Establish `e2` using `hg (Equiv.swap a b) y`. Rewrite `e1`, `e2` using `[hfix, hsg]`.

Establish `z1 : cf f y = 0` using `by linear_combination e1 / 2`. Establish `z2 : cf g y = 0` using `by linear_combination e2 / 2`. Rewrite using `[z1, z2]`.
-/
private theorem asym_eq_of_strictAnti {n : ℕ} {f g : FR n} (hf : ASym f) (hg : ASym g)
    (h : ∀ y : Wt n, StrictAnti y → cf f y = cf g y) (y : Wt n) : cf f y = cf g y := by
  by_cases hy : Function.Injective y
  · obtain ⟨w, hw⟩ := ((rearr n).2.1 y).2.1
    have ha : Antitone (y ∘ ⇑w) := hw ▸ ((rearr n).2.1 y).1
    have hs : StrictAnti (y ∘ ⇑w) := ha.strictAnti_of_injective (hy.comp w.injective)
    have e := h _ hs
    rw [hf w y, hg w y] at e
    have hne : sg w ≠ 0 := by
      unfold sg
      rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h1 | h1 <;> simp [h1]
    exact mul_left_cancel₀ hne e
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hy
    have hfix : y ∘ ⇑(Equiv.swap a b) = y := by
      funext i
      simp only [Function.comp_apply, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · subst h1; exact hab.symm
      · subst h2; exact hab
      · rfl
    have hsg : sg (Equiv.swap a b) = -1 := by
      simp [sg, Equiv.Perm.sign_swap hne]
    have e1 := hf (Equiv.swap a b) y
    have e2 := hg (Equiv.swap a b) y
    rw [hfix, hsg] at e1 e2
    have z1 : cf f y = 0 := by linear_combination e1 / 2
    have z2 : cf g y = 0 := by linear_combination e2 / 2
    rw [z1, z2]

/- English proof (translation)
Introduce `n f hf`. Use `set s := f.coeff.support.filter (fun x => StrictAnti x) with hs`. Establish `hmem : ∀ x, x ∈ s ↔ cf f x ≠ 0 ∧ StrictAnti x`. Introduce `x`. Simplify using `[hs, cf, Finsupp.mem_support_iff]`.

Use `⟨s, fun x hx => ⟨((hmem x).1 hx).2, ((hmem x).1 hx).1⟩, ?_⟩` and prove the remaining obligations. Establish `hR : ASym (∑ x ∈ s, cf f x • alt x)`. Introduce `w z`. Rewrite using `[cf_sum_smul, cf_sum_smul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[(cfBasic n).2.2.2.2.2.2.2.2.1 x w z]`. Expand and normalize the polynomial expressions, which then agree. Apply `(cfBasic n).2.2.1` to reduce the goal to its premises. Introduce `y`. Apply `asym_eq_of_strictAnti hf hR` to reduce the goal to its premises.

Introduce `y hy`. Rewrite using `[cf_sum_smul, Finset.sum_eq_single y, ((cfBasic n).2.2.2.2.2.2.2.2.2.2.2.1 y hy).1, mul_one]`. Introduce `x hx hxy`. Rewrite using `[((cfBasic n).2.2.2.2.2.2.2.2.2.2.2.1 x ((hmem x).1 hx).2).2 y hy (Ne.symm hxy), mul_zero]`. Introduce `hy'`.

Establish `: cf f y = 0`. Assume the negation of the conclusion as `hc`. Conclude with `hy' ((hmem y).2 ⟨hc, hy⟩)`. Rewrite using `[this, zero_mul]`.
-/
theorem UpperTheory.RealTr.asymExp :
    ∀ (n : ℕ) (f : FR n), ASym f → ∃ s : Finset (Wt n), (∀ x ∈ s, StrictAnti x ∧ cf f x ≠ 0) ∧ f = ∑ x ∈ s, cf f x • alt x := by
  intro n f hf
  classical
  set s := f.coeff.support.filter (fun x => StrictAnti x) with hs
  have hmem : ∀ x, x ∈ s ↔ cf f x ≠ 0 ∧ StrictAnti x := by
    intro x
    simp [hs, cf, Finsupp.mem_support_iff]
  refine ⟨s, fun x hx => ⟨((hmem x).1 hx).2, ((hmem x).1 hx).1⟩, ?_⟩
  have hR : ASym (∑ x ∈ s, cf f x • alt x) := by
    intro w z
    rw [cf_sum_smul, cf_sum_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [(cfBasic n).2.2.2.2.2.2.2.2.1 x w z]
    ring
  apply (cfBasic n).2.2.1
  intro y
  apply asym_eq_of_strictAnti hf hR
  intro y hy
  rw [cf_sum_smul, Finset.sum_eq_single y, ((cfBasic n).2.2.2.2.2.2.2.2.2.2.2.1 y hy).1, mul_one]
  · intro x hx hxy
    rw [((cfBasic n).2.2.2.2.2.2.2.2.2.2.2.1 x ((hmem x).1 hx).2).2 y hy (Ne.symm hxy), mul_zero]
  · intro hy'
    have : cf f y = 0 := by
      by_contra hc
      exact hy' ((hmem y).2 ⟨hc, hy⟩)
    rw [this, zero_mul]
