import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeContrSelfApply

set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm.FlatAcyc.DbarAdjSq

def contrL {m : ℕ} (i : Fin m) : Ext m →ₗ[ℂ] Ext m where
  toFun := contr i
  map_add' := contr_add i
  map_smul' := contr_smul i

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem contrL_apply {m : ℕ} (i : Fin m) (w : Ext m) : contrL i w = contr i w := rfl

def adjL {g : ℕ} (G : Matrix (Fin g) (Fin g) ℂ) (a : Fin g) : Ext (0 + 0 + g) →ₗ[ℂ] Ext (0 + 0 + g) :=
  -∑ c, G a c • contrL (dzb 0 c)

/- English proof (translation)
Simplify using `[adjL, LinearMap.sum_apply]`.
-/
theorem adjL_apply {g : ℕ} (G : Matrix (Fin g) (Fin g) ℂ) (a : Fin g) (w : Ext (0 + 0 + g)) :
    adjL G a w = -∑ c, G a c • contr (dzb 0 c) w := by
  simp [adjL, LinearMap.sum_apply]

/- English proof (translation)
Establish `key : ∀ b b' : Fin g, adjL G b (adjL G b' w) = ∑ c, ∑ c', (G b c * G b' c') • contr (dzb 0 c) (contr (dzb 0 c') w)`. Introduce `b b'`. Simplify using `only [adjL, LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_neg, map_sum, map_smul, contrL_apply, Finset.smul_sum, smul_smul, neg_neg, Finset.sum_neg_distrib]`. Simplify using `only [Finset.smul_sum, smul_neg, Finset.sum_neg_distrib, neg_neg, smul_smul]`. Use `first`.

Consider the case `rw [Finset.sum_comm (β := Ext (0 + 0 + g))]`. Consider the case `rw [Finset.sum_comm (M := Ext (0 + 0 + g))]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun c' _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.

Rewrite using `[key, key]`. Use `first`. Consider the case `rw [Finset.sum_comm (β := Ext (0 + 0 + g))]`. Consider the case `rw [Finset.sum_comm (M := Ext (0 + 0 + g))]`. Rewrite using `[← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun c' _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[contr_contr, smul_neg, mul_comm]`.
-/
theorem adjL_comm {g : ℕ} (G : Matrix (Fin g) (Fin g) ℂ) (a a' : Fin g) (w : Ext (0 + 0 + g)) :
    adjL G a (adjL G a' w) = -adjL G a' (adjL G a w) := by
  have key : ∀ b b' : Fin g, adjL G b (adjL G b' w) =
      ∑ c, ∑ c', (G b c * G b' c') • contr (dzb 0 c) (contr (dzb 0 c') w) := by
    intro b b'
    simp only [adjL, LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_neg, map_sum,
      map_smul, contrL_apply, Finset.smul_sum, smul_smul, neg_neg, Finset.sum_neg_distrib]
    simp only [Finset.smul_sum, smul_neg, Finset.sum_neg_distrib, neg_neg, smul_smul]
    first
      | rw [Finset.sum_comm (β := Ext (0 + 0 + g))]
      | rw [Finset.sum_comm (M := Ext (0 + 0 + g))]
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [mul_comm]
  rw [key, key]
  first
    | rw [Finset.sum_comm (β := Ext (0 + 0 + g))]
    | rw [Finset.sum_comm (M := Ext (0 + 0 + g))]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [contr_contr, smul_neg, mul_comm]

/- English proof (translation)
The claim follows from `dz_clinear_map_comm ((L.restrictScalars ℝ).toContinuousLinearMap) (fun c w => L.map_smul c w) hF v`.
-/
theorem d10_comp_linearMap {g m : ℕ} (L : Ext m →ₗ[ℂ] Ext m) {F : (Fin g → ℂ) → Ext m} {P : Fin g → ℂ}
    (hF : DifferentiableAt ℝ F P) (v : Fin g → ℂ) :
    d10 (fun Q => L (F Q)) P v = L (d10 F P v) :=
  dz_clinear_map_comm ((L.restrictScalars ℝ).toContinuousLinearMap) (fun c w => L.map_smul c w) hF v

/- English proof (translation)
Simplify using `only [dbarAdjF, adjL_apply, Finset.sum_neg_distrib]`.
-/
theorem dbarAdjF_eq {g : ℕ} (G : Matrix (Fin g) (Fin g) ℂ) (ψ : (Fin g → ℂ) → ℂ)
    (F : (Fin g → ℂ) → Ext (0 + 0 + g)) (z : Fin g → ℂ) :
    dbarAdjF G ψ F z = ∑ a, adjL G a (d10 F z (ev a) + d10 ψ z (ev a) • F z) := by
  simp only [dbarAdjF, adjL_apply, Finset.sum_neg_distrib]

/- English proof (translation)
Introduce `g G ψ f hf hψ hf1 hψ1 hsf hsψ z`. Use `set A : Fin g → (Fin g → ℂ) → Ext (0 + 0 + g) := fun a z => d10 f z (ev a) + d10 ψ z (ev a) • f z with hAdef`. Establish `hA : ∀ a, Differentiable ℝ (A a)` using `fun a => (hf1 _).add ((hψ1 _).smul hf)`. Establish `hE : dbarAdjF G ψ f = fun z => ∑ a', adjL G a' (A a' z)` using `funext (dbarAdjF_eq G ψ f)`. Establish `hd : ∀ a, d10 (dbarAdjF G ψ f) z (ev a) = ∑ a', adjL G a' (d10 (A a') z (ev a))`.

Introduce `a`. Rewrite using `[hE, d10_finset_sum']`. Conclude with `Finset.sum_congr rfl fun a' _ => d10_comp_linearMap _ ((hA a') z) _`. Introduce `a' _`. Conclude with `((adjL G a').restrictScalars ℝ).toContinuousLinearMap.differentiableAt.comp z ((hA a') z)`.

Establish `hdA : ∀ a a', d10 (A a') z (ev a) = d10 (fun z' => d10 f z' (ev a')) z (ev a) + (d10 (fun z' => d10 ψ z' (ev a')) z (ev a) • f z + d10 ψ z (ev a') • d10 f z (ev a))`. Introduce `a a'`. Use `show d10 (fun z' => d10 f z' (ev a') + d10 ψ z' (ev a') • f z') z (ev a) = _`. Rewrite using `[dz_add_vector (G := fun z' => d10 ψ z' (ev a') • f z') ((hf1 _) z) (((hψ1 _) z).smul (hf z)), d10_smul ((hψ1 _) z) (hf z)]`. Use `set B : Fin g → Fin g → Ext (0 + 0 + g) := fun a a' => d10 (fun z' => d10 f z' (ev a')) z (ev a) + (d10 (fun z' => d10 ψ z' (ev a')) z (ev a) • f z + d10 ψ z (ev a') • d10 f z (ev a)) + d10 ψ z (ev a) • A a' z with hBdef`.

Establish `hB : ∀ a a', B a a' = B a' a`. Introduce `a a'`. Simplify using `only [hBdef, hAdef]`. Rewrite using `[hsf z (ev a') (ev a), hsψ z (ev a') (ev a)]`. Simplify using `only [smul_add, smul_smul]`.

Rewrite using `[mul_comm (d10 ψ z (ev a)) (d10 ψ z (ev a'))]`. Normalize the expressions using the abelian group laws. Establish `hX : dbarAdjF G ψ (dbarAdjF G ψ f) z = ∑ a, ∑ a', adjL G a (adjL G a' (B a a'))`. Rewrite using `[dbarAdjF_eq G ψ (dbarAdjF G ψ f) z]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[hd a, dbarAdjF_eq G ψ f z, Finset.smul_sum, ← Finset.sum_add_distrib, map_sum]`. Use `Finset.sum_congr rfl fun a' _ => ?_` and prove the remaining obligations. Rewrite using `[← map_smul, ← map_add, hdA]`. Establish `hneg : dbarAdjF G ψ (dbarAdjF G ψ f) z = -dbarAdjF G ψ (dbarAdjF G ψ f) z` using `by conv_rhs => rw [hX, Finset.sum_comm, ← Finset.sum_neg_distrib]`. Rewrite using `[hX]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun a' _ => ?_` and prove the remaining obligations. Rewrite using `[adjL_comm, hB]`. Use function extensionality and compare the values at `S`.

Establish `h'` using `congrFun hneg S`. Simplify using `only [Pi.neg_apply] at h'`. Use `show dbarAdjF G ψ (dbarAdjF G ψ f) z S = 0`. Take the linear combination `h' / 2`.
-/
theorem dbarAdjF_dbarAdjF : ∀ {g : ℕ} (G : Matrix (Fin g) (Fin g) ℂ) (ψ : (Fin g → ℂ) → ℂ)
    (f : (Fin g → ℂ) → Ext (0 + 0 + g)) (hf : Differentiable ℝ f) (hψ : Differentiable ℝ ψ)
    (hf1 : ∀ v, Differentiable ℝ (fun z => d10 f z v)) (hψ1 : ∀ v, Differentiable ℝ (fun z => d10 ψ z v))
    (hsf : ∀ z v w, d10 (fun z' => d10 f z' v) z w = d10 (fun z' => d10 f z' w) z v)
    (hsψ : ∀ z v w, d10 (fun z' => d10 ψ z' v) z w = d10 (fun z' => d10 ψ z' w) z v)
    (z : Fin g → ℂ), dbarAdjF G ψ (dbarAdjF G ψ f) z = 0 := by
  intro g G ψ f hf hψ hf1 hψ1 hsf hsψ z
  set A : Fin g → (Fin g → ℂ) → Ext (0 + 0 + g) := fun a z => d10 f z (ev a) + d10 ψ z (ev a) • f z
    with hAdef
  have hA : ∀ a, Differentiable ℝ (A a) := fun a => (hf1 _).add ((hψ1 _).smul hf)
  have hE : dbarAdjF G ψ f = fun z => ∑ a', adjL G a' (A a' z) := funext (dbarAdjF_eq G ψ f)
  have hd : ∀ a, d10 (dbarAdjF G ψ f) z (ev a) = ∑ a', adjL G a' (d10 (A a') z (ev a)) := by
    intro a
    rw [hE, d10_finset_sum']
    · exact Finset.sum_congr rfl fun a' _ => d10_comp_linearMap _ ((hA a') z) _
    · intro a' _
      exact ((adjL G a').restrictScalars ℝ).toContinuousLinearMap.differentiableAt.comp z ((hA a') z)
  have hdA : ∀ a a', d10 (A a') z (ev a) = d10 (fun z' => d10 f z' (ev a')) z (ev a) +
      (d10 (fun z' => d10 ψ z' (ev a')) z (ev a) • f z + d10 ψ z (ev a') • d10 f z (ev a)) := by
    intro a a'
    show d10 (fun z' => d10 f z' (ev a') + d10 ψ z' (ev a') • f z') z (ev a) = _
    rw [dz_add_vector (G := fun z' => d10 ψ z' (ev a') • f z') ((hf1 _) z) (((hψ1 _) z).smul (hf z)),
      d10_smul ((hψ1 _) z) (hf z)]
  set B : Fin g → Fin g → Ext (0 + 0 + g) := fun a a' =>
    d10 (fun z' => d10 f z' (ev a')) z (ev a) +
      (d10 (fun z' => d10 ψ z' (ev a')) z (ev a) • f z + d10 ψ z (ev a') • d10 f z (ev a)) +
      d10 ψ z (ev a) • A a' z with hBdef
  have hB : ∀ a a', B a a' = B a' a := by
    intro a a'
    simp only [hBdef, hAdef]
    rw [hsf z (ev a') (ev a), hsψ z (ev a') (ev a)]
    simp only [smul_add, smul_smul]
    rw [mul_comm (d10 ψ z (ev a)) (d10 ψ z (ev a'))]
    abel
  have hX : dbarAdjF G ψ (dbarAdjF G ψ f) z = ∑ a, ∑ a', adjL G a (adjL G a' (B a a')) := by
    rw [dbarAdjF_eq G ψ (dbarAdjF G ψ f) z]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hd a, dbarAdjF_eq G ψ f z, Finset.smul_sum, ← Finset.sum_add_distrib, map_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← map_smul, ← map_add, hdA]
  have hneg : dbarAdjF G ψ (dbarAdjF G ψ f) z = -dbarAdjF G ψ (dbarAdjF G ψ f) z := by
    conv_rhs => rw [hX, Finset.sum_comm, ← Finset.sum_neg_distrib]
    rw [hX]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [adjL_comm, hB]
  funext S
  have h' := congrFun hneg S
  simp only [Pi.neg_apply] at h'
  show dbarAdjF G ψ (dbarAdjF G ψ f) z S = 0
  linear_combination h' / 2

end GlobalTheory.TorsionForm.FlatAcyc.DbarAdjSq
