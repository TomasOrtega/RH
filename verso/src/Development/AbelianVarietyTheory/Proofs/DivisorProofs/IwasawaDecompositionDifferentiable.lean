import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityHermitianMetrics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobiDensityWeightedThetaIntegralZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqFormDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeWeightedRootProductSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentTriangularFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni

open Filter Topology MeasureTheory Matrix
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (emb jacDens)
open GlobalTheory.FlagFibre (Low uni)
open GlobalTheory.FlagFormDeg (apolar)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell

def diffOnRing {m : ℕ} (s : Set (Low m → ℂ)) : Subring (s → ℂ) where
  carrier := {f | ∃ F : (Low m → ℂ) → ℂ, ∀ x : s, DifferentiableAt ℂ F x ∧ F x = f x}
  mul_mem' := by
    rintro f g ⟨F, hF⟩ ⟨G, hG⟩
    exact ⟨fun y => F y * G y, fun x => ⟨(hF x).1.mul (hG x).1, by simp [(hF x).2, (hG x).2]⟩⟩
  one_mem' := ⟨fun _ => 1, fun _ => ⟨differentiableAt_const _, rfl⟩⟩
  add_mem' := by
    rintro f g ⟨F, hF⟩ ⟨G, hG⟩
    exact ⟨fun y => F y + G y, fun x => ⟨(hF x).1.add (hG x).1, by simp [(hF x).2, (hG x).2]⟩⟩
  zero_mem' := ⟨fun _ => 0, fun _ => ⟨differentiableAt_const _, rfl⟩⟩
  neg_mem' := by
    rintro f ⟨F, hF⟩
    exact ⟨fun y => -F y, fun x => ⟨(hF x).1.neg, by simp [(hF x).2]⟩⟩

def diffOnEval {m : ℕ} {s : Set (Low m → ℂ)} (x : s) : diffOnRing s →+* ℂ :=
  (Pi.evalRingHom (fun _ : s => ℂ) x).comp (diffOnRing s).subtype

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diffOnEval_apply {m : ℕ} {s : Set (Low m → ℂ)} (x : s) (f : diffOnRing s) :
    diffOnEval x f = f.1 x := rfl

/- English proof (translation)
Take `⟨F, hF⟩` from `f.2`. Set `g : diffOnRing s` to `⟨fun x => (f.1 x)⁻¹, ⟨fun y => (F y)⁻¹, fun x => ⟨(hF x).1.inv (by rw [(hF x).2]; exact h x), by simp [(hF x).2]⟩⟩⟩`. Conclude with `isUnit_iff_exists_inv.2 ⟨g, Subtype.ext (funext fun x => mul_inv_cancel₀ (h x))⟩`.
-/
theorem diffOnRing_isUnit {m : ℕ} {s : Set (Low m → ℂ)} (f : diffOnRing s) (h : ∀ x, f.1 x ≠ 0) :
    IsUnit f := by
  obtain ⟨F, hF⟩ := f.2
  let g : diffOnRing s := ⟨fun x => (f.1 x)⁻¹, ⟨fun y => (F y)⁻¹, fun x =>
    ⟨(hF x).1.inv (by rw [(hF x).2]; exact h x), by simp [(hF x).2]⟩⟩⟩
  exact isUnit_iff_exists_inv.2 ⟨g, Subtype.ext (funext fun x => mul_inv_cancel₀ (h x))⟩

/- English proof (translation)
Distinguish the cases in `h : c < k`. Establish `: (fun y : Low m → ℂ => uni y k c) = fun y => y ⟨(k, c), h⟩`. Use function extensionality and compare the values at `y`. Rewrite using `[← uniR_eq_uni, uniR_apply, dif_pos h]`. Rewrite using `[this]`.

Use `fun_prop`. Establish `: (fun y : Low m → ℂ => uni y k c) = fun _ => if k = c then (1 : ℂ) else 0`. Use function extensionality and compare the values at `y`. Rewrite using `[← uniR_eq_uni, uniR_apply, dif_neg h]`. Rewrite using `[this]`.

Conclude with `differentiable_const _`.
-/
theorem differentiable_uni_apply {m : ℕ} (k c : Fin m) :
    Differentiable ℂ fun x : Low m → ℂ => uni x k c := by
  by_cases h : c < k
  · have : (fun y : Low m → ℂ => uni y k c) = fun y => y ⟨(k, c), h⟩ := by
      funext y; rw [← uniR_eq_uni, uniR_apply, dif_pos h]
    rw [this]; fun_prop
  · have : (fun y : Low m → ℂ => uni y k c) = fun _ => if k = c then (1 : ℂ) else 0 := by
      funext y; rw [← uniR_eq_uni, uniR_apply, dif_neg h]
    rw [this]; exact differentiable_const _

/- English proof (translation)
Introduce `m g`. Set `s : Set (Low m → ℂ)` to `{x | ∀ l : Fin (m + 1), ((g * uni x).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0}`. Establish `hd : ∀ a c, Differentiable ℂ fun y : Low m → ℂ => (g * uni y) a c`. Introduce `a c`. Establish `hu` using `fun k => differentiable_uni_apply (m := m) k c`.

Simplify using `only [Matrix.mul_apply]`. Use `fun_prop`. Set `A : Matrix (Fin m) (Fin m) (diffOnRing s)` to `Matrix.of fun a c => ⟨fun x => (g * uni x.1) a c, ⟨fun y => (g * uni y) a c, fun x => ⟨hd a c x, rfl⟩⟩⟩`. Establish `hA : ∀ x : s, A.map (diffOnEval x) = g * uni x.1`. Introduce `x`.

Use extensionality with `a c`. Both sides reduce to the same expression. Establish `hmin : ∀ l : Fin (m + 1), IsUnit (A.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det`. Introduce `l`. Apply `diffOnRing_isUnit` to reduce the goal to its premises.

Introduce `x`. Rewrite using `[← diffOnEval_apply, RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, hA]`. Conclude with `x.2 l`. Take `⟨n, M, hM, hMu, hAe⟩` from `exists_lu (diffOnRing s) m A hmin`. Use `choose Fn hFn using fun l => (n l).2`.

Use `choose FM hFM using fun a c => (M a c).2`. Use `⟨fun y l => Fn l y, fun y => Matrix.of fun a c => FM a c y, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Set `xs : s` to `⟨x, hx⟩`. Establish `hB : (Matrix.of fun a c => FM a c x) = M.map (diffOnEval xs)`.

Use extensionality with `a c`. Conclude with `(hFM a c xs).2`. Establish `hφ : (fun l => Fn l x) = fun l => diffOnEval xs (n l)` using `funext fun l => (hFn l xs).2`. Establish `key : A.map (diffOnEval xs) = (uniR n * M).map (diffOnEval xs)` using `by rw [← hAe]`. Rewrite `key` using `[hA xs, Matrix.map_mul, map_uniR]`.

Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (Matrix.of fun a c => FM a c x).BlockTriangular id`. Rewrite using `[hB]`. Introduce `i j hij`. Simplify using `[hM hij]`.

Use `show IsUnit (Matrix.of fun a c => FM a c x).det`. Rewrite using `[hB, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `hMu.map _`. Use `show g * uni x = uni (fun l => Fn l x) * Matrix.of fun a c => FM a c x`. Rewrite using `[hB, hφ, ← uniR_eq_uni]`.

Conclude with `key`. Conclude with `differentiableAt_pi.2 fun l => (hFn l xs).1`. Introduce `a c`. Conclude with `(show DifferentiableAt ℂ (FM a c) x from (hFM a c xs).1)`.
-/
theorem exists_lu_differentiable : ∀ (m : ℕ) (g : Matrix (Fin m) (Fin m) ℂ), ∃ (φ : (Low m → ℂ) → Low m → ℂ) (B : (Low m → ℂ) → Matrix (Fin m) (Fin m) ℂ), ∀ x : Low m → ℂ, (∀ l : Fin (m + 1), ((g * uni x).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0) → (B x).BlockTriangular id ∧ IsUnit (B x).det ∧ g * uni x = uni (φ x) * B x ∧ DifferentiableAt ℂ φ x ∧ ∀ a c, DifferentiableAt ℂ (fun y => B y a c) x := by
  intro m g
  let s : Set (Low m → ℂ) := {x | ∀ l : Fin (m + 1),
    ((g * uni x).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0}
  have hd : ∀ a c, Differentiable ℂ fun y : Low m → ℂ => (g * uni y) a c := by
    intro a c
    have hu := fun k => differentiable_uni_apply (m := m) k c
    simp only [Matrix.mul_apply]
    fun_prop
  let A : Matrix (Fin m) (Fin m) (diffOnRing s) := Matrix.of fun a c =>
    ⟨fun x => (g * uni x.1) a c, ⟨fun y => (g * uni y) a c, fun x => ⟨hd a c x, rfl⟩⟩⟩
  have hA : ∀ x : s, A.map (diffOnEval x) = g * uni x.1 := by
    intro x; ext a c; rfl
  have hmin : ∀ l : Fin (m + 1), IsUnit (A.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det := by
    intro l
    apply diffOnRing_isUnit
    intro x
    rw [← diffOnEval_apply, RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, hA]
    exact x.2 l
  obtain ⟨n, M, hM, hMu, hAe⟩ := exists_lu (diffOnRing s) m A hmin
  choose Fn hFn using fun l => (n l).2
  choose FM hFM using fun a c => (M a c).2
  refine ⟨fun y l => Fn l y, fun y => Matrix.of fun a c => FM a c y, ?_⟩
  intro x hx
  let xs : s := ⟨x, hx⟩
  have hB : (Matrix.of fun a c => FM a c x) = M.map (diffOnEval xs) := by
    ext a c; exact (hFM a c xs).2
  have hφ : (fun l => Fn l x) = fun l => diffOnEval xs (n l) := funext fun l => (hFn l xs).2
  have key : A.map (diffOnEval xs) = (uniR n * M).map (diffOnEval xs) := by rw [← hAe]
  rw [hA xs, Matrix.map_mul, map_uniR] at key
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (Matrix.of fun a c => FM a c x).BlockTriangular id
    rw [hB]; intro i j hij; simp [hM hij]
  · show IsUnit (Matrix.of fun a c => FM a c x).det
    rw [hB, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hMu.map _
  · show g * uni x = uni (fun l => Fn l x) * Matrix.of fun a c => FM a c x
    rw [hB, hφ, ← uniR_eq_uni]; exact key
  · exact differentiableAt_pi.2 fun l => (hFn l xs).1
  · intro a c; exact (show DifferentiableAt ℂ (FM a c) x from (hFM a c xs).1)

end GlobalTheory.FlagCell
