import Mathlib
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph

set_option autoImplicit false

noncomputable section

open Set Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder

namespace GlobalTheory.LineCos

def hform (G : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2 → ℂ) : ℂ :=
  ∑ i, ∑ j, a i * starRingEnd ℂ (b j) * G i j

def lineVec (s : Bool) (x : ℂ) : Fin 2 → ℂ := if s then ![x, 1] else ![1, x]

def cosSq (s : Bool) (G : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) : ℝ :=
  ‖hform G (lineVec s x) (Pi.single 0 1)‖ ^ 2 / ((hform G (lineVec s x) (lineVec s x)).re * (G 0 0).re)

def base {d : ℕ} (z : V (d + 1)) : Fin d → ℂ := fun i => z (Fin.castSucc i)

def fib {d : ℕ} (z : V (d + 1)) : ℂ := z (Fin.last d)

/- English proof (translation)
Simplify using `only [hform, dotProduct, mulVec, Fin.sum_univ_two, Function.comp_apply, Pi.star_apply, RCLike.star_def, Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_self (G : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin 2 → ℂ) :
    hform G a a = star (starRingEnd ℂ ∘ a) ⬝ᵥ (G *ᵥ (starRingEnd ℂ ∘ a)) := by
  simp only [hform, dotProduct, mulVec, Fin.sum_univ_two, Function.comp_apply, Pi.star_apply, RCLike.star_def,
    Complex.conj_conj]
  ring

/- English proof (translation)
Establish `hne : (starRingEnd ℂ ∘ a) ≠ 0` using `fun h => ha (funext fun i => by`. Simplify using `using congrFun h i)`. Use `hG.dotProduct_mulVec_pos hne` as an intermediate fact. Rewrite using `[hform_self]`. Conclude with `(Complex.pos_iff.1 this).1`.
-/
theorem re_hform_pos {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) {a : Fin 2 → ℂ} (ha : a ≠ 0) :
    0 < (hform G a a).re := by
  have hne : (starRingEnd ℂ ∘ a) ≠ 0 := fun h => ha (funext fun i => by
    simpa using congrFun h i)
  have := hG.dotProduct_mulVec_pos hne
  rw [hform_self]
  exact (Complex.pos_iff.1 this).1

/- English proof (translation)
Introduce `h`. Consider the cases of `s`. Simplify `congrFun h 0` using `[lineVec]`. Simplify `congrFun h 1` using `[lineVec]`.
-/
theorem lineVec_ne_zero (s : Bool) (x : ℂ) : lineVec s x ≠ 0 := by
  intro h
  cases s
  · simpa [lineVec] using congrFun h 0
  · simpa [lineVec] using congrFun h 1

/- English proof (translation)
Use `re_hform_pos hG (a := Pi.single 0 1) (by simp)` as an intermediate fact. Simplify `this` using `[hform, Fin.sum_univ_two, Pi.single_apply]`.
-/
theorem re_corner_pos {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) : 0 < (G 0 0).re := by
  have := re_hform_pos hG (a := Pi.single 0 1) (by simp)
  simpa [hform, Fin.sum_univ_two, Pi.single_apply] using this

/- English proof (translation)
Establish `he : ∀ i j, ContinuousOn (fun z => G (base z) i j) O` using `fun i j => (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hc)`. Establish `hx : Continuous (fun z : V (d + 1) => fib z)`. Unfold `fib`. Use `fun_prop`. Establish `hw : ∀ i, Continuous (fun z : V (d + 1) => lineVec s (fib z) i)` using `fun i => by`.

Consider the cases of `s`. Use `fin_cases i`. Conclude with `continuous_const`. Conclude with `hx`. Use `fin_cases i`.

Conclude with `hx`. Conclude with `continuous_const`. Establish `hh : ∀ (b : V (d + 1) → Fin 2 → ℂ), (∀ j, Continuous fun z => b z j) → ContinuousOn (fun z => hform (G (base z)) (lineVec s (fib z)) (b z)) O` using `fun b hb => by`. Unfold `hform`. Use `continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_` and prove the remaining obligations.

Conclude with `(((hw i).mul ((Complex.continuous_conj).comp (hb j))).continuousOn).mul (he i j)`. Establish `hn : ContinuousOn (fun z => ‖hform (G (base z)) (lineVec s (fib z)) (Pi.single (0 : Fin 2) (1 : ℂ))‖ ^ 2) O` using `(hh (fun _ => Pi.single (0 : Fin 2) (1 : ℂ)) fun j => continuous_const).norm.pow 2`. Establish `hd : ContinuousOn (fun z => (hform (G (base z)) (lineVec s (fib z)) (lineVec s (fib z))).re * (G (base z) 0 0).re) O` using `(Complex.continuous_re.comp_continuousOn (hh (fun z => lineVec s (fib z)) hw)).mul (Complex.continuous_re.comp_continuousOn (he 0 0))`. Establish `h0 : ∀ z ∈ O, (hform (G (base z)) (lineVec s (fib z)) (lineVec s (fib z))).re * (G (base z) 0 0).re ≠ 0` using `fun z hz => (mul_pos (re_hform_pos (hp z hz) (lineVec_ne_zero s _)) (re_corner_pos (hp z hz))).ne'`. Conclude with `hn.div hd h0`.
-/
theorem continuousOn_cosSq {d : ℕ} {O : Set (V (d + 1))} {G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ} (s : Bool)
    (hc : ContinuousOn (fun z => G (base z)) O) (hp : ∀ z ∈ O, (G (base z)).PosDef) :
    ContinuousOn (fun z => cosSq s (G (base z)) (fib z)) O := by
  have he : ∀ i j, ContinuousOn (fun z => G (base z) i j) O := fun i j =>
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hc)
  have hx : Continuous (fun z : V (d + 1) => fib z) := by
    unfold fib
    fun_prop
  have hw : ∀ i, Continuous (fun z : V (d + 1) => lineVec s (fib z) i) := fun i => by
    cases s
    · fin_cases i
      · exact continuous_const
      · exact hx
    · fin_cases i
      · exact hx
      · exact continuous_const
  have hh : ∀ (b : V (d + 1) → Fin 2 → ℂ), (∀ j, Continuous fun z => b z j) →
      ContinuousOn (fun z => hform (G (base z)) (lineVec s (fib z)) (b z)) O := fun b hb => by
    unfold hform
    refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
    exact (((hw i).mul ((Complex.continuous_conj).comp (hb j))).continuousOn).mul (he i j)
  have hn : ContinuousOn (fun z => ‖hform (G (base z)) (lineVec s (fib z)) (Pi.single (0 : Fin 2) (1 : ℂ))‖ ^ 2) O :=
    (hh (fun _ => Pi.single (0 : Fin 2) (1 : ℂ)) fun j => continuous_const).norm.pow 2
  have hd : ContinuousOn (fun z => (hform (G (base z)) (lineVec s (fib z)) (lineVec s (fib z))).re * (G (base z) 0 0).re) O :=
    (Complex.continuous_re.comp_continuousOn (hh (fun z => lineVec s (fib z)) hw)).mul (Complex.continuous_re.comp_continuousOn (he 0 0))
  have h0 : ∀ z ∈ O, (hform (G (base z)) (lineVec s (fib z)) (lineVec s (fib z))).re * (G (base z) 0 0).re ≠ 0 :=
    fun z hz => (mul_pos (re_hform_pos (hp z hz) (lineVec_ne_zero s _)) (re_corner_pos (hp z hz))).ne'
  exact hn.div hd h0

end GlobalTheory.LineCos
