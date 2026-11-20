import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.MonicFintype

open Polynomial

namespace PI.SqfDivDeg.W

/- English proof (translation)
Introduce `g r _ hr hg a ha1 ha2 T hT`. Establish `h1` using `hA g a ha1`. Establish `h2` using `hA g (r - a) (by omega)`. Establish `h3` using `hB g r a (by omega) T hT`. Establish `e : (g : ℝ) ^ r = (g : ℝ) ^ a * (g : ℝ) ^ (r - a)`.

Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `h1' : ((g : ℝ) ^ a) ≤ 2 * ((Rt g a).card : ℝ)` using `by exact_mod_cast h1`. Establish `h2' : ((g : ℝ) ^ (r - a)) ≤ 2 * ((Rt g (r - a)).card : ℝ)` using `by exact_mod_cast h2`.

Establish `p1 : (0 : ℝ) ≤ (g : ℝ) ^ a` using `by positivity`. Establish `p2 : (0 : ℝ) ≤ (g : ℝ) ^ (r - a)` using `by positivity`. Establish `hm : (g : ℝ) ^ a * (g : ℝ) ^ (r - a) ≤ (2 * ((Rt g a).card : ℝ)) * (2 * ((Rt g (r - a)).card : ℝ))` using `mul_le_mul h1' h2' p2 (by linarith)`. Rewrite `h3`, the goal using `[e]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sqfDivDeg_of (hA : RootDense) (hB : MainCount) : PI.SqfDivDeg.Claim := by
  intro g r _ hr hg a ha1 ha2 T hT
  have h1 := hA g a ha1
  have h2 := hA g (r - a) (by omega)
  have h3 := hB g r a (by omega) T hT
  have e : (g : ℝ) ^ r = (g : ℝ) ^ a * (g : ℝ) ^ (r - a) := by
    rw [← pow_add]; congr 1; omega
  have h1' : ((g : ℝ) ^ a) ≤ 2 * ((Rt g a).card : ℝ) := by exact_mod_cast h1
  have h2' : ((g : ℝ) ^ (r - a)) ≤ 2 * ((Rt g (r - a)).card : ℝ) := by exact_mod_cast h2
  have p1 : (0 : ℝ) ≤ (g : ℝ) ^ a := by positivity
  have p2 : (0 : ℝ) ≤ (g : ℝ) ^ (r - a) := by positivity
  have hm : (g : ℝ) ^ a * (g : ℝ) ^ (r - a) ≤
      (2 * ((Rt g a).card : ℝ)) * (2 * ((Rt g (r - a)).card : ℝ)) :=
    mul_le_mul h1' h2' p2 (by linarith)
  rw [e] at h3 ⊢
  nlinarith

end PI.SqfDivDeg.W
