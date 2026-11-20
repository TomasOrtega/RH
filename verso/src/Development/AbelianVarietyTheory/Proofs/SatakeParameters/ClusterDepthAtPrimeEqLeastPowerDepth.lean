import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

/- English proof (translation)
Introduce `D L l hl hlA`. Establish `hl' : (11 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hx : (1 : ℝ) < (l : ℝ) - 1` using `by linarith`. Establish `hA : (0 : ℝ) < LevelStarExponents.lA L` using `by linarith`. Establish `key : ∀ j : ℕ, LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j ↔ ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ ≤ j`.

Introduce `j`. Rewrite using `[Nat.ceil_le, Real.logb_le_iff_le_rpow hx hA, Real.rpow_natCast]`. Establish `hlog : 1 < Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)`. Rewrite using `[Real.lt_logb_iff_rpow_lt hx hA, Real.rpow_one]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hc : 1 ≤ ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊`. Rewrite using `[Nat.one_le_ceil_iff]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hset : {j : ℕ | LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j} = Set.Ici ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊`. Use extensionality with `j`.

Simplify using `only [Set.mem_setOf_eq, Set.mem_Ici]`. Conclude with `key j`. Unfold `jA depth`. Rewrite using `[hset, csInf_Ici, max_eq_right hc]`.
-/
theorem jA_eq_depth : ∀ {D : D7} (L : SizeData₂ D) (l : ℕ), 11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → jA L l = depth L l := by
  intro D L l hl hlA
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hx : (1 : ℝ) < (l : ℝ) - 1 := by linarith
  have hA : (0 : ℝ) < LevelStarExponents.lA L := by linarith
  have key : ∀ j : ℕ, LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j ↔ ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ ≤ j := by
    intro j
    rw [Nat.ceil_le, Real.logb_le_iff_le_rpow hx hA, Real.rpow_natCast]
  have hlog : 1 < Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L) := by
    rw [Real.lt_logb_iff_rpow_lt hx hA, Real.rpow_one]; linarith
  have hc : 1 ≤ ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ := by
    rw [Nat.one_le_ceil_iff]; linarith
  have hset : {j : ℕ | LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j} = Set.Ici ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ := by
    ext j; simp only [Set.mem_setOf_eq, Set.mem_Ici]; exact key j
  unfold jA depth
  rw [hset, csInf_Ici, max_eq_right hc]

end GlobalTheory.HTW.Rec
