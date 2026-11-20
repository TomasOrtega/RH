import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Proof.baseSize_bounds_along_family

open Formalism.BasicNotions

/- English proof (translation)
Introduce `W0 hW`. Establish `hls : Formalism.MainNotions.TwistedPlaces.lStar L = LevelStarExponents.lStar L` using `rfl`. Establish `hl0 : 0 < LevelStarExponents.lStar L` using `hls ▸ Formalism.MainNotions.TwistedPlaces.lStar_pos L`. Establish `hgt : L.sc.b' < LevelStarExponents.lStar L` using `hls ▸ Formalism.MainNotions.TwistedPlaces.lStar_gt L P`. Establish `hleb : LevelStarExponents.lStar L ≤ L.sc.b` using `hls ▸ Formalism.MainNotions.TwistedPlaces.lStar_le_b L`.

Establish `hw` using `Formalism.MainNotions.TwistedPlaces.w''_le_b' L`. Establish `hb'0` using `Formalism.MainNotions.TwistedPlaces.b'_pos L`. Establish `hx` using `L.sc.one_lt_alt`. Establish `hbx : L.sc.b' / L.sc.x ≤ L.sc.b'` using `div_le_self hb'0.le hx.le`. Establish `hfl0 : (0 : ℝ) ≤ ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ)`.

Conclude with `Int.floor_nonneg.2 (div_nonneg hb'0.le (by linarith))` after adjusting the coercions. Establish `hfl1 : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' / L.sc.x` using `Int.floor_le _`. Establish `h3 : 3 * LevelStarExponents.lStar L ≤ L.sc.b`. Establish `hp2` using `Formalism.MainNotions.TwistedPlaces.lStar_part2 L`. Rewrite `hp2` using `[hls]`.

Establish `hk` using `Formalism.MainNotions.TwistedPlaces.m_le_k D`. Establish `hm` using `Formalism.MainNotions.TwistedPlaces.m_ge_one D`. Establish `hn` using `Formalism.MainNotions.TwistedPlaces.n_ge_one D`. Establish `ht : (7 : ℝ) ≤ D.R.t`. Use `Formalism.MainNotions.TwistedPlaces.t_ge D` as an intermediate fact.

Use `Formalism.MainNotions.TwistedPlaces.k_le_r D` as an intermediate fact. Use `Formalism.MainNotions.TwistedPlaces.k_ge_five D` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hS` using `L.Sc_pos`. Establish `hLg` using `Formalism.MainNotions.TwistedPlaces.Lg_nonneg L`.

Establish `hn2 : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2` using `by nlinarith`. Establish `hA : 3 * (D.R.m : ℝ) ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + Formalism.MainNotions.TwistedPlaces.large₂ L)`. Establish `e1 : (3 : ℝ) ≤ (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + Formalism.MainNotions.TwistedPlaces.large₂ L)` using `by nlinarith`. Establish `e2 : (D.R.m : ℝ) * 3 ≤ (D.R.k : ℝ) * ((D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + Formalism.MainNotions.TwistedPlaces.large₂ L))` using `mul_le_mul hk e1 (by norm_num) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: LevelStarExponents.lStar L * (3 * (D.R.m : ℝ)) ≤ D.R.m * L.sc.b` using `le_trans (mul_le_mul_of_nonneg_left hA hl0.le) hp2`. Use the polynomial consequences of the given equalities and inequalities. Establish `hη` using `L.etaSz_pos`. Establish `hm` using `Formalism.MainNotions.TwistedPlaces.m_ge_one D`. Establish `hq : 0 ≤ L.sc.b / LevelStarExponents.lStar L` using `div_nonneg (by linarith) hl0.le`.

Establish `hlow : 2 * (L.sc.b / LevelStarExponents.lStar L) + (D.R.t : ℝ) / 2 + 3 ≤ L.sc.w'' D.R.n`. Establish `h1` using `P.h0_ge.1`. Establish `h2 : LevelStarExponents.h0 L ≤ L.etaSz` using `div_le_self hη.le hm`. Establish `h3'` using `P.mteta`. Establish `ht : (0 : ℝ) ≤ D.R.t` using `by positivity`.

Establish `h4 : L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz`. Establish `: (1 : ℝ) ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1)` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `h7 : 12 * L.sc.b / LevelStarExponents.lStar L = 12 * (L.sc.b / LevelStarExponents.lStar L)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Break down `hW with rfl | rfl | ⟨t, rfl⟩` into its components or cases. Conclude with `⟨le_trans hlow (by linarith), le_rfl⟩`. Conclude with `⟨hlow, by linarith⟩`. Establish `h1` using `L.bT_ge t`. Establish `h2` using `Formalism.MainNotions.TwistedPlaces.bT_le_two_mul_b' L P t`.

Conclude with `⟨by linarith, by linarith⟩`.
-/
theorem baseSize_bounds {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) :
    ∀ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes L,
      2 * (L.sc.b / LevelStarExponents.lStar L) + (D.R.t : ℝ) / 2 + 3 ≤ W0 ∧ W0 ≤ L.sc.b := by
  intro W0 hW
  have hls : Formalism.MainNotions.TwistedPlaces.lStar L = LevelStarExponents.lStar L := rfl
  have hl0 : 0 < LevelStarExponents.lStar L := hls ▸ Formalism.MainNotions.TwistedPlaces.lStar_pos L
  have hgt : L.sc.b' < LevelStarExponents.lStar L := hls ▸ Formalism.MainNotions.TwistedPlaces.lStar_gt L P
  have hleb : LevelStarExponents.lStar L ≤ L.sc.b := hls ▸ Formalism.MainNotions.TwistedPlaces.lStar_le_b L
  have hw := Formalism.MainNotions.TwistedPlaces.w''_le_b' L
  have hb'0 := Formalism.MainNotions.TwistedPlaces.b'_pos L
  have hx := L.sc.one_lt_alt
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hx.le
  have hfl0 : (0 : ℝ) ≤ ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.floor_nonneg.2 (div_nonneg hb'0.le (by linarith))
  have hfl1 : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' / L.sc.x := Int.floor_le _

  have h3 : 3 * LevelStarExponents.lStar L ≤ L.sc.b := by
    have hp2 := Formalism.MainNotions.TwistedPlaces.lStar_part2 L
    rw [hls] at hp2
    have hk := Formalism.MainNotions.TwistedPlaces.m_le_k D
    have hm := Formalism.MainNotions.TwistedPlaces.m_ge_one D
    have hn := Formalism.MainNotions.TwistedPlaces.n_ge_one D
    have ht : (7 : ℝ) ≤ D.R.t := by
      have := Formalism.MainNotions.TwistedPlaces.t_ge D; have := Formalism.MainNotions.TwistedPlaces.k_le_r D; have := Formalism.MainNotions.TwistedPlaces.k_ge_five D; linarith
    have hS := L.Sc_pos
    have hLg := Formalism.MainNotions.TwistedPlaces.Lg_nonneg L
    have hn2 : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by nlinarith
    have hA : 3 * (D.R.m : ℝ) ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + Formalism.MainNotions.TwistedPlaces.large₂ L) := by
      have e1 : (3 : ℝ) ≤ (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + Formalism.MainNotions.TwistedPlaces.large₂ L) := by nlinarith
      have e2 : (D.R.m : ℝ) * 3 ≤ (D.R.k : ℝ) * ((D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + Formalism.MainNotions.TwistedPlaces.large₂ L)) :=
        mul_le_mul hk e1 (by norm_num) (by linarith)
      linarith
    have : LevelStarExponents.lStar L * (3 * (D.R.m : ℝ)) ≤ D.R.m * L.sc.b :=
      le_trans (mul_le_mul_of_nonneg_left hA hl0.le) hp2
    nlinarith

  have hη := L.etaSz_pos
  have hm := Formalism.MainNotions.TwistedPlaces.m_ge_one D
  have hq : 0 ≤ L.sc.b / LevelStarExponents.lStar L := div_nonneg (by linarith) hl0.le
  have hlow : 2 * (L.sc.b / LevelStarExponents.lStar L) + (D.R.t : ℝ) / 2 + 3 ≤ L.sc.w'' D.R.n := by
    have h1 := P.h0_ge.1
    have h2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη.le hm
    have h3' := P.mteta
    have ht : (0 : ℝ) ≤ D.R.t := by positivity
    have h4 : L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by
      have : (1 : ℝ) ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) := by nlinarith
      nlinarith
    have h7 : 12 * L.sc.b / LevelStarExponents.lStar L = 12 * (L.sc.b / LevelStarExponents.lStar L) := by ring
    linarith
  rcases hW with rfl | rfl | ⟨t, rfl⟩
  · exact ⟨le_trans hlow (by linarith), le_rfl⟩
  · exact ⟨hlow, by linarith⟩
  · have h1 := L.bT_ge t
    have h2 := Formalism.MainNotions.TwistedPlaces.bT_le_two_mul_b' L P t
    exact ⟨by linarith, by linarith⟩

/- English proof (translation)
Introduce `eps Fm x hx a W0 hW`. Conclude with `baseSize_bounds (Fm.L x a) (Fm.params x hx a) W0 hW`.
-/
theorem main : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ), Fm.x1 < x → ∀ (a : Fm.Ix x), ∀ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes (Fm.L x a),
    2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + ((Fm.D x a).R.t : ℝ) / 2 + 3 ≤ W0 ∧ W0 ≤ (Fm.L x a).sc.b := by
  intro eps Fm x hx a W0 hW
  exact baseSize_bounds (Fm.L x a) (Fm.params x hx a) W0 hW

end GlobalTheory.Proof.baseSize_bounds_along_family
