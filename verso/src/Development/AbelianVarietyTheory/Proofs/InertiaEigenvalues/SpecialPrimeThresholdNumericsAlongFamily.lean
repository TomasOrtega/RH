import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory

/- English proof (translation)
Introduce `eps Fm x hx a`. Establish `P` using `Fm.params x hx a`. Use `set L := Fm.L x a with hLdef`. Establish `e : Formalism.MainNotions.TwistedPlaces.lStar L = LevelStarExponents.lStar L` using `rfl`. Establish `hls` using `Formalism.MainNotions.TwistedPlaces.lStar_pos L`.

Establish `h7` using `Formalism.MainNotions.TwistedPlaces.seven_lt_lStar L P`. Establish `hmD` using `Formalism.MainNotions.TwistedPlaces.lStar_mul_Den L`. Establish `hDen` using `Formalism.MainNotions.TwistedPlaces.Den_ge L`. Establish `hDp` using `Formalism.MainNotions.TwistedPlaces.Den_pos L`. Rewrite `hls`, `h7`, `hmD` using `[e]`.

Establish `h1` using `P.lstar1`. Establish `h2` using `P.lstar2`. Establish `hb` using `Formalism.MainNotions.TwistedPlaces.one_le_b L`. Establish `he` using `L.etaSz_pos`. Establish `hS` using `L.Sc_pos`.

Establish `ht` using `Formalism.MainNotions.TwistedPlaces.t_ge_one (Fm.D x a)`. Establish `hk` using `Formalism.MainNotions.TwistedPlaces.k_ge_five (Fm.D x a)`. Establish `hmk` using `Formalism.MainNotions.TwistedPlaces.m_le_k (Fm.D x a)`. Establish `hm1` using `Formalism.MainNotions.TwistedPlaces.m_ge_one (Fm.D x a)`. Establish `hn` using `Formalism.MainNotions.TwistedPlaces.n_ge_one (Fm.D x a)`.

Establish `hL1` using `Formalism.MainNotions.TwistedPlaces.L_ge_one L`. Establish `hbl : 0 ≤ L.sc.b / LevelStarExponents.lStar L` using `div_nonneg (by linarith) hls.le`. Establish `h8 : 8 * L.sc.b / LevelStarExponents.lStar L = 8 * (L.sc.b / LevelStarExponents.lStar L)` using `by ring`. Rewrite `h2` using `[h8]`. Establish `hDen2 : 2 * ((Fm.D x a).R.m : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.Den L`.

Unfold `Formalism.MainNotions.TwistedPlaces.Den`. Establish `hn2 : (1 : ℝ) ≤ ((Fm.D x a).R.n : ℝ) ^ 2` using `by nlinarith`. Establish `hLg0 : (0 : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.large₂ L` using `by linarith`. Establish `h0 : (0 : ℝ) ≤ ((Fm.D x a).R.n : ℝ) * ((Fm.D x a).R.t : ℝ) ^ 2 * (((Fm.D x a).R.N (Fm.D x a).R.m : ℝ) + (Fm.D x a).R.t) * Formalism.MainNotions.TwistedPlaces.large₂ L ^ 2` using `by positivity`. Establish `hA : (2 : ℝ) ≤ L.Sc + (Fm.D x a).R.t + Formalism.MainNotions.TwistedPlaces.large₂ L` using `by linarith`.

Establish `hB : (1 : ℝ) ≤ ((Fm.D x a).R.k : ℝ) * ((Fm.D x a).R.n : ℝ) ^ 2` using `by nlinarith`. Establish `: 2 * ((Fm.D x a).R.k : ℝ) * ((Fm.D x a).R.n : ℝ) ^ 2 ≤ ((Fm.D x a).R.k : ℝ) * ((Fm.D x a).R.n : ℝ) ^ 2 * (L.Sc + (Fm.D x a).R.t + Formalism.MainNotions.TwistedPlaces.large₂ L)`. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Establish `hlb : 2 * LevelStarExponents.lStar L ≤ L.sc.b` using `by nlinarith`.

Establish `hb'` using `Formalism.MainNotions.TwistedPlaces.b'_pos L`. Establish `hq : L.sc.b / LevelStarExponents.lStar L * LevelStarExponents.lStar L = L.sc.b` using `div_mul_cancel₀ _ hls.ne'`. Use `⟨P.t_le_eta, he, hbl, hS.le, by linarith, h2, ?_⟩` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem lStar_numerics_at_record : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ), Fm.x1 < x → ∀ (a : Fm.Ix x),
    ((Fm.D x a).R.t : ℝ) ≤ (Fm.L x a).etaSz ∧ 0 < (Fm.L x a).etaSz ∧ 0 ≤ (Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a) ∧
    0 ≤ (Fm.L x a).Sc ∧ 1 < LevelStarExponents.lStar (Fm.L x a) ∧
    2 * (Fm.L x a).etaSz + (Fm.D x a).R.t + 8 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + 7 < LevelStarExponents.lStar (Fm.L x a) ∧
    ((Fm.L x a).sc.b + (Fm.L x a).Sc + 2 * (Fm.L x a).etaSz + 3) * LevelStarExponents.lStar (Fm.L x a) ≤
      2 * (Fm.L x a).sc.b * (LevelStarExponents.lStar (Fm.L x a) - 1) := by
  intro eps Fm x hx a
  have P := Fm.params x hx a
  set L := Fm.L x a with hLdef
  have e : Formalism.MainNotions.TwistedPlaces.lStar L = LevelStarExponents.lStar L := rfl
  have hls := Formalism.MainNotions.TwistedPlaces.lStar_pos L
  have h7 := Formalism.MainNotions.TwistedPlaces.seven_lt_lStar L P
  have hmD := Formalism.MainNotions.TwistedPlaces.lStar_mul_Den L
  have hDen := Formalism.MainNotions.TwistedPlaces.Den_ge L
  have hDp := Formalism.MainNotions.TwistedPlaces.Den_pos L
  rw [e] at hls h7 hmD
  have h1 := P.lstar1
  have h2 := P.lstar2
  have hb := Formalism.MainNotions.TwistedPlaces.one_le_b L
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have ht := Formalism.MainNotions.TwistedPlaces.t_ge_one (Fm.D x a)
  have hk := Formalism.MainNotions.TwistedPlaces.k_ge_five (Fm.D x a)
  have hmk := Formalism.MainNotions.TwistedPlaces.m_le_k (Fm.D x a)
  have hm1 := Formalism.MainNotions.TwistedPlaces.m_ge_one (Fm.D x a)
  have hn := Formalism.MainNotions.TwistedPlaces.n_ge_one (Fm.D x a)
  have hL1 := Formalism.MainNotions.TwistedPlaces.L_ge_one L
  have hbl : 0 ≤ L.sc.b / LevelStarExponents.lStar L := div_nonneg (by linarith) hls.le
  have h8 : 8 * L.sc.b / LevelStarExponents.lStar L = 8 * (L.sc.b / LevelStarExponents.lStar L) := by ring
  rw [h8] at h2

  have hDen2 : 2 * ((Fm.D x a).R.m : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.Den L := by
    unfold Formalism.MainNotions.TwistedPlaces.Den
    have hn2 : (1 : ℝ) ≤ ((Fm.D x a).R.n : ℝ) ^ 2 := by nlinarith
    have hLg0 : (0 : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.large₂ L := by linarith
    have h0 : (0 : ℝ) ≤ ((Fm.D x a).R.n : ℝ) * ((Fm.D x a).R.t : ℝ) ^ 2 *
        (((Fm.D x a).R.N (Fm.D x a).R.m : ℝ) + (Fm.D x a).R.t) * Formalism.MainNotions.TwistedPlaces.large₂ L ^ 2 := by positivity
    have hA : (2 : ℝ) ≤ L.Sc + (Fm.D x a).R.t + Formalism.MainNotions.TwistedPlaces.large₂ L := by linarith
    have hB : (1 : ℝ) ≤ ((Fm.D x a).R.k : ℝ) * ((Fm.D x a).R.n : ℝ) ^ 2 := by nlinarith
    have : 2 * ((Fm.D x a).R.k : ℝ) * ((Fm.D x a).R.n : ℝ) ^ 2 ≤
        ((Fm.D x a).R.k : ℝ) * ((Fm.D x a).R.n : ℝ) ^ 2 * (L.Sc + (Fm.D x a).R.t + Formalism.MainNotions.TwistedPlaces.large₂ L) := by
      nlinarith
    nlinarith
  have hlb : 2 * LevelStarExponents.lStar L ≤ L.sc.b := by nlinarith
  have hb' := Formalism.MainNotions.TwistedPlaces.b'_pos L
  have hq : L.sc.b / LevelStarExponents.lStar L * LevelStarExponents.lStar L = L.sc.b := div_mul_cancel₀ _ hls.ne'
  refine ⟨P.t_le_eta, he, hbl, hS.le, by linarith, h2, ?_⟩
  nlinarith

end GlobalTheory
