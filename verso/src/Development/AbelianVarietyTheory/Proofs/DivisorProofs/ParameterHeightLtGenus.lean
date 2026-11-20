import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie

namespace GlobalTheory.ExpTie

/- English proof (translation)
Establish `hx : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hL0 : 0 < L.sc.L` using `by unfold Scale.L; exact Real.rpow_pos_of_pos hx0 _`. Establish `hb : L.sc.b = Real.exp L.sc.L` using `rfl`. Establish `hb1 : 1 < L.sc.b`.

Use `Real.add_one_lt_exp (ne_of_gt hL0)` as an intermediate fact. Rewrite using `[hb]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb0 : 0 < L.sc.b` using `by linarith`. Establish `hb'0 : 0 < L.sc.b'`.

Unfold `Scale.b' Scale.a Scale.X' Scale.b`. Check the signs of the components of the expression. Establish `hS0 : 0 < L.Sc` using `L.Sc_pos`. Establish `hη0 : 0 < L.etaSz` using `L.etaSz_pos`. Establish `hm2 : 2 ≤ D.R.m` using `D.R.two_le_m`.

Establish `hmk : D.R.m + 3 ≤ D.R.k` using `D.R.m_add_three_le_k`. Establish `ht1 : 1 ≤ D.R.t` using `by have := D.R.three_m_lt_t; omega`. Establish `hn1 : 1 ≤ D.R.n` using `Formalism.HC.Frame.ord_pos _`. Establish `hmR : (2 : ℝ) ≤ (D.R.m : ℝ)` using `by exact_mod_cast hm2`. Establish `hmkR : (D.R.m : ℝ) + 3 ≤ (D.R.k : ℝ)` using `by exact_mod_cast hmk`.

Establish `htR : (1 : ℝ) ≤ (D.R.t : ℝ)` using `by exact_mod_cast ht1`. Establish `hnR : (1 : ℝ) ≤ (D.R.n : ℝ)` using `by exact_mod_cast hn1`. Use `set den : ℝ := (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 + (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) with hden`. Establish `hd1 : 0 ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2` using `by positivity`. Establish `hn2 : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2` using `by nlinarith`.

Establish `hd2 : (D.R.m : ℝ) ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L)`. Establish `h1 : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L)` using `by nlinarith`. Establish `hk0 : (0 : ℝ) ≤ (D.R.k : ℝ)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hdm : (D.R.m : ℝ) ≤ den` using `by rw [hden]; linarith`.

Establish `hden0 : 0 < den` using `by linarith`. Establish `hls : LevelStarExponents.lStar L = (D.R.m : ℝ) * L.sc.b / den` using `rfl`. Establish `hl0 : 0 < LevelStarExponents.lStar L` using `by rw [hls]; positivity`. Establish `hlb : LevelStarExponents.lStar L ≤ L.sc.b`. Rewrite using `[hls, div_le_iff₀ hden0]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hbl : 0 < L.sc.b / LevelStarExponents.lStar L` using `div_pos hb0 hl0`. Establish `h1` using `P.lstar1`. Establish `h2` using `P.t_le_eta`. Establish `hh : (parOf L j).h = L.sc.b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1` using `rfl`.

Establish `hh3 : (parOf L j).h < 3 * L.sc.b + 1` using `by rw [hh]; linarith`. Establish `hkb : 1 ≤ (D.R.k : ℝ) * L.sc.b` using `by nlinarith`. Establish `hk8 : (D.R.k : ℝ) * L.sc.b ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8` using `le_self_pow₀ hkb (by norm_num)`. Establish `h3 : 3 * L.sc.b + 1 ≤ (D.R.k : ℝ) * L.sc.b` using `by nlinarith`. Take `⟨Y, hY, -, -, hg⟩` from `P.g_Y`.

Use `(hg a).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem parOf_h_lt_g {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (j : Fin D.R.m) (a : Fin 2) :
    (parOf L j).h < (D.host.g a : ℝ) := by
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hL0 : 0 < L.sc.L := by unfold Scale.L; exact Real.rpow_pos_of_pos hx0 _
  have hb : L.sc.b = Real.exp L.sc.L := rfl
  have hb1 : 1 < L.sc.b := by
    have := Real.add_one_lt_exp (ne_of_gt hL0)
    rw [hb]; linarith
  have hb0 : 0 < L.sc.b := by linarith
  have hb'0 : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X' Scale.b
    positivity
  have hS0 : 0 < L.Sc := L.Sc_pos
  have hη0 : 0 < L.etaSz := L.etaSz_pos
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hmk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have ht1 : 1 ≤ D.R.t := by have := D.R.three_m_lt_t; omega
  have hn1 : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
  have hmR : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hm2
  have hmkR : (D.R.m : ℝ) + 3 ≤ (D.R.k : ℝ) := by exact_mod_cast hmk
  have htR : (1 : ℝ) ≤ (D.R.t : ℝ) := by exact_mod_cast ht1
  have hnR : (1 : ℝ) ≤ (D.R.n : ℝ) := by exact_mod_cast hn1

  set den : ℝ := (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 +
    (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) with hden
  have hd1 : 0 ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 := by positivity
  have hn2 : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by nlinarith
  have hd2 : (D.R.m : ℝ) ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) := by
    have h1 : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) := by nlinarith
    have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) := by positivity
    nlinarith
  have hdm : (D.R.m : ℝ) ≤ den := by rw [hden]; linarith
  have hden0 : 0 < den := by linarith
  have hls : LevelStarExponents.lStar L = (D.R.m : ℝ) * L.sc.b / den := rfl
  have hl0 : 0 < LevelStarExponents.lStar L := by rw [hls]; positivity
  have hlb : LevelStarExponents.lStar L ≤ L.sc.b := by
    rw [hls, div_le_iff₀ hden0]
    nlinarith
  have hbl : 0 < L.sc.b / LevelStarExponents.lStar L := div_pos hb0 hl0
  have h1 := P.lstar1
  have h2 := P.t_le_eta

  have hh : (parOf L j).h = L.sc.b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1 := rfl
  have hh3 : (parOf L j).h < 3 * L.sc.b + 1 := by rw [hh]; linarith

  have hkb : 1 ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
  have hk8 : (D.R.k : ℝ) * L.sc.b ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := le_self_pow₀ hkb (by norm_num)
  have h3 : 3 * L.sc.b + 1 ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
  obtain ⟨Y, hY, -, -, hg⟩ := P.g_Y
  have := (hg a).1
  linarith

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ⟨0, fun x hx _ i _ _ _ j a => parOf_h_lt_g (Fm.L x i) (Fm.params x hx i) j a⟩⟩⟩`.
-/
theorem atPts_h_lt_g : AtPts fun Fm x _ i _ =>
    ∀ (j : Fin (Fm.D x i).R.m) a, (GlobalTheory.ExpTie.parOf (Fm.L x i) j).h < ((Fm.D x i).host.g a : ℝ) :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, fun x hx _ i _ _ _ j a => parOf_h_lt_g (Fm.L x i) (Fm.params x hx i) j a⟩⟩⟩

end GlobalTheory.ExpTie

end
