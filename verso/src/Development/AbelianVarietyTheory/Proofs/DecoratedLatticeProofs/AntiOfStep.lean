import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SizesLe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.HdNc

/- English proof (translation)
Establish `key : ∀ (d a : ℕ) (ha : a + d < r), f ⟨a + d, ha⟩ ≤ f ⟨a, by omega⟩`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro a ha`. Conclude with `le_rfl`.

Consider the case `succ d ih`. Introduce `a ha`. Establish `h1` using `h ⟨a + d, by omega⟩ (by simp only []; omega)`. Establish `h2` using `ih a (by omega)`. Establish `e : (⟨(⟨a + d, by omega⟩ : Fin r).1 + 1, by simp only []; omega⟩ : Fin r) = ⟨a + (d + 1), ha⟩` using `by ext; simp only []; omega`.

Rewrite `h1` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `a b hab`. Establish `hd` using `key (b.1 - a.1) a.1 (by omega)`. Establish `e1 : (⟨a.1 + (b.1 - a.1), by omega⟩ : Fin r) = b` using `by ext; simp only []; omega`.

Rewrite `hd` using `[e1]`. Conclude with `hd`.
-/
theorem anti_of_step {r : ℕ} (f : Fin r → ℝ) (h : ∀ (i : Fin r) (hi : i.1 + 1 < r), f ⟨i.1 + 1, hi⟩ < f i) :
    ∀ a b : Fin r, a ≤ b → f b ≤ f a := by
  have key : ∀ (d a : ℕ) (ha : a + d < r), f ⟨a + d, ha⟩ ≤ f ⟨a, by omega⟩ := by
    intro d
    induction d with
    | zero => intro a ha; exact le_rfl
    | succ d ih =>
      intro a ha
      have h1 := h ⟨a + d, by omega⟩ (by simp only []; omega)
      have h2 := ih a (by omega)
      have e : (⟨(⟨a + d, by omega⟩ : Fin r).1 + 1, by simp only []; omega⟩ : Fin r) = ⟨a + (d + 1), ha⟩ := by
        ext; simp only []; omega
      rw [e] at h1
      linarith
  intro a b hab
  have hd := key (b.1 - a.1) a.1 (by omega)
  have e1 : (⟨a.1 + (b.1 - a.1), by omega⟩ : Fin r) = b := by ext; simp only []; omega
  rw [e1] at hd
  exact hd

/- English proof (translation)
Unfold `lamS`. Rewrite using `[dif_neg (by simp only []; omega)]`. Establish `e : R.k - 1 + j - (R.k - 1) = j` using `by omega`. Simplify using `only [e, dif_pos hj]`.
-/
theorem lamS_node (R : Ranks) (P : HCParam R) (j : ℕ) (hj : j < R.m) (hi : R.k - 1 + j < R.r) :
    lamS R P ⟨R.k - 1 + j, hi⟩ = -(((P.b ⟨j, hj⟩ : ℚ)) : ℝ) := by
  unfold lamS
  rw [dif_neg (by simp only []; omega)]
  have e : R.k - 1 + j - (R.k - 1) = j := by omega
  simp only [e, dif_pos hj]

/- English proof (translation)
Assume the negation of the conclusion as `hb`. Use `push_neg at hb`. Apply `hne` to reduce the goal to its premises. Establish `ha : a.1 < R.k - 1`. Establish `: a.1 < b.1` using `hab`.

Use linear arithmetic over natural numbers and integers. Unfold `epsS`. Rewrite using `[if_pos ha]`. Distinguish the cases in `h1 : b.1 < R.k - 1`. Rewrite using `[if_pos h1]`.

Rewrite using `[if_neg h1]`. Establish `: b.1 - (R.k - 1) = 0` using `by omega`. Simplify using `[this]`.
-/
theorem node_of_sign (R : Ranks) (a b : Fin R.r) (hab : a < b) (hne : epsS R a ≠ epsS R b) : R.k ≤ b.1 := by
  by_contra hb
  push_neg at hb
  apply hne
  have ha : a.1 < R.k - 1 := by
    have : a.1 < b.1 := hab
    omega
  unfold epsS
  rw [if_pos ha]
  by_cases h1 : b.1 < R.k - 1
  · rw [if_pos h1]
  · rw [if_neg h1]
    have : b.1 - (R.k - 1) = 0 := by omega
    simp [this]

/- English proof (translation)
Establish `hkb` using `node_of_sign D.R a b hab hne`. Establish `hbr : b.1 < D.R.r` using `b.2`. Establish `hm2` using `D.R.two_le_m`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`.

Establish `hgap` using `GlobalTheory.Core.Rk.HdGap.gap_of H τ (b.1 - D.R.k) (by omega)`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlam, -, -, hCl⟩` from `H`. Establish `hstep : ∀ (i : Fin D.R.r) (hi : i.1 + 1 < D.R.r), lamS D.R (D.hc τ) ⟨i.1 + 1, hi⟩ < lamS D.R (D.hc τ) i`. Introduce `i hi`. Use `hlam τ i hi` as an intermediate fact.

Establish `h0 : (0 : ℝ) ≤ Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 4 + (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set j := b.1 - D.R.k with hj`. Establish `hj1 : j + 1 < D.R.m` using `by omega`. Establish `e1 : b = ⟨D.R.k - 1 + (j + 1), by omega⟩` using `by ext; simp only []; omega`.

Establish `hc : (⟨D.R.k - 1 + j, by omega⟩ : Fin D.R.r) ≤ b`. Rewrite using `[Fin.le_def]`. Simplify using `only []`. Use linear arithmetic over natural numbers and integers. Establish `hac : a ≤ (⟨D.R.k - 1 + j, by omega⟩ : Fin D.R.r)`.

Rewrite using `[Fin.le_def]`. Simplify using `only []`. Establish `: a.1 < b.1` using `hab`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `anti_of_step _ hstep _ _ hac`.

Establish `h2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ≤ (((D.hc τ).b ⟨j + 1, hj1⟩ : ℚ) : ℝ) - (((D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ)` using `hgap`. Rewrite `h1` using `[lamS_node D.R (D.hc τ) j (by omega) (by omega)]`. Rewrite using `[e1, lamS_node D.R (D.hc τ) (j + 1) hj1 (by omega)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gap_lt {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (H : GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (τ : D.what₂.Tau) (a b : Fin D.R.r) (hab : a < b) (hne : epsS D.R a ≠ epsS D.R b) :
    Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ≤ lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) b := by
  have hkb := node_of_sign D.R a b hab hne
  have hbr : b.1 < D.R.r := b.2
  have hm2 := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hgap := GlobalTheory.Core.Rk.HdGap.gap_of H τ (b.1 - D.R.k) (by omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlam, -, -, hCl⟩ := H
  have hstep : ∀ (i : Fin D.R.r) (hi : i.1 + 1 < D.R.r),
      lamS D.R (D.hc τ) ⟨i.1 + 1, hi⟩ < lamS D.R (D.hc τ) i := by
    intro i hi
    have := hlam τ i hi
    have h0 : (0 : ℝ) ≤ Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 4 + (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 := by positivity
    linarith
  set j := b.1 - D.R.k with hj
  have hj1 : j + 1 < D.R.m := by omega
  have e1 : b = ⟨D.R.k - 1 + (j + 1), by omega⟩ := by ext; simp only []; omega
  have hc : (⟨D.R.k - 1 + j, by omega⟩ : Fin D.R.r) ≤ b := by
    rw [Fin.le_def]; simp only []; omega
  have hac : a ≤ (⟨D.R.k - 1 + j, by omega⟩ : Fin D.R.r) := by
    rw [Fin.le_def]; simp only []; have : a.1 < b.1 := hab; omega
  have h1 := anti_of_step _ hstep _ _ hac
  have h2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ≤
      (((D.hc τ).b ⟨j + 1, hj1⟩ : ℚ) : ℝ) - (((D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) := hgap
  rw [lamS_node D.R (D.hc τ) j (by omega) (by omega)] at h1
  rw [e1, lamS_node D.R (D.hc τ) (j + 1) hj1 (by omega)]
  linarith

/- English proof (translation)
Use `⟨1801, fun D L C' Cl Cg cb Cu cT CT hCl H X => ?_⟩` and prove the remaining obligations. Establish `HL` using `H.2.2.1`. Take `⟨hS, hr⟩` from `GlobalTheory.Core.Rk.HdGap.scale_of hCl HL`. Establish `hr1 : (1 : ℝ) ≤ (D.R.r : ℝ)` using `by exact_mod_cast (show 1 ≤ D.R.r by omega)`. Establish `h4 : 100 * (D.R.r : ℝ) ^ 4 ≤ 1801 * (D.R.r : ℝ) ^ 19`.

Establish `: (D.R.r : ℝ) ^ 4 ≤ (D.R.r : ℝ) ^ 19` using `pow_le_pow_right₀ hr1 (by norm_num)`. Establish `: (0 : ℝ) ≤ (D.R.r : ℝ) ^ 4` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : ∀ (τ : D.what₂.Tau) (a b : Fin D.R.r), epsS D.R a ≠ epsS D.R b → 100 * (D.R.r : ℝ) ^ 4 ≤ |lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) b|`. Introduce `τ a b hne`.

Establish `hp : (0 : ℝ) ≤ 100 * (D.R.r : ℝ) ^ 4` using `by positivity`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Use `gap_lt HL τ a b h hne` as an intermediate fact. Rewrite using `[abs_of_nonneg (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `absurd (by rw [h]) hne`. Use `gap_lt HL τ b a h (Ne.symm hne)` as an intermediate fact. Rewrite using `[abs_sub_comm, abs_of_nonneg (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `v a b hab`.

Rewrite `hab` using `[X.eps_eq, X.eps_eq]`. Rewrite using `[X.lam_eq, X.lam_eq]`. Conclude with `key _ _ _ hab`.
-/
theorem hd_nc : ∃ Cl₀ : ℝ, ∀ (D : D7) (L C' Cl Cg cb Cu cT CT : ℝ), Cl₀ ≤ Cl → HD D L C' Cl Cg cb Cu cT CT →
    ∀ X : Formalism.L2.SG.HidaSetting.HidaSetting D, GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) := by
  refine ⟨1801, fun D L C' Cl Cg cb Cu cT CT hCl H X => ?_⟩
  have HL := H.2.2.1
  obtain ⟨hS, hr⟩ := GlobalTheory.Core.Rk.HdGap.scale_of hCl HL
  have hr1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by exact_mod_cast (show 1 ≤ D.R.r by omega)
  have h4 : 100 * (D.R.r : ℝ) ^ 4 ≤ 1801 * (D.R.r : ℝ) ^ 19 := by
    have : (D.R.r : ℝ) ^ 4 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hr1 (by norm_num)
    have : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 4 := by positivity
    linarith
  have key : ∀ (τ : D.what₂.Tau) (a b : Fin D.R.r), epsS D.R a ≠ epsS D.R b →
      100 * (D.R.r : ℝ) ^ 4 ≤ |lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) b| := by
    intro τ a b hne
    have hp : (0 : ℝ) ≤ 100 * (D.R.r : ℝ) ^ 4 := by positivity
    rcases lt_trichotomy a b with h | h | h
    · have := gap_lt HL τ a b h hne
      rw [abs_of_nonneg (by linarith)]
      linarith
    · exact absurd (by rw [h]) hne
    · have := gap_lt HL τ b a h (Ne.symm hne)
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
  intro v a b hab
  rw [X.eps_eq, X.eps_eq] at hab
  rw [X.lam_eq, X.lam_eq]
  exact key _ _ _ hab

end GlobalTheory.Core.Rk.HdNc
