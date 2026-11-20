import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ComponentModelWeightDimensionDictionary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
  GlobalTheory.CompHS GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RecGaps

open Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.NTheta

variable {R : Ranks}

/- English proof (translation)
Take `⟨a, ha⟩` from `lamAt_int h n`. Take `⟨b, hb⟩` from `lamAt_int h (n + 1)`. Establish `hl` using `lamAt_lt h n hn`. Rewrite `hl`, the goal using `[ha, hb]`. Use `⟨a - b, by push_cast; ring, ?_⟩` and prove the remaining obligations.

Establish `: b < a` using `by exact_mod_cast hl`. Use linear arithmetic over natural numbers and integers.
-/
theorem lam_step (h : HCParam R) (n : ℕ) (hn : n + 1 < R.r) :
    ∃ z : ℤ, lamAt h n - lamAt h (n + 1) = z ∧ 1 ≤ z := by
  obtain ⟨a, ha⟩ := lamAt_int h n
  obtain ⟨b, hb⟩ := lamAt_int h (n + 1)
  have hl := lamAt_lt h n hn
  rw [ha, hb] at hl ⊢
  refine ⟨a - b, by push_cast; ring, ?_⟩
  have : b < a := by exact_mod_cast hl
  omega

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro _`. Simplify using the standard rewrite rules. Consider the case `succ d ih`.

Introduce `hd`. Establish `h1` using `ih (by omega)`. Take `⟨z, hz, hz1⟩` from `lam_step h (a + d) (by omega)`. Establish `: (1 : ℚ) ≤ z` using `by exact_mod_cast hz1`. Rewrite `hd`, the goal using `[← add_assoc]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lam_mono (h : HCParam R) (a : ℕ) : ∀ d : ℕ, a + d < R.r → lamAt h (a + d) + d ≤ lamAt h a := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    obtain ⟨z, hz, hz1⟩ := lam_step h (a + d) (by omega)
    have : (1 : ℚ) ≤ z := by exact_mod_cast hz1
    rw [← add_assoc] at hd ⊢
    push_cast
    linarith

/- English proof (translation)
Unfold `lamAt`. Rewrite using `[dif_neg (by omega)]`. Establish `e : R.k - 1 + l - (R.k - 1) = l` using `by omega`. Rewrite using `[dif_pos (by omega)]`. Use `congr 2`.

Conclude with `Fin.ext e`.
-/
theorem lam_b (h : HCParam R) (l : ℕ) (hl : l < R.m) : lamAt h (R.k - 1 + l) = -h.b ⟨l, hl⟩ := by
  unfold lamAt
  rw [dif_neg (by omega)]
  have e : R.k - 1 + l - (R.k - 1) = l := by omega
  rw [dif_pos (by omega)]
  congr 2
  exact Fin.ext e

/- English proof (translation)
Take `⟨s1, s2, s3⟩` from `P.sig_gaps t`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hm` using `D.R.two_le_m`. Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Distinguish the cases in `h1 : n + 1 < D.R.k - 1`.

Establish `e1 : lamAt (D.hc t) n = (D.hc t).v ⟨n, by omega⟩` using `by unfold lamAt; rw [dif_pos (by omega)]`. Establish `e2 : lamAt (D.hc t) (n + 1) = (D.hc t).v ⟨n + 1, h1⟩` using `by unfold lamAt; rw [dif_pos h1]`. Rewrite using `[e1, e2]`. Conclude with `s1 n h1`. Distinguish the cases in `h2 : n + 1 = D.R.k - 1`.

Establish `e1 : lamAt (D.hc t) n = (D.hc t).v ⟨D.R.k - 2, by omega⟩`. Unfold `lamAt; rw [dif_pos (by omega)]; congr 1; exact Fin.ext (by simp; omega)`. Establish `e2 : lamAt (D.hc t) (n + 1) = -(D.hc t).b ⟨0, by omega⟩`. Use `lam_b (D.hc t) 0 (by omega)` as an intermediate fact. Rewrite using `[show n + 1 = D.R.k - 1 + 0 by omega]; exact this`.

Rewrite using `[e1, e2, sub_neg_eq_add]; exact s2 (by omega) (by omega)`. Establish `hj : n + 1 - (D.R.k - 1) < D.R.m` using `by omega`. Establish `e1 : lamAt (D.hc t) n = -(D.hc t).b ⟨n - (D.R.k - 1), by omega⟩`. Use `lam_b (D.hc t) (n - (D.R.k - 1)) (by omega)` as an intermediate fact. Rewrite `this` using `[show D.R.k - 1 + (n - (D.R.k - 1)) = n by omega]`. Then use the resulting hypothesis.

Establish `e2 : lamAt (D.hc t) (n + 1) = -(D.hc t).b ⟨n - (D.R.k - 1) + 1, by omega⟩`. Use `lam_b (D.hc t) (n - (D.R.k - 1) + 1) (by omega)` as an intermediate fact. Rewrite `this` using `[show D.R.k - 1 + (n - (D.R.k - 1) + 1) = n + 1 by omega]`. Then use the resulting hypothesis. Rewrite using `[e1, e2, neg_sub_neg]; exact s3 (n - (D.R.k - 1)) (by omega)`.
-/
theorem lam_gapS {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (t : D.what₂.Tau) (n : ℕ) (hn : n + 1 < D.R.r) :
    LevelStarExponents.gapS D P.Cgap < ((lamAt (D.hc t) n - lamAt (D.hc t) (n + 1) : ℚ) : ℝ) := by
  obtain ⟨s1, s2, s3⟩ := P.sig_gaps t
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  by_cases h1 : n + 1 < D.R.k - 1
  · have e1 : lamAt (D.hc t) n = (D.hc t).v ⟨n, by omega⟩ := by unfold lamAt; rw [dif_pos (by omega)]
    have e2 : lamAt (D.hc t) (n + 1) = (D.hc t).v ⟨n + 1, h1⟩ := by unfold lamAt; rw [dif_pos h1]
    rw [e1, e2]; exact s1 n h1
  · by_cases h2 : n + 1 = D.R.k - 1
    · have e1 : lamAt (D.hc t) n = (D.hc t).v ⟨D.R.k - 2, by omega⟩ := by
        unfold lamAt; rw [dif_pos (by omega)]; congr 1; exact Fin.ext (by simp; omega)
      have e2 : lamAt (D.hc t) (n + 1) = -(D.hc t).b ⟨0, by omega⟩ := by
        have := lam_b (D.hc t) 0 (by omega)
        rw [show n + 1 = D.R.k - 1 + 0 by omega]; exact this
      rw [e1, e2, sub_neg_eq_add]; exact s2 (by omega) (by omega)
    · have hj : n + 1 - (D.R.k - 1) < D.R.m := by omega
      have e1 : lamAt (D.hc t) n = -(D.hc t).b ⟨n - (D.R.k - 1), by omega⟩ := by
        have := lam_b (D.hc t) (n - (D.R.k - 1)) (by omega)
        rwa [show D.R.k - 1 + (n - (D.R.k - 1)) = n by omega] at this
      have e2 : lamAt (D.hc t) (n + 1) = -(D.hc t).b ⟨n - (D.R.k - 1) + 1, by omega⟩ := by
        have := lam_b (D.hc t) (n - (D.R.k - 1) + 1) (by omega)
        rwa [show D.R.k - 1 + (n - (D.R.k - 1) + 1) = n + 1 by omega] at this
      rw [e1, e2, neg_sub_neg]; exact s3 (n - (D.R.k - 1)) (by omega)

section Ent

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
  {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

open GlobalTheory.BigTop Formalism.IndefR.Links

/- English proof (translation)
The claim follows from `D.sp.W_sigval _ (by omega) (by have := i.2; omega) _`.
-/
theorem sig_Wc (i : Fin D.R.m) (t : D.what₂.Tau) :
    (Wc D i).sig (Formalism.BasicNotions.TH.tauE D t) = D.R.sigW ((i : ℕ) + 1) :=
  D.sp.W_sigval _ (by omega) (by have := i.2; omega) _

/- English proof (translation)
Establish `h` using `P.h0_ge.2.2.2.2.1`. Establish `: (0 : ℝ) ≤ 4 * (D.R.N D.R.m : ℝ) ^ 3` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem two_nodeGap_add_six_le_roundingConstant (P : ParameterChoice' D L) : 2 * (D.R.t : ℝ) + 6 ≤ LevelStarExponents.h0 L := by
  have h := P.h0_ge.2.2.2.2.1
  have : (0 : ℝ) ≤ 4 * (D.R.N D.R.m : ℝ) ^ 3 := by positivity
  linarith

/- English proof (translation)
Establish `hnn : 0 ≤ ⌊lamAt (D.hc t) j + (D.hc t).e i - (((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - (j + 1)) - ((D.R.t : ℚ) + 1) / 2⌋`. Apply `Int.floor_nonneg.2` to reduce the goal to its premises. Establish `hsw : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ)` using `by simp only [Ranks.sigW]; omega`. Take `⟨d, hd⟩ : ∃ d, D.R.k + (i : ℕ) = j + d + 1` from `⟨D.R.k + (i : ℕ) - j - 1, by omega⟩`. Establish `hk` using `D.R.m_add_three_le_k`.

Establish `hm` using `D.R.m_le_f`. Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `hmono` using `lam_mono (D.hc t) j d (by have := i.2; omega)`. Establish `hb` using `lam_b (D.hc t) (i : ℕ) i.2`. Rewrite `hmono` using `[show j + d = D.R.k - 1 + (i : ℕ) by omega, hb]`.

Establish `hce` using `P.e_centred t i`. Establish `h0t` using `two_nodeGap_add_six_le_roundingConstant P`. Establish `hcast : (((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - (j + 1)) = d`. Rewrite using `[hsw, hd]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hcast]`. Establish `key : (0 : ℝ) ≤ ((lamAt (D.hc t) j + (D.hc t).e i - d - ((D.R.t : ℚ) + 1) / 2 : ℚ) : ℝ)`. Establish `hm' : (((-(D.hc t).b i + d : ℚ)) : ℝ) ≤ ((lamAt (D.hc t) j : ℚ) : ℝ)` using `by exact_mod_cast hmono`. Establish `hce'` using `(abs_le.1 hce).1`.

Move the coercions through the operations in `at hm' hce' ⊢`. Establish `: (i : Fin D.R.m) = ⟨(i : ℕ), i.2⟩` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `key` after adjusting the coercions. Use `⟨?_, hnn⟩` and prove the remaining obligations.

Rewrite using `[GlobalTheory.Shares.WtDic.wtA_tau]`. Unfold `ext0`. Rewrite using `[dif_pos hj, (p.fw.kap i t).1 ⟨j, hj⟩, sig_Wc]`. Unfold `aPl`. Rewrite using `[if_pos hj]`.

Conclude with `Int.toNat_of_nonneg hnn`.
-/
theorem bigEnt (p : PtAt ex Csz) (P : ParameterChoice' D L) (i : Fin D.R.m) (t : D.what₂.Tau) (j : ℕ)
    (hj : j < (D.R.sigW ((i : ℕ) + 1)).1) :
    ((wtA (p.κ i) (DV.tauEmb D t, j) : ℕ) : ℤ) =
      ⌊lamAt (D.hc t) j + (D.hc t).e i - (((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - (j + 1)) - ((D.R.t : ℚ) + 1) / 2⌋ ∧
    0 ≤ ⌊lamAt (D.hc t) j + (D.hc t).e i - (((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - (j + 1)) - ((D.R.t : ℚ) + 1) / 2⌋ := by
  have hnn : 0 ≤ ⌊lamAt (D.hc t) j + (D.hc t).e i - (((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - (j + 1)) -
      ((D.R.t : ℚ) + 1) / 2⌋ := by
    apply Int.floor_nonneg.2
    have hsw : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) := by simp only [Ranks.sigW]; omega
    obtain ⟨d, hd⟩ : ∃ d, D.R.k + (i : ℕ) = j + d + 1 := ⟨D.R.k + (i : ℕ) - j - 1, by omega⟩
    have hk := D.R.m_add_three_le_k
    have hm := D.R.m_le_f
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    have hmono := lam_mono (D.hc t) j d (by have := i.2; omega)
    have hb := lam_b (D.hc t) (i : ℕ) i.2
    rw [show j + d = D.R.k - 1 + (i : ℕ) by omega, hb] at hmono
    have hce := P.e_centred t i
    have h0t := two_nodeGap_add_six_le_roundingConstant P
    have hcast : (((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - (j + 1)) = d := by
      rw [hsw, hd]; push_cast; ring
    rw [hcast]
    have key : (0 : ℝ) ≤ ((lamAt (D.hc t) j + (D.hc t).e i - d - ((D.R.t : ℚ) + 1) / 2 : ℚ) : ℝ) := by
      have hm' : (((-(D.hc t).b i + d : ℚ)) : ℝ) ≤ ((lamAt (D.hc t) j : ℚ) : ℝ) := by exact_mod_cast hmono
      have hce' := (abs_le.1 hce).1
      push_cast at hm' hce' ⊢
      have : (i : Fin D.R.m) = ⟨(i : ℕ), i.2⟩ := rfl
      linarith
    exact_mod_cast key
  refine ⟨?_, hnn⟩
  rw [GlobalTheory.Shares.WtDic.wtA_tau]
  unfold ext0
  rw [dif_pos hj, (p.fw.kap i t).1 ⟨j, hj⟩, sig_Wc]
  unfold aPl
  rw [if_pos hj]
  exact Int.toNat_of_nonneg hnn

/- English proof (translation)
Establish `hsw1 : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ)` using `by simp only [Ranks.sigW]; omega`. Establish `hsw2 : (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m - ((i : ℕ) + 1)` using `rfl`. Establish `hnn : 0 ≤ ⌊-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) + ((s : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2)⌋`. Apply `Int.floor_nonneg.2` to reduce the goal to its premises. Establish `hk` using `D.R.m_add_three_le_k`.

Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `hi1 : (i : ℕ) + 1 < D.R.m` using `by omega`. Establish `hmono` using `lam_mono (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1) s (by omega)`. Establish `hb` using `lam_b (D.hc t) ((i : ℕ) + 1) hi1`. Rewrite `hb` using `[show D.R.k - 1 + ((i : ℕ) + 1) = (D.R.sigW ((i : ℕ) + 1)).1 by omega]`.

Rewrite `hmono` using `[hb]`. Establish `hce` using `P.e_centred t i`. Establish `hng` using `(P.nodes_gap t (i : ℕ) hi1).1`. Establish `h0t` using `two_nodeGap_add_six_le_roundingConstant P`. Establish `key : (0 : ℝ) ≤ ((-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) + ((s : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2) : ℚ) : ℝ)`.

Establish `hm' : (((lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) + s : ℚ)) : ℝ) ≤ ((-(D.hc t).b ⟨(i : ℕ) + 1, hi1⟩ : ℚ) : ℝ)` using `by exact_mod_cast hmono`. Establish `hce'` using `(abs_le.1 hce).2`. Move the coercions through the operations in `at hm' hce' hng ⊢`. Establish `: (i : Fin D.R.m) = ⟨(i : ℕ), i.2⟩` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `key` after adjusting the coercions. Use `⟨?_, hnn⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.Shares.WtDic.wtA_conj]`. Unfold `ext0`. Rewrite using `[dif_pos (by omega), (p.fw.kap i t).2.1 ⟨_, by omega⟩, sig_Wc]`.

Unfold `aMi`. Rewrite using `[if_pos (by omega)]`. Establish `e1 : (D.R.sigW ((i : ℕ) + 1)).2 - ((D.R.sigW ((i : ℕ) + 1)).2 - 1 - s) = s + 1` using `by omega`. Establish `e2 : (D.R.sigW ((i : ℕ) + 1)).1 + (s + 1) - 1 = (D.R.sigW ((i : ℕ) + 1)).1 + s` using `by omega`. Simplify using `only [e1, e2]`.

Use `push_cast`. Conclude with `Int.toNat_of_nonneg hnn`.
-/
theorem smallEnt (p : PtAt ex Csz) (P : ParameterChoice' D L) (i : Fin D.R.m) (t : D.what₂.Tau) (s : ℕ)
    (hs : s < (D.R.sigW ((i : ℕ) + 1)).2) :
    ((wtA (p.κ i) (conjEmb (DV.tauEmb D t), (D.R.sigW ((i : ℕ) + 1)).2 - 1 - s) : ℕ) : ℤ) =
      ⌊-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) + ((s : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2)⌋ ∧
    0 ≤ ⌊-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) + ((s : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2)⌋ := by
  have hsw1 : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) := by simp only [Ranks.sigW]; omega
  have hsw2 : (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m - ((i : ℕ) + 1) := rfl
  have hnn : 0 ≤ ⌊-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) + ((s : ℚ) + 1) +
      ((D.R.t : ℚ) - 1) / 2)⌋ := by
    apply Int.floor_nonneg.2
    have hk := D.R.m_add_three_le_k
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    have hi1 : (i : ℕ) + 1 < D.R.m := by omega
    have hmono := lam_mono (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1) s (by omega)
    have hb := lam_b (D.hc t) ((i : ℕ) + 1) hi1
    rw [show D.R.k - 1 + ((i : ℕ) + 1) = (D.R.sigW ((i : ℕ) + 1)).1 by omega] at hb
    rw [hb] at hmono
    have hce := P.e_centred t i
    have hng := (P.nodes_gap t (i : ℕ) hi1).1
    have h0t := two_nodeGap_add_six_le_roundingConstant P
    have key : (0 : ℝ) ≤ ((-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) + ((s : ℚ) + 1) +
        ((D.R.t : ℚ) - 1) / 2) : ℚ) : ℝ) := by
      have hm' : (((lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) + s : ℚ)) : ℝ) ≤
          ((-(D.hc t).b ⟨(i : ℕ) + 1, hi1⟩ : ℚ) : ℝ) := by exact_mod_cast hmono
      have hce' := (abs_le.1 hce).2
      push_cast at hm' hce' hng ⊢
      have : (i : Fin D.R.m) = ⟨(i : ℕ), i.2⟩ := rfl
      linarith
    exact_mod_cast key
  refine ⟨?_, hnn⟩
  rw [GlobalTheory.Shares.WtDic.wtA_conj]
  unfold ext0
  rw [dif_pos (by omega), (p.fw.kap i t).2.1 ⟨_, by omega⟩, sig_Wc]
  unfold aMi
  rw [if_pos (by omega)]
  have e1 : (D.R.sigW ((i : ℕ) + 1)).2 - ((D.R.sigW ((i : ℕ) + 1)).2 - 1 - s) = s + 1 := by omega
  have e2 : (D.R.sigW ((i : ℕ) + 1)).1 + (s + 1) - 1 = (D.R.sigW ((i : ℕ) + 1)).1 + s := by omega
  simp only [e1, e2]
  push_cast
  exact Int.toNat_of_nonneg hnn

end Ent

open GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CompHS in

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y0 cX ex Csz p P i hi`. Establish `hQ : p.T.Q.Pins` using `p.fw.laws.pins`. Establish `hj : InR D ((i : ℕ) + 1)` using `⟨by omega, by omega⟩`. Take `⟨hp, hq, -⟩` from `hQ.2.2.2 _ hj`. Establish `hp' : (dat p i).p = (D.R.sigW ((i : ℕ) + 1)).1` using `hp`.

Establish `hq' : (dat p i).q = (D.R.sigW ((i : ℕ) + 1)).2` using `hq`. Establish `hk0` using `D.R.m_add_three_le_k`. Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `hpq : (dat p i).p + (dat p i).q = D.R.r` using `by rw [hp', hq']; simp only [Ranks.sigW]; omega`. Use `⟨hpq, ?_, ?_⟩` and prove the remaining obligations.

Unfold `GlobalTheory.FlagTan.dimFlag`. Rewrite using `[hpq, GlobalTheory.PinNum.finrank_host D, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]`. Introduce `τ k hk`. Take `⟨t, ht⟩` from `ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi p.T.Q hQ.1 τ.1 τ.2`. Establish `hn` using `(p.fw.kap i t).2.2`.

Establish `hgap : gap (uW p i τ) k = (if k < (D.R.sigW ((i : ℕ) + 1)).1 then ((wtA (p.κ i) (DV.tauEmb D t, k) : ℕ) : ℤ) + ((D.R.nV / 2 : ℕ) : ℤ) else -((wtA (p.κ i) (conjEmb (DV.tauEmb D t), (D.R.sigW ((i : ℕ) + 1)).2 - 1 - (k - (D.R.sigW ((i : ℕ) + 1)).1)) : ℕ) : ℤ) - ((D.R.nV / 2 : ℕ) : ℤ …`. Unfold `gap`. Rewrite using `[dif_pos hk]`. Simplify using `only [uW, uWt, Pi.sub_apply, GlobalTheory.FlatLine.parWt, laOf, weightOf, hp', hq', ht, hn]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hgap, hp']`. Establish `hPQ : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.r` using `by rw [← hp', ← hq']; exact hpq`. Rewrite `hk` using `[hp', hq']`. Establish `hPv : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ)` using `by simp only [Ranks.sigW]; omega`. Establish `hev : Even D.R.nV` using `hn ▸ (p.κ i).n_even`.

Establish `hgS : 0 < LevelStarExponents.gapS D P.Cgap`. Unfold `LevelStarExponents.gapS`. Use `P.Cgap_pos` as an intermediate fact. Establish `hm` using `D.R.two_le_m`. Establish `: (0 : ℝ) < (D.R.k : ℝ)` using `by exact_mod_cast (show 0 < D.R.k by omega)`.

Check the signs of the components of the expression. Break down `lt_trichotomy (k + 1) (D.R.sigW ((i : ℕ) + 1)).1 with hA | hB | hC` into its components or cases. Rewrite using `[if_pos (by omega), if_pos hA]`. Take `⟨e1, -⟩` from `bigEnt p P i t k (by omega)`. Take `⟨e2, -⟩` from `bigEnt p P i t (k + 1) hA`.

Rewrite using `[e1, e2]`. Take `⟨z, hz, -⟩` from `lam_step (D.hc t) k (by omega)`. Establish `hfl : ⌊lamAt (D.hc t) k + (D.hc t).e i - ((((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℚ) - ((k : ℚ) + 1)) - ((D.R.t : ℚ) + 1) / 2⌋ = ⌊lamAt (D.hc t) (k + 1) + (D.hc t).e i - ((((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℚ) - (((k + 1 : ℕ) : ℚ) + 1)) - ((D.R.t : ℚ) + 1) / 2⌋ + (z - 1)`. Rewrite using `[← Int.floor_add_intCast]`. Use `congr 1`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hfl]`. Use `⟨fun _ => ?_, fun h => absurd h (by omega)⟩` and prove the remaining obligations. Establish `hg` using `lam_gapS P t k (by omega)`.

Rewrite `hg` using `[hz]`. Move the coercions through the operations in `at hg ⊢`. Use `min_le_left (LevelStarExponents.gapS D P.Cgap) (LevelStarExponents.h0 L)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[if_pos (by omega), if_neg (by omega), show k + 1 - (D.R.sigW ((i : ℕ) + 1)).1 = 0 by omega]`.

Take `⟨e1, -⟩` from `bigEnt p P i t k (by omega)`. Take `⟨e2, -⟩` from `smallEnt p P i t 0 (by omega)`. Rewrite using `[e1, e2]`. Use `⟨fun h => absurd h (by omega), fun _ => ?_⟩` and prove the remaining obligations. Establish `hi1 : (i : ℕ) + 1 < D.R.m` using `hi`.

Establish `hb0` using `lam_b (D.hc t) (i : ℕ) i.2`. Establish `hb1` using `lam_b (D.hc t) ((i : ℕ) + 1) hi1`. Rewrite `hb0` using `[show D.R.k - 1 + (i : ℕ) = k by omega]`. Rewrite `hb1` using `[show D.R.k - 1 + ((i : ℕ) + 1) = (D.R.sigW ((i : ℕ) + 1)).1 + 0 by omega]`. Establish `hX` using `Int.sub_one_lt_floor (lamAt (D.hc t) k + (D.hc t).e i - ((((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℚ) - ((k : ℚ) + 1)) - ((D.R.t : ℚ) + 1) / 2)`.

Establish `hY` using `Int.sub_one_lt_floor (-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + 0) + (((0 : ℕ) : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2))`. Establish `hkq : (((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℝ) = (k : ℝ) + 1` using `by rw [← hB]; push_cast; ring`. Establish `hb0' : ((lamAt (D.hc t) k : ℚ) : ℝ) = -(((D.hc t).b i : ℚ) : ℝ)` using `by rw [hb0]; push_cast; ring`. Establish `hb1' : ((lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + 0) : ℚ) : ℝ) = -(((D.hc t).b ⟨(i : ℕ) + 1, hi1⟩ : ℚ) : ℝ)`. Rewrite using `[hb1]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hX'` using `(Rat.cast_lt (K := ℝ)).2 hX`. Establish `hY'` using `(Rat.cast_lt (K := ℝ)).2 hY`. Establish `hng` using `(P.nodes_gap t (i : ℕ) hi1).1`.

Establish `hc2z : ((D.R.nV / 2 : ℕ) : ℤ) * 2 = (D.R.r : ℤ) + D.R.t`. Use `Nat.div_two_mul_two_of_even hev` as an intermediate fact. Unfold `Ranks.nV at this ⊢`. Use linear arithmetic over natural numbers and integers. Generalize the expression as in `((D.R.nV / 2 : ℕ) : ℤ) = c at hc2z ⊢`.

Establish `hc2r : (c : ℝ) * 2 = (D.R.r : ℝ) + D.R.t` using `by exact_mod_cast hc2z`. Move the coercions through the operations in `at hX' hY' hng ⊢`. Establish `: (i : Fin D.R.m) = ⟨(i : ℕ), i.2⟩` using `rfl`. Rewrite `hng` using `[← this]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨s, rfl⟩ : ∃ s, k = (D.R.sigW ((i : ℕ) + 1)).1 + s` from `⟨k - (D.R.sigW ((i : ℕ) + 1)).1, by omega⟩`. Rewrite using `[if_neg (by omega), if_neg (by omega), show (D.R.sigW ((i : ℕ) + 1)).1 + s - (D.R.sigW ((i : ℕ) + 1)).1 = s by omega, show (D.R.sigW ((i : ℕ) + 1)).1 + s + 1 - (D.R.sigW ((i : ℕ) + 1)).1 = s + 1 by omega]`. Take `⟨e1, -⟩` from `smallEnt p P i t s (by omega)`. Take `⟨e2, -⟩` from `smallEnt p P i t (s + 1) (by omega)`. Rewrite using `[e1, e2]`.

Take `⟨z, hz, -⟩` from `lam_step (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) (by omega)`. Establish `hfl : ⌊-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + (s + 1)) + (((s + 1 : ℕ) : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2)⌋ = ⌊-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) + ((s : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2)⌋ + (z - 1)`. Rewrite using `[← Int.floor_add_intCast]`. Use `congr 1`. Rewrite using `[show (D.R.sigW ((i : ℕ) + 1)).1 + (s + 1) = (D.R.sigW ((i : ℕ) + 1)).1 + s + 1 by ring]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hfl]`. Use `⟨fun _ => ?_, fun h => absurd h (by omega)⟩` and prove the remaining obligations. Establish `hg` using `lam_gapS P t ((D.R.sigW ((i : ℕ) + 1)).1 + s) (by omega)`.

Rewrite `hg` using `[hz]`. Move the coercions through the operations in `at hg ⊢`. Use `min_le_left (LevelStarExponents.gapS D P.Cgap) (LevelStarExponents.h0 L)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gaps : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
    (p : PtAt ex Csz) (P : ParameterChoice' D L) (i : Fin D.R.m), (i : ℕ) + 1 < D.R.m →
    (dat p i).p + (dat p i).q = D.R.r ∧ GlobalTheory.FlagTan.dimFlag (dat p i) = D.R.f * D.R.r.choose 2 ∧
    ∀ (τ : Psi p.T.Q.H) (k : ℕ), k + 1 < (dat p i).p + (dat p i).q →
      (k + 1 ≠ (dat p i).p → min (LevelStarExponents.gapS D P.Cgap) (LevelStarExponents.h0 L) - 2 ≤ (gap (uW p i τ) k : ℝ)) ∧
      (k + 1 = (dat p i).p → LevelStarExponents.h0 L + D.R.r - 3 ≤ (gap (uW p i τ) k : ℝ)) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p P i hi
  have hQ : p.T.Q.Pins := p.fw.laws.pins
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, by omega⟩
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 _ hj
  have hp' : (dat p i).p = (D.R.sigW ((i : ℕ) + 1)).1 := hp
  have hq' : (dat p i).q = (D.R.sigW ((i : ℕ) + 1)).2 := hq
  have hk0 := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hpq : (dat p i).p + (dat p i).q = D.R.r := by rw [hp', hq']; simp only [Ranks.sigW]; omega
  refine ⟨hpq, ?_, ?_⟩
  · unfold GlobalTheory.FlagTan.dimFlag
    rw [hpq, GlobalTheory.PinNum.finrank_host D, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  · intro τ k hk
    obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi p.T.Q hQ.1 τ.1 τ.2

    have hn := (p.fw.kap i t).2.2
    have hgap : gap (uW p i τ) k =
        (if k < (D.R.sigW ((i : ℕ) + 1)).1 then ((wtA (p.κ i) (DV.tauEmb D t, k) : ℕ) : ℤ) + ((D.R.nV / 2 : ℕ) : ℤ)
          else -((wtA (p.κ i) (conjEmb (DV.tauEmb D t), (D.R.sigW ((i : ℕ) + 1)).2 - 1 - (k - (D.R.sigW ((i : ℕ) + 1)).1)) : ℕ) : ℤ)
            - ((D.R.nV / 2 : ℕ) : ℤ)) -
        (if k + 1 < (D.R.sigW ((i : ℕ) + 1)).1 then ((wtA (p.κ i) (DV.tauEmb D t, k + 1) : ℕ) : ℤ) + ((D.R.nV / 2 : ℕ) : ℤ)
          else -((wtA (p.κ i) (conjEmb (DV.tauEmb D t), (D.R.sigW ((i : ℕ) + 1)).2 - 1 - (k + 1 - (D.R.sigW ((i : ℕ) + 1)).1)) : ℕ) : ℤ)
            - ((D.R.nV / 2 : ℕ) : ℤ)) := by
      unfold gap
      rw [dif_pos hk]
      simp only [uW, uWt, Pi.sub_apply, GlobalTheory.FlatLine.parWt, laOf, weightOf, hp', hq', ht, hn]
      ring
    rw [hgap, hp']

    have hPQ : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.r := by rw [← hp', ← hq']; exact hpq
    rw [hp', hq'] at hk
    have hPv : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) := by simp only [Ranks.sigW]; omega
    have hev : Even D.R.nV := hn ▸ (p.κ i).n_even
    have hgS : 0 < LevelStarExponents.gapS D P.Cgap := by
      unfold LevelStarExponents.gapS
      have := P.Cgap_pos
      have hm := D.R.two_le_m
      have : (0 : ℝ) < (D.R.k : ℝ) := by exact_mod_cast (show 0 < D.R.k by omega)
      positivity
    rcases lt_trichotomy (k + 1) (D.R.sigW ((i : ℕ) + 1)).1 with hA | hB | hC
    · rw [if_pos (by omega), if_pos hA]
      obtain ⟨e1, -⟩ := bigEnt p P i t k (by omega)
      obtain ⟨e2, -⟩ := bigEnt p P i t (k + 1) hA
      rw [e1, e2]
      obtain ⟨z, hz, -⟩ := lam_step (D.hc t) k (by omega)
      have hfl : ⌊lamAt (D.hc t) k + (D.hc t).e i - ((((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℚ) - ((k : ℚ) + 1)) - ((D.R.t : ℚ) + 1) / 2⌋ =
          ⌊lamAt (D.hc t) (k + 1) + (D.hc t).e i - ((((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℚ) - (((k + 1 : ℕ) : ℚ) + 1)) -
            ((D.R.t : ℚ) + 1) / 2⌋ + (z - 1) := by
        rw [← Int.floor_add_intCast]; congr 1; push_cast; linarith
      rw [hfl]
      refine ⟨fun _ => ?_, fun h => absurd h (by omega)⟩
      have hg := lam_gapS P t k (by omega)
      rw [hz] at hg
      push_cast at hg ⊢
      have := min_le_left (LevelStarExponents.gapS D P.Cgap) (LevelStarExponents.h0 L)
      linarith
    · rw [if_pos (by omega), if_neg (by omega), show k + 1 - (D.R.sigW ((i : ℕ) + 1)).1 = 0 by omega]
      obtain ⟨e1, -⟩ := bigEnt p P i t k (by omega)
      obtain ⟨e2, -⟩ := smallEnt p P i t 0 (by omega)
      rw [e1, e2]
      refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
      have hi1 : (i : ℕ) + 1 < D.R.m := hi
      have hb0 := lam_b (D.hc t) (i : ℕ) i.2
      have hb1 := lam_b (D.hc t) ((i : ℕ) + 1) hi1
      rw [show D.R.k - 1 + (i : ℕ) = k by omega] at hb0
      rw [show D.R.k - 1 + ((i : ℕ) + 1) = (D.R.sigW ((i : ℕ) + 1)).1 + 0 by omega] at hb1
      have hX := Int.sub_one_lt_floor (lamAt (D.hc t) k + (D.hc t).e i - ((((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℚ) - ((k : ℚ) + 1)) -
        ((D.R.t : ℚ) + 1) / 2)
      have hY := Int.sub_one_lt_floor (-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + 0) + (((0 : ℕ) : ℚ) + 1) +
        ((D.R.t : ℚ) - 1) / 2))
      have hkq : (((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℝ) = (k : ℝ) + 1 := by rw [← hB]; push_cast; ring
      have hb0' : ((lamAt (D.hc t) k : ℚ) : ℝ) = -(((D.hc t).b i : ℚ) : ℝ) := by rw [hb0]; push_cast; ring
      have hb1' : ((lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + 0) : ℚ) : ℝ) = -(((D.hc t).b ⟨(i : ℕ) + 1, hi1⟩ : ℚ) : ℝ) := by
        rw [hb1]; push_cast; ring
      have hX' := (Rat.cast_lt (K := ℝ)).2 hX
      have hY' := (Rat.cast_lt (K := ℝ)).2 hY
      have hng := (P.nodes_gap t (i : ℕ) hi1).1
      have hc2z : ((D.R.nV / 2 : ℕ) : ℤ) * 2 = (D.R.r : ℤ) + D.R.t := by
        have := Nat.div_two_mul_two_of_even hev
        unfold Ranks.nV at this ⊢; omega
      generalize ((D.R.nV / 2 : ℕ) : ℤ) = c at hc2z ⊢
      have hc2r : (c : ℝ) * 2 = (D.R.r : ℝ) + D.R.t := by exact_mod_cast hc2z
      push_cast at hX' hY' hng ⊢
      have : (i : Fin D.R.m) = ⟨(i : ℕ), i.2⟩ := rfl
      rw [← this] at hng
      linarith
    · obtain ⟨s, rfl⟩ : ∃ s, k = (D.R.sigW ((i : ℕ) + 1)).1 + s := ⟨k - (D.R.sigW ((i : ℕ) + 1)).1, by omega⟩
      rw [if_neg (by omega), if_neg (by omega), show (D.R.sigW ((i : ℕ) + 1)).1 + s - (D.R.sigW ((i : ℕ) + 1)).1 = s by omega,
        show (D.R.sigW ((i : ℕ) + 1)).1 + s + 1 - (D.R.sigW ((i : ℕ) + 1)).1 = s + 1 by omega]
      obtain ⟨e1, -⟩ := smallEnt p P i t s (by omega)
      obtain ⟨e2, -⟩ := smallEnt p P i t (s + 1) (by omega)
      rw [e1, e2]
      obtain ⟨z, hz, -⟩ := lam_step (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) (by omega)
      have hfl : ⌊-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + (s + 1)) + (((s + 1 : ℕ) : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2)⌋ =
          ⌊-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) + ((s : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2)⌋ + (z - 1) := by
        rw [← Int.floor_add_intCast]; congr 1
        rw [show (D.R.sigW ((i : ℕ) + 1)).1 + (s + 1) = (D.R.sigW ((i : ℕ) + 1)).1 + s + 1 by ring]
        push_cast; linarith
      rw [hfl]
      refine ⟨fun _ => ?_, fun h => absurd h (by omega)⟩
      have hg := lam_gapS P t ((D.R.sigW ((i : ℕ) + 1)).1 + s) (by omega)
      rw [hz] at hg
      push_cast at hg ⊢
      have := min_le_left (LevelStarExponents.gapS D P.Cgap) (LevelStarExponents.h0 L)
      linarith

end GlobalTheory.RecGaps

end
