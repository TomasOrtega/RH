import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsNDF

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Deg

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

open Classical in

def rows_KZ (D : D7) (u u' : D.what₂.Word) (Z : GramM D) : ℝ :=
  ∏ τ : D.what₂.Tau, if leadMinorE Z D.R.rS = 0 then 1 else
    (1 + ‖embS D τ (leadMinorE Z (D.R.rS + 1) / leadMinorE Z D.R.rS)‖ / Real.sqrt ((Tu D u : ℝ) * (Tu D u' : ℝ))) /
      Real.sqrt ((‖embS D τ (leadMinorE Z (D.R.rS + 1) / leadMinorE Z D.R.rS)‖ /
        Real.sqrt ((Tu D u : ℝ) * (Tu D u' : ℝ))) ^ 2 - 1)

/- English proof (translation)
Unfold `rows_KZ`. Rewrite using `[rows_leadMinor_inv h D.R.rS, rows_leadMinor_inv h (D.R.rS + 1)]`.
-/
theorem rows_KZ_inv {Z Z₂ : GramM D} (h : ZEquiv Z Z₂) (u u' : D.what₂.Word) : rows_KZ D u u' Z₂ = rows_KZ D u u' Z := by
  unfold rows_KZ
  rw [rows_leadMinor_inv h D.R.rS, rows_leadMinor_inv h (D.R.rS + 1)]

/- English proof (translation)
Unfold `rows_Kt rows_KZ`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[rows_chRatio_eq Y hrd t τ]`. Unfold `onePlusChSh`. Distinguish the cases in `h0 : Dr (X.fl t) (X.fl' t) = 0`.

Establish `h0' : leadMinorE (termGramMatrix X t) D.R.rS = 0` using `h0`. Rewrite using `[if_pos h0, if_pos h0']`. Establish `h0' : ¬ leadMinorE (termGramMatrix X t) D.R.rS = 0` using `h0`. Rewrite using `[if_neg h0, if_neg h0']`. Both sides reduce to the same expression.
-/
theorem rows_Kt_KZ (hrd : 0 < D.host.rdE) (t : D.s.Term u u') : rows_Kt Y t = rows_KZ D u u' (termGramMatrix X t) := by
  unfold rows_Kt rows_KZ
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [rows_chRatio_eq Y hrd t τ]
  unfold onePlusChSh
  by_cases h0 : Dr (X.fl t) (X.fl' t) = 0
  · have h0' : leadMinorE (termGramMatrix X t) D.R.rS = 0 := h0
    rw [if_pos h0, if_pos h0']
  · have h0' : ¬ leadMinorE (termGramMatrix X t) D.R.rS = 0 := h0
    rw [if_neg h0, if_neg h0']
    rfl

def rows_KBound (Y : LoopTie D large₂ X u u' C1) (c : ℝ) : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t →
    rows_Kt Y t ^ 2 ≤ 9 ^ D.R.f * HHZ D large₂.sc.b c (termGramMatrix X t) ^ 3

def rows_GamD (D : D7) (large₂ : SizeData₂ D) (Ca C2 : ℝ) : ℝ :=
  GamS D large₂ * Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) ^ 2 * (Ca / D.R.k) ^ (D.R.k * D.R.f)

def rows_lam (D : D7) (large₂ : SizeData₂ D) (c Ca C2 Ch : ℝ) (q : ℕ) (Z : GramM D) : ℝ :=
  (HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
    (GamS D large₂ * sizeZ D large₂.sc.b Ch Z ^ (C2 * (D.R.m : ℝ) ^ 2)) *
    (Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) * sizeZ D large₂.sc.b Ch Z ^ (C2 * (D.R.m : ℝ) ^ 4)) ^ 2 *
    (Ca / D.R.k) ^ (D.R.k * D.R.f) * sizeZ D large₂.sc.b Ch Z ^ (-(2 * (q : ℝ) / ((D.R.rS : ℝ) + 1)))

/- English proof (translation)
The claim follows from `(D.R.k_even.mul_right _).pow_nonneg _`.
-/
theorem rows_CK_nonneg (D : D7) (Ca : ℝ) : 0 ≤ (Ca / D.R.k) ^ (D.R.k * D.R.f) :=
  (D.R.k_even.mul_right _).pow_nonneg _

/- English proof (translation)
Unfold `rows_GamD`. Establish `h3 : 0 < GamS D large₂` using `by unfold GamS; exact Real.exp_pos _`. Use `rows_CK_nonneg D Ca` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem rows_GamD_nonneg (D : D7) (large₂ : SizeData₂ D) (Ca C2 : ℝ) : 0 ≤ rows_GamD D large₂ Ca C2 := by
  unfold rows_GamD
  have h3 : 0 < GamS D large₂ := by unfold GamS; exact Real.exp_pos _
  have := rows_CK_nonneg D Ca
  positivity

/- English proof (translation)
Establish `hs : 0 < sizeZ D large₂.sc.b Ch Z` using `lt_of_lt_of_le one_pos (rows_one_le_sizeZ _ _ _)`. Unfold `rows_lam rows_GamD`. Rewrite using `[Real.rpow_add hs, mul_pow, rows_rpow_pow hs]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rows_lam_eq (D : D7) (large₂ : SizeData₂ D) (c Ca C2 Ch : ℝ) (q : ℕ) (Z : GramM D) :
    rows_lam D large₂ c Ca C2 Ch q Z = (HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
      (rows_GamD D large₂ Ca C2 * sizeZ D large₂.sc.b Ch Z ^ (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2)) *
      sizeZ D large₂.sc.b Ch Z ^ (-(2 * (q : ℝ) / ((D.R.rS : ℝ) + 1))) := by
  have hs : 0 < sizeZ D large₂.sc.b Ch Z := lt_of_lt_of_le one_pos (rows_one_le_sizeZ _ _ _)
  unfold rows_lam rows_GamD
  rw [Real.rpow_add hs, mul_pow, rows_rpow_pow hs]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[rows_lam_eq]`. Establish `h1` using `rows_one_le_HHZ' D large₂ c Z`. Establish `h2` using `rows_one_le_sizeZ (D := D) large₂.sc.b Ch Z`. Establish `h3` using `rows_GamD_nonneg D large₂ Ca C2`. Check the signs of the components of the expression.
-/
theorem rows_lam_nonneg (D : D7) (large₂ : SizeData₂ D) (c Ca C2 Ch : ℝ) (q : ℕ) (Z : GramM D) : 0 ≤ rows_lam D large₂ c Ca C2 Ch q Z := by
  rw [rows_lam_eq]
  have h1 := rows_one_le_HHZ' D large₂ c Z
  have h2 := rows_one_le_sizeZ (D := D) large₂.sc.b Ch Z
  have h3 := rows_GamD_nonneg D large₂ Ca C2
  positivity

def rows_alD (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (c Ca C2 Ch : ℝ) (q : ℕ) (Z : GramM D) : ℝ :=
  Real.sqrt (rows_lam D large₂ c Ca C2 Ch q Z /
    (wordPairGramNorm D u u' Z * rows_KZ D u u' Z ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f)))

def rows_DeD (D : D7) (u u' : D.what₂.Word) (s : ℕ) (x y : GramM D) : ℝ :=
  (2 / gg D) ^ ((s - 2) * D.R.f) * Real.sqrt (wordPairGramProduct D u u' x * wordPairGramProduct D u u' y) * (Tr D u)⁻¹ ^ D.R.f *
    rows_KZ D u u' x * rows_KZ D u u' y

def rows_RD (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (c Ca C2 Ch : ℝ) (s : ℕ) : ℝ :=
  (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) *
    (XiS D u (rows_P D large₂ c Ch ^ 2) c s *
      ((rows_P D large₂ c Ch ^ pairCountExponent D c s) ^ 2 * (rows_P D large₂ c Ch ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
        (c * s * D.R.f) ^ (6 * s * D.R.f) * rows_GamD D large₂ Ca C2))

def rows_degB (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (c Ca C2 Ch : ℝ) (s : ℕ) : ℝ :=
  rows_RD D large₂ u c Ca C2 Ch s * rows_Phi D large₂ c Ch ^ 2

variable {C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm : ℝ} {q : ℕ}

/- English proof (translation)
Take `⟨t, hG, hrel, hE, _⟩` from `hZ`. Rewrite using `[rows_KZ_inv hE, ← rows_Kt_KZ Y (d_rdE_pos h.hH.1)]`. Conclude with `rowsT_Kt_pos Y (d_rdE_pos h.hH.1) t hG hrel`.
-/
theorem rows_KZ_pos (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) {Z : GramM D}
    (hZ : wordPairGramGood X u u' large₂ c Z) : 0 < rows_KZ D u u' Z := by
  obtain ⟨t, hG, hrel, hE, _⟩ := hZ
  rw [rows_KZ_inv hE, ← rows_Kt_KZ Y (d_rdE_pos h.hH.1)]
  exact rowsT_Kt_pos Y (d_rdE_pos h.hH.1) t hG hrel

/- English proof (translation)
Establish `h1` using `rows_nZ_pos Y h hZ`. Establish `h2` using `rows_KZ_pos Y h hZ`. Establish `h3` using `rows_Tr_pos D u`. Check the signs of the components of the expression.
-/
theorem rows_den_pos (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) {Z : GramM D}
    (hZ : wordPairGramGood X u u' large₂ c Z) :
    0 < wordPairGramNorm D u u' Z * rows_KZ D u u' Z ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f) := by
  have h1 := rows_nZ_pos Y h hZ
  have h2 := rows_KZ_pos Y h hZ
  have h3 := rows_Tr_pos D u
  positivity

/- English proof (translation)
Take `⟨hEq, hGood⟩` from `rows_Zr_spec Y h.hH h.hHH t hG hrel`. Establish `h1` using `rows_term_MINdec Y h.hH h.hDEC h.ha h.hb h.hp h.hpp h.hV h.hT h.hCh t hG hrel q h.hq`. Rewrite `h1` using `[rows_Kt_KZ Y (d_rdE_pos h.hH.1), ← rows_KZ_inv hEq, ← rows_nZ_inv hEq, ← rows_HHZ_inv hEq, ← rows_sizeZ_inv hEq]`. Establish `h2 : aT X t ^ 2 / dimPi (hc` using `D.hcW) u ≤ rows_lam D large₂ c Ca C2 Ch q (termReducedGramMatrix Y h.hH h.hHH t) / (wordPairGramNorm D u u' (termReducedGramMatrix Y h.hH h.hHH t) * rows_KZ D u u' (termReducedGramMatrix Y h.hH h.hHH t) ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f)) := by`. Rewrite using `[le_div_iff₀ (rows_den_pos Y h hGood)]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h3 : aT X t / Real.sqrt (dimPi (hc` using `D.hcW) u) = Real.sqrt (aT X t ^ 2 / dimPi (hc := D.hcW) u) := by`. Rewrite using `[Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (aT_nonneg X t)]`. Rewrite using `[h3]`. Conclude with `Real.sqrt_le_sqrt h2`.
-/
theorem rows_deg_term (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (t : D.s.Term u u')
    (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t) :
    aT X t / Real.sqrt (dimPi (hc := D.hcW) u) ≤ rows_alD D large₂ u u' c Ca C2 Ch q (termReducedGramMatrix Y h.hH h.hHH t) := by
  obtain ⟨hEq, hGood⟩ := rows_Zr_spec Y h.hH h.hHH t hG hrel
  have h1 := rows_term_MINdec Y h.hH h.hDEC h.ha h.hb h.hp h.hpp h.hV h.hT h.hCh t hG hrel q h.hq
  rw [rows_Kt_KZ Y (d_rdE_pos h.hH.1), ← rows_KZ_inv hEq, ← rows_nZ_inv hEq, ← rows_HHZ_inv hEq,
    ← rows_sizeZ_inv hEq] at h1
  have h2 : aT X t ^ 2 / dimPi (hc := D.hcW) u ≤ rows_lam D large₂ c Ca C2 Ch q (termReducedGramMatrix Y h.hH h.hHH t) /
      (wordPairGramNorm D u u' (termReducedGramMatrix Y h.hH h.hHH t) * rows_KZ D u u' (termReducedGramMatrix Y h.hH h.hHH t) ^ (2 * D.R.k) *
        (Tr D u)⁻¹ ^ (D.R.k * D.R.f)) := by
    rw [le_div_iff₀ (rows_den_pos Y h hGood)]
    calc aT X t ^ 2 / dimPi (hc := D.hcW) u * (wordPairGramNorm D u u' (termReducedGramMatrix Y h.hH h.hHH t) *
          rows_KZ D u u' (termReducedGramMatrix Y h.hH h.hHH t) ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f))
        = wordPairGramNorm D u u' (termReducedGramMatrix Y h.hH h.hHH t) * aT X t ^ 2 * rows_KZ D u u' (termReducedGramMatrix Y h.hH h.hHH t) ^ (2 * D.R.k) *
            (Tr D u)⁻¹ ^ (D.R.k * D.R.f) / dimPi (hc := D.hcW) u := by ring
      _ ≤ _ := h1
  have h3 : aT X t / Real.sqrt (dimPi (hc := D.hcW) u) = Real.sqrt (aT X t ^ 2 / dimPi (hc := D.hcW) u) := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (aT_nonneg X t)]
  rw [h3]
  exact Real.sqrt_le_sqrt h2

include Y in

/- English proof (translation)
Establish `h` using `((rows_thmA Y hThA hSt p hG1 hG2 hs).2 hnd).2.2`. Establish `e1 : G0 (X.abelian₂ (D.s.pfst p)) (gS D) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) = wordPairGramProduct D u u' (termGramMatrix X (D.s.pfst p))` using `hG0 (D.s.pfst p) hG1`. Establish `e2 : G0 (X.abelian₂ (D.s.psnd p)) (gS D) (X.fl (D.s.psnd p)) (X.fl' (D.s.psnd p)) = wordPairGramProduct D u u' (termGramMatrix X (D.s.psnd p))` using `hG0 (D.s.psnd p) hG2`. Rewrite `e2` using `[← X.pLam p, ← X.pfl p]`. Rewrite `h` using `[e1, e2, ← X.s0_eq p, ← rows_gg_eq, rows_Kpair_eq Y hrd, rows_Kt_KZ Y hrd, rows_Kt_KZ Y hrd]`.

Unfold `rows_DeD`. Establish `e3 : (Tr D u)⁻¹ ^ D.R.f = (((Tu D u : ℕ) : ℝ) ^ D.R.f)⁻¹` using `by rw [inv_pow]; rfl`. Rewrite using `[e3]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rows_thmA_deg (hThA : VanishingOnXAndXPlus.adm14 D u u') (hSt : Cnt.Stand D u u') (hG0 : @LatticeDeterminantFactorization D X u u') (hrd : 0 < D.host.rdE)
    (p : D.s.Pair u u') (hG1 : D.s.Gterm (D.s.pfst p) ≠ 0) (hG2 : D.s.Gterm (D.s.psnd p) ≠ 0) (hs : 2 ≤ D.s.s0 p)
    (hnd : ¬ ndP X p) :
    pairDeterminant X p ≤ rows_DeD D u u' (D.s.s0 p) (termGramMatrix X (D.s.pfst p)) (termGramMatrix X (D.s.psnd p)) := by
  have h := ((rows_thmA Y hThA hSt p hG1 hG2 hs).2 hnd).2.2
  have e1 : G0 (X.abelian₂ (D.s.pfst p)) (gS D) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) =
      wordPairGramProduct D u u' (termGramMatrix X (D.s.pfst p)) := hG0 (D.s.pfst p) hG1
  have e2 : G0 (X.abelian₂ (D.s.psnd p)) (gS D) (X.fl (D.s.psnd p)) (X.fl' (D.s.psnd p)) =
      wordPairGramProduct D u u' (termGramMatrix X (D.s.psnd p)) := hG0 (D.s.psnd p) hG2
  rw [← X.pLam p, ← X.pfl p] at e2
  rw [e1, e2, ← X.s0_eq p, ← rows_gg_eq, rows_Kpair_eq Y hrd, rows_Kt_KZ Y hrd, rows_Kt_KZ Y hrd] at h
  unfold rows_DeD
  have e3 : (Tr D u)⁻¹ ^ D.R.f = (((Tu D u : ℕ) : ℝ) ^ D.R.f)⁻¹ := by rw [inv_pow]; rfl
  rw [e3]
  calc pairDeterminant X p ≤ _ := h
    _ = _ := by ring

/- English proof (translation)
Establish `hb` using `d_two_le_b D large₂`. Establish `hb0 : 0 < large₂.sc.b` using `by linarith`. Establish `hm2 : (2 : ℝ) ≤ D.R.m` using `by rw [rows_m_cast]; have : (0 : ℝ) ≤ D.R.rS := by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hf0 : (0 : ℝ) ≤ D.R.f` using `by positivity`.

Establish `h2 : 1 ≤ sizeZ D large₂.sc.b c Z ^ 4` using `one_le_pow₀ (rows_one_le_sizeZ _ _ _)`. Establish `hE : ((2 * D.R.f : ℕ) : ℝ) ≤ c * (D.R.m : ℝ) ^ 2 * D.R.f * (c * D.R.m)`. Establish `e : c * (D.R.m : ℝ) ^ 2 * D.R.f * (c * D.R.m) = (c ^ 2 * (D.R.m : ℝ) ^ 3) * D.R.f` using `by ring`. Rewrite using `[e]`. Use `push_cast`.

Establish `h8 : (2 : ℝ) ≤ c ^ 2 * (D.R.m : ℝ) ^ 3`. Establish `a1 : (1 : ℝ) ≤ c ^ 2` using `one_le_pow₀ hc`. Establish `a2 : (2 : ℝ) ≤ (D.R.m : ℝ) ^ 3` using `by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ D.R.m) (by linarith : (0:ℝ) ≤ D.R.m)]`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `mul_le_mul_of_nonneg_right h8 hf0`.

Establish `h1 : (3 : ℝ) ^ D.R.f ≤ (large₂.sc.b ^ (c * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (c * (D.R.m : ℝ))`. Rewrite using `[← Real.rpow_mul hb0.le]`. Combine the equalities or inequalities in the displayed calculation. Unfold `HHZ`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rows_three_le (D : D7) (large₂ : SizeData₂ D) {c : ℝ} (hc : 1 ≤ c) (Z : GramM D) : (3 : ℝ) ^ D.R.f ≤ HHZ D large₂.sc.b c Z := by
  have hb := d_two_le_b D large₂
  have hb0 : 0 < large₂.sc.b := by linarith
  have hm2 : (2 : ℝ) ≤ D.R.m := by rw [rows_m_cast]; have : (0 : ℝ) ≤ D.R.rS := by positivity
                                   linarith
  have hf0 : (0 : ℝ) ≤ D.R.f := by positivity
  have h2 : 1 ≤ sizeZ D large₂.sc.b c Z ^ 4 := one_le_pow₀ (rows_one_le_sizeZ _ _ _)
  have hE : ((2 * D.R.f : ℕ) : ℝ) ≤ c * (D.R.m : ℝ) ^ 2 * D.R.f * (c * D.R.m) := by
    have e : c * (D.R.m : ℝ) ^ 2 * D.R.f * (c * D.R.m) = (c ^ 2 * (D.R.m : ℝ) ^ 3) * D.R.f := by ring
    rw [e]; push_cast
    have h8 : (2 : ℝ) ≤ c ^ 2 * (D.R.m : ℝ) ^ 3 := by
      have a1 : (1 : ℝ) ≤ c ^ 2 := one_le_pow₀ hc
      have a2 : (2 : ℝ) ≤ (D.R.m : ℝ) ^ 3 := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ D.R.m) (by linarith : (0:ℝ) ≤ D.R.m)]
      nlinarith
    exact mul_le_mul_of_nonneg_right h8 hf0
  have h1 : (3 : ℝ) ^ D.R.f ≤ (large₂.sc.b ^ (c * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (c * (D.R.m : ℝ)) := by
    rw [← Real.rpow_mul hb0.le]
    calc (3 : ℝ) ^ D.R.f ≤ (large₂.sc.b ^ 2) ^ D.R.f := pow_le_pow_left₀ (by norm_num) (by nlinarith) _
      _ = large₂.sc.b ^ ((2 * D.R.f : ℕ) : ℝ) := by rw [Real.rpow_natCast, pow_mul]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) hE
  unfold HHZ
  calc (3 : ℝ) ^ D.R.f ≤ (large₂.sc.b ^ (c * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (c * (D.R.m : ℝ)) * 1 := by rw [mul_one]; exact h1
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

/- English proof (translation)
Establish `hg2` using `two_le_gg_of_count_hypotheses h.hH.1`. Establish `h1` using `rows_KZ_pos Y h gx`. Establish `h2` using `rows_KZ_pos Y h gy`. Establish `h3` using `rows_Tr_pos D u`. Establish `: 0 ≤ gg D` using `by linarith`.

Unfold `rows_DeD`. Check the signs of the components of the expression.
-/
theorem rows_DeD_nonneg (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (s : ℕ) {x y : GramM D}
    (gx : wordPairGramGood X u u' large₂ c x) (gy : wordPairGramGood X u u' large₂ c y) : 0 ≤ rows_DeD D u u' s x y := by
  have hg2 := two_le_gg_of_count_hypotheses h.hH.1
  have h1 := rows_KZ_pos Y h gx
  have h2 := rows_KZ_pos Y h gy
  have h3 := rows_Tr_pos D u
  have : 0 ≤ gg D := by linarith
  unfold rows_DeD
  positivity

/- English proof (translation)
Establish `hg2` using `two_le_gg_of_count_hypotheses h.hH.1`. Establish `hrd` using `d_rdE_pos h.hH.1`. Establish `hDe0` using `rows_DeD_nonneg Y h s gx gy`. Distinguish the cases in `hne : S'.Nonempty`. Take `⟨p₀, hp₀⟩` from `hne`.

Establish `hDe_of : ∀ p ∈ S', pairDeterminant X p ≤ rows_DeD D u u' s x y`. Introduce `p hp`. Take `⟨⟨hG1, hG2, hs0, hnd⟩, e1, e2⟩` from `hS p hp`. Establish `h'` using `rows_thmA_deg Y h.hThA h.hH.2.1 h.hG0 hrd p hG1 hG2 (by rw [hs0]; exact hs) hnd`. Unfold `rows_DeD at h' ⊢`.

Rewrite `h'` using `[hs0, ← gramProductG0_equiv_invariant e1, ← gramProductG0_equiv_invariant e2, ← rows_KZ_inv e1, ← rows_KZ_inv e2]`. Conclude with `h'`. Establish `h1 : 1 ≤ rows_DeD D u u' s x y` using `le_trans (rows_DetGeOne_of h.hH.2.1 p₀ (hS p₀ hp₀).1.1 (hS p₀ hp₀).1.2.1) (hDe_of p₀ hp₀)`. Establish `kb : ∀ Z, wordPairGramGood X u u' large₂ c Z → rows_KZ D u u' Z ^ 2 ≤ 9 ^ D.R.f * HHZ D large₂.sc.b c Z ^ 3`. Introduce and unpack `Z ⟨t, hG, hrel, hE, _⟩`.

Rewrite using `[rows_KZ_inv hE, rows_HHZ_inv hE, ← rows_Kt_KZ Y hrd]`. Conclude with `hK t hG hrel`. Establish `h9 : (9 : ℝ) ^ D.R.f ≤ HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y`. Establish `e : (9 : ℝ) ^ D.R.f = 3 ^ D.R.f * 3 ^ D.R.f` using `by rw [← mul_pow]; norm_num`. Rewrite using `[e]`.

Conclude with `mul_le_mul (rows_three_le D large₂ hc1 x) (rows_three_le D large₂ hc1 y) (by positivity) (le_trans zero_le_one (rows_one_le_HHZ D large₂ h.hc x))`. Establish `hT1 : 1 ≤ Tr D u` using `by unfold Tr; exact_mod_cast (D.mem u).A.T_prime.pos`. Establish `h2 : rows_DeD D u u' s x y ≤ (HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) ^ (3 : ℝ)`. Use `Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.deDegBound D.R.f s (gg D) (Tr D u) (wordPairGramProduct D u u' x) (wordPairGramProduct D u u' y) (rows_KZ D u u' x) (rows_KZ D u u' y) (HHZ D large₂.sc.b c x) (HHZ D large₂.sc.b c y) hg2 hT1 (gramProductG0_pos Y h.hH.1 h.h …` as an intermediate fact. Rewrite using `[show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`.

Conclude with `this`. Take `⟨t1, hG1, hr1, hE1, _⟩` from `gx`. Take `⟨t2, hG2, hr2, hE2, _⟩` from `gy`. Use `rows_count Y h.hH h.hC3 x y (rows_RelZ_inv hE1 (rows_RelZ_term X t1 hG1 hr1)) (rows_RelZ_inv hE2 (rows_RelZ_term X t2 hG2 hr2)) s hs hsk _ h1 h2 (rows_c3B_nonneg D large₂ u h.hc x y s hDe0) _ ?_` and prove the remaining obligations. Introduce `p hp`.

Conclude with `⟨(hS p hp).1.1, (hS p hp).1.2.1, (hS p hp).2.1, (hS p hp).2.2, (hS p hp).1.2.2.1, hDe_of p hp⟩`. Rewrite using `[Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]`. Conclude with `mul_nonneg (rows_massRows_nonneg Y) (rows_c3B_nonneg D large₂ u h.hc x y s hDe0)`.
-/
theorem rows_deg_count (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (hK : rows_KBound Y c)
    (hc1 : 1 ≤ c) (s : ℕ) (hs : 2 ≤ s)
    (hsk : s ≤ D.R.k) (x y : GramM D) (gx : wordPairGramGood X u u' large₂ c x) (gy : wordPairGramGood X u u' large₂ c y)
    (S' : Finset (D.s.Pair u u'))
    (hS : ∀ p ∈ S', clsDeg X s p ∧ ZEquiv (termGramMatrix X (D.s.pfst p)) x ∧ ZEquiv (termGramMatrix X (D.s.psnd p)) y) :
    ∑ p ∈ S', X.wRow p ≤ massRows D Y.F0 Y.what₂ * wordSublatticeTripleBound D large₂ u c x y s (rows_DeD D u u' s x y) := by
  have hg2 := two_le_gg_of_count_hypotheses h.hH.1
  have hrd := d_rdE_pos h.hH.1
  have hDe0 := rows_DeD_nonneg Y h s gx gy
  by_cases hne : S'.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hne
    have hDe_of : ∀ p ∈ S', pairDeterminant X p ≤ rows_DeD D u u' s x y := by
      intro p hp
      obtain ⟨⟨hG1, hG2, hs0, hnd⟩, e1, e2⟩ := hS p hp
      have h' := rows_thmA_deg Y h.hThA h.hH.2.1 h.hG0 hrd p hG1 hG2 (by rw [hs0]; exact hs) hnd
      unfold rows_DeD at h' ⊢
      rw [hs0, ← gramProductG0_equiv_invariant e1, ← gramProductG0_equiv_invariant e2, ← rows_KZ_inv e1, ← rows_KZ_inv e2] at h'
      exact h'
    have h1 : 1 ≤ rows_DeD D u u' s x y :=
      le_trans (rows_DetGeOne_of h.hH.2.1 p₀ (hS p₀ hp₀).1.1 (hS p₀ hp₀).1.2.1) (hDe_of p₀ hp₀)
    have kb : ∀ Z, wordPairGramGood X u u' large₂ c Z → rows_KZ D u u' Z ^ 2 ≤ 9 ^ D.R.f * HHZ D large₂.sc.b c Z ^ 3 := by
      rintro Z ⟨t, hG, hrel, hE, _⟩
      rw [rows_KZ_inv hE, rows_HHZ_inv hE, ← rows_Kt_KZ Y hrd]
      exact hK t hG hrel
    have h9 : (9 : ℝ) ^ D.R.f ≤ HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y := by
      have e : (9 : ℝ) ^ D.R.f = 3 ^ D.R.f * 3 ^ D.R.f := by rw [← mul_pow]; norm_num
      rw [e]
      exact mul_le_mul (rows_three_le D large₂ hc1 x) (rows_three_le D large₂ hc1 y) (by positivity)
        (le_trans zero_le_one (rows_one_le_HHZ D large₂ h.hc x))
    have hT1 : 1 ≤ Tr D u := by unfold Tr; exact_mod_cast (D.mem u).A.T_prime.pos
    have h2 : rows_DeD D u u' s x y ≤ (HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) ^ (3 : ℝ) := by
      have := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.deDegBound D.R.f s (gg D) (Tr D u) (wordPairGramProduct D u u' x) (wordPairGramProduct D u u' y)
        (rows_KZ D u u' x) (rows_KZ D u u' y)
        (HHZ D large₂.sc.b c x) (HHZ D large₂.sc.b c y) hg2 hT1 (gramProductG0_pos Y h.hH.1 h.hT gx).le
        (gramProductG0_pos Y h.hH.1 h.hT gy).le (gramProductG0_le_height Y h.hH h.hHH h.hT gx)
        (gramProductG0_le_height Y h.hH h.hHH h.hT gy) (rows_KZ_pos Y h gx).le (rows_KZ_pos Y h gy).le (kb x gx) (kb y gy) h9
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact this
    obtain ⟨t1, hG1, hr1, hE1, _⟩ := gx
    obtain ⟨t2, hG2, hr2, hE2, _⟩ := gy
    refine rows_count Y h.hH h.hC3 x y (rows_RelZ_inv hE1 (rows_RelZ_term X t1 hG1 hr1))
      (rows_RelZ_inv hE2 (rows_RelZ_term X t2 hG2 hr2)) s hs hsk _ h1 h2
      (rows_c3B_nonneg D large₂ u h.hc x y s hDe0) _ ?_
    intro p hp
    exact ⟨(hS p hp).1.1, (hS p hp).1.2.1, (hS p hp).2.1, (hS p hp).2.2, (hS p hp).1.2.2.1, hDe_of p hp⟩
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]
    exact mul_nonneg (rows_massRows_nonneg Y) (rows_c3B_nonneg D large₂ u h.hc x y s hDe0)

/- English proof (translation)
Establish `hrd` using `d_rdE_pos h.hH.1`. Establish `hb2` using `d_two_le_b D large₂`. Establish `hg2` using `two_le_gg_of_count_hypotheses h.hH.1`. Establish `hc` using `h.hc`. Establish `hv1 : 1 ≤ D.host.v`.

Take `⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩` from `h.hH.1.1`. Conclude with `h19`. Establish `hk1 : 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `hx1` using `rows_one_le_HHZ D large₂ hc x`. Establish `hy1` using `rows_one_le_HHZ D large₂ hc y`.

Establish `sx1` using `rows_one_le_sizeZ (D := D) large₂.sc.b Ch x`. Establish `sy1` using `rows_one_le_sizeZ (D := D) large₂.sc.b Ch y`. Establish `hh0 : 0 ≤ HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y` using `mul_nonneg (by linarith) (by linarith)`. Establish `hP1` using `rows_P_one_le D large₂ c Ch`. Establish `cx : HHZ D large₂.sc.b c x ≤ rows_P D large₂ c Ch * sizeZ D large₂.sc.b Ch x ^ 4` using `rows_HHZ_cmp hrd (by linarith) c Ch x`.

Establish `cy : HHZ D large₂.sc.b c y ≤ rows_P D large₂ c Ch * sizeZ D large₂.sc.b Ch y ^ 4` using `rows_HHZ_cmp hrd (by linarith) c Ch y`. Establish `hαsq : ∀ Z, wordPairGramGood X u u' large₂ c Z → LatticeSumBounds.nTot D.R.k D.R.f D.host.v (wordPairGramProduct D u u' Z) (NT D u) * rows_alD D large₂ u u' c Ca C2 Ch q Z ^ 2 * rows_KZ D u u' Z ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f) ≤ rows_lam D large₂ c Ca C2 Ch q Z`. Introduce `Z hZ`. Establish `e : wordPairGramNorm D u u' Z = LatticeSumBounds.nTot D.R.k D.R.f D.host.v (wordPairGramProduct D u u' Z) (NT D u)` using `d_nProduct h.hH.1 Z`. Rewrite using `[← e]`.

Unfold `rows_alD`. Rewrite using `[Real.sq_sqrt (div_nonneg (rows_lam_nonneg D large₂ c Ca C2 Ch q Z) (rows_den_pos Y h hZ).le)]`. Establish `hd` using `(rows_den_pos Y h hZ).ne'`. Use `le_of_eq ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `n1` using `Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.degRow D.R.k D.R.f s (gg D) D.host.v (Tr D u) (NT D u) (wordPairGramProduct D u u' x) (wordPairGramProduct D u u' y) (rows_KZ D u u' x) (rows_KZ D u u' y) (XiS D u (HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) c s) ((HHZ …`. Establish `hXi : XiS D u (HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) c s ≤ XiS D u (rows_P D large₂ c Ch ^ 2) c s * (sizeZ D large₂.sc.b Ch x * sizeZ D large₂.sc.b Ch y) ^ (4 * (c * D.R.k))`. Use `rows_Xi_le D u hh0 (by positivity) (one_le_mul_of_one_le_of_one_le sx1 sy1) hc ?_ s` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `he : 4 * (c * D.R.k) + 4 * pairCountExponent D c s + 4 * (c * (D.R.rS : ℝ) ^ 2) + (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 - 2 * (q : ℝ) / ((D.R.rS : ℝ) + 1) / 2 ≤ -(12 * ((D.R.rS : ℝ) + 1) ^ 2)`.

Establish `e : 2 * (q : ℝ) / ((D.R.rS : ℝ) + 1) / 2 = (q : ℝ) / ((D.R.rS : ℝ) + 1)` using `by ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `n2` using `rows_num_pair (P := rows_P D large₂ c Ch) (σ₁ := sizeZ D large₂.sc.b Ch x) (σ₂ := sizeZ D large₂.sc.b Ch y) (h₁ := HHZ D large₂.sc.b c x) (h₂ := HHZ D large₂.sc.b c y) (cr := c * (D.R.rS : ℝ) ^ 2) (Γ := rows_GamD D large₂ Ca C2) (a2 := C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 …`. Establish `hA0 : 0 ≤ (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f)`.

Establish `hpi` using `Real.pi_pos`. Establish `: 0 ≤ gg D` using `by linarith`. Establish `: 0 ≤ D.host.v` using `by linarith`. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rows_deg_prod (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (s : ℕ) (hs : 2 ≤ s)
    (hq2 : 4 * (c * D.R.k) + 4 * pairCountExponent D c s + 4 * (c * (D.R.rS : ℝ) ^ 2) +
      (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 + 12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1))
    (x y : GramM D) (gx : wordPairGramGood X u u' large₂ c x) (gy : wordPairGramGood X u u' large₂ c y) :
    wordSublatticeTripleBound D large₂ u c x y s (rows_DeD D u u' s x y) *
        (rows_alD D large₂ u u' c Ca C2 Ch q x * rows_alD D large₂ u u' c Ca C2 Ch q y) ≤
      rows_RD D large₂ u c Ca C2 Ch s * (sizeZ D large₂.sc.b Ch x ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2)) *
        sizeZ D large₂.sc.b Ch y ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2))) := by
  have hrd := d_rdE_pos h.hH.1
  have hb2 := d_two_le_b D large₂
  have hg2 := two_le_gg_of_count_hypotheses h.hH.1
  have hc := h.hc
  have hv1 : 1 ≤ D.host.v := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩ := h.hH.1.1
    exact h19
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hx1 := rows_one_le_HHZ D large₂ hc x
  have hy1 := rows_one_le_HHZ D large₂ hc y
  have sx1 := rows_one_le_sizeZ (D := D) large₂.sc.b Ch x
  have sy1 := rows_one_le_sizeZ (D := D) large₂.sc.b Ch y
  have hh0 : 0 ≤ HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y := mul_nonneg (by linarith) (by linarith)
  have hP1 := rows_P_one_le D large₂ c Ch
  have cx : HHZ D large₂.sc.b c x ≤ rows_P D large₂ c Ch * sizeZ D large₂.sc.b Ch x ^ 4 := rows_HHZ_cmp hrd (by linarith) c Ch x
  have cy : HHZ D large₂.sc.b c y ≤ rows_P D large₂ c Ch * sizeZ D large₂.sc.b Ch y ^ 4 := rows_HHZ_cmp hrd (by linarith) c Ch y
  have hαsq : ∀ Z, wordPairGramGood X u u' large₂ c Z →
      LatticeSumBounds.nTot D.R.k D.R.f D.host.v (wordPairGramProduct D u u' Z) (NT D u) * rows_alD D large₂ u u' c Ca C2 Ch q Z ^ 2 *
        rows_KZ D u u' Z ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f) ≤ rows_lam D large₂ c Ca C2 Ch q Z := by
    intro Z hZ
    have e : wordPairGramNorm D u u' Z = LatticeSumBounds.nTot D.R.k D.R.f D.host.v (wordPairGramProduct D u u' Z) (NT D u) := d_nProduct h.hH.1 Z
    rw [← e]
    unfold rows_alD
    rw [Real.sq_sqrt (div_nonneg (rows_lam_nonneg D large₂ c Ca C2 Ch q Z) (rows_den_pos Y h hZ).le)]
    have hd := (rows_den_pos Y h hZ).ne'
    refine le_of_eq ?_
    calc wordPairGramNorm D u u' Z * (rows_lam D large₂ c Ca C2 Ch q Z /
          (wordPairGramNorm D u u' Z * rows_KZ D u u' Z ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f))) *
          rows_KZ D u u' Z ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f)
        = (wordPairGramNorm D u u' Z * rows_KZ D u u' Z ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f)) *
            (rows_lam D large₂ c Ca C2 Ch q Z /
              (wordPairGramNorm D u u' Z * rows_KZ D u u' Z ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f))) := by ring
      _ = _ := mul_div_cancel₀ _ hd
  have n1 := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.degRow D.R.k D.R.f s (gg D) D.host.v (Tr D u) (NT D u) (wordPairGramProduct D u u' x)
    (wordPairGramProduct D u u' y) (rows_KZ D u u' x) (rows_KZ D u u' y)
    (XiS D u (HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) c s)
    ((HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) ^ pairCountExponent D c s * (c * s * D.R.f) ^ (6 * s * D.R.f))
    (wordSublatticeTripleBound D large₂ u c x y s (rows_DeD D u u' s x y)) (rows_alD D large₂ u u' c Ca C2 Ch q x)
    (rows_alD D large₂ u u' c Ca C2 Ch q y)
    (rows_lam D large₂ c Ca C2 Ch q x) (rows_lam D large₂ c Ca C2 Ch q y) hk1 hs (by linarith) (by linarith)
    (rows_Tr_pos D u) (rows_NT_pos D u) (gramProductG0_pos Y h.hH.1 h.hT gx) (gramProductG0_pos Y h.hH.1 h.hT gy)
    (rows_KZ_pos Y h gx) (rows_KZ_pos Y h gy) (rows_XiS_nonneg D u hh0 hc s)
    (by positivity) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (le_of_eq (by unfold wordSublatticeTripleBound pairCountExponent rows_DeD; ring)) (hαsq x gx) (hαsq y gy)
  have hXi : XiS D u (HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) c s ≤
      XiS D u (rows_P D large₂ c Ch ^ 2) c s * (sizeZ D large₂.sc.b Ch x * sizeZ D large₂.sc.b Ch y) ^ (4 * (c * D.R.k)) := by
    refine rows_Xi_le D u hh0 (by positivity) (one_le_mul_of_one_le_of_one_le sx1 sy1) hc ?_ s
    calc HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y
        ≤ (rows_P D large₂ c Ch * sizeZ D large₂.sc.b Ch x ^ 4) * (rows_P D large₂ c Ch * sizeZ D large₂.sc.b Ch y ^ 4) :=
          mul_le_mul cx cy (by linarith) (by positivity)
      _ = rows_P D large₂ c Ch ^ 2 * (sizeZ D large₂.sc.b Ch x * sizeZ D large₂.sc.b Ch y) ^ 4 := by ring
  have he : 4 * (c * D.R.k) + 4 * pairCountExponent D c s + 4 * (c * (D.R.rS : ℝ) ^ 2) +
      (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 -
      2 * (q : ℝ) / ((D.R.rS : ℝ) + 1) / 2 ≤ -(12 * ((D.R.rS : ℝ) + 1) ^ 2) := by
    have e : 2 * (q : ℝ) / ((D.R.rS : ℝ) + 1) / 2 = (q : ℝ) / ((D.R.rS : ℝ) + 1) := by ring
    rw [e]; linarith
  have n2 := rows_num_pair (P := rows_P D large₂ c Ch) (σ₁ := sizeZ D large₂.sc.b Ch x) (σ₂ := sizeZ D large₂.sc.b Ch y)
    (h₁ := HHZ D large₂.sc.b c x) (h₂ := HHZ D large₂.sc.b c y)
    (cr := c * (D.R.rS : ℝ) ^ 2) (Γ := rows_GamD D large₂ Ca C2) (a2 := C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2)
    (dq := 2 * (q : ℝ) / ((D.R.rS : ℝ) + 1)) (E1 := pairCountExponent D c s) (F6 := (c * s * D.R.f) ^ (6 * s * D.R.f))
    (XiH := XiS D u (HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) c s) (XiP := XiS D u (rows_P D large₂ c Ch ^ 2) c s)
    (ck := c * D.R.k) (e := 12 * ((D.R.rS : ℝ) + 1) ^ 2) (l₁ := rows_lam D large₂ c Ca C2 Ch q x)
    (l₂ := rows_lam D large₂ c Ca C2 Ch q y)
    hP1 sx1 sy1 hx1 hy1 cx cy (by positivity) (rows_GamD_nonneg D large₂ Ca C2) (pairCountExponent_nonneg D hc s) (by positivity)
    (rows_XiS_nonneg D u hh0 hc s) hXi (rows_lam_eq D large₂ c Ca C2 Ch q x) (rows_lam_eq D large₂ c Ca C2 Ch q y) he
  have hA0 : 0 ≤ (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) *
      ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) := by
    have hpi := Real.pi_pos
    have : 0 ≤ gg D := by linarith
    have : 0 ≤ D.host.v := by linarith
    positivity
  calc wordSublatticeTripleBound D large₂ u c x y s (rows_DeD D u u' s x y) *
        (rows_alD D large₂ u u' c Ca C2 Ch q x * rows_alD D large₂ u u' c Ca C2 Ch q y)
      = wordSublatticeTripleBound D large₂ u c x y s (rows_DeD D u u' s x y) * rows_alD D large₂ u u' c Ca C2 Ch q x *
          rows_alD D large₂ u u' c Ca C2 Ch q y := by ring
    _ ≤ _ := n1
    _ = (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) *
          ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) *
          (XiS D u (HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) c s *
            ((HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) ^ pairCountExponent D c s * (c * s * D.R.f) ^ (6 * s * D.R.f)) *
            Real.sqrt (rows_lam D large₂ c Ca C2 Ch q x * rows_lam D large₂ c Ca C2 Ch q y)) := by ring
    _ ≤ (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) *
          ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) *
          (XiS D u (rows_P D large₂ c Ch ^ 2) c s * ((rows_P D large₂ c Ch ^ pairCountExponent D c s) ^ 2 *
            (rows_P D large₂ c Ch ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 * (c * s * D.R.f) ^ (6 * s * D.R.f) * rows_GamD D large₂ Ca C2) *
            (sizeZ D large₂.sc.b Ch x ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2)) *
              sizeZ D large₂.sc.b Ch y ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2)))) :=
        mul_le_mul_of_nonneg_left n2 hA0
    _ = _ := by unfold rows_RD; ring

/- English proof (translation)
Establish `hg2` using `two_le_gg_of_count_hypotheses h.hH.1`. Establish `hv1 : 1 ≤ D.host.v`. Take `⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩` from `h.hH.1.1`. Conclude with `h19`. Establish `hP1` using `rows_P_one_le D large₂ c Ch`.

Establish `hG` using `rows_GamD_nonneg D large₂ Ca C2`. Establish `hXiP0 : 0 ≤ XiS D u (rows_P D large₂ c Ch ^ 2) c s` using `rows_XiS_nonneg D u (by positivity) h.hc s`. Establish `hpi` using `Real.pi_pos`. Establish `: 0 ≤ gg D` using `by linarith`. Establish `: 0 ≤ D.host.v` using `by linarith`.

Use `h.hc` as an intermediate fact. Unfold `rows_RD`. Check the signs of the components of the expression.
-/
theorem rows_RD_nonneg (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (s : ℕ) :
    0 ≤ rows_RD D large₂ u c Ca C2 Ch s := by
  have hg2 := two_le_gg_of_count_hypotheses h.hH.1
  have hv1 : 1 ≤ D.host.v := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩ := h.hH.1.1
    exact h19
  have hP1 := rows_P_one_le D large₂ c Ch
  have hG := rows_GamD_nonneg D large₂ Ca C2
  have hXiP0 : 0 ≤ XiS D u (rows_P D large₂ c Ch ^ 2) c s := rows_XiS_nonneg D u (by positivity) h.hc s
  have hpi := Real.pi_pos
  have : 0 ≤ gg D := by linarith
  have : 0 ≤ D.host.v := by linarith
  have := h.hc
  unfold rows_RD
  positivity

/- English proof (translation)
Use `rowBound_relevant Y (fun p hp => ⟨hp.1, hp.2.1⟩) ?_` and prove the remaining obligations. Introduce `S hS`. Establish `sp1 : ∀ p ∈ S, ZEquiv (termGramMatrix X (D.s.pfst p)) (termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p)) ∧ wordPairGramGood X u u' large₂ c (termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p))` using `fun p hp => rows_Zr_spec Y h.hH h.hHH _ (hS p hp).1.1 (hS p hp).2.1`. Establish `sp2 : ∀ p ∈ S, ZEquiv (termGramMatrix X (D.s.psnd p)) (termReducedGramMatrix Y h.hH h.hHH (D.s.psnd p)) ∧ wordPairGramGood X u u' large₂ c (termReducedGramMatrix Y h.hH h.hHH (D.s.psnd p))` using `fun p hp => rows_Zr_spec Y h.hH h.hHH _ (hS p hp).1.2.1 (hS p hp).2.2`. Establish `key` using `weighted_sum_le' S (fun p => X.wRow p) (fun p => aT X (D.s.pfst p) / Real.sqrt (dimPi (hc := D.hcW) u)) (fun p => aT X (D.s.psnd p) / Real.sqrt (dimPi (hc := D.hcW) u)) (fun p => termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p)) (fun p => termReducedGramMatrix Y h.hH h.hHH (D.s.ps …`.

Introduce and unpack `x y ⟨p1, hp1, rfl⟩ ⟨p2, hp2, rfl⟩ S' hS' hl`. Use `rows_deg_count Y h hK hc1 s hs hsk _ _ (sp1 p1 hp1).2 (sp2 p2 hp2).2 S' fun p hp => ?_` and prove the remaining obligations. Use `⟨(hS p (hS' hp)).1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← (hl p hp).1]`. Conclude with `(sp1 p (hS' hp)).1`.

Rewrite using `[← (hl p hp).2]`. Conclude with `(sp2 p (hS' hp)).1)`. Use the proof step `(by`. Introduce and unpack `x y ⟨p1, hp1, rfl⟩ ⟨p2, hp2, rfl⟩`. Conclude with `rows_deg_prod Y h s hs hq2 _ _ (sp1 p1 hp1).2 (sp2 p2 hp2).2)`.

Use the proof step `(fun x => Real.sqrt_nonneg _)`. Use the proof step `(fun x => Real.rpow_nonneg (le_trans zero_le_one (rows_one_le_sizeZ _ _ _)) _)`. Use the proof step `(fun 𝒵 h𝒵 => rows_nd_size Y h 𝒵 fun Z hZ => by obtain ⟨p, hp, rfl⟩ := h𝒵 Z hZ; exact (sp1 p hp).2)`. Use the proof step `(fun 𝒵 h𝒵 => rows_nd_size Y h 𝒵 fun Z hZ => by obtain ⟨p, hp, rfl⟩ := h𝒵 Z hZ; exact (sp2 p hp).2)`. Rewrite using `[rows_wP_sum h.hdim S]`.

Combine the equalities or inequalities in the displayed calculation. Unfold `rows_degB`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rows_Deg_record (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (hK : rows_KBound Y c)
    (hc1 : 1 ≤ c) (s : ℕ) (hs : 2 ≤ s) (hsk : s ≤ D.R.k)
    (hq2 : 4 * (c * D.R.k) + 4 * pairCountExponent D c s + 4 * (c * (D.R.rS : ℝ) ^ 2) +
      (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 + 12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1)) :
    RowBound X Y (clsDeg X s) (rows_degB D large₂ u c Ca C2 Ch s) := by
  refine rowBound_relevant Y (fun p hp => ⟨hp.1, hp.2.1⟩) ?_
  intro S hS
  have sp1 : ∀ p ∈ S, ZEquiv (termGramMatrix X (D.s.pfst p)) (termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p)) ∧
      wordPairGramGood X u u' large₂ c (termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p)) := fun p hp =>
    rows_Zr_spec Y h.hH h.hHH _ (hS p hp).1.1 (hS p hp).2.1
  have sp2 : ∀ p ∈ S, ZEquiv (termGramMatrix X (D.s.psnd p)) (termReducedGramMatrix Y h.hH h.hHH (D.s.psnd p)) ∧
      wordPairGramGood X u u' large₂ c (termReducedGramMatrix Y h.hH h.hHH (D.s.psnd p)) := fun p hp =>
    rows_Zr_spec Y h.hH h.hHH _ (hS p hp).1.2.1 (hS p hp).2.2
  have key := weighted_sum_le' S (fun p => X.wRow p) (fun p => aT X (D.s.pfst p) / Real.sqrt (dimPi (hc := D.hcW) u))
    (fun p => aT X (D.s.psnd p) / Real.sqrt (dimPi (hc := D.hcW) u)) (fun p => termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p))
    (fun p => termReducedGramMatrix Y h.hH h.hHH (D.s.psnd p)) (massRows D Y.F0 Y.what₂) (rows_RD D large₂ u c Ca C2 Ch s)
    (rows_Phi D large₂ c Ch) (fun x y => wordSublatticeTripleBound D large₂ u c x y s (rows_DeD D u u' s x y))
    (rows_alD D large₂ u u' c Ca C2 Ch q) (fun Z => sizeZ D large₂.sc.b Ch Z ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2)))
    (rows_massRows_nonneg Y) (rows_RD_nonneg Y h s)
    (fun p _ => (X.wRow_pos p).le) (fun p _ => div_nonneg (aT_nonneg _ _) (Real.sqrt_nonneg _))
    (fun p _ => div_nonneg (aT_nonneg _ _) (Real.sqrt_nonneg _))
    (fun p hp => rows_deg_term Y h _ (hS p hp).1.1 (hS p hp).2.1)
    (fun p hp => rows_deg_term Y h _ (hS p hp).1.2.1 (hS p hp).2.2)
    (by
      rintro x y ⟨p1, hp1, rfl⟩ ⟨p2, hp2, rfl⟩ S' hS' hl
      refine rows_deg_count Y h hK hc1 s hs hsk _ _ (sp1 p1 hp1).2 (sp2 p2 hp2).2 S' fun p hp => ?_
      refine ⟨(hS p (hS' hp)).1, ?_, ?_⟩
      · rw [← (hl p hp).1]; exact (sp1 p (hS' hp)).1
      · rw [← (hl p hp).2]; exact (sp2 p (hS' hp)).1)
    (by
      rintro x y ⟨p1, hp1, rfl⟩ ⟨p2, hp2, rfl⟩
      exact rows_deg_prod Y h s hs hq2 _ _ (sp1 p1 hp1).2 (sp2 p2 hp2).2)
    (fun x => Real.sqrt_nonneg _)
    (fun x => Real.rpow_nonneg (le_trans zero_le_one (rows_one_le_sizeZ _ _ _)) _)
    (fun 𝒵 h𝒵 => rows_nd_size Y h 𝒵 fun Z hZ => by obtain ⟨p, hp, rfl⟩ := h𝒵 Z hZ; exact (sp1 p hp).2)
    (fun 𝒵 h𝒵 => rows_nd_size Y h 𝒵 fun Z hZ => by obtain ⟨p, hp, rfl⟩ := h𝒵 Z hZ; exact (sp2 p hp).2)
  rw [rows_wP_sum h.hdim S]
  calc dimPi (hc := D.hcW) u * _
      ≤ dimPi (hc := D.hcW) u * (massRows D Y.F0 Y.what₂ * (rows_RD D large₂ u c Ca C2 Ch s * rows_Phi D large₂ c Ch ^ 2)) :=
        mul_le_mul_of_nonneg_left key h.hdim.le
    _ = massRows D Y.F0 Y.what₂ * dimPi (hc := D.hcW) u * rows_degB D large₂ u c Ca C2 Ch s := by
        unfold rows_degB; ring

end Deg

end Formalism.MainNotions.BridgeLemma₂

end
