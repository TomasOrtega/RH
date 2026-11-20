import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOneIdealIffAdditiveValuationPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeGapBound
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OneLeLetterBlockLength
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.TypeSize

variable {D : D7}

/- English proof (translation)
Establish `h : Fintype.card D.host.TT ≤ Fintype.card D.what₂.Tau`. Use `Fintype.card_le_of_injective (fun t => D.eTau.symm ⟨D.R.tau1 t, (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩) ?_` and prove the remaining obligations. Introduce `a b hab`. Establish `h1` using `congrArg Subtype.val (D.eTau.symm.injective hab)`. Conclude with `Subtype.ext (GlobalTheory.FockDegreeGap.tau1_injective h1)`.

Rewrite `h` using `[Fintype.card_coe, D.what₂.card_Tau]`. Conclude with `h` after adjusting the coercions.
-/
theorem card_TT_le (D : D7) : (D.host.TT.card : ℝ) ≤ D.R.f := by
  have h : Fintype.card D.host.TT ≤ Fintype.card D.what₂.Tau := by
    refine Fintype.card_le_of_injective
      (fun t => D.eTau.symm ⟨D.R.tau1 t, (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩) ?_
    intro a b hab
    have h1 := congrArg Subtype.val (D.eTau.symm.injective hab)
    exact Subtype.ext (GlobalTheory.FockDegreeGap.tau1_injective h1)
  rw [Fintype.card_coe, D.what₂.card_Tau] at h
  exact_mod_cast h

/- English proof (translation)
Take `⟨j1, j2⟩` from `Finset.mem_Icc.1 hj`. Take `⟨e1, e2, e3⟩` from `GlobalTheory.FockDegreeGap.errors_le h P`. Establish `hb` using `GlobalTheory.HCEntries.one_le_b L`. Establish `hb'` using `GlobalTheory.HCEntries.b'_pos L`. Establish `hbb : L.sc.b' ≤ L.sc.b`.

Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hS, -⟩` from `h`. Combine the linear relations using `[GlobalTheory.HCEntries.b'_Sc_le hS, L.Sc_pos]`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hbx : L.sc.b' / L.sc.x ≤ L.sc.b` using `(div_le_self hb'.le (by linarith)).trans hbb`. Establish `hTT` using `card_TT_le D`.

Establish `hf0 : (0 : ℝ) ≤ D.R.f` using `Nat.cast_nonneg _`. Establish `hTT0 : (0 : ℝ) ≤ D.host.TT.card` using `Nat.cast_nonneg _`. Establish `hw0 : 0 ≤ ∑ τ : D.what₂.Tau, wj D j τ` using `Finset.sum_nonneg fun τ _ => (GlobalTheory.HCEntries.wj_bounds h hx j j1 j2 τ).1`. Establish `hw1 : ∑ τ : D.what₂.Tau, wj D j τ ≤ D.R.f * (3 * L.sc.b)`. Use `Finset.sum_le_card_nsmul (Finset.univ : Finset D.what₂.Tau) (fun τ => wj D j τ) (3 * L.sc.b) (fun τ _ => (GlobalTheory.HCEntries.wj_bounds h hx j j1 j2 τ).2)` as an intermediate fact.

Rewrite `this` using `[Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]`. Then use the resulting hypothesis. Establish `hS` using `L.Sc_pos`. Establish `he` using `L.etaSz_pos`. Establish `hN0 : (0 : ℝ) ≤ Formalism.MainNotions.G.Nm D` using `by unfold Formalism.MainNotions.G.Nm; positivity`. Establish `hmt : (D.R.m : ℝ) * D.R.t * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz`.

Establish `: (0 : ℝ) ≤ D.R.m` using `Nat.cast_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Establish `hkN : (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D ≤ L.sc.b` using `e3`. Use `set Y : ℝ := (D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz + (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D) + (D.host.TT.card : ℝ) * L.sc.b' / L.sc.x with hY`. Establish `hY0 : 0 ≤ Y`.

Rewrite using `[hY]`. Establish `: 0 ≤ (D.R.m : ℝ) * D.R.t * L.etaSz` using `by positivity`. Establish `: 0 ≤ (D.R.k : ℝ) * L.Sc` using `by positivity`. Establish `: 0 ≤ (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D` using `by positivity`. Establish `: 0 ≤ (D.host.TT.card : ℝ) * L.sc.b' / L.sc.x` using `by positivity`.

Check the signs of the components of the expression. Establish `hY1 : Y ≤ 4 * D.R.f * L.sc.b`. Rewrite using `[hY, mul_div_assoc]`. Establish `a1 : (D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz + (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D) ≤ D.R.f * (3 * L.sc.b)` using `mul_le_mul_of_nonneg_left (by linarith) hf0`. Establish `a2 : (D.host.TT.card : ℝ) * (L.sc.b' / L.sc.x) ≤ D.R.f * L.sc.b` using `mul_le_mul hTT hbx (by positivity) hf0`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hCY : |C * Y| ≤ 4 * |C| * D.R.f * L.sc.b`. Rewrite using `[abs_mul, abs_of_nonneg hY0]`. Combine the equalities or inequalities in the displayed calculation. Establish `e : WeightDegreeSizes.errG L C j = 2 * (∑ τ : D.what₂.Tau, wj D j τ) + C * Y`.

Unfold `WeightDegreeSizes.errG`. Rewrite using `[hY]`. Rewrite using `[e]`. Use `(abs_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[abs_of_nonneg (by positivity : 0 ≤ 2 * (∑ τ : D.what₂.Tau, wj D j τ))]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem errG_abs_le {L : SizeData₂ D} (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (C : ℝ) (j : ℕ)
    (hj : j ∈ SizeData₂.lifts D) : |WeightDegreeSizes.errG L C j| ≤ (6 + 4 * |C|) * D.R.f * L.sc.b := by
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨e1, e2, e3⟩ := GlobalTheory.FockDegreeGap.errors_le h P
  have hb := GlobalTheory.HCEntries.one_le_b L
  have hb' := GlobalTheory.HCEntries.b'_pos L
  have hbb : L.sc.b' ≤ L.sc.b := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hS, -⟩ := h
    linarith [GlobalTheory.HCEntries.b'_Sc_le hS, L.Sc_pos]
  have hx0 : 0 < L.sc.x := by linarith
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b := (div_le_self hb'.le (by linarith)).trans hbb
  have hTT := card_TT_le D
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hTT0 : (0 : ℝ) ≤ D.host.TT.card := Nat.cast_nonneg _
  have hw0 : 0 ≤ ∑ τ : D.what₂.Tau, wj D j τ :=
    Finset.sum_nonneg fun τ _ => (GlobalTheory.HCEntries.wj_bounds h hx j j1 j2 τ).1
  have hw1 : ∑ τ : D.what₂.Tau, wj D j τ ≤ D.R.f * (3 * L.sc.b) := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset D.what₂.Tau) (fun τ => wj D j τ) (3 * L.sc.b)
      (fun τ _ => (GlobalTheory.HCEntries.wj_bounds h hx j j1 j2 τ).2)
    rwa [Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at this
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hN0 : (0 : ℝ) ≤ Formalism.MainNotions.G.Nm D := by unfold Formalism.MainNotions.G.Nm; positivity
  have hmt : (D.R.m : ℝ) * D.R.t * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by
    have : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
    nlinarith
  have hkN : (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D ≤ L.sc.b := e3
  set Y : ℝ := (D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz + (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D) +
    (D.host.TT.card : ℝ) * L.sc.b' / L.sc.x with hY
  have hY0 : 0 ≤ Y := by
    rw [hY]
    have : 0 ≤ (D.R.m : ℝ) * D.R.t * L.etaSz := by positivity
    have : 0 ≤ (D.R.k : ℝ) * L.Sc := by positivity
    have : 0 ≤ (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D := by positivity
    have : 0 ≤ (D.host.TT.card : ℝ) * L.sc.b' / L.sc.x := by positivity
    positivity
  have hY1 : Y ≤ 4 * D.R.f * L.sc.b := by
    rw [hY, mul_div_assoc]
    have a1 : (D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz + (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D) ≤
        D.R.f * (3 * L.sc.b) := mul_le_mul_of_nonneg_left (by linarith) hf0
    have a2 : (D.host.TT.card : ℝ) * (L.sc.b' / L.sc.x) ≤ D.R.f * L.sc.b :=
      mul_le_mul hTT hbx (by positivity) hf0
    linarith
  have hCY : |C * Y| ≤ 4 * |C| * D.R.f * L.sc.b := by
    rw [abs_mul, abs_of_nonneg hY0]
    calc |C| * Y ≤ |C| * (4 * D.R.f * L.sc.b) := mul_le_mul_of_nonneg_left hY1 (abs_nonneg _)
      _ = _ := by ring
  have e : WeightDegreeSizes.errG L C j = 2 * (∑ τ : D.what₂.Tau, wj D j τ) + C * Y := by
    unfold WeightDegreeSizes.errG; rw [hY]
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg (by positivity : 0 ≤ 2 * (∑ τ : D.what₂.Tau, wj D j τ))]
  nlinarith

/- English proof (translation)
Introduce `i u j hj`. Establish `hL : 1 ≤ L.sc.L` using `Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le`. Establish `hmn` using `D.R.two_le_m`. Establish `hkn` using `D.R.m_add_three_le_k`. Establish `hmfn : D.R.m ≤ D.R.f` using `D.R.m_le_f`.

Establish `hm : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast (by omega : 1 ≤ D.R.m)`. Establish `hk : (1 : ℝ) ≤ D.R.k` using `by exact_mod_cast (by omega : 1 ≤ D.R.k)`. Establish `hmf : (D.R.m : ℝ) ≤ D.R.f` using `by exact_mod_cast hmfn`. Establish `hf : (1 : ℝ) ≤ D.R.f` using `hm.trans hmf`. Establish `ht : (1 : ℝ) ≤ D.R.t` using `L.t_win.1`.

Establish `hN : (1 : ℝ) ≤ D.R.N D.R.m`. Conclude with `(by unfold Ranks.N; omega : 1 ≤ D.R.N D.R.m)` after adjusting the coercions. Establish `hη0` using `L.etaSz_pos.le`. Establish `hNη : (D.R.N D.R.m : ℝ) ^ 2 ≤ L.etaSz`. Establish `a1` using `P.h0_ge.2.2.2.2.1`.

Establish `a2 : LevelStarExponents.h0 L ≤ L.etaSz` using `div_le_self hη0 hm`. Establish `a3 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (D.R.N D.R.m : ℝ) ^ 3` using `pow_le_pow_right₀ hN (by norm_num)`. Establish `a4 : 0 ≤ (D.R.N D.R.m : ℝ) ^ 3` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfη : (D.R.f : ℝ) * L.etaSz ≤ L.sc.b`.

Establish `a1` using `P.eta_le`. Rewrite `a1` using `[le_div_iff₀ (by positivity)]`. Establish `a2 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * (D.R.k : ℝ) ^ 3` using `one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht) (one_le_pow₀ hk)`. Establish `a3 : (D.R.f : ℝ) * L.etaSz ≤ (D.R.f : ℝ) * L.etaSz * ((D.R.t : ℝ) ^ 3 * (D.R.k : ℝ) ^ 3)` using `le_mul_of_one_le_right (by positivity) a2`. Combine the equalities or inequalities in the displayed calculation.

Establish `hg0 : (0 : ℝ) < D.host.g i` using `by exact_mod_cast (D.host.g_prime i).pos`. Establish `hlg0 : 0 ≤ Real.log (D.host.g i)` using `Real.log_natCast_nonneg _`. Establish `hlg : Real.log (D.host.g i) ≤ (P.CYL + 1) * L.sc.L`. Take `⟨Y, -, -, hY, hg⟩` from `P.g_Y`. Establish `hY0 : 0 < Y` using `by linarith [(hg i).2]`.

Establish `a1 : Real.log (D.host.g i) ≤ Real.log (2 * Y)` using `Real.log_le_log hg0 (hg i).2`. Rewrite `a1` using `[Real.log_mul (by norm_num) hY0.ne']`. Establish `a2 : Real.log 2 ≤ 2 - 1` using `Real.log_le_sub_one_of_pos (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key` using `GlobalTheory.TypeLoss.arith_bound (WeightDegreeSizes.errG L Cd j) ((padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) * Real.log (D.host.g i)) _ (Real.log (D.host.g i)) D.R.f D.R.m L.sc.b L.sc.L (D.R.N D.R.m) L.etaSz (6 + 4 * |Cd|) C₂ c.g P.CYL L.B0 rfl hf hm hL hN P.CYL_pos.le (err …`.

Establish `e : (WeightDegreeSizes.errG L Cd j + 2 * (padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) + 2 * (c.g * (D.R.f : ℝ) * (Formalism.MainNotions.G.Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz))) * Real.log (D.host.g i : ℝ) = WeightDegreeSizes.errG L Cd j * Real.log (D.host.g i) + 2 * ((padicVa …`. Unfold `Formalism.MainNotions.G.Nm`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(le_abs_self _).trans key`.
-/
theorem typePrime_sizes_le_budget_single {L : SizeData₂ D} (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (c : ErrC) (Cd C₂ : ℝ)
    (h2 : FactDGam D C₂) :
    WeightDegreeSizes.TypePrimeSizeBound D L c Cd (|(6 + 4 * |Cd|)| * (P.CYL + 1) + 2 * |C₂| + 4 * |c.g| * (P.CYL + 1)) := by
  intro i u j hj
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hmn := D.R.two_le_m
  have hkn := D.R.m_add_three_le_k
  have hmfn : D.R.m ≤ D.R.f := D.R.m_le_f
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hmf : (D.R.m : ℝ) ≤ D.R.f := by exact_mod_cast hmfn
  have hf : (1 : ℝ) ≤ D.R.f := hm.trans hmf
  have ht : (1 : ℝ) ≤ D.R.t := L.t_win.1
  have hN : (1 : ℝ) ≤ D.R.N D.R.m := by
    exact_mod_cast (by unfold Ranks.N; omega : 1 ≤ D.R.N D.R.m)
  have hη0 := L.etaSz_pos.le
  have hNη : (D.R.N D.R.m : ℝ) ^ 2 ≤ L.etaSz := by
    have a1 := P.h0_ge.2.2.2.2.1
    have a2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη0 hm
    have a3 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (D.R.N D.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hN (by norm_num)
    have a4 : 0 ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
    linarith
  have hfη : (D.R.f : ℝ) * L.etaSz ≤ L.sc.b := by
    have a1 := P.eta_le
    rw [le_div_iff₀ (by positivity)] at a1
    have a2 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * (D.R.k : ℝ) ^ 3 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht) (one_le_pow₀ hk)
    have a3 : (D.R.f : ℝ) * L.etaSz ≤ (D.R.f : ℝ) * L.etaSz * ((D.R.t : ℝ) ^ 3 * (D.R.k : ℝ) ^ 3) :=
      le_mul_of_one_le_right (by positivity) a2
    calc _ ≤ _ := a3
      _ = L.etaSz * ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) := by ring
      _ ≤ _ := a1
  have hg0 : (0 : ℝ) < D.host.g i := by exact_mod_cast (D.host.g_prime i).pos
  have hlg0 : 0 ≤ Real.log (D.host.g i) := Real.log_natCast_nonneg _
  have hlg : Real.log (D.host.g i) ≤ (P.CYL + 1) * L.sc.L := by
    obtain ⟨Y, -, -, hY, hg⟩ := P.g_Y
    have hY0 : 0 < Y := by linarith [(hg i).2]
    have a1 : Real.log (D.host.g i) ≤ Real.log (2 * Y) := Real.log_le_log hg0 (hg i).2
    rw [Real.log_mul (by norm_num) hY0.ne'] at a1
    have a2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have key := GlobalTheory.TypeLoss.arith_bound (WeightDegreeSizes.errG L Cd j)
    ((padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) * Real.log (D.host.g i)) _ (Real.log (D.host.g i))
    D.R.f D.R.m L.sc.b L.sc.L (D.R.N D.R.m) L.etaSz (6 + 4 * |Cd|) C₂ c.g P.CYL L.B0 rfl hf hm hL hN P.CYL_pos.le
    (errG_abs_le h P hx Cd j hj)
    (mul_nonneg (Nat.cast_nonneg _) hlg0)
    ((GlobalTheory.TypeLoss.padic_log_le _ _ (D.host.g_prime i)).trans (h2 u)) rfl hlg0 hlg hη0 hNη hmf hfη
  have e : (WeightDegreeSizes.errG L Cd j + 2 * (padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) +
      2 * (c.g * (D.R.f : ℝ) * (Formalism.MainNotions.G.Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz))) * Real.log (D.host.g i : ℝ) =
      WeightDegreeSizes.errG L Cd j * Real.log (D.host.g i) +
        2 * ((padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) * Real.log (D.host.g i)) +
        2 * (c.g * (D.R.f : ℝ) * ((D.R.N D.R.m : ℝ) ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz)) * Real.log (D.host.g i) := by
    unfold Formalism.MainNotions.G.Nm; ring
  rw [e]
  exact (le_abs_self _).trans key

/- English proof (translation)
Introduce `eps Fm _ _ ⟨C₂, x₂, h2⟩ Cd`. Use `⟨max (|(6 + 4 * |Cd|)| * (Fm.CYL + 1) + 2 * |C₂| + 4 * |Fm.cX.err.g| * (Fm.CYL + 1)) 0, max 2 x₂, le_max_right _ _, ?_⟩` and prove the remaining obligations. Introduce `x hx0 hx i`. Establish `a` using `typePrime_sizes_le_budget_single (Fm.sizes x hx i) (Fm.params x hx i) (by rw [Fm.L_x x i hx]; exact (le_max_left _ _).trans hx0) Fm.cX.err Cd C₂ (h2 x ((le_max_right _ _).trans hx0) i)`. Rewrite `a` using `[Fm.params_CYL x hx i]`.

Introduce `k u j hj`. Conclude with `(a k u j hj).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (WeightDegreeSizes.loss_bound_nonneg _))`.
-/
theorem typePrimeSizeBound_of_eps_lt_one_div_fiftyTwo : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → DGamSize Fm → ∀ Cd : ℝ, ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.TypePrimeSizeBound (Fm.D x i) (Fm.L x i) Fm.cX.err Cd C := by
  intro eps Fm _ _ ⟨C₂, x₂, h2⟩ Cd
  refine ⟨max (|(6 + 4 * |Cd|)| * (Fm.CYL + 1) + 2 * |C₂| + 4 * |Fm.cX.err.g| * (Fm.CYL + 1)) 0, max 2 x₂,
    le_max_right _ _, ?_⟩
  · intro x hx0 hx i
    have a := typePrime_sizes_le_budget_single (Fm.sizes x hx i) (Fm.params x hx i)
      (by rw [Fm.L_x x i hx]; exact (le_max_left _ _).trans hx0) Fm.cX.err Cd C₂
      (h2 x ((le_max_right _ _).trans hx0) i)
    rw [Fm.params_CYL x hx i] at a
    intro k u j hj
    exact (a k u j hj).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (WeightDegreeSizes.loss_bound_nonneg _))

end GlobalTheory.TypeSize

end
