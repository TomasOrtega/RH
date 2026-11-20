import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThresholdBounds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData

noncomputable section

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt

namespace Formalism.L2.SG.Pf.ThresholdAtPlaceBounds

/- English proof (translation)
Introduce `x hx`. Take `⟨i, -, -, hx⟩` from `hx`. Establish `hC0 : 0 < C` using `by linarith`. Break down `hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨s, -, -, rfl⟩ | rfl` into its components or cases. Use `Finset.prod_pos fun w _ => ?_` and prove the remaining obligations.

Establish `hw` using `hB1 w`. Unfold `Formalism.FourierDecayAlt.Sz.xHat`. Check the signs of the components of the expression. Use `Finset.prod_pos fun w _ => ?_` and prove the remaining obligations. Establish `hw` using `hB w`.

Unfold `Formalism.FourierDecayAlt.Sz.xHat`. Check the signs of the components of the expression. Use `Finset.prod_pos fun w _ => ?_` and prove the remaining obligations. Establish `hw` using `hB w`. Unfold `Formalism.FourierDecayAlt.Sz.lamHat`.

Check the signs of the components of the expression. Use `Finset.prod_pos fun w _ => ?_` and prove the remaining obligations. Establish `hw` using `hB w`. Establish `hs : 0 < Real.sqrt (T * T')` using `Real.sqrt_pos.mpr hTT`. Unfold `Formalism.FourierDecayAlt.Sz.lamPrimeHat`.

Apply `Real.sqrt_pos.mpr` to reduce the goal to its premises. Check the signs of the components of the expression.
-/
theorem thrSet_pos {ι : Type} [Fintype ι] (G : Sz.Glob ι) {C : ℝ} (hC : 1 ≤ C) {de de' : ℕ → ℝ} {T T' : ℝ} {l : ℕ}
    (hB : ∀ w, 0 < G.supI de de' T T' l w) (hB1 : ∀ w, 0 < G.cutSupLong de de' T T' l w)
    (hka : 0 < G.ka) (hN : 0 < G.N) (hg : 0 < G.g) (hI : 0 < G.lenI) (hTT : 0 < T * T') :
    ∀ x ∈ G.thrSet C de de' T T' l, 0 < x := by
  intro x hx
  obtain ⟨i, -, -, hx⟩ := hx
  have hC0 : 0 < C := by linarith
  rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨s, -, -, rfl⟩ | rfl
  · refine Finset.prod_pos fun w _ => ?_
    have hw := hB1 w
    unfold Formalism.FourierDecayAlt.Sz.xHat
    positivity
  · refine Finset.prod_pos fun w _ => ?_
    have hw := hB w
    unfold Formalism.FourierDecayAlt.Sz.xHat
    positivity
  · refine Finset.prod_pos fun w _ => ?_
    have hw := hB w
    unfold Formalism.FourierDecayAlt.Sz.lamHat
    positivity
  · refine Finset.prod_pos fun w _ => ?_
    have hw := hB w
    have hs : 0 < Real.sqrt (T * T') := Real.sqrt_pos.mpr hTT
    unfold Formalism.FourierDecayAlt.Sz.lamPrimeHat
    apply Real.sqrt_pos.mpr
    positivity

variable {D : D7}

/- English proof (translation)
Simplify using `only [Formalism.FourierDecayAlt.Sz.Glob.place, Formalism.MainNotions.BridgeLemma.cfgOf, Formalism.L2.SG.SpectralTiesReal.gOf]`. Use `congr 1`. Conclude with `Formalism.MainNotions.BridgeLemma.sza_m_eq D`.
-/
theorem gOf_place' (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (w : InfinitePlace D.host.E) :
    (Formalism.L2.SG.SpectralTiesReal.gOf D e).place w = Formalism.MainNotions.BridgeLemma.cfgOf D (e w) := by
  simp only [Formalism.FourierDecayAlt.Sz.Glob.place, Formalism.MainNotions.BridgeLemma.cfgOf, Formalism.L2.SG.SpectralTiesReal.gOf]
  congr 1
  exact Formalism.MainNotions.BridgeLemma.sza_m_eq D

/- English proof (translation)
Unfold `Formalism.L2.SG.SpectralTiesReal.lOf`. Use `split_ifs with h`. Use `(Nat.find_spec h).2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `D.R.m_add_three_le_k` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem lOf_succ_le (de de' : ℕ → ℝ) : Formalism.L2.SG.SpectralTiesReal.lOf D de de' + 1 ≤ D.R.k := by
  unfold Formalism.L2.SG.SpectralTiesReal.lOf
  split_ifs with h
  · have := (Nat.find_spec h).2.1
    omega
  · have := D.R.m_add_three_le_k
    omega

/- English proof (translation)
Establish `hHc` using `hH`. Take `⟨-, -, a3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, a20, -, -, -, -, -⟩` from `hHc`. Establish `hk5 : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D`. Establish `hL` using `Formalism.MainNotions.BridgeLemma.one_le_L large₂`. Establish `hf16 : (16 : ℝ) ≤ D.R.f`.

Establish `h2` using `D.R.two_le_m`. Establish `: 16 ≤ D.R.m ^ 4`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_trans this a3` after adjusting the coercions. Use `set x : ℝ := (D.R.k : ℝ) * D.R.f * large₂.sc.L with hx`.

Establish `hx1 : 1 ≤ x`. Apply the tactic sequence `have : (1 : ℝ) * 1 * 1 ≤ (D.R.k : ℝ) * D.R.f * large₂.sc.L := by gcongr <;> linarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp : x ^ (5 : ℝ) ≤ x ^ Cl` using `Real.rpow_le_rpow_of_exponent_le hx1 h5`. Establish `e5 : x ^ (5 : ℝ) = x ^ (5 : ℕ)`.

Rewrite using `[show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`. Rewrite `hp` using `[e5]`. Establish `hx5 : x ^ 5 = (D.R.k : ℝ) ^ 3 * ((D.R.k : ℝ) ^ 2 * (D.R.f : ℝ) ^ 5 * large₂.sc.L ^ 5)` using `by rw [hx]; ring`. Establish `hf5 : (16 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5` using `pow_le_pow_left₀ (by norm_num) hf16 5`. Establish `hL5 : 1 ≤ large₂.sc.L ^ 5` using `one_le_pow₀ hL`.

Establish `hk2 : (25 : ℝ) ≤ (D.R.k : ℝ) ^ 2` using `by nlinarith`. Establish `hprod : (16000 : ℝ) ≤ (D.R.k : ℝ) ^ 2 * (D.R.f : ℝ) ^ 5 * large₂.sc.L ^ 5`. Establish `a : (25 : ℝ) * 16 ^ 5 * 1 ≤ (D.R.k : ℝ) ^ 2 * (D.R.f : ℝ) ^ 5 * large₂.sc.L ^ 5` using `by gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk3 : 0 ≤ (D.R.k : ℝ) ^ 3` using `by positivity`.

Establish `: 16000 * (D.R.k : ℝ) ^ 3 ≤ x ^ 5` using `by rw [hx5]; nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem del_big {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (h5 : 5 ≤ Cl) :
    16000 * (D.R.k : ℝ) ^ 3 ≤ D.s.Del := by
  have hHc := hH
  obtain ⟨-, -, a3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, a20, -, -, -, -, -⟩ := hHc
  have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D
  have hL := Formalism.MainNotions.BridgeLemma.one_le_L large₂
  have hf16 : (16 : ℝ) ≤ D.R.f := by
    have h2 := D.R.two_le_m
    have : 16 ≤ D.R.m ^ 4 := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ D.R.m ^ 4 := Nat.pow_le_pow_left h2 4
    exact_mod_cast le_trans this a3
  set x : ℝ := (D.R.k : ℝ) * D.R.f * large₂.sc.L with hx
  have hx1 : 1 ≤ x := by
    have : (1 : ℝ) * 1 * 1 ≤ (D.R.k : ℝ) * D.R.f * large₂.sc.L := by gcongr <;> linarith
    linarith
  have hp : x ^ (5 : ℝ) ≤ x ^ Cl := Real.rpow_le_rpow_of_exponent_le hx1 h5
  have e5 : x ^ (5 : ℝ) = x ^ (5 : ℕ) := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e5] at hp
  have hx5 : x ^ 5 = (D.R.k : ℝ) ^ 3 * ((D.R.k : ℝ) ^ 2 * (D.R.f : ℝ) ^ 5 * large₂.sc.L ^ 5) := by rw [hx]; ring
  have hf5 : (16 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hf16 5
  have hL5 : 1 ≤ large₂.sc.L ^ 5 := one_le_pow₀ hL
  have hk2 : (25 : ℝ) ≤ (D.R.k : ℝ) ^ 2 := by nlinarith
  have hprod : (16000 : ℝ) ≤ (D.R.k : ℝ) ^ 2 * (D.R.f : ℝ) ^ 5 * large₂.sc.L ^ 5 := by
    have a : (25 : ℝ) * 16 ^ 5 * 1 ≤ (D.R.k : ℝ) ^ 2 * (D.R.f : ℝ) ^ 5 * large₂.sc.L ^ 5 := by gcongr
    linarith
  have hk3 : 0 ≤ (D.R.k : ℝ) ^ 3 := by positivity
  have : 16000 * (D.R.k : ℝ) ^ 3 ≤ x ^ 5 := by rw [hx5]; nlinarith
  linarith

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, h8, -, -, -, -, -, -, -, h16, -⟩` from `hH`. Establish `hm` using `D.R.two_le_m`. Establish `hk3` using `D.R.m_add_three_le_k`. Establish `h1m : (1 : ℕ) ≤ D.R.m` using `by omega`. Establish `hb` using `h8 τ 1 le_rfl h1m`.

Establish `hkpos : (0 : ℝ) < (D.R.k : ℝ)` using `by exact_mod_cast (by omega : 0 < D.R.k)`. Establish `hk : (0 : ℝ) < (D.R.k : ℝ) ^ Cl` using `Real.rpow_pos_of_pos hkpos _`. Establish `hkb : (D.R.k : ℝ) ^ Cl ≤ bOne D τ 1` using `le_trans (le_max_left _ _) (h16 τ 1 le_rfl h1m).1`. Simplify using `only [Formalism.MainNotions.BridgeLemma.cfgOf]`. Break down `le_or_gt 0 ((D.R.m : ℝ) * D.R.k * D.s.Del) with h0 | h0` into its components or cases.

Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem first_size_lower_bound {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ} (hD : StandingNumericalData D C0) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (h40 : 40 ≤ Cl) (τ : D.what₂.Tau) :
    40 * ((Formalism.MainNotions.BridgeLemma.cfgOf D τ).m : ℝ) * (Formalism.MainNotions.BridgeLemma.cfgOf D τ).k * (Formalism.MainNotions.BridgeLemma.cfgOf D τ).Del ≤
      (Formalism.MainNotions.BridgeLemma.cfgOf D τ).b 1 := by
  obtain ⟨-, -, -, -, -, -, -, h8, -, -, -, -, -, -, -, h16, -⟩ := hH
  have hm := D.R.two_le_m
  have hk3 := D.R.m_add_three_le_k
  have h1m : (1 : ℕ) ≤ D.R.m := by omega
  have hb := h8 τ 1 le_rfl h1m
  have hkpos : (0 : ℝ) < (D.R.k : ℝ) := by exact_mod_cast (by omega : 0 < D.R.k)
  have hk : (0 : ℝ) < (D.R.k : ℝ) ^ Cl := Real.rpow_pos_of_pos hkpos _
  have hkb : (D.R.k : ℝ) ^ Cl ≤ bOne D τ 1 := le_trans (le_max_left _ _) (h16 τ 1 le_rfl h1m).1
  dsimp only [Formalism.MainNotions.BridgeLemma.cfgOf]
  rcases le_or_gt 0 ((D.R.m : ℝ) * D.R.k * D.s.Del) with h0 | h0
  · nlinarith
  · nlinarith

/- English proof (translation)
Establish `hk5 : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D`. Establish `hDel` using `del_big hH (by linarith)`. Establish `hHc` using `hH`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, a19, -, -, -, -, -, -⟩` from `hHc`. Establish `hT : ((D.mem u).A.T : ℝ) ≠ 0` using `by exact_mod_cast (D.mem u).A.T_prime.ne_zero`.

Establish `hT' : ((D.mem u').A.T : ℝ) ≠ 0` using `by exact_mod_cast (D.mem u').A.T_prime.ne_zero`. Establish `hTp : (0 : ℝ) < (D.mem u).A.T` using `by exact_mod_cast (D.mem u).A.T_prime.pos`. Establish `hTp' : (0 : ℝ) < (D.mem u').A.T` using `by exact_mod_cast (D.mem u').A.T_prime.pos`. Establish `hka : 0 < (Formalism.L2.SG.SpectralTiesReal.gOf D e).ka` using `by show 0 < Real.pi / D.host.v`. Conclude with `div_pos Real.pi_pos (by linarith)`.

Establish `hg : 0 < (Formalism.L2.SG.SpectralTiesReal.gOf D e).g` using `by show 0 < ((D.host.g 0 : ℕ) : ℝ) * ((D.host.g 1 : ℕ) : ℝ)`. Establish `a : (0 : ℝ) < ((D.host.g 0 : ℕ) : ℝ)` using `by exact_mod_cast (D.host.g_prime 0).pos`. Establish `b : (0 : ℝ) < ((D.host.g 1 : ℕ) : ℝ)` using `by exact_mod_cast (D.host.g_prime 1).pos`. Conclude with `mul_pos a b`. Establish `hrk : (D.R.rS : ℝ) + 1 ≤ D.R.k`.

Establish `h1` using `Formalism.MainNotions.BridgeLemma.m_eq D`. Establish `h2` using `D.R.m_add_three_le_k`. Conclude with `(by omega : D.R.rS + 1 ≤ D.R.k)` after adjusting the coercions. Establish `hN : (Formalism.L2.SG.SpectralTiesReal.gOf D e).N = 4 * 5 * ((D.R.rS : ℝ) + 1)` using `rfl`. Establish `hr0 : (0 : ℝ) ≤ D.R.rS` using `Nat.cast_nonneg _`.

Establish `hN3 : (Formalism.L2.SG.SpectralTiesReal.gOf D e).N ^ 3 ≤ D.s.Del / 2`. Rewrite using `[hN]`. Establish `: ((D.R.rS : ℝ) + 1) ^ 3 ≤ (D.R.k : ℝ) ^ 3` using `pow_le_pow_left₀ (by linarith) hrk 3`. Use the polynomial consequences of the given equalities and inequalities. Establish `hN1 : (11 / 4 : ℝ) ≤ (Formalism.L2.SG.SpectralTiesReal.gOf D e).N ^ 3`.

Rewrite using `[hN]`. Establish `h20 : (20 : ℝ) ≤ 4 * 5 * ((D.R.rS : ℝ) + 1)` using `by nlinarith`. Use `pow_le_pow_left₀ (by norm_num) h20 3` as an intermediate fact. Evaluate the numerical expressions using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hl` using `lOf_succ_le (D := D) (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u')`. Establish `hk3 : (125 : ℝ) ≤ (D.R.k : ℝ) ^ 3`. Use `pow_le_pow_left₀ (by norm_num) hk5 3` as an intermediate fact. Evaluate the numerical expressions using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hD11 : (11 / 2 : ℝ) ≤ D.s.Del` using `by nlinarith`. Use `thrSet_pos _ hCA (fun w => ?_) (fun w => ?_) hka (by rw [hN]; positivity) hg ?_ (mul_pos hTp hTp')` and prove the remaining obligations. Unfold `Sz.Glob.supI`. Rewrite using `[gOf_place']`. Conclude with `ThresholdBounds.supI_pos _ (Formalism.MainNotions.BridgeLemma.cfg_ok hD hH (e w)) (first_size_lower_bound hD hH h40 (e w)) hD11 (Formalism.MainNotions.BridgeLemma.isWord_deOf D u) (Formalism.MainNotions.BridgeLemma.isWord_deOf D u') hl hT hT' hka (pow_pos hg _)`.

Unfold `Sz.Glob.cutSupLong`. Rewrite using `[gOf_place']`. Conclude with `ThresholdBounds.sSup_be_image_cutIntervalLong_pos _ (Formalism.MainNotions.BridgeLemma.cfg_ok hD hH (e w)) (first_size_lower_bound hD hH h40 (e w)) hN1 hN3 (Formalism.MainNotions.BridgeLemma.isWord_deOf D u) (Formalism.MainNotions.BridgeLemma.isWord_deOf D u') hl hT hT' hka (pow_ …`. Use `show 0 < (D.s.Del : ℝ) / 2 - 5 / 2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem thrSet_pos_at {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ} (hD : StandingNumericalData D C0)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (h40 : 40 ≤ Cl) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) {CA : ℝ}
    (hCA : 1 ≤ CA) (u u' : D.what₂.Word) :
    ∀ x ∈ (Formalism.L2.SG.SpectralTiesReal.gOf D e).thrSet CA (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u')
      (D.mem u).A.T (D.mem u').A.T
      (Formalism.L2.SG.SpectralTiesReal.lOf D (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u')), 0 < x := by
  have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D
  have hDel := del_big hH (by linarith)
  have hHc := hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, a19, -, -, -, -, -, -⟩ := hHc
  have hT : ((D.mem u).A.T : ℝ) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero
  have hT' : ((D.mem u').A.T : ℝ) ≠ 0 := by exact_mod_cast (D.mem u').A.T_prime.ne_zero
  have hTp : (0 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hTp' : (0 : ℝ) < (D.mem u').A.T := by exact_mod_cast (D.mem u').A.T_prime.pos
  have hka : 0 < (Formalism.L2.SG.SpectralTiesReal.gOf D e).ka := by
    show 0 < Real.pi / D.host.v
    exact div_pos Real.pi_pos (by linarith)
  have hg : 0 < (Formalism.L2.SG.SpectralTiesReal.gOf D e).g := by
    show 0 < ((D.host.g 0 : ℕ) : ℝ) * ((D.host.g 1 : ℕ) : ℝ)
    have a : (0 : ℝ) < ((D.host.g 0 : ℕ) : ℝ) := by exact_mod_cast (D.host.g_prime 0).pos
    have b : (0 : ℝ) < ((D.host.g 1 : ℕ) : ℝ) := by exact_mod_cast (D.host.g_prime 1).pos
    exact mul_pos a b
  have hrk : (D.R.rS : ℝ) + 1 ≤ D.R.k := by
    have h1 := Formalism.MainNotions.BridgeLemma.m_eq D
    have h2 := D.R.m_add_three_le_k
    exact_mod_cast (by omega : D.R.rS + 1 ≤ D.R.k)
  have hN : (Formalism.L2.SG.SpectralTiesReal.gOf D e).N = 4 * 5 * ((D.R.rS : ℝ) + 1) := rfl
  have hr0 : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
  have hN3 : (Formalism.L2.SG.SpectralTiesReal.gOf D e).N ^ 3 ≤ D.s.Del / 2 := by
    rw [hN]
    have : ((D.R.rS : ℝ) + 1) ^ 3 ≤ (D.R.k : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) hrk 3
    nlinarith
  have hN1 : (11 / 4 : ℝ) ≤ (Formalism.L2.SG.SpectralTiesReal.gOf D e).N ^ 3 := by
    rw [hN]
    have h20 : (20 : ℝ) ≤ 4 * 5 * ((D.R.rS : ℝ) + 1) := by nlinarith
    have := pow_le_pow_left₀ (by norm_num) h20 3
    norm_num at this
    linarith
  have hl := lOf_succ_le (D := D) (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u')
  have hk3 : (125 : ℝ) ≤ (D.R.k : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hk5 3
    norm_num at this
    linarith
  have hD11 : (11 / 2 : ℝ) ≤ D.s.Del := by nlinarith
  refine thrSet_pos _ hCA (fun w => ?_) (fun w => ?_) hka (by rw [hN]; positivity) hg ?_ (mul_pos hTp hTp')
  · unfold Sz.Glob.supI
    rw [gOf_place']
    exact ThresholdBounds.supI_pos _ (Formalism.MainNotions.BridgeLemma.cfg_ok hD hH (e w)) (first_size_lower_bound hD hH h40 (e w)) hD11
      (Formalism.MainNotions.BridgeLemma.isWord_deOf D u) (Formalism.MainNotions.BridgeLemma.isWord_deOf D u') hl hT hT' hka (pow_pos hg _)
  · unfold Sz.Glob.cutSupLong
    rw [gOf_place']
    exact ThresholdBounds.sSup_be_image_cutIntervalLong_pos _ (Formalism.MainNotions.BridgeLemma.cfg_ok hD hH (e w)) (first_size_lower_bound hD hH h40 (e w)) hN1 hN3
      (Formalism.MainNotions.BridgeLemma.isWord_deOf D u) (Formalism.MainNotions.BridgeLemma.isWord_deOf D u') hl hT hT' hka (pow_pos hg _)
  · show 0 < (D.s.Del : ℝ) / 2 - 5 / 2
    linarith

end Formalism.L2.SG.Pf.ThresholdAtPlaceBounds
