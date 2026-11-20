import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

noncomputable section

namespace GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Use `haveI : NeZero q := ⟨hq⟩`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Nat.card_eq_fintype_card]`. Use `show Fintype.card (Fin r → Fin r → ZMod q) = q ^ (r * r)`. Rewrite using `[Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, ← pow_mul]`.
-/
theorem card_GL_zmod_le (r q : ℕ) (hq : q ≠ 0) :
    Nat.card (GL (Fin r) (ZMod q)) ≤ q ^ (r * r) := by
  haveI : NeZero q := ⟨hq⟩
  calc Nat.card (GL (Fin r) (ZMod q)) ≤ Nat.card (Matrix (Fin r) (Fin r) (ZMod q)) :=
        Nat.card_le_card_of_injective (fun u => (u : Matrix (Fin r) (Fin r) (ZMod q))) (fun a b h => Units.ext h)
    _ = q ^ (r * r) := by
        rw [Nat.card_eq_fintype_card]
        show Fintype.card (Fin r → Fin r → ZMod q) = q ^ (r * r)
        rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, ← pow_mul]

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y0 cX ex Csz p _ _ PP A hN`. Establish `hq : ∀ k, D.host.g k ≠ 0`. Introduce `k h0`. Establish `h` using `hN.cop`. Apply the tactic sequence `fin_cases k <;> simp_all [Nat.Coprime]`.

Establish `hcard : Nat.card p.P.Gp = ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Nat.card (GL (Fin D.R.r) (ZMod (D.host.g kv.1)))`. Rewrite using `[Nat.card_congr (p.R.eG.trans p.cG).toEquiv]`. Conclude with `Nat.card_pi`. Establish `hleN : Fintype.card p.P.Gp ≤ ∏ kv : (Σ k : Fin 2, D.nd.PlG k), D.host.g kv.1 ^ (D.R.r * D.R.r)`. Rewrite using `[← Nat.card_eq_fintype_card, hcard]`.

Conclude with `Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun kv _ => card_GL_zmod_le _ _ (hq kv.1))`. Establish `hpos : (0 : ℝ) < (Fintype.card p.P.Gp : ℝ)` using `by exact_mod_cast Fintype.card_pos`. Establish `hleR : (Fintype.card p.P.Gp : ℝ) ≤ ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℝ) ^ (D.R.r * D.R.r))`. Conclude with `hleN` after adjusting the coercions. Establish `hlog : Real.log (Fintype.card p.P.Gp : ℝ) ≤ (2 * D.R.f : ℝ) * ((D.R.r : ℝ) * D.R.r) * (9 * L.sc.L + 1)`.

Use `(Real.log_le_log hpos hleR).trans ?_` and prove the remaining obligations. Rewrite using `[Real.log_prod (fun kv _ => pow_ne_zero _ (by exact_mod_cast hq kv.1))]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun kv _ => ?_` and prove the remaining obligations. Rewrite using `[Real.log_pow]`.

Use `push_cast`. Conclude with `mul_le_mul_of_nonneg_left (hN.logg kv.1) (by positivity)`. Use `_ = (2 * D.R.f : ℝ) * ((D.R.r : ℝ) * D.R.r) * (9 * L.sc.L + 1) := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_sigma]`. Simplify using `[D.nd.card_PlG, nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨-, hL10, hLx, -⟩` from `hN.big`. Establish `hf8 : (8 : ℝ) ≤ D.R.f` using `by exact_mod_cast hN.f8`. Take `⟨-, -, hpoly⟩` from `hN.poly`. Establish `hroom` using `hN.room`.

Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hX0 : 0 < L.sc.x ^ A` using `Real.rpow_pos_of_pos hx0 A`. Establish `h3 : (L.sc.x ^ A) ^ (3 : ℝ) = (L.sc.x ^ A) ^ (3 : ℕ)`. Rewrite using `[show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`. Rewrite `hroom` using `[h3]`.

Establish `hrn : (D.R.r : ℝ) ≤ D.R.nV`. Establish `: D.R.r ≤ D.R.nV` using `by unfold Formalism.BasicNotions.Ranks.nV; omega`. Conclude with `this` after adjusting the coercions. Use `set X := L.sc.x ^ A with hX`. Use `set f : ℝ := (D.R.f : ℝ)`.

Use `set r : ℝ := (D.R.r : ℝ)`. Use `set Lr := L.sc.L`. Establish `hr0 : 0 ≤ r` using `by positivity`. Establish `hY : f * r * r * Lr ≤ X`. Use `le_trans ?_ hpoly` and prove the remaining obligations.

Establish `: f * r * r * Lr = (f * r) * Lr * r` using `by ring`. Establish `: f * r * (D.R.nV : ℝ) * Lr = (f * r) * Lr * D.R.nV` using `by ring`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ f) hr0) (by linarith : (0:ℝ) ≤ Lr)]`. Establish `key : 2 * ((2 * f) * (r * r) * (9 * Lr + 1)) ≤ L.sc.b`. Break down `Nat.eq_zero_or_pos D.R.r with h0 | h1` into its components or cases.

Establish `: r = 0` using `by simp [r, h0]`. Rewrite using `[this]`. Use polynomial arithmetic with `[pow_pos hX0 3]`. Establish `hr1 : (1 : ℝ) ≤ r` using `Nat.one_le_cast.mpr h1`. Establish `hY80 : 80 ≤ f * r * r * Lr`.

Establish `: (1:ℝ) ≤ r * r` using `by nlinarith`. Establish `: (80:ℝ) ≤ f * Lr` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hX80 : 80 ≤ X` using `le_trans hY80 hY`. Establish `hA : 2 * ((2 * f) * (r * r) * (9 * Lr + 1)) ≤ 40 * (f * r * r * Lr)`.

Establish `: 0 ≤ f * r * r` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hB : 40 * X ≤ X ^ 3`. Establish `hXX : 40 ≤ X * X` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation.

Use the polynomial consequences of the given equalities and inequalities. Use polynomial arithmetic with `[hlog]`.
-/
theorem two_log_card_levels_le : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → GlobalTheory.CovTop.RecTied D L →
    ∀ PP A : ℝ, GlobalTheory.CovTop.HostNum D L PP A 3 → 2 * Real.log (Fintype.card p.P.Gp : ℕ) ≤ L.sc.b := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p _ _ PP A hN
  have hq : ∀ k, D.host.g k ≠ 0 := by
    intro k h0
    have h := hN.cop
    fin_cases k <;> simp_all [Nat.Coprime]
  have hcard : Nat.card p.P.Gp =
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Nat.card (GL (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
    rw [Nat.card_congr (p.R.eG.trans p.cG).toEquiv]
    exact Nat.card_pi
  have hleN : Fintype.card p.P.Gp ≤
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), D.host.g kv.1 ^ (D.R.r * D.R.r) := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun kv _ => card_GL_zmod_le _ _ (hq kv.1))
  have hpos : (0 : ℝ) < (Fintype.card p.P.Gp : ℝ) := by exact_mod_cast Fintype.card_pos
  have hleR : (Fintype.card p.P.Gp : ℝ) ≤
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℝ) ^ (D.R.r * D.R.r)) := by
    exact_mod_cast hleN
  have hlog : Real.log (Fintype.card p.P.Gp : ℝ) ≤
      (2 * D.R.f : ℝ) * ((D.R.r : ℝ) * D.R.r) * (9 * L.sc.L + 1) := by
    refine (Real.log_le_log hpos hleR).trans ?_
    rw [Real.log_prod (fun kv _ => pow_ne_zero _ (by exact_mod_cast hq kv.1))]
    calc ∑ kv : (Σ k : Fin 2, D.nd.PlG k), Real.log ((D.host.g kv.1 : ℝ) ^ (D.R.r * D.R.r))
        ≤ ∑ _kv : (Σ k : Fin 2, D.nd.PlG k), ((D.R.r : ℝ) * D.R.r) * (9 * L.sc.L + 1) := by
          refine Finset.sum_le_sum fun kv _ => ?_
          rw [Real.log_pow]
          push_cast
          exact mul_le_mul_of_nonneg_left (hN.logg kv.1) (by positivity)
      _ = (2 * D.R.f : ℝ) * ((D.R.r : ℝ) * D.R.r) * (9 * L.sc.L + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_sigma]
          simp [D.nd.card_PlG, nsmul_eq_mul]
          ring

  obtain ⟨-, hL10, hLx, -⟩ := hN.big
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hN.f8
  obtain ⟨-, -, hpoly⟩ := hN.poly
  have hroom := hN.room
  have hx0 : 0 < L.sc.x := by linarith
  have hX0 : 0 < L.sc.x ^ A := Real.rpow_pos_of_pos hx0 A
  have h3 : (L.sc.x ^ A) ^ (3 : ℝ) = (L.sc.x ^ A) ^ (3 : ℕ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h3] at hroom
  have hrn : (D.R.r : ℝ) ≤ D.R.nV := by
    have : D.R.r ≤ D.R.nV := by unfold Formalism.BasicNotions.Ranks.nV; omega
    exact_mod_cast this
  set X := L.sc.x ^ A with hX
  set f : ℝ := (D.R.f : ℝ)
  set r : ℝ := (D.R.r : ℝ)
  set Lr := L.sc.L
  have hr0 : 0 ≤ r := by positivity
  have hY : f * r * r * Lr ≤ X := by
    refine le_trans ?_ hpoly
    have : f * r * r * Lr = (f * r) * Lr * r := by ring
    have : f * r * (D.R.nV : ℝ) * Lr = (f * r) * Lr * D.R.nV := by ring
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ f) hr0) (by linarith : (0:ℝ) ≤ Lr)]
  have key : 2 * ((2 * f) * (r * r) * (9 * Lr + 1)) ≤ L.sc.b := by
    rcases Nat.eq_zero_or_pos D.R.r with h0 | h1
    · have : r = 0 := by simp [r, h0]
      rw [this]; nlinarith [pow_pos hX0 3]
    · have hr1 : (1 : ℝ) ≤ r := Nat.one_le_cast.mpr h1
      have hY80 : 80 ≤ f * r * r * Lr := by
        have : (1:ℝ) ≤ r * r := by nlinarith
        have : (80:ℝ) ≤ f * Lr := by nlinarith
        nlinarith
      have hX80 : 80 ≤ X := le_trans hY80 hY
      have hA : 2 * ((2 * f) * (r * r) * (9 * Lr + 1)) ≤ 40 * (f * r * r * Lr) := by
        have : 0 ≤ f * r * r := by positivity
        nlinarith
      have hB : 40 * X ≤ X ^ 3 := by
        have hXX : 40 ≤ X * X := by nlinarith
        calc 40 * X ≤ X * X * X := by nlinarith
          _ = X ^ 3 := by ring
      nlinarith
  nlinarith [hlog]

end GlobalTheory.CovTop

end
