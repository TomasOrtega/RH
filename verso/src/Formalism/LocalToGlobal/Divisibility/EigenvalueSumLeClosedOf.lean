import Mathlib
import Formalism.LocalToGlobal.Divisibility.NumericScaleExponentEqExtended
import Formalism.LocalToGlobal.Divisibility.TwistedPlaceEtaSumLeExtended
import Formalism.LocalToGlobal.Divisibility.ConstantGeTwentyEightAlt
import Formalism.LocalToGlobal.Divisibility.SmallTies
import Formalism.LocalToGlobal.GroupLattices.JointServices.VwResChar
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.Divisibility.NumbersLink
import Formalism.LocalToGlobal.Divisibility.ZscOfNum
import Formalism.SharpRestriction.ElevenLe
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.Divisibility.SlopeExcess.ConstRankBaseLePolyFourth
import Formalism.SharpRestriction.Divisibility.HookProducts.LwPNonneg
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GZeroLogBound
import Formalism.LocalToGlobal.Divisibility.DivisibilityConstruction.RBLam

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions
open Formalism.LatticeIndexTer (ph)

section Scale

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

structure ClosedScale3 (A3 : FamIn3 K G Pl0 I0 Ty T m) (Nd : NumDatum) (eJz : A3.fam3.base3.J ≃ Fin Nd.R.m) (Nc : ℝ)
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) : Prop where
  l3m : ∀ Zs j, (Zsc Zs).l3m j = ∑ ρ : RPl Nd.R, (((Nd.R.k : ℝ) + (((eJz j).1 + 1 : ℕ) : ℝ) - 1) -
    ((Nd.R.m : ℝ) - (((eJz j).1 + 1 : ℕ) : ℝ))) * Nd.w ((eJz j).1 + 1) ρ * Nd.logOm
  l3u : ∀ Zs, (Zsc Zs).l3u = Nd.B0 * Real.log (Real.log Nd.sc.x)
  E1u : ∀ Zs, (Zsc Zs).E1u = Nd.unitE Nc
  x : ∀ Zs, (Zsc Zs).x = Nd.sc.x
  b : ∀ Zs, (Zsc Zs).b = Nd.sc.b
  la : ∀ Zs, (Zsc Zs).la = Real.log (Fintype.card G)
  de : ∀ Zs, (Zsc Zs).de = 8 * (Nd.R.f : ℝ) * (Nd.R.r : ℝ) / ((min (Nd.g 0) (Nd.g 1) : ℕ) : ℝ)

def ZscFix3 (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Nd : NumDatum)
    (eJz : A3.fam3.base3.J ≃ Fin Nd.R.m) (Nc Cf : ℝ) (Zs : DefSub A3.fam3.amb3) : IndefScale A3.fam3.base3 :=
  let z := ZscOfNum3 A3 P0 ψ0 Nd eJz Nc Zs
  { z with l6m := fun j => z.l6m j - Cf * z.l6u, l6u := 0 }

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩`.
-/
theorem closedScale3_fix (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Nd : NumDatum)
    (eJz : A3.fam3.base3.J ≃ Fin Nd.R.m) (Nc Cf : ℝ) : ClosedScale3 A3 Nd eJz Nc (ZscFix3 A3 P0 ψ0 Nd eJz Nc Cf) :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/- English proof (translation)
Use `show (∑ ρ : RPl Nd.R, Nd.logHook ((eJz j).1 + 1) ρ) - Cf * ((Nd.R.f : ℝ) * (Nd.R.nV : ℝ) ^ 2 * Nd.Lp) - C * 0 = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem levelSix_fixed_eq (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Nd : NumDatum)
    (eJz : A3.fam3.base3.J ≃ Fin Nd.R.m) (Nc Cf : ℝ) (Zs : DefSub A3.fam3.amb3) (C : ℝ) (j : A3.fam3.base3.J) :
    (ZscFix3 A3 P0 ψ0 Nd eJz Nc Cf Zs).l6m j - C * (ZscFix3 A3 P0 ψ0 Nd eJz Nc Cf Zs).l6u =
      (∑ ρ : RPl Nd.R, Nd.logHook ((eJz j).1 + 1) ρ) - Cf * ((Nd.R.f : ℝ) * (Nd.R.nV : ℝ) ^ 2 * Nd.Lp) := by
  show (∑ ρ : RPl Nd.R, Nd.logHook ((eJz j).1 + 1) ρ) - Cf * ((Nd.R.f : ℝ) * (Nd.R.nV : ℝ) ^ 2 * Nd.Lp) - C * 0 = _
  ring

end Scale

section Fields

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {Nd : NumDatum} {eJz : A3.fam3.base3.J ≃ Fin Nd.R.m} {Nc : ℝ}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}
variable (hZ : ClosedScale3 A3 Nd eJz Nc Zsc)
  (eJ : A3.fam3.base3.J ≃ Fin Nd.R.m) (δ : Code Nd) (Tl : ℕ) (lam0 C0 ce Ch Sw C1 : ℝ) (H : Nd.NumFacts δ Nc lam0 C0 ce Ch Sw C1)

/- English proof (translation)
The claim follows from `h`.
-/
theorem twentyEight_le_constant (h : 28 ≤ C0) : 28 ≤ (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).C0 := h

/- English proof (translation)
The claim follows from `h`.
-/
theorem logCard_le_lambda (h : Real.log (Fintype.card G) ≤ lam0) :
    Real.log (Fintype.card G) ≤ (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).lam0 := h

include hZ in

/- English proof (translation)
Use `show (Zsc Zs).la ≤ lam0`. Rewrite using `[hZ.la]`. Conclude with `h`.
-/
theorem logCardGroup_le_lambda (Zs : DefSub A3.fam3.amb3) (C CH : ℝ) (h : Real.log (Fintype.card G) ≤ lam0) :
    ((Zsc Zs).num C CH).la ≤ (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).lam0 := by
  show (Zsc Zs).la ≤ lam0
  rw [hZ.la]
  exact h

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Nd.sum_lifts (fun l => (∑ ρ : RPl Nd.R, Nd.logHook l ρ) - Ch * ((Nd.R.f : ℝ) * (Nd.R.nV : ℝ) ^ 2 * Nd.Lp)) eJz]`. Use `Finset.sum_congr rfl fun l _ => by ring` and prove the remaining obligations. Use `_ ≤ ∑ j, ((Zsc Zs).num C CH).l6 j := Finset.sum_le_sum fun j _ => hl6 j`.
-/
theorem eigenvalue_sum_le_closed_of (Zs : DefSub A3.fam3.amb3) (C CH : ℝ)
    (hl6 : ∀ j, (∑ ρ : RPl Nd.R, Nd.logHook ((eJz j).1 + 1) ρ) - Ch * ((Nd.R.f : ℝ) * (Nd.R.nV : ℝ) ^ 2 * Nd.Lp) ≤
      (Zsc Zs).l6m j - C * (Zsc Zs).l6u) :
    ∑ j, (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).hX j ≤ ∑ j, ((Zsc Zs).num C CH).l6 j := by
  calc ∑ j, (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).hX j
      = ∑ l ∈ Nd.lifts, ((∑ ρ : RPl Nd.R, Nd.logHook l ρ) - Ch * (Nd.R.f : ℝ) * (Nd.R.nV : ℝ) ^ 2 * Nd.Lp) :=
        Nd.sum_lifts (fun l => (∑ ρ : RPl Nd.R, Nd.logHook l ρ) - Ch * (Nd.R.f : ℝ) * (Nd.R.nV : ℝ) ^ 2 * Nd.Lp) eJ
    _ = ∑ j, ((∑ ρ : RPl Nd.R, Nd.logHook ((eJz j).1 + 1) ρ) - Ch * ((Nd.R.f : ℝ) * (Nd.R.nV : ℝ) ^ 2 * Nd.Lp)) := by
        rw [Nd.sum_lifts (fun l => (∑ ρ : RPl Nd.R, Nd.logHook l ρ) - Ch * ((Nd.R.f : ℝ) * (Nd.R.nV : ℝ) ^ 2 * Nd.Lp)) eJz]
        refine Finset.sum_congr rfl fun l _ => by ring
    _ ≤ ∑ j, ((Zsc Zs).num C CH).l6 j := Finset.sum_le_sum fun j _ => hl6 j

include hZ in

/- English proof (translation)
Establish `hl : ∀ (e : A3.fam3.base3.J ≃ Fin Nd.R.m), ∑ j, ∑ ρ : RPl Nd.R, ((((Nd.R.k : ℝ) + (((e j).1 + 1 : ℕ) : ℝ) - 1) - ((Nd.R.m : ℝ) - (((e j).1 + 1 : ℕ) : ℝ))) * Nd.w ((e j).1 + 1) ρ * Nd.logOm) = ∑ l ∈ Nd.lifts, ∑ ρ : RPl Nd.R, (((Nd.R.k : ℝ) + (l : ℝ) - 1) - ((Nd.R.m : ℝ) - (l : ℝ)) …` using `fun e => Nd.sum_lifts (fun l => ∑ ρ : RPl Nd.R, (((Nd.R.k : ℝ) + (l : ℝ) - 1) - ((Nd.R.m : ℝ) - (l : ℝ))) * Nd.w l ρ * Nd.logOm) e`. Establish `hc : (Fintype.card A3.fam3.base3.J : ℝ) = (Nd.R.m : ℝ)` using `by rw [Fintype.card_congr eJ, Fintype.card_fin]`. Use `show ∑ j, ((Zsc Zs).l3m j + C * (Zsc Zs).l3u) ≤ _`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]`. Establish `e1 : ∑ j, (Zsc Zs).l3m j = ∑ l ∈ Nd.lifts, ∑ ρ : RPl Nd.R, (((Nd.R.k : ℝ) + (l : ℝ) - 1) - ((Nd.R.m : ℝ) - (l : ℝ))) * Nd.w l ρ * Nd.logOm`.

Rewrite using `[← hl eJz]`. Conclude with `Finset.sum_congr rfl fun j _ => hZ.l3m Zs j`. Establish `e2 : ∑ j, ∑ ρ, (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).pq j * (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).w j ρ * (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).logOm = ∑ l ∈ Nd.lifts, ∑ ρ : RPl Nd.R, (((Nd.R.k : ℝ) + (l : ℝ) - 1) - ((Nd.R.m : ℝ) - (l : ℝ …` using `hl eJ`. Rewrite using `[e1, e2]`.
-/
theorem levelThree_bound_closed (Zs : DefSub A3.fam3.amb3) (C CH : ℝ) :
    ∑ j, ((Zsc Zs).num C CH).l3 j ≤
      (∑ j, ∑ ρ, (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).pq j *
          (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).w j ρ *
          (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).logOm) +
        (Nd.R.m : ℝ) * (C * (Zsc Zs).l3u) := by
  have hl : ∀ (e : A3.fam3.base3.J ≃ Fin Nd.R.m), ∑ j, ∑ ρ : RPl Nd.R, ((((Nd.R.k : ℝ) + (((e j).1 + 1 : ℕ) : ℝ) - 1) -
      ((Nd.R.m : ℝ) - (((e j).1 + 1 : ℕ) : ℝ))) * Nd.w ((e j).1 + 1) ρ * Nd.logOm) =
      ∑ l ∈ Nd.lifts, ∑ ρ : RPl Nd.R, (((Nd.R.k : ℝ) + (l : ℝ) - 1) - ((Nd.R.m : ℝ) - (l : ℝ))) * Nd.w l ρ * Nd.logOm :=
    fun e => Nd.sum_lifts (fun l => ∑ ρ : RPl Nd.R, (((Nd.R.k : ℝ) + (l : ℝ) - 1) - ((Nd.R.m : ℝ) - (l : ℝ))) * Nd.w l ρ * Nd.logOm) e
  have hc : (Fintype.card A3.fam3.base3.J : ℝ) = (Nd.R.m : ℝ) := by rw [Fintype.card_congr eJ, Fintype.card_fin]
  show ∑ j, ((Zsc Zs).l3m j + C * (Zsc Zs).l3u) ≤ _
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
  have e1 : ∑ j, (Zsc Zs).l3m j = ∑ l ∈ Nd.lifts, ∑ ρ : RPl Nd.R,
      (((Nd.R.k : ℝ) + (l : ℝ) - 1) - ((Nd.R.m : ℝ) - (l : ℝ))) * Nd.w l ρ * Nd.logOm := by
    rw [← hl eJz]
    exact Finset.sum_congr rfl fun j _ => hZ.l3m Zs j
  have e2 : ∑ j, ∑ ρ, (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).pq j *
          (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).w j ρ *
          (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).logOm = ∑ l ∈ Nd.lifts, ∑ ρ : RPl Nd.R,
      (((Nd.R.k : ℝ) + (l : ℝ) - 1) - ((Nd.R.m : ℝ) - (l : ℝ))) * Nd.w l ρ * Nd.logOm := hl eJ
  rw [e1, e2]

include hZ in

/- English proof (translation)
Use `show 0 ≤ (Zsc Zs).de`. Rewrite using `[hZ.de]`. Check the signs of the components of the expression.
-/
theorem delta_nonneg (Zs : DefSub A3.fam3.amb3) (C CH : ℝ) : 0 ≤ ((Zsc Zs).num C CH).de := by
  show 0 ≤ (Zsc Zs).de
  rw [hZ.de]
  positivity

include hZ in

/- English proof (translation)
Use `show 3 * (Zsc Zs).de * Q ≤ 1`. Rewrite using `[hZ.de]`. Establish `hg0 : (0 : ℝ) < ((min (Nd.g 0) (Nd.g 1) : ℕ) : ℝ)`. Establish `h0` using `(Nd.g_prime 0).pos`. Establish `h1` using `(Nd.g_prime 1).pos`.

Conclude with `(lt_min h0 h1)` after adjusting the coercions. Rewrite using `[show 3 * (8 * (Nd.R.f : ℝ) * (Nd.R.r : ℝ) / ((min (Nd.g 0) (Nd.g 1) : ℕ) : ℝ)) * Q = (24 * (Nd.R.f : ℝ) * (Nd.R.r : ℝ) * Q) / ((min (Nd.g 0) (Nd.g 1) : ℕ) : ℝ) by ring]`. Rewrite using `[div_le_one hg0]`. Conclude with `hg`.
-/
theorem delta_mul_Q_le_one (Zs : DefSub A3.fam3.amb3) (C CH Q : ℝ)
    (hg : 24 * (Nd.R.f : ℝ) * (Nd.R.r : ℝ) * Q ≤ ((min (Nd.g 0) (Nd.g 1) : ℕ) : ℝ)) :
    3 * ((Zsc Zs).num C CH).de * Q ≤ 1 := by
  show 3 * (Zsc Zs).de * Q ≤ 1
  rw [hZ.de]
  have hg0 : (0 : ℝ) < ((min (Nd.g 0) (Nd.g 1) : ℕ) : ℝ) := by
    have h0 := (Nd.g_prime 0).pos
    have h1 := (Nd.g_prime 1).pos
    exact_mod_cast (lt_min h0 h1)
  rw [show 3 * (8 * (Nd.R.f : ℝ) * (Nd.R.r : ℝ) / ((min (Nd.g 0) (Nd.g 1) : ℕ) : ℝ)) * Q =
    (24 * (Nd.R.f : ℝ) * (Nd.R.r : ℝ) * Q) / ((min (Nd.g 0) (Nd.g 1) : ℕ) : ℝ) by ring]
  rw [div_le_one hg0]
  exact hg

end Fields

section QB

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1}
  {Sp : SPer Dc} {N : IndefNum Bs}

def QOfR (B : ℝ) (N : IndefNum Bs) : ℝ := max 1 (B + N.hh + 28 * N.la)

/- English proof (translation)
The claim follows from `le_max_left _ _`.
-/
theorem one_le_Q (B : ℝ) (N : IndefNum Bs) : 1 ≤ QOfR B N := le_max_left _ _

/- English proof (translation)
Use `le_trans ?_ (le_max_right _ _)` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Q_ge_bound_add (P : IndefCoreR Df0 Df1 Dc Sp N) (LG E3 : ℝ) (E2 : Bs.J → ℝ) (B : ℝ) (hB : boundBR P LG E3 E2 ≤ B) :
    boundBR P LG E3 E2 + N.hh + 28 * N.la ≤ QOfR B N := by
  refine le_trans ?_ (le_max_right _ _)
  linarith

end QB

section ErrB

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable {A3 : FamIn3 K G Pl0 I0 Ty T m} (Nd : NumDatum) {eJz : A3.fam3.base3.J ≃ Fin Nd.R.m} (Nc : ℝ)
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}

/- English proof (translation)
Unfold `NumDatum.unitE`. Establish `hx : 1 ≤ Nd.sc.x ^ Nd.sc.eps` using `Real.one_le_rpow Nd.sc.one_lt_alt.le Nd.sc.eps_pos.le`. Establish `hB` using `Nd.one_le_B0`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_le_unitE {Nc : ℝ} (hNc : 0 ≤ Nc) : 1 ≤ Nd.unitE Nc := by
  unfold NumDatum.unitE
  have hx : 1 ≤ Nd.sc.x ^ Nd.sc.eps := Real.one_le_rpow Nd.sc.one_lt_alt.le Nd.sc.eps_pos.le
  have hB := Nd.one_le_B0
  nlinarith

/- English proof (translation)
Establish `key` using `errB_of_units (Zsc Zs) C CH (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H) (lgDef (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H) s) 1 (etaSumBound bd dg s) C cG (c13 + cD) 1 hC (le_of_eq (hZ.E1u Zs)) ?_ ?_ ?_ ?_ hce`. Conclude with `key`. Use `show C * (Zsc Zs).l3u ≤ C * Nd.unitE Nc`. Rewrite using `[hZ.l3u Zs]`. Use `mul_le_mul_of_nonneg_left ?_ hC` and prove the remaining obligations.

Establish `hll` using `Nd.logLog_le H.logx`. Establish `hB` using `Nd.loss_bound_nonneg`. Establish `hx : 0 ≤ Nd.sc.x ^ Nd.sc.eps` using `Real.rpow_nonneg Nd.x_pos.le _`. Establish `h1 : Nd.B0 * Real.log (Real.log Nd.sc.x) ≤ Nd.B0 * Nd.sc.x ^ Nd.sc.eps` using `mul_le_mul_of_nonneg_left hll hB`. Establish `h2 : 0 ≤ Nd.sc.x ^ Nd.sc.eps * Nc` using `mul_nonneg hx H.Nc0`.

Unfold `NumDatum.unitE`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `hLam`. Introduce `j show bd j + Real.log (dg : ℝ) + Real.log (s : ℝ) ≤ (c13 + cD) * Nd.unitE Nc`. Use `hbd j` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `show (1 : ℝ) ≤ 1 * ((Nd.R.m : ℝ) * Nd.unitE Nc)`. Rewrite using `[one_mul]`. Conclude with `Nd.one_le_m_unitE H.Nc0`.
-/
theorem error_bound_closed_numbers (hZ : ClosedScale3 A3 Nd eJz Nc Zsc) (eJ : A3.fam3.base3.J ≃ Fin Nd.R.m) (δ : Code Nd) (Tl : ℕ)
    (lam0 C0 ce Ch Sw C1 : ℝ) (H : Nd.NumFacts δ Nc lam0 C0 ce Ch Sw C1) (Zs : DefSub A3.fam3.amb3) (C CH : ℝ) (hC : 0 ≤ C) (bd : A3.fam3.base3.J → ℝ) (dg s : ℕ)
    (c13 cG cD : ℝ) (hbd : ∀ j, bd j ≤ c13 * Nd.unitE Nc)
    (hLam : lam0 + Real.log (s : ℝ) ≤ cG * ((Nd.R.m : ℝ) * Nd.unitE Nc))
    (hdg : Real.log (dg : ℝ) + Real.log (s : ℝ) ≤ cD * Nd.unitE Nc) (hce : C + cG + C + (c13 + cD) + 1 ≤ ce) :
    (Nd.R.m : ℝ) * (C * (Zsc Zs).l3u) +
        lgDef (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H) s +
        (∑ j, (((Zsc Zs).num C CH).E1 j + etaSumBound bd dg s j)) + 1 ≤
      (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).errB := by
  have key := errB_of_units (Zsc Zs) C CH (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H)
    (lgDef (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H) s) 1 (etaSumBound bd dg s)
    C cG (c13 + cD) 1 hC (le_of_eq (hZ.E1u Zs)) ?_ ?_ ?_ ?_ hce
  · exact key
  · show C * (Zsc Zs).l3u ≤ C * Nd.unitE Nc
    rw [hZ.l3u Zs]
    refine mul_le_mul_of_nonneg_left ?_ hC
    have hll := Nd.logLog_le H.logx
    have hB := Nd.loss_bound_nonneg
    have hx : 0 ≤ Nd.sc.x ^ Nd.sc.eps := Real.rpow_nonneg Nd.x_pos.le _
    have h1 : Nd.B0 * Real.log (Real.log Nd.sc.x) ≤ Nd.B0 * Nd.sc.x ^ Nd.sc.eps := mul_le_mul_of_nonneg_left hll hB
    have h2 : 0 ≤ Nd.sc.x ^ Nd.sc.eps * Nc := mul_nonneg hx H.Nc0
    unfold NumDatum.unitE
    nlinarith
  · exact hLam
  · intro j
    show bd j + Real.log (dg : ℝ) + Real.log (s : ℝ) ≤ (c13 + cD) * Nd.unitE Nc
    have := hbd j
    linarith
  · show (1 : ℝ) ≤ 1 * ((Nd.R.m : ℝ) * Nd.unitE Nc)
    rw [one_mul]
    exact Nd.one_le_m_unitE H.Nc0

end ErrB

section Record

open Formalism.MainNotions

variable {D : D7} (L : SizeData₂ D) (Del h0 : ℕ)

/- English proof (translation)
Unfold `divSize NumDatum.unitE`. Establish `e : L.B0 = (ofRecord D L Del h0).B0` using `rfl`. Rewrite using `[e]`. Use `show Ce * L.sc.x ^ L.sc.eps * ((ofRecord D L Del h0).B0 + L.Nc) = Ce * ((ofRecord D L Del h0).sc.x ^ (ofRecord D L Del h0).sc.eps * ((ofRecord D L Del h0).B0 + L.Nc))`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem divSize_eq_unitE (Ce : ℝ) : divSize L Ce = Ce * (ofRecord D L Del h0).unitE L.Nc := by
  unfold divSize NumDatum.unitE
  have e : L.B0 = (ofRecord D L Del h0).B0 := rfl
  rw [e]
  show Ce * L.sc.x ^ L.sc.eps * ((ofRecord D L Del h0).B0 + L.Nc) =
    Ce * ((ofRecord D L Del h0).sc.x ^ (ofRecord D L Del h0).sc.eps * ((ofRecord D L Del h0).B0 + L.Nc))
  ring

end Record

section Bundle

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

/- English proof (translation)
The claim follows from `eigenvalue_sum_le_closed_of eJ δ Tl lam0 C0 ce Ch Sw C1 H Pk.Zs C CH hl6 hG0 := logCard_le_lambda (A3 := A3) eJ δ Tl lam0 C0 ce Ch Sw C1 H hG l3 := ⟨(Nd.R.m : ℝ) * (C * (Zsc Pk.Zs).l3u), levelThree_bound_closed hZ eJ δ Tl lam0 C0 ce Ch Sw C1 H Pk.Zs C CH, error_bound_closed_numbe …`.
-/
theorem arithAt_scale3 (A3 : FamIn3 K G Pl0 I0 Ty T m) (s : ℕ) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* Kˣ) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
    (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (Nd : NumDatum) (eJz : A3.fam3.base3.J ≃ Fin Nd.R.m) (Nc : ℝ)
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (hZ : ClosedScale3 A3 Nd eJz Nc Zsc)
    (cf : ConvFace A3.fam3.base3) (C CH : ℝ)
    (Pk : IndefPkgR A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) cf C CH)
    (eJ : A3.fam3.base3.J ≃ Fin Nd.R.m) (δ : Code Nd) (Tl : ℕ) (lam0 C0 ce Ch Sw C1 : ℝ)
    (H : Nd.NumFacts δ Nc lam0 C0 ce Ch Sw C1) (bd : Fin m → ℝ) (dg : ℕ)
    (hl6 : ∀ j, (∑ ρ : RPl Nd.R, Nd.logHook ((eJz j).1 + 1) ρ) - Ch * ((Nd.R.f : ℝ) * (Nd.R.nV : ℝ) ^ 2 * Nd.Lp) ≤
      (Zsc Pk.Zs).l6m j - C * (Zsc Pk.Zs).l6u)
    (hC0 : 0 ≤ C) (h28 : 28 ≤ C0) (hG : Real.log (Fintype.card G) ≤ lam0)
    (c13 cG cD : ℝ) (hbd : ∀ j, bd j ≤ c13 * Nd.unitE Nc)
    (hLam : lam0 + Real.log (s : ℝ) ≤ cG * ((Nd.R.m : ℝ) * Nd.unitE Nc))
    (hdg : Real.log (dg : ℝ) + Real.log (s : ℝ) ≤ cD * Nd.unitE Nc) (hce : C + cG + C + (c13 + cD) + 1 ≤ ce)
    (B : ℝ)
    (hB : boundBR Pk.core (lgDef (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H) s) 1 (etaSumBound bd dg s) ≤ B)
    (hg : 24 * (Nd.R.f : ℝ) * (Nd.R.r : ℝ) * QOfR B ((Zsc Pk.Zs).num C CH) ≤ ((min (Nd.g 0) (Nd.g 1) : ℕ) : ℝ)) :
    ArithAt A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc cf C CH Pk (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H) bd dg where
  eig6 := eigenvalue_sum_le_closed_of eJ δ Tl lam0 C0 ce Ch Sw C1 H Pk.Zs C CH hl6
  hG0 := logCard_le_lambda (A3 := A3) eJ δ Tl lam0 C0 ce Ch Sw C1 H hG
  l3 := ⟨(Nd.R.m : ℝ) * (C * (Zsc Pk.Zs).l3u), levelThree_bound_closed hZ eJ δ Tl lam0 C0 ce Ch Sw C1 H Pk.Zs C CH,
    error_bound_closed_numbers Nd Nc hZ eJ δ Tl lam0 C0 ce Ch Sw C1 H Pk.Zs C CH hC0 bd dg s c13 cG cD hbd hLam hdg hce⟩
  q := ⟨QOfR B ((Zsc Pk.Zs).num C CH), delta_nonneg hZ Pk.Zs C CH, delta_mul_Q_le_one hZ Pk.Zs C CH _ hg, one_le_Q _ _,
    Q_ge_bound_add Pk.core _ _ _ B hB⟩
  la_le := logCardGroup_le_lambda hZ eJ δ Tl lam0 C0 ce Ch Sw C1 H Pk.Zs C CH hG
  constant_ge_twenty_eight := twentyEight_le_constant (A3 := A3) eJ δ Tl lam0 C0 ce Ch Sw C1 H h28

/- English proof (translation)
The claim follows from `arithAt_scale3 A3 s P0 ψ0 P1 ψ1 Dc Sp Nd eJz Nc _ (closedScale3_fix A3 P0 ψ0 Nd eJz Nc Ch) cf C CH Pk eJ δ Tl lam0 C0 ce Ch Sw C1 H bd dg (fun j => le_of_eq (levelSix_fixed_eq A3 P0 ψ0 Nd eJz Nc Ch Pk.Zs C j).symm) hC0 h28 hG c13 cG cD hbd hLam hdg hce B hB hg`.
-/
theorem arithmetic_fixed_scale (A3 : FamIn3 K G Pl0 I0 Ty T m) (s : ℕ) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* Kˣ) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
    (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (Nd : NumDatum) (eJz : A3.fam3.base3.J ≃ Fin Nd.R.m) (Nc : ℝ)
    (cf : ConvFace A3.fam3.base3) (C CH : ℝ) (eJ : A3.fam3.base3.J ≃ Fin Nd.R.m) (δ : Code Nd) (Tl : ℕ)
    (lam0 C0 ce Ch Sw C1 : ℝ) (H : Nd.NumFacts δ Nc lam0 C0 ce Ch Sw C1)
    (Pk : IndefPkgR A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp (ZscFix3 A3 P0 ψ0 Nd eJz Nc Ch)) cf C CH)
    (bd : Fin m → ℝ) (dg : ℕ) (hC0 : 0 ≤ C) (h28 : 28 ≤ C0) (hG : Real.log (Fintype.card G) ≤ lam0)
    (c13 cG cD : ℝ) (hbd : ∀ j, bd j ≤ c13 * Nd.unitE Nc)
    (hLam : lam0 + Real.log (s : ℝ) ≤ cG * ((Nd.R.m : ℝ) * Nd.unitE Nc))
    (hdg : Real.log (dg : ℝ) + Real.log (s : ℝ) ≤ cD * Nd.unitE Nc) (hce : C + cG + C + (c13 + cD) + 1 ≤ ce)
    (B : ℝ)
    (hB : boundBR Pk.core (lgDef (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H) s) 1 (etaSumBound bd dg s) ≤ B)
    (hg : 24 * (Nd.R.f : ℝ) * (Nd.R.r : ℝ) * QOfR B ((ZscFix3 A3 P0 ψ0 Nd eJz Nc Ch Pk.Zs).num C CH) ≤
      ((min (Nd.g 0) (Nd.g 1) : ℕ) : ℝ)) :
    ArithAt A3 s P0 ψ0 P1 ψ1 Dc Sp (ZscFix3 A3 P0 ψ0 Nd eJz Nc Ch) cf C CH Pk
      (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H) bd dg :=
  arithAt_scale3 A3 s P0 ψ0 P1 ψ1 Dc Sp Nd eJz Nc _ (closedScale3_fix A3 P0 ψ0 Nd eJz Nc Ch) cf C CH Pk eJ δ Tl
    lam0 C0 ce Ch Sw C1 H bd dg (fun j => le_of_eq (levelSix_fixed_eq A3 P0 ψ0 Nd eJz Nc Ch Pk.Zs C j).symm) hC0 h28 hG
    c13 cG cD hbd hLam hdg hce B hB hg

end Bundle

section RecordQ

open Formalism.MainNotions

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable {D : D7} (L : SizeData₂ D) (Del h0 : ℕ)

/- English proof (translation)
Establish `hb1 : 1 ≤ L.sc.b` using `(ofRecord D L Del h0).one_le_b`. Establish `hb0 : 0 ≤ L.sc.b` using `by linarith`. Unfold `QOfR`. Use `max_le (by nlinarith) ?_` and prove the remaining obligations. Use `show B + (Zsc Zs).x ^ CH * (Zsc Zs).b + 28 * (Zsc Zs).la ≤ 3 * L.sc.b ^ 2`.

Rewrite using `[hZ.x, hZ.b, hZ.la]`. Express the relevant statement in the definitionally equal form `B + L.sc.x ^ CH * L.sc.b + 28 * Real.log (Fintype.card G) ≤ 3 * L.sc.b ^ 2`. Use `mul_le_mul_of_nonneg_right hCH hb0` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem QOfR_le_record {A3 : FamIn3 K G Pl0 I0 Ty T m} {eJz : A3.fam3.base3.J ≃ Fin (ofRecord D L Del h0).R.m} {Nc : ℝ}
    {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} (hZ : ClosedScale3 A3 (ofRecord D L Del h0) eJz Nc Zsc)
    (Zs : DefSub A3.fam3.amb3) (C CH B : ℝ)
    (hB : B ≤ L.sc.b ^ 2) (hCH : L.sc.x ^ CH ≤ L.sc.b) (hG : 28 * Real.log (Fintype.card G) ≤ L.sc.b ^ 2) :
    QOfR B ((Zsc Zs).num C CH) ≤ 3 * L.sc.b ^ 2 := by
  have hb1 : 1 ≤ L.sc.b := (ofRecord D L Del h0).one_le_b
  have hb0 : 0 ≤ L.sc.b := by linarith
  unfold QOfR
  refine max_le (by nlinarith) ?_
  show B + (Zsc Zs).x ^ CH * (Zsc Zs).b + 28 * (Zsc Zs).la ≤ 3 * L.sc.b ^ 2
  rw [hZ.x, hZ.b, hZ.la]
  change B + L.sc.x ^ CH * L.sc.b + 28 * Real.log (Fintype.card G) ≤ 3 * L.sc.b ^ 2
  have := mul_le_mul_of_nonneg_right hCH hb0
  nlinarith

/- English proof (translation)
Establish `hb1 : 1 ≤ L.sc.b` using `(ofRecord D L Del h0).one_le_b`. Establish `hQ` using `QOfR_le_record L Del h0 hZ Zs C CH B hB hCH hG`. Establish `hQ1 : 1 ≤ QOfR B ((Zsc Zs).num C CH)` using `one_le_Q _ _`. Establish `hfr0 : 0 ≤ 24 * (D.R.f : ℝ) * (D.R.r : ℝ)` using `by positivity`. Establish `hk : (1 : ℝ) ≤ (D.R.k : ℝ)`.

Establish `h2 : 2 ≤ D.R.k` using `(ofRecord D L Del h0).k_two`. Conclude with `(show 1 ≤ D.R.k by omega)` after adjusting the coercions. Establish `h8 : L.sc.b ^ 8 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8`. Apply `pow_le_pow_left₀ (by linarith)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.

Establish `hmain : 24 * (D.R.f : ℝ) * (D.R.r : ℝ) * QOfR B ((Zsc Zs).num C CH) ≤ L.sc.b ^ 8`. Combine the equalities or inequalities in the displayed calculation. Establish `hg : ∀ i : Fin 2, L.sc.b ^ 8 ≤ (D.host.g i : ℝ)` using `fun i => h8.trans (hSG i i).1`. Use `show 24 * (D.R.f : ℝ) * (D.R.r : ℝ) * QOfR B ((Zsc Zs).num C CH) ≤ (((min (D.host.g 0) (D.host.g 1)) : ℕ) : ℝ)`. Rewrite using `[Nat.cast_min]`.

Conclude with `le_min (hmain.trans (hg 0)) (hmain.trans (hg 1))`.
-/
theorem hg_of_sizeG (hSG : SizeG L) {A3 : FamIn3 K G Pl0 I0 Ty T m} {eJz : A3.fam3.base3.J ≃ Fin (ofRecord D L Del h0).R.m}
    {Nc : ℝ} {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} (hZ : ClosedScale3 A3 (ofRecord D L Del h0) eJz Nc Zsc)
    (Zs : DefSub A3.fam3.amb3) (C CH B : ℝ)
    (hB : B ≤ L.sc.b ^ 2) (hCH : L.sc.x ^ CH ≤ L.sc.b) (hG : 28 * Real.log (Fintype.card G) ≤ L.sc.b ^ 2)
    (hfr : 72 * (D.R.f : ℝ) * (D.R.r : ℝ) ≤ L.sc.b ^ 6) :
    24 * ((ofRecord D L Del h0).R.f : ℝ) * ((ofRecord D L Del h0).R.r : ℝ) *
        QOfR B ((Zsc Zs).num C CH) ≤
      (((min ((ofRecord D L Del h0).g 0) ((ofRecord D L Del h0).g 1)) : ℕ) : ℝ) := by
  have hb1 : 1 ≤ L.sc.b := (ofRecord D L Del h0).one_le_b
  have hQ := QOfR_le_record L Del h0 hZ Zs C CH B hB hCH hG
  have hQ1 : 1 ≤ QOfR B ((Zsc Zs).num C CH) := one_le_Q _ _
  have hfr0 : 0 ≤ 24 * (D.R.f : ℝ) * (D.R.r : ℝ) := by positivity
  have hk : (1 : ℝ) ≤ (D.R.k : ℝ) := by
    have h2 : 2 ≤ D.R.k := (ofRecord D L Del h0).k_two
    exact_mod_cast (show 1 ≤ D.R.k by omega)
  have h8 : L.sc.b ^ 8 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := by
    apply pow_le_pow_left₀ (by linarith)
    nlinarith
  have hmain : 24 * (D.R.f : ℝ) * (D.R.r : ℝ) *
      QOfR B ((Zsc Zs).num C CH) ≤ L.sc.b ^ 8 := by
    calc 24 * (D.R.f : ℝ) * (D.R.r : ℝ) * QOfR B ((Zsc Zs).num C CH)
        ≤ 24 * (D.R.f : ℝ) * (D.R.r : ℝ) * (3 * L.sc.b ^ 2) := mul_le_mul_of_nonneg_left hQ hfr0
      _ = (72 * (D.R.f : ℝ) * (D.R.r : ℝ)) * L.sc.b ^ 2 := by ring
      _ ≤ L.sc.b ^ 6 * L.sc.b ^ 2 := mul_le_mul_of_nonneg_right hfr (by positivity)
      _ = L.sc.b ^ 8 := by ring
  have hg : ∀ i : Fin 2, L.sc.b ^ 8 ≤ (D.host.g i : ℝ) := fun i => h8.trans (hSG i i).1
  show 24 * (D.R.f : ℝ) * (D.R.r : ℝ) * QOfR B ((Zsc Zs).num C CH) ≤
    (((min (D.host.g 0) (D.host.g 1)) : ℕ) : ℝ)
  rw [Nat.cast_min]
  exact le_min (hmain.trans (hg 0)) (hmain.trans (hg 1))

end RecordQ

section FTieRec

variable {D : D7} (L : SizeData₂ D) (Del h0 : ℕ) {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

/- English proof (translation)
Establish `hj : j ∈ SizeData₂.lifts D`. Unfold `SizeData₂.lifts`. Conclude with `Finset.mem_Icc.2 ⟨h1, h2⟩`. Rewrite using `[hFD j hj (D.plEq.symm y), ofRecord_Fval D L Del h0 hK h1 h2]`. Unfold `NumDatum.Fj`.

Rewrite using `[← Formalism.L2.G.ServJoint.plc_plEq D (D.plEq.symm y), Equiv.apply_symm_apply]`.
-/
theorem Fj_ofRecord_eq (hK : DV.KapDef D) (hFD : L.FDef) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (y : HeightOneSpectrum (𝓞 D.what₂.LL)) : (ofRecord D L Del h0).Fj j y = L.F j (D.plEq.symm y) := by
  have hj : j ∈ SizeData₂.lifts D := by
    unfold SizeData₂.lifts
    exact Finset.mem_Icc.2 ⟨h1, h2⟩
  rw [hFD j hj (D.plEq.symm y), ofRecord_Fval D L Del h0 hK h1 h2]
  unfold NumDatum.Fj
  rw [← Formalism.L2.G.ServJoint.plc_plEq D (D.plEq.symm y), Equiv.apply_symm_apply]

/- English proof (translation)
Introduce `y j`. Use `show (Zsc Zs).F0 y j = _`. Rewrite using `[hF0 Zs y j]`. Conclude with `Fj_ofRecord_eq L Del h0 hK hFD (by omega) (eJz j).2 y`.
-/
theorem fTie_rec (hK : DV.KapDef D) (hFD : L.FDef) {A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m}
    (eJz : A3.fam3.base3.J ≃ Fin D.R.m) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (hF0 : ∀ Zs y j, (Zsc Zs).F0 y j = (ofRecord D L Del h0).Fj ((eJz j).1 + 1) y) (Zs : DefSub A3.fam3.amb3) (C CH : ℝ) :
    FTie L ((Zsc Zs).num C CH) eJz := by
  intro y j
  show (Zsc Zs).F0 y j = _
  rw [hF0 Zs y j]
  exact Fj_ofRecord_eq L Del h0 hK hFD (by omega) (eJz j).2 y

/- English proof (translation)
The claim follows from `fTie_rec L Del h0 hK hFD eJz _ (fun _ _ _ => rfl) Zs C CH`.
-/
theorem fixedScale_tied (hK : DV.KapDef D) (hFD : L.FDef) (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m) (P0 : Subgroup G)
    (ψ0 : P0 →* D.what₂.LLˣ) (eJz : A3.fam3.base3.J ≃ Fin D.R.m) (Nc Cf : ℝ) (Zs : DefSub A3.fam3.amb3) (C CH : ℝ) :
    FTie L ((ZscFix3 A3 P0 ψ0 (ofRecord D L Del h0) eJz Nc Cf Zs).num C CH) eJz :=
  fTie_rec L Del h0 hK hFD eJz _ (fun _ _ _ => rfl) Zs C CH

end FTieRec

end Formalism.L2.DIV

end

noncomputable section

namespace Formalism.L2.DIV.Arith4S

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.DIV.Proofs
open Formalism.MainNotions.DIV.Proofs.HHParts (one_le_szPol f_le k_le m_le t_le N_le L_le one_le_b a_nonneg b'_nonneg one_le_X' n_pos
  k_one w''_nonneg w''_le eta_le)

/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Rewrite using `[Real.rpow_def_of_pos hx0]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `hl` using `Real.log_le_rpow_div hx0.le (half_pos he)`. Establish `hT0 : 0 ≤ x ^ (e / 2)` using `Real.rpow_nonneg hx0.le _`.

Establish `hxe : x ^ e = x ^ (e / 2) * x ^ (e / 2)` using `by rw [← Real.rpow_add hx0]; ring_nf`. Rewrite using `[hxe]`. Establish `h1 : Real.log x * c ≤ x ^ (e / 2) / (e / 2) * c` using `mul_le_mul_of_nonneg_right hl hc`. Establish `h2 : x ^ (e / 2) / (e / 2) * c = (2 * c / e) * x ^ (e / 2)` using `by field_simp`. Establish `h3 : (2 * c / e) * x ^ (e / 2) ≤ x ^ (e / 2) * x ^ (e / 2)` using `mul_le_mul_of_nonneg_right hT hT0`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rpow_le_exp_of {x c e : ℝ} (hx : 1 ≤ x) (he : 0 < e) (hc : 0 ≤ c) (hT : 2 * c / e ≤ x ^ (e / 2)) :
    x ^ c ≤ Real.exp (x ^ e) := by
  have hx0 : 0 < x := by linarith
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.mpr
  have hl := Real.log_le_rpow_div hx0.le (half_pos he)
  have hT0 : 0 ≤ x ^ (e / 2) := Real.rpow_nonneg hx0.le _
  have hxe : x ^ e = x ^ (e / 2) * x ^ (e / 2) := by rw [← Real.rpow_add hx0]; ring_nf
  rw [hxe]
  have h1 : Real.log x * c ≤ x ^ (e / 2) / (e / 2) * c := mul_le_mul_of_nonneg_right hl hc
  have h2 : x ^ (e / 2) / (e / 2) * c = (2 * c / e) * x ^ (e / 2) := by field_simp
  have h3 : (2 * c / e) * x ^ (e / 2) ≤ x ^ (e / 2) * x ^ (e / 2) := mul_le_mul_of_nonneg_right hT hT0
  linarith

/- English proof (translation)
Establish `h` using `Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x) (half_pos he)`. Establish `: x ^ (e / 2) / (e / 2) = 2 / e * x ^ (e / 2)` using `by field_simp`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_le_half {x e : ℝ} (hx : 1 ≤ x) (he : 0 < e) : Real.log x ≤ 2 / e * x ^ (e / 2) := by
  have h := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x) (half_pos he)
  have : x ^ (e / 2) / (e / 2) = 2 / e * x ^ (e / 2) := by field_simp
  linarith

variable {D : D7} (L : SizeData₂ D)

def BigX : Prop :=
  16 ≤ L.sc.x ∧ 48 * (max L.Ct 5 + 3) / L.sc.eps + 6 / L.sc.eps + 2 ≤ L.sc.x ^ (L.sc.eps / 6)

variable {L}

/- English proof (translation)
The claim follows from `L.sc.one_lt_alt.le`.
-/
theorem x_one : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
/- English proof (translation)
The claim follows from `lt_trans one_pos L.sc.one_lt_alt`.
-/
theorem x_pos' : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt

/- English proof (translation)
The claim follows from `Real.rpow_le_rpow_of_exponent_le x_one (by linarith [L.sc.eps_pos])`.
-/
theorem rpow_sixth_le_half : L.sc.x ^ (L.sc.eps / 6) ≤ L.sc.x ^ (L.sc.eps / 2) :=
  Real.rpow_le_rpow_of_exponent_le x_one (by linarith [L.sc.eps_pos])

/- English proof (translation)
Establish `hx9 : 9 ≤ L.sc.x` using `by linarith [hB.1]`. Establish `hP` using `Formalism.MainNotions.DIV.Proofs.szPol_le_rpow hS hx9`. Establish `hP1` using `one_le_szPol L`. Use `set Q := max L.Ct 5 + 3 with hQ`. Establish `hQ0 : 0 ≤ Q` using `by have := le_max_right L.Ct 5; linarith`.

Establish `h1 : szPol L ^ e ≤ (L.sc.x ^ Q) ^ e` using `pow_le_pow_left₀ (by linarith) hP e`. Establish `h2 : (L.sc.x ^ Q) ^ e = L.sc.x ^ (Q * e)` using `by rw [← Real.rpow_natCast, ← Real.rpow_mul x_pos'.le]`. Establish `h3 : L.sc.x ^ (Q * e) ≤ L.sc.x ^ (8 * Q)`. Apply `Real.rpow_le_rpow_of_exponent_le x_one` to reduce the goal to its premises. Establish `: (e : ℝ) ≤ 8` using `by exact_mod_cast he`.

Use the polynomial consequences of the given equalities and inequalities. Establish `heps` using `L.sc.eps_pos`. Establish `h4 : L.sc.x ^ (8 * Q) ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3))`. Apply `rpow_le_exp_of x_one (by linarith) (by linarith)` to reduce the goal to its premises. Establish `e1 : 2 * (8 * Q) / (L.sc.eps / 3) = 48 * Q / L.sc.eps` using `by field_simp; ring`.

Establish `e2 : L.sc.eps / 3 / 2 = L.sc.eps / 6` using `by ring`. Rewrite using `[e1, e2]`. Establish `: 0 ≤ 6 / L.sc.eps` using `by positivity`. Combine the linear relations using `[hB.2]`. Unfold `Scale.X'`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem P_le_X' (hS : SizesAt L) (hB : BigX L) {e : ℕ} (he : e ≤ 8) : szPol L ^ e ≤ L.sc.X' := by
  have hx9 : 9 ≤ L.sc.x := by linarith [hB.1]
  have hP := Formalism.MainNotions.DIV.Proofs.szPol_le_rpow hS hx9
  have hP1 := one_le_szPol L
  set Q := max L.Ct 5 + 3 with hQ
  have hQ0 : 0 ≤ Q := by have := le_max_right L.Ct 5; linarith
  have h1 : szPol L ^ e ≤ (L.sc.x ^ Q) ^ e := pow_le_pow_left₀ (by linarith) hP e
  have h2 : (L.sc.x ^ Q) ^ e = L.sc.x ^ (Q * e) := by rw [← Real.rpow_natCast, ← Real.rpow_mul x_pos'.le]
  have h3 : L.sc.x ^ (Q * e) ≤ L.sc.x ^ (8 * Q) := by
    apply Real.rpow_le_rpow_of_exponent_le x_one
    have : (e : ℝ) ≤ 8 := by exact_mod_cast he
    nlinarith
  have heps := L.sc.eps_pos
  have h4 : L.sc.x ^ (8 * Q) ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3)) := by
    apply rpow_le_exp_of x_one (by linarith) (by linarith)
    have e1 : 2 * (8 * Q) / (L.sc.eps / 3) = 48 * Q / L.sc.eps := by field_simp; ring
    have e2 : L.sc.eps / 3 / 2 = L.sc.eps / 6 := by ring
    rw [e1, e2]
    have : 0 ≤ 6 / L.sc.eps := by positivity
    linarith [hB.2]
  unfold Scale.X'
  linarith

/- English proof (translation)
Unfold `Scale.X' Scale.b Scale.L`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Conclude with `Real.rpow_le_rpow_of_exponent_le x_one (by linarith [L.sc.eps_pos])`.
-/
theorem X'_le_b : L.sc.X' ≤ L.sc.b := by
  unfold Scale.X' Scale.b Scale.L
  apply Real.exp_le_exp.mpr
  exact Real.rpow_le_rpow_of_exponent_le x_one (by linarith [L.sc.eps_pos])

/- English proof (translation)
The claim follows from `(P_le_X' hS hB he).trans X'_le_b`.
-/
theorem P_le_b (hS : SizesAt L) (hB : BigX L) {e : ℕ} (he : e ≤ 8) : szPol L ^ e ≤ L.sc.b :=
  (P_le_X' hS hB he).trans X'_le_b

/- English proof (translation)
Establish `heps` using `L.sc.eps_pos`. Establish `hl` using `log_le_half (x_one (L := L)) heps`. Use `set T := L.sc.x ^ (L.sc.eps / 2) with hT`. Establish `hT1 : 2 / L.sc.eps ≤ T`. Establish `h` using `hB.2`.

Establish `: 0 ≤ 48 * (max L.Ct 5 + 3) / L.sc.eps`. Use `le_max_right L.Ct 5` as an intermediate fact. Apply `div_nonneg (by linarith) heps.le` to reduce the goal to its premises. Establish `: 2 / L.sc.eps ≤ 6 / L.sc.eps` using `div_le_div_of_nonneg_right (by norm_num) heps.le`. Combine the linear relations using `[rpow_sixth_le_half (L := L)]`.

Establish `hT0 : 0 ≤ T` using `Real.rpow_nonneg x_pos'.le _`. Establish `hLT : L.sc.L = T * T` using `by show L.sc.x ^ L.sc.eps = _`. Rewrite using `[hT, ← Real.rpow_add x_pos']`. Put the polynomial expressions in normal form. Rewrite using `[hLT]`.

Use `mul_le_mul_of_nonneg_right hT1 hT0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem logx_le_L (hB : BigX L) : Real.log L.sc.x ≤ L.sc.L := by
  have heps := L.sc.eps_pos
  have hl := log_le_half (x_one (L := L)) heps
  set T := L.sc.x ^ (L.sc.eps / 2) with hT
  have hT1 : 2 / L.sc.eps ≤ T := by
    have h := hB.2
    have : 0 ≤ 48 * (max L.Ct 5 + 3) / L.sc.eps := by
      have := le_max_right L.Ct 5
      apply div_nonneg (by linarith) heps.le
    have : 2 / L.sc.eps ≤ 6 / L.sc.eps := div_le_div_of_nonneg_right (by norm_num) heps.le
    linarith [rpow_sixth_le_half (L := L)]
  have hT0 : 0 ≤ T := Real.rpow_nonneg x_pos'.le _
  have hLT : L.sc.L = T * T := by
    show L.sc.x ^ L.sc.eps = _
    rw [hT, ← Real.rpow_add x_pos']; ring_nf
  rw [hLT]
  have := mul_le_mul_of_nonneg_right hT1 hT0
  linarith

variable (L) (Del h0 : ℕ)

/- English proof (translation)
Use `show ((D.R.N D.R.m : ℕ) : ℝ) ^ 2 ≤ L.sc.b`. Establish `h` using `N_le L`. Establish `h0 : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Conclude with `(pow_le_pow_left₀ h0 h 2).trans (P_le_b hS hB (by norm_num))`.
-/
theorem rank_sq_le_b (hS : SizesAt L) (hB : BigX L) :
    ((ofRecord D L Del h0).Nm : ℝ) ^ 2 ≤ (ofRecord D L Del h0).sc.b := by
  show ((D.R.N D.R.m : ℕ) : ℝ) ^ 2 ≤ L.sc.b
  have h := N_le L
  have h0 : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) := Nat.cast_nonneg _
  exact (pow_le_pow_left₀ h0 h 2).trans (P_le_b hS hB (by norm_num))

/- English proof (translation)
Use `show (D.R.m : ℝ) ^ 3 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 2 * L.sc.L ≤ L.sc.b`. Establish `hm` using `m_le L`. Establish `hN` using `N_le L`. Establish `hL` using `L_le L`. Establish `hm0 : (0 : ℝ) ≤ D.R.m` using `Nat.cast_nonneg _`.

Establish `hN0 : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Establish `hL0 : 0 ≤ L.sc.L` using `(Formalism.MainNotions.DIV.Proofs.HHParts.sc_L_pos L).le`. Establish `hP0 : (0 : ℝ) ≤ szPol L` using `by linarith [one_le_szPol L]`. Establish `hP3 : (0 : ℝ) ≤ szPol L ^ 3` using `pow_nonneg hP0 3`. Establish `hP32 : (0 : ℝ) ≤ szPol L ^ 3 * szPol L ^ 2` using `by positivity`.

Establish `h1 : (D.R.m : ℝ) ^ 3 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 2 * L.sc.L ≤ szPol L ^ 3 * szPol L ^ 2 * szPol L` using `by gcongr`. Establish `h2 : szPol L ^ 3 * szPol L ^ 2 * szPol L = szPol L ^ 6` using `by ring`. Combine the linear relations using `[P_le_b hS hB (e := 6) (by norm_num)]`.
-/
theorem cube_rank_sq_le_b (hS : SizesAt L) (hB : BigX L) :
    ((ofRecord D L Del h0).R.m : ℝ) ^ 3 * ((ofRecord D L Del h0).Nm : ℝ) ^ 2 * (ofRecord D L Del h0).sc.L ≤
      (ofRecord D L Del h0).sc.b := by
  show (D.R.m : ℝ) ^ 3 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 2 * L.sc.L ≤ L.sc.b
  have hm := m_le L; have hN := N_le L; have hL := L_le L
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hL0 : 0 ≤ L.sc.L := (Formalism.MainNotions.DIV.Proofs.HHParts.sc_L_pos L).le
  have hP0 : (0 : ℝ) ≤ szPol L := by linarith [one_le_szPol L]
  have hP3 : (0 : ℝ) ≤ szPol L ^ 3 := pow_nonneg hP0 3
  have hP32 : (0 : ℝ) ≤ szPol L ^ 3 * szPol L ^ 2 := by positivity
  have h1 : (D.R.m : ℝ) ^ 3 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 2 * L.sc.L ≤ szPol L ^ 3 * szPol L ^ 2 * szPol L := by
    gcongr
  have h2 : szPol L ^ 3 * szPol L ^ 2 * szPol L = szPol L ^ 6 := by ring
  linarith [P_le_b hS hB (e := 6) (by norm_num)]

/- English proof (translation)
Use `show (D.R.k : ℝ) * ((D.R.N D.R.m : ℕ) : ℝ) ≤ L.sc.b`. Establish `hk` using `k_le L`. Establish `hN` using `N_le L`. Establish `hk0 : (0 : ℝ) ≤ D.R.k` using `Nat.cast_nonneg _`. Establish `hN0 : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ)` using `Nat.cast_nonneg _`.

Establish `hP0 : (0 : ℝ) ≤ szPol L` using `by linarith [one_le_szPol L]`. Establish `h1 : (D.R.k : ℝ) * ((D.R.N D.R.m : ℕ) : ℝ) ≤ szPol L * szPol L` using `by gcongr`. Establish `h2` using `P_le_b hS hB (e := 2) (by norm_num)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem nf_kN (hS : SizesAt L) (hB : BigX L) :
    ((ofRecord D L Del h0).R.k : ℝ) * ((ofRecord D L Del h0).Nm : ℝ) ≤ (ofRecord D L Del h0).sc.b := by
  show (D.R.k : ℝ) * ((D.R.N D.R.m : ℕ) : ℝ) ≤ L.sc.b
  have hk := k_le L; have hN := N_le L
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hP0 : (0 : ℝ) ≤ szPol L := by linarith [one_le_szPol L]
  have h1 : (D.R.k : ℝ) * ((D.R.N D.R.m : ℕ) : ℝ) ≤ szPol L * szPol L := by gcongr
  have h2 := P_le_b hS hB (e := 2) (by norm_num)
  nlinarith

/- English proof (translation)
Use `show L.sc.b' * ((D.R.N D.R.m : ℕ) : ℝ) ≤ L.sc.a`. Establish `hN` using `N_le L`. Establish `hX` using `P_le_X' hS hB (e := 1) (by norm_num)`. Rewrite `hX` using `[pow_one]`. Establish `hX1` using `one_le_X' L`.

Establish `ha` using `a_nonneg L`. Unfold `Scale.b'`. Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ (by linarith)]`. Conclude with `mul_le_mul_of_nonneg_left (hN.trans hX) ha`.
-/
theorem nf_bN (hS : SizesAt L) (hB : BigX L) :
    (ofRecord D L Del h0).sc.b' * ((ofRecord D L Del h0).Nm : ℝ) ≤ (ofRecord D L Del h0).sc.a := by
  show L.sc.b' * ((D.R.N D.R.m : ℕ) : ℝ) ≤ L.sc.a
  have hN := N_le L
  have hX := P_le_X' hS hB (e := 1) (by norm_num)
  rw [pow_one] at hX
  have hX1 := one_le_X' L
  have ha := a_nonneg L
  unfold Scale.b'
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  exact mul_le_mul_of_nonneg_left (hN.trans hX) ha

/- English proof (translation)
Use `show (D.R.m : ℝ) * (D.R.k : ℝ) * L.sc.b' ≤ L.sc.a`. Establish `hm` using `m_le L`. Establish `hk` using `k_le L`. Establish `hm0 : (0 : ℝ) ≤ D.R.m` using `Nat.cast_nonneg _`. Establish `hk0 : (0 : ℝ) ≤ D.R.k` using `Nat.cast_nonneg _`.

Establish `hX` using `P_le_X' hS hB (e := 2) (by norm_num)`. Establish `hX1` using `one_le_X' L`. Establish `ha` using `a_nonneg L`. Establish `h1 : (D.R.m : ℝ) * (D.R.k : ℝ) ≤ L.sc.X'`. Establish `hP0 : (0 : ℝ) ≤ szPol L` using `by linarith [one_le_szPol L]`.

Establish `: (D.R.m : ℝ) * (D.R.k : ℝ) ≤ szPol L * szPol L` using `by gcongr`. Use the polynomial consequences of the given equalities and inequalities. Unfold `Scale.b'`. Rewrite using `[mul_div_assoc', div_le_iff₀ (by linarith)]`. Conclude with `mul_le_mul_of_nonneg_right h1 ha |>.trans_eq (mul_comm _ _)`.
-/
theorem nf_mkb (hS : SizesAt L) (hB : BigX L) :
    ((ofRecord D L Del h0).R.m : ℝ) * ((ofRecord D L Del h0).R.k : ℝ) * (ofRecord D L Del h0).sc.b' ≤
      (ofRecord D L Del h0).sc.a := by
  show (D.R.m : ℝ) * (D.R.k : ℝ) * L.sc.b' ≤ L.sc.a
  have hm := m_le L; have hk := k_le L
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hX := P_le_X' hS hB (e := 2) (by norm_num)
  have hX1 := one_le_X' L
  have ha := a_nonneg L
  have h1 : (D.R.m : ℝ) * (D.R.k : ℝ) ≤ L.sc.X' := by
    have hP0 : (0 : ℝ) ≤ szPol L := by linarith [one_le_szPol L]
    have : (D.R.m : ℝ) * (D.R.k : ℝ) ≤ szPol L * szPol L := by gcongr
    nlinarith
  unfold Scale.b'
  rw [mul_div_assoc', div_le_iff₀ (by linarith)]
  exact mul_le_mul_of_nonneg_right h1 ha |>.trans_eq (mul_comm _ _)

/- English proof (translation)
Use `show ((D.R.N D.R.m : ℕ) : ℝ) * L.sc.w'' D.R.n ≤ L.sc.b`. Establish `hN` using `N_le L`. Establish `hX` using `P_le_X' hS hB (e := 1) (by norm_num)`. Rewrite `hX` using `[pow_one]`. Establish `hX1` using `one_le_X' L`.

Establish `hn` using `n_pos hS.1`. Establish `hx` using `x_pos' (L := L)`. Establish `hb` using `one_le_b L`. Establish `hw : L.sc.w'' D.R.n = L.sc.b / (L.sc.X' * D.R.n)`. Unfold `Scale.w'' Scale.b' Scale.a`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hw, mul_div_assoc', div_le_iff₀ (by positivity)]`. Establish `h1 : ((D.R.N D.R.m : ℕ) : ℝ) ≤ L.sc.X' * D.R.n` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem nf_Nw (hS : SizesAt L) (hB : BigX L) :
    ((ofRecord D L Del h0).Nm : ℝ) * (ofRecord D L Del h0).sc.w'' (ofRecord D L Del h0).R.n ≤ (ofRecord D L Del h0).sc.b := by
  show ((D.R.N D.R.m : ℕ) : ℝ) * L.sc.w'' D.R.n ≤ L.sc.b
  have hN := N_le L
  have hX := P_le_X' hS hB (e := 1) (by norm_num)
  rw [pow_one] at hX
  have hX1 := one_le_X' L
  have hn := n_pos hS.1
  have hx := x_pos' (L := L)
  have hb := one_le_b L
  have hw : L.sc.w'' D.R.n = L.sc.b / (L.sc.X' * D.R.n) := by
    unfold Scale.w'' Scale.b' Scale.a
    field_simp
  rw [hw, mul_div_assoc', div_le_iff₀ (by positivity)]
  have h1 : ((D.R.N D.R.m : ℕ) : ℝ) ≤ L.sc.X' * D.R.n := by nlinarith
  nlinarith

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hDl, -⟩` from `hS`. Establish `e : (ofRecord D L Del h0).Sc = L.Sc`. Rewrite using `[L.Sc_eq]`. Use `show (D.R.k : ℝ) * (4 * (Del : ℝ)) = (D.R.k : ℝ) * (4 * ((D.s.Del : ℚ) : ℝ))`. Rewrite using `[hDel]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hDl.2.2.2.1`.
-/
theorem nf_kS (hS : SizesAt L) (hDel : D.s.Del = (Del : ℚ)) :
    ((ofRecord D L Del h0).R.k : ℝ) * (ofRecord D L Del h0).Sc ≤ (ofRecord D L Del h0).sc.w'' (ofRecord D L Del h0).R.n := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hDl, -⟩ := hS
  have e : (ofRecord D L Del h0).Sc = L.Sc := by
    rw [L.Sc_eq]
    show (D.R.k : ℝ) * (4 * (Del : ℝ)) = (D.R.k : ℝ) * (4 * ((D.s.Del : ℚ) : ℝ))
    rw [hDel]; push_cast; ring
  rw [e]
  exact hDl.2.2.2.1

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -⟩` from `hS`. Establish `e : (ofRecord D L Del h0).eta = L.etaSz` using `by rw [hh0]; rfl`. Rewrite using `[e]`. Conclude with `hE.2.2.2.2.1`.
-/
theorem nf_blkW (hS : SizesAt L) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)) :
    ((ofRecord D L Del h0).R.m : ℝ) * (((ofRecord D L Del h0).R.t : ℝ) + 1) * (ofRecord D L Del h0).eta ≤
      (ofRecord D L Del h0).sc.w'' (ofRecord D L Del h0).R.n := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -⟩ := hS
  have e : (ofRecord D L Del h0).eta = L.etaSz := by rw [hh0]; rfl
  rw [e]
  exact hE.2.2.2.2.1

/- English proof (translation)
Unfold `SizeData₂.Nc budgetNc rankBudget bSize`. Use `x_pos' (L := L)` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem cloudConstant_nonneg : 0 ≤ L.Nc := by
  unfold SizeData₂.Nc budgetNc rankBudget bSize
  have := x_pos' (L := L)
  positivity

/- English proof (translation)
The claim follows from `Real.log_nonneg (by exact_mod_cast Fintype.card_pos)`.
-/
theorem logCardGroup_nonneg (G : Type) [Group G] [Fintype G] : 0 ≤ Real.log (Fintype.card G : ℝ) :=
  Real.log_nonneg (by exact_mod_cast Fintype.card_pos)

/- English proof (translation)
The claim follows from `logx_le_L hB`.
-/
theorem nf_logx (hB : BigX L) : Real.log (ofRecord D L Del h0).sc.x ≤ (ofRecord D L Del h0).sc.L := logx_le_L hB

/- English proof (translation)
Establish `hrt : D.R.r + 5 ≤ D.R.t`. Use `D.R.rank_add_five_le` as an intermediate fact. Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers. Conclude with `(by omega : 5 ≤ D.R.t)` after adjusting the coercions.
-/
theorem t_five : (5 : ℝ) ≤ D.R.t := by
  have hrt : D.R.r + 5 ≤ D.R.t := by
    have := D.R.rank_add_five_le
    unfold Ranks.r
    omega
  exact_mod_cast (by omega : 5 ≤ D.R.t)

/- English proof (translation)
Establish `hrt : D.R.r + 5 ≤ D.R.t`. Use `D.R.rank_add_five_le` as an intermediate fact. Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers. Conclude with `(by omega : D.R.r ≤ D.R.t)` after adjusting the coercions.
-/
theorem r_le_alt_alt : (D.R.r : ℝ) ≤ D.R.t := by
  have hrt : D.R.r + 5 ≤ D.R.t := by
    have := D.R.rank_add_five_le
    unfold Ranks.r
    omega
  exact_mod_cast (by omega : D.R.r ≤ D.R.t)

/- English proof (translation)
Establish `hN` using `hS.1`. Take `⟨-, -, hK, hKR, -, -, -, -, -, -, -, -, -, hE, -⟩` from `hS`. Establish `e : (ofRecord D L Del h0).eta = L.etaSz` using `by rw [hh0]; rfl`. Rewrite using `[e, (ofRecord D L Del h0).Nm_cast]`. Use `show (D.R.m : ℝ) * L.etaSz * ((D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1)) * L.sc.L ≤ L.sc.b`.

Establish `hmL : (D.R.m : ℝ) ^ 2 * L.sc.L ≤ D.R.k` using `hKR.2.2.2.2.1`. Establish `hm1 : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)`. Establish `hL1 : 1 ≤ L.sc.L` using `le_of_lt (Formalism.L2.DIV.NumDatum.one_lt_L (ofRecord D L Del h0))`. Establish `hmk : (D.R.m : ℝ) ≤ D.R.k` using `by nlinarith`. Establish `hLk : L.sc.L ≤ D.R.k`.

Establish `hm2 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2` using `by nlinarith`. Establish `: L.sc.L ≤ (D.R.m : ℝ) ^ 2 * L.sc.L` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht` using `t_five (D := D)`. Establish `hk1` using `k_one hK`.

Establish `hn` using `n_pos hN`. Establish `hf : (1 : ℝ) ≤ D.R.f` using `by rw [Formalism.MainNotions.DIV.Proofs.HHParts.f_eq]; linarith`. Establish `hE0 : 0 ≤ L.etaSz` using `L.etaSz_pos.le`. Establish `hEb : L.etaSz ≤ L.sc.b / ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3)` using `hE.2.1`. Establish `hM : 0 < (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3` using `by positivity`.

Establish `hEM : L.etaSz * ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) ≤ L.sc.b`. Rewrite `hEb` using `[le_div_iff₀ hM]`. Then use the resulting hypothesis. Establish `hNk : (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ 3 * D.R.k * D.R.t` using `by nlinarith`. Establish `hk0 : (0 : ℝ) ≤ D.R.k` using `by linarith`. Establish `hA : (D.R.m : ℝ) * ((D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1)) * L.sc.L ≤ (D.R.k : ℝ) * (3 * D.R.k * D.R.t) * D.R.k`.

Establish `h0 : (0 : ℝ) ≤ (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `hB3 : (D.R.k : ℝ) * (3 * D.R.k * D.R.t) * D.R.k ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3`. Establish `ht2 : (3 : ℝ) ≤ (D.R.t : ℝ) ^ 2` using `by nlinarith`. Establish `ht3 : 3 * (D.R.t : ℝ) ≤ (D.R.t : ℝ) ^ 3`.

Establish `e : (D.R.t : ℝ) ^ 3 = (D.R.t : ℝ) ^ 2 * D.R.t` using `by ring`. Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities. Establish `ht30 : (0 : ℝ) ≤ (D.R.t : ℝ) ^ 3` using `by positivity`. Establish `h3 : 3 * (D.R.t : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f` using `by nlinarith`.

Establish `hk3 : (0 : ℝ) ≤ (D.R.k : ℝ) ^ 3` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hC` using `hA.trans hB3`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem nf_eta (hS : SizesAt L) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)) :
    ((ofRecord D L Del h0).R.m : ℝ) * (ofRecord D L Del h0).eta * ((ofRecord D L Del h0).Nm : ℝ) *
      (ofRecord D L Del h0).sc.L ≤ (ofRecord D L Del h0).sc.b := by
  have hN := hS.1
  obtain ⟨-, -, hK, hKR, -, -, -, -, -, -, -, -, -, hE, -⟩ := hS
  have e : (ofRecord D L Del h0).eta = L.etaSz := by rw [hh0]; rfl
  rw [e, (ofRecord D L Del h0).Nm_cast]
  show (D.R.m : ℝ) * L.etaSz * ((D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1)) * L.sc.L ≤ L.sc.b
  have hmL : (D.R.m : ℝ) ^ 2 * L.sc.L ≤ D.R.k := hKR.2.2.2.2.1
  have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hL1 : 1 ≤ L.sc.L := le_of_lt (Formalism.L2.DIV.NumDatum.one_lt_L (ofRecord D L Del h0))
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by nlinarith
  have hLk : L.sc.L ≤ D.R.k := by
    have hm2 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by nlinarith
    have : L.sc.L ≤ (D.R.m : ℝ) ^ 2 * L.sc.L := by nlinarith
    linarith
  have ht := t_five (D := D)
  have hk1 := k_one hK
  have hn := n_pos hN
  have hf : (1 : ℝ) ≤ D.R.f := by rw [Formalism.MainNotions.DIV.Proofs.HHParts.f_eq]; linarith
  have hE0 : 0 ≤ L.etaSz := L.etaSz_pos.le
  have hEb : L.etaSz ≤ L.sc.b / ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) := hE.2.1
  have hM : 0 < (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 := by positivity
  have hEM : L.etaSz * ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) ≤ L.sc.b := by
    rwa [le_div_iff₀ hM] at hEb
  have hNk : (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ 3 * D.R.k * D.R.t := by nlinarith
  have hk0 : (0 : ℝ) ≤ D.R.k := by linarith
  have hA : (D.R.m : ℝ) * ((D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1)) * L.sc.L ≤
      (D.R.k : ℝ) * (3 * D.R.k * D.R.t) * D.R.k := by
    have h0 : (0 : ℝ) ≤ (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) := by positivity
    calc (D.R.m : ℝ) * ((D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1)) * L.sc.L
        ≤ (D.R.k : ℝ) * ((D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1)) * L.sc.L := by gcongr
      _ ≤ (D.R.k : ℝ) * (3 * D.R.k * D.R.t) * L.sc.L := by gcongr
      _ ≤ (D.R.k : ℝ) * (3 * D.R.k * D.R.t) * D.R.k := by gcongr
  have hB3 : (D.R.k : ℝ) * (3 * D.R.k * D.R.t) * D.R.k ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 := by
    have ht2 : (3 : ℝ) ≤ (D.R.t : ℝ) ^ 2 := by nlinarith
    have ht3 : 3 * (D.R.t : ℝ) ≤ (D.R.t : ℝ) ^ 3 := by
      have e : (D.R.t : ℝ) ^ 3 = (D.R.t : ℝ) ^ 2 * D.R.t := by ring
      rw [e]; nlinarith
    have ht30 : (0 : ℝ) ≤ (D.R.t : ℝ) ^ 3 := by positivity
    have h3 : 3 * (D.R.t : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f := by nlinarith
    have hk3 : (0 : ℝ) ≤ (D.R.k : ℝ) ^ 3 := by positivity
    nlinarith
  have hC := hA.trans hB3
  calc (D.R.m : ℝ) * L.etaSz * ((D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1)) * L.sc.L
      = L.etaSz * ((D.R.m : ℝ) * ((D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1)) * L.sc.L) := by ring
    _ ≤ L.etaSz * ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) := mul_le_mul_of_nonneg_left hC hE0
    _ ≤ L.sc.b := hEM

/- English proof (translation)
Establish `heps` using `L.sc.eps_pos`. Establish `h` using `hB.2`. Establish `: 0 ≤ 48 * (max L.Ct 5 + 3) / L.sc.eps`. Use `le_max_right L.Ct 5` as an intermediate fact. Apply `div_nonneg (by linarith) heps.le` to reduce the goal to its premises.

Combine the linear relations using `[rpow_sixth_le_half (L := L)]`.
-/
theorem T_big (hB : BigX L) : 6 / L.sc.eps + 2 ≤ L.sc.x ^ (L.sc.eps / 2) := by
  have heps := L.sc.eps_pos
  have h := hB.2
  have : 0 ≤ 48 * (max L.Ct 5 + 3) / L.sc.eps := by
    have := le_max_right L.Ct 5
    apply div_nonneg (by linarith) heps.le
  linarith [rpow_sixth_le_half (L := L)]

/- English proof (translation)
Use `show L.sc.x ^ L.sc.eps = _`. Rewrite using `[← Real.rpow_add x_pos']`. Put the polynomial expressions in normal form.
-/
theorem L_eq_TT : L.sc.L = L.sc.x ^ (L.sc.eps / 2) * L.sc.x ^ (L.sc.eps / 2) := by
  show L.sc.x ^ L.sc.eps = _
  rw [← Real.rpow_add x_pos']; ring_nf

/- English proof (translation)
Rewrite using `[ofRecord_rd D L Del h0]`. Use `show Real.log D.host.rdE ≤ L.sc.L`. Establish `hN` using `hS.1`. Establish `hQD : SizeQD L` using `hS.2.2.2.2.2.2.1`. Establish `hq` using `Formalism.MainNotions.DIV.Proofs.HHParts.q_pos hQD`.

Establish `hd` using `Formalism.MainNotions.DIV.Proofs.HHParts.d_pos hQD`. Take `⟨-, -, hq2, -, hd2, -, hr1, hr2⟩` from `hQD`. Establish `hn` using `n_pos hN`. Establish `heps` using `L.sc.eps_pos`. Establish `heps'` using `L.sc.eps_lt`.

Establish `hx1` using `x_one (L := L)`. Establish `hx0` using `x_pos' (L := L)`. Use `set T := L.sc.x ^ (L.sc.eps / 2) with hT`. Establish `hT1 : 1 ≤ T` using `Real.one_le_rpow hx1 (by linarith)`. Establish `hTb` using `T_big L hB`.

Establish `hQ3 : (D.host.QS : ℝ) / 2 ≤ 2 * L.sc.x ^ (3 : ℝ)`. Establish `hQ` using `L.QS_tie`. Establish `hθ : 0 ≤ L.sc.x ^ (L.sc.eps / 100)` using `Real.rpow_nonneg hx0.le _`. Establish `hn3 : (D.R.n : ℝ) * L.sc.x ^ (L.sc.eps / 100) ≤ L.sc.x ^ (3 : ℝ)`. Use `(mul_le_mul_of_nonneg_right hN.2 hθ).trans ?_` and prove the remaining obligations.

Rewrite using `[← Real.rpow_add hx0]`. Use `Real.rpow_le_rpow_of_exponent_le hx1 ?_` and prove the remaining obligations. Unfold `szTh`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hx3 : 0 < L.sc.x ^ (3 : ℝ)` using `Real.rpow_pos_of_pos hx0 _`. Establish `h1 : Real.log D.host.rdE ≤ Real.log 2 + 3 * Real.log L.sc.x + (Real.log D.host.q + Real.log D.host.d) / 2`. Establish `hr3 : D.host.rdE ≤ 2 * L.sc.x ^ (3 : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d)` using `hr2.trans (mul_le_mul_of_nonneg_right hQ3 (Real.sqrt_nonneg _))`. Use `(Real.log_le_log (by linarith) hr3).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_rpow hx0]`.

Establish `hqT : Real.log D.host.q ≤ T` using `hq2.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by unfold szTh; linarith))`. Establish `hdT : Real.log D.host.d ≤ T` using `hd2.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by unfold szTh; linarith))`. Establish `hlx` using `log_le_half hx1 heps`. Establish `hl2 : Real.log 2 ≤ 1` using `by have := Real.log_two_lt_d9; linarith`. Rewrite using `[L_eq_TT L]`.

Establish `hk : 6 / L.sc.eps * T + T + 1 ≤ T * T` using `by nlinarith`. Establish `e3 : 3 * (2 / L.sc.eps * T) = 6 / L.sc.eps * T` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nf_logrd (hS : SizesAt L) (hB : BigX L) :
    Real.log (ofRecord D L Del h0).rd ≤ (ofRecord D L Del h0).sc.L := by
  rw [ofRecord_rd D L Del h0]
  show Real.log D.host.rdE ≤ L.sc.L
  have hN := hS.1
  have hQD : SizeQD L := hS.2.2.2.2.2.2.1
  have hq := Formalism.MainNotions.DIV.Proofs.HHParts.q_pos hQD
  have hd := Formalism.MainNotions.DIV.Proofs.HHParts.d_pos hQD
  obtain ⟨-, -, hq2, -, hd2, -, hr1, hr2⟩ := hQD
  have hn := n_pos hN
  have heps := L.sc.eps_pos
  have heps' := L.sc.eps_lt
  have hx1 := x_one (L := L)
  have hx0 := x_pos' (L := L)
  set T := L.sc.x ^ (L.sc.eps / 2) with hT
  have hT1 : 1 ≤ T := Real.one_le_rpow hx1 (by linarith)
  have hTb := T_big L hB

  have hQ3 : (D.host.QS : ℝ) / 2 ≤ 2 * L.sc.x ^ (3 : ℝ) := by
    have hQ := L.QS_tie
    have hθ : 0 ≤ L.sc.x ^ (L.sc.eps / 100) := Real.rpow_nonneg hx0.le _
    have hn3 : (D.R.n : ℝ) * L.sc.x ^ (L.sc.eps / 100) ≤ L.sc.x ^ (3 : ℝ) := by
      refine (mul_le_mul_of_nonneg_right hN.2 hθ).trans ?_
      rw [← Real.rpow_add hx0]
      refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
      unfold szTh; linarith
    linarith
  have hx3 : 0 < L.sc.x ^ (3 : ℝ) := Real.rpow_pos_of_pos hx0 _

  have h1 : Real.log D.host.rdE ≤ Real.log 2 + 3 * Real.log L.sc.x + (Real.log D.host.q + Real.log D.host.d) / 2 := by
    have hr3 : D.host.rdE ≤ 2 * L.sc.x ^ (3 : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) :=
      hr2.trans (mul_le_mul_of_nonneg_right hQ3 (Real.sqrt_nonneg _))
    refine (Real.log_le_log (by linarith) hr3).trans (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_sqrt (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_rpow hx0]

  have hqT : Real.log D.host.q ≤ T := hq2.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by unfold szTh; linarith))
  have hdT : Real.log D.host.d ≤ T := hd2.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by unfold szTh; linarith))
  have hlx := log_le_half hx1 heps
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  rw [L_eq_TT L]
  have hk : 6 / L.sc.eps * T + T + 1 ≤ T * T := by nlinarith
  have e3 : 3 * (2 / L.sc.eps * T) = 6 / L.sc.eps * T := by ring
  linarith

/- English proof (translation)
Rewrite using `[ofRecord_logOm D L Del h0, ofRecord_La D L Del h0]`. Take `⟨-, -, -, -, -, -, hQD, -⟩` from `hS`. Take `⟨-, -, -, -, -, hdl, hr1, -⟩` from `hQD`. Establish `hx0` using `x_pos' (L := L)`. Establish `hb0 : 0 < L.sc.b` using `by have := one_le_b L; linarith`.

Establish `hr0 : 0 < D.host.rdE` using `by linarith`. Establish `hlr : 0 ≤ Real.log D.host.rdE` using `Real.log_nonneg hr1`. Establish `hLa : L.La = Real.log L.sc.x + L.sc.L + Real.log D.host.rdE`. Unfold `SizeData₂.La Scale.a`. Rewrite using `[Real.log_mul (by positivity) hr0.ne', Real.log_mul hx0.ne' hb0.ne']`.

Unfold `Scale.b`. Rewrite using `[Real.log_exp]`. Establish `hOm : L.logOm = Real.eulerMascheroniConstant + (Real.log Real.pi + Real.log 2 - Real.log D.host.rdE) - L.logDerivativeAtOne`. Unfold `SizeData₂.logOm Host.v`. Rewrite using `[div_div_eq_mul_div, Real.log_div (by positivity) hr0.ne', Real.log_mul Real.pi_pos.ne' (by norm_num)]`.

Rewrite using `[hLa, hOm]`. Establish `hg1` using `Real.eulerMascheroniConstant_lt_two_thirds`. Establish `hg0 : 0 ≤ Real.eulerMascheroniConstant` using `by have := Real.one_half_lt_eulerMascheroniConstant; linarith`. Establish `hpi : Real.log Real.pi ≤ 2 * Real.log 2`. Rewrite using `[← Real.log_rpow (by norm_num : (0:ℝ) < 2)]`.

Conclude with `Real.log_le_log Real.pi_pos (by have := Real.pi_lt_four; norm_num; linarith)`. Establish `hpi0 : 0 ≤ Real.log Real.pi` using `Real.log_nonneg (by linarith [Real.pi_gt_three])`. Establish `hl2` using `Real.log_two_gt_d9`. Establish `hl20 : 0 ≤ Real.log 2` using `by linarith`. Establish `hx16 : 4 * Real.log 2 ≤ Real.log L.sc.x`.

Establish `: Real.log 16 ≤ Real.log L.sc.x` using `Real.log_le_log (by norm_num) hB.1`. Establish `e : Real.log 16 = 4 * Real.log 2`. Rewrite using `[show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdl'` using `abs_le.1 hdl`.

Establish `hLx : L.sc.x ^ L.sc.eps = L.sc.L` using `rfl`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> nlinarith [hdl'.1, hdl'.2]`.
-/
theorem nf_Om (hS : SizesAt L) (hB : BigX L) : |(ofRecord D L Del h0).logOm| ≤ (ofRecord D L Del h0).La := by
  rw [ofRecord_logOm D L Del h0, ofRecord_La D L Del h0]
  obtain ⟨-, -, -, -, -, -, hQD, -⟩ := hS
  obtain ⟨-, -, -, -, -, hdl, hr1, -⟩ := hQD
  have hx0 := x_pos' (L := L)
  have hb0 : 0 < L.sc.b := by have := one_le_b L; linarith
  have hr0 : 0 < D.host.rdE := by linarith
  have hlr : 0 ≤ Real.log D.host.rdE := Real.log_nonneg hr1
  have hLa : L.La = Real.log L.sc.x + L.sc.L + Real.log D.host.rdE := by
    unfold SizeData₂.La Scale.a
    rw [Real.log_mul (by positivity) hr0.ne', Real.log_mul hx0.ne' hb0.ne']
    unfold Scale.b
    rw [Real.log_exp]
  have hOm : L.logOm = Real.eulerMascheroniConstant + (Real.log Real.pi + Real.log 2 - Real.log D.host.rdE) - L.logDerivativeAtOne := by
    unfold SizeData₂.logOm Host.v
    rw [div_div_eq_mul_div, Real.log_div (by positivity) hr0.ne', Real.log_mul Real.pi_pos.ne' (by norm_num)]
  rw [hLa, hOm]
  have hg1 := Real.eulerMascheroniConstant_lt_two_thirds
  have hg0 : 0 ≤ Real.eulerMascheroniConstant := by have := Real.one_half_lt_eulerMascheroniConstant; linarith
  have hpi : Real.log Real.pi ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num : (0:ℝ) < 2)]
    exact Real.log_le_log Real.pi_pos (by have := Real.pi_lt_four; norm_num; linarith)
  have hpi0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hl2 := Real.log_two_gt_d9
  have hl20 : 0 ≤ Real.log 2 := by linarith
  have hx16 : 4 * Real.log 2 ≤ Real.log L.sc.x := by
    have : Real.log 16 ≤ Real.log L.sc.x := Real.log_le_log (by norm_num) hB.1
    have e : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    linarith
  have hdl' := abs_le.1 hdl
  have hLx : L.sc.x ^ L.sc.eps = L.sc.L := rfl
  rw [abs_le]
  constructor <;> nlinarith [hdl'.1, hdl'.2]

/- English proof (translation)
Use `show (D.R.m : ℝ) * Real.log (Fintype.card G : ℝ) ≤ L.sc.b`. Establish `hS'` using `hS`. Establish `hK` using `hS.2.2.1`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hSG, -⟩` from `hS`. Establish `hg0 : (0 : ℝ) < D.host.g 0` using `by exact_mod_cast (D.host.g_prime 0).pos`.

Establish `hlam : Real.log (Fintype.card G : ℝ) ≤ 2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * Real.log (2 * (D.host.g 0 : ℝ))`. Establish `h` using `GZeroLogBound D (D.host.g 0 : ℝ) (fun i => (hSG i 0).2.1)`. Rewrite using `[hc]`. Conclude with `h`. Establish `hL1 : 1 ≤ L.sc.L` using `le_of_lt (Formalism.L2.DIV.NumDatum.one_lt_L (ofRecord D L Del h0))`.

Establish `hth` using `Formalism.MainNotions.DIV.Proofs.HHParts.xth_le (L := L)`. Establish `hlg : Real.log (2 * (D.host.g 0 : ℝ)) ≤ 2 * L.sc.L ^ 2`. Rewrite using `[Real.log_mul (by norm_num) hg0.ne']`. Establish `h1` using `(hSG 0 0).2.2`. Establish `h2 : L.sc.x ^ szTh L * L.sc.L ≤ L.sc.L * L.sc.L` using `mul_le_mul_of_nonneg_right hth (by linarith)`.

Establish `h3` using `Real.log_two_lt_d9`. Use the polynomial consequences of the given equalities and inequalities. Establish `hP1` using `one_le_szPol L`. Establish `hP0 : (0 : ℝ) ≤ szPol L` using `by linarith`. Establish `hm` using `m_le L`.

Establish `hf` using `f_le L`. Establish `hL` using `L_le L`. Establish `hr : (D.R.r : ℝ) ≤ szPol L` using `(r_le_alt_alt (D := D)).trans (t_le L)`. Establish `hm0 : (0 : ℝ) ≤ D.R.m` using `Nat.cast_nonneg _`. Establish `hf0 : (0 : ℝ) ≤ D.R.f` using `Nat.cast_nonneg _`.

Establish `hr0 : (0 : ℝ) ≤ D.R.r` using `Nat.cast_nonneg _`. Establish `hL0 : (0 : ℝ) ≤ L.sc.L` using `by linarith`. Establish `hP4 : 16 ≤ szPol L` using `hB.1.trans (Formalism.MainNotions.DIV.Proofs.HHParts.x_le L hK)`. Establish `hlog0 : 0 ≤ Real.log (Fintype.card G : ℝ)` using `Real.log_nonneg (by exact_mod_cast Fintype.card_pos)`. Establish `h1 : (D.R.m : ℝ) * Real.log (Fintype.card G : ℝ) ≤ (D.R.m : ℝ) * (2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (2 * L.sc.L ^ 2))`.

Apply `mul_le_mul_of_nonneg_left _ hm0` to reduce the goal to its premises. Conclude with `hlam.trans (mul_le_mul_of_nonneg_left hlg (by positivity))`. Establish `h2 : (D.R.m : ℝ) * (2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (2 * L.sc.L ^ 2)) ≤ 4 * (szPol L * (szPol L * szPol L ^ 2 * szPol L ^ 2))`. Establish `e : (D.R.m : ℝ) * (2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (2 * L.sc.L ^ 2)) = 4 * ((D.R.m : ℝ) * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L ^ 2))` using `by ring`. Rewrite using `[e]`.

Use `gcongr`. Establish `h3 : 4 * (szPol L * (szPol L * szPol L ^ 2 * szPol L ^ 2)) ≤ szPol L ^ 7`. Establish `e : szPol L ^ 7 = szPol L * (szPol L * (szPol L * szPol L ^ 2 * szPol L ^ 2))` using `by ring`. Rewrite using `[e]`. Establish `: (0 : ℝ) ≤ szPol L * (szPol L * szPol L ^ 2 * szPol L ^ 2)` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear relations using `[P_le_b hS' hB (e := 7) (by norm_num)]`.
-/
theorem nf_lam (G : Type) [Group G] [Fintype G] (hS : SizesAt L) (hB : BigX L) (hc : Fintype.card G = D.what₂.restRowsFiniteGroupCard) :
    ((ofRecord D L Del h0).R.m : ℝ) * Real.log (Fintype.card G : ℝ) ≤ (ofRecord D L Del h0).sc.b := by
  show (D.R.m : ℝ) * Real.log (Fintype.card G : ℝ) ≤ L.sc.b
  have hS' := hS
  have hK := hS.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hSG, -⟩ := hS
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hlam : Real.log (Fintype.card G : ℝ) ≤
      2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * Real.log (2 * (D.host.g 0 : ℝ)) := by
    have h := GZeroLogBound D (D.host.g 0 : ℝ) (fun i => (hSG i 0).2.1)
    rw [hc]
    exact h
  have hL1 : 1 ≤ L.sc.L := le_of_lt (Formalism.L2.DIV.NumDatum.one_lt_L (ofRecord D L Del h0))
  have hth := Formalism.MainNotions.DIV.Proofs.HHParts.xth_le (L := L)
  have hlg : Real.log (2 * (D.host.g 0 : ℝ)) ≤ 2 * L.sc.L ^ 2 := by
    rw [Real.log_mul (by norm_num) hg0.ne']
    have h1 := (hSG 0 0).2.2
    have h2 : L.sc.x ^ szTh L * L.sc.L ≤ L.sc.L * L.sc.L := mul_le_mul_of_nonneg_right hth (by linarith)
    have h3 := Real.log_two_lt_d9
    nlinarith
  have hP1 := one_le_szPol L
  have hP0 : (0 : ℝ) ≤ szPol L := by linarith
  have hm := m_le L; have hf := f_le L; have hL := L_le L
  have hr : (D.R.r : ℝ) ≤ szPol L := (r_le_alt_alt (D := D)).trans (t_le L)
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ L.sc.L := by linarith
  have hP4 : 16 ≤ szPol L := hB.1.trans (Formalism.MainNotions.DIV.Proofs.HHParts.x_le L hK)
  have hlog0 : 0 ≤ Real.log (Fintype.card G : ℝ) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have h1 : (D.R.m : ℝ) * Real.log (Fintype.card G : ℝ) ≤
      (D.R.m : ℝ) * (2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (2 * L.sc.L ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ hm0
    exact hlam.trans (mul_le_mul_of_nonneg_left hlg (by positivity))
  have h2 : (D.R.m : ℝ) * (2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (2 * L.sc.L ^ 2)) ≤
      4 * (szPol L * (szPol L * szPol L ^ 2 * szPol L ^ 2)) := by
    have e : (D.R.m : ℝ) * (2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (2 * L.sc.L ^ 2)) =
        4 * ((D.R.m : ℝ) * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L ^ 2)) := by ring
    rw [e]
    gcongr
  have h3 : 4 * (szPol L * (szPol L * szPol L ^ 2 * szPol L ^ 2)) ≤ szPol L ^ 7 := by
    have e : szPol L ^ 7 = szPol L * (szPol L * (szPol L * szPol L ^ 2 * szPol L ^ 2)) := by ring
    rw [e]
    have : (0 : ℝ) ≤ szPol L * (szPol L * szPol L ^ 2 * szPol L ^ 2) := by positivity
    nlinarith
  linarith [P_le_b hS' hB (e := 7) (by norm_num)]

/- English proof (translation)
Establish `hN` using `hS.1`. Take `⟨-, -, hK, -, -, -, -, -, -, -, -, -, -, hE, -⟩` from `hS`. Establish `ht` using `t_five (D := D)`. Establish `hk1` using `k_one hK`. Establish `hn` using `n_pos hN`.

Establish `hf : (1 : ℝ) ≤ D.R.f` using `by rw [Formalism.MainNotions.DIV.Proofs.HHParts.f_eq]; linarith`. Establish `hb` using `one_le_b L`. Establish `hM : (2 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3`. Establish `h1 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 3` using `one_le_pow₀ hk1`. Establish `h2 : (2 : ℝ) ≤ (D.R.t : ℝ) ^ 3`.

Use `pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) (show (2:ℝ) ≤ D.R.t by linarith) 3` as an intermediate fact. Evaluate the numerical expressions using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : (2 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Use `hE.2.1.trans ?_` and prove the remaining obligations. Conclude with `div_le_div_of_nonneg_left (by linarith) (by norm_num) hM`.
-/
theorem eta_half (hS : SizesAt L) : L.etaSz ≤ L.sc.b / 2 := by
  have hN := hS.1
  obtain ⟨-, -, hK, -, -, -, -, -, -, -, -, -, -, hE, -⟩ := hS
  have ht := t_five (D := D)
  have hk1 := k_one hK
  have hn := n_pos hN
  have hf : (1 : ℝ) ≤ D.R.f := by rw [Formalism.MainNotions.DIV.Proofs.HHParts.f_eq]; linarith
  have hb := one_le_b L
  have hM : (2 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 := by
    have h1 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ hk1
    have h2 : (2 : ℝ) ≤ (D.R.t : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) (show (2:ℝ) ≤ D.R.t by linarith) 3
      norm_num at this
      linarith
    have h3 : (2 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f := by nlinarith
    nlinarith
  refine hE.2.1.trans ?_
  exact div_le_div_of_nonneg_left (by linarith) (by norm_num) hM

/- English proof (translation)
Establish `hK` using `hS.2.2.1`. Establish `hxP` using `Formalism.MainNotions.DIV.Proofs.HHParts.x_le L hK`. Establish `hP16 : 16 ≤ szPol L` using `hB.1.trans hxP`. Establish `hX` using `P_le_X' hS hB (e := 2) (by norm_num)`. Establish `hX1` using `one_le_X' L`.

Establish `hx0` using `x_pos' (L := L)`. Establish `hb` using `one_le_b L`. Establish `h4x : 4 * L.sc.x ≤ L.sc.X'` using `by nlinarith`. Unfold `Scale.b' Scale.a`. Rewrite using `[div_le_div_iff₀ (by linarith) (by norm_num)]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem b'_quarter (hS : SizesAt L) (hB : BigX L) : L.sc.b' ≤ L.sc.b / 4 := by
  have hK := hS.2.2.1
  have hxP := Formalism.MainNotions.DIV.Proofs.HHParts.x_le L hK
  have hP16 : 16 ≤ szPol L := hB.1.trans hxP
  have hX := P_le_X' hS hB (e := 2) (by norm_num)
  have hX1 := one_le_X' L
  have hx0 := x_pos' (L := L)
  have hb := one_le_b L
  have h4x : 4 * L.sc.x ≤ L.sc.X' := by nlinarith
  unfold Scale.b' Scale.a
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith

/- English proof (translation)
Introduce `j h1 h2 z`. Rewrite using `[ofRecord_w D L Del h0 h1 z]`. Use `show wj D j (tauPl D z) ≤ 2 * L.sc.b`. Establish `hN` using `hS.1`. Establish `hK` using `hS.2.2.1`.

Establish `hRho : SizeRho L` using `hS.2.2.2.2.2.2.2.2.2.1`. Establish `hBot : SizeBot L` using `hS.2.2.2.2.2.2.2.2.2.2.1`. Establish `hLa : SizeLa L` using `hS.2.2.2.2.2.2.2.2.1`. Establish `hEh` using `eta_half L hS`. Establish `hb'q` using `b'_quarter L hS hB`.

Establish `hb` using `one_le_b L`. Establish `hb'0` using `b'_nonneg L`. Establish `hx0` using `x_pos' (L := L)`. Establish `hXb` using `X'_le_b (L := L)`. Establish `hxP` using `Formalism.MainNotions.DIV.Proofs.HHParts.x_le L hK`.

Establish `hX` using `P_le_X' hS hB (e := 1) (by norm_num)`. Rewrite `hX` using `[pow_one]`. Establish `hb16 : 16 ≤ L.sc.b` using `by linarith [hB.1]`. Establish `h2' : j ≤ D.R.m` using `h2`. Use `set τ := tauPl D z`.

Break down `Formalism.MainNotions.DIV.Proofs.HHParts.top_or τ with ⟨t, ht⟩ | hnt` into its components or cases. Take `⟨-, w2⟩` from `L.win_top j h1 h2' τ t ht`. Establish `hbt` using `hBot t`. Establish `hk0 : (0 : ℝ) < D.R.k` using `by linarith [k_one hK]`. Establish `hLaG` using `Formalism.MainNotions.DIV.Proofs.HHParts.LaG_pos hLa`.

Establish `hNst : 0 ≤ szNst L`. Unfold `szNst Scale.delta1`. Use `x_pos' (L := L)` as an intermediate fact. Check the signs of the components of the expression. Establish `hxe : 0 ≤ L.sc.x ^ L.sc.eps` using `Real.rpow_nonneg hx0.le _`.

Establish `hq : szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1`. Establish `h2t : 0 ≤ L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k`. Use `Real.log_nonneg (x_one (L := L))` as an intermediate fact. Use `Real.rpow_nonneg hx0.le (szTh L)` as an intermediate fact. Check the signs of the components of the expression.

Establish `hxm2 : L.sc.x ^ (-2 : ℝ) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos (x_one (L := L)) (by norm_num)`. Establish `hR` using `hRho`. Unfold `SizeRho at hR`. Establish `e : 4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k)` using `by ring`. Rewrite `hR` using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbt2 : (L.bT t : ℝ) ≤ 2 * L.sc.b'`. Establish `e : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k = (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b'` using `by ring`. Rewrite `hbt` using `[e]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hbx : L.sc.b' / L.sc.x ≤ L.sc.b'` using `div_le_self hb'0 (x_one (L := L))`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hth : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces`. Take `⟨-, w2⟩` from `L.win_thick j h1 h2' τ hth`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hthin : D.host.IsThin (D.eTau τ : D.R.GG)` using `⟨(D.eTau τ).2, hnt, hth⟩`. Take `⟨-, w2⟩` from `L.win_thin j h1 h2' τ hthin`. Establish `hw` using `w''_le (L := L) hN`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem size_le_two_b (hS : SizesAt L) (hB : BigX L) :
    ∀ j, 1 ≤ j → j ≤ (ofRecord D L Del h0).R.m → ∀ z, (ofRecord D L Del h0).w j z ≤ 2 * (ofRecord D L Del h0).sc.b := by
  intro j h1 h2 z
  rw [ofRecord_w D L Del h0 h1 z]
  show wj D j (tauPl D z) ≤ 2 * L.sc.b
  have hN := hS.1
  have hK := hS.2.2.1
  have hRho : SizeRho L := hS.2.2.2.2.2.2.2.2.2.1
  have hBot : SizeBot L := hS.2.2.2.2.2.2.2.2.2.2.1
  have hLa : SizeLa L := hS.2.2.2.2.2.2.2.2.1
  have hEh := eta_half L hS
  have hb'q := b'_quarter L hS hB
  have hb := one_le_b L
  have hb'0 := b'_nonneg L
  have hx0 := x_pos' (L := L)
  have hXb := X'_le_b (L := L)
  have hxP := Formalism.MainNotions.DIV.Proofs.HHParts.x_le L hK
  have hX := P_le_X' hS hB (e := 1) (by norm_num)
  rw [pow_one] at hX
  have hb16 : 16 ≤ L.sc.b := by linarith [hB.1]
  have h2' : j ≤ D.R.m := h2
  set τ := tauPl D z
  rcases Formalism.MainNotions.DIV.Proofs.HHParts.top_or τ with ⟨t, ht⟩ | hnt
  · obtain ⟨-, w2⟩ := L.win_top j h1 h2' τ t ht
    have hbt := hBot t
    have hk0 : (0 : ℝ) < D.R.k := by linarith [k_one hK]
    have hLaG := Formalism.MainNotions.DIV.Proofs.HHParts.LaG_pos hLa
    have hNst : 0 ≤ szNst L := by
      unfold szNst Scale.delta1
      have := x_pos' (L := L)
      positivity
    have hxe : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg hx0.le _
    have hq : szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 := by
      have h2t : 0 ≤ L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k := by
        have := Real.log_nonneg (x_one (L := L))
        have := Real.rpow_nonneg hx0.le (szTh L)
        positivity
      have hxm2 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (x_one (L := L)) (by norm_num)
      have hR := hRho
      unfold SizeRho at hR
      have e : 4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
      rw [e] at hR
      linarith
    have hbt2 : (L.bT t : ℝ) ≤ 2 * L.sc.b' := by
      have e : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
          (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
      rw [e] at hbt
      nlinarith
    have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0 (x_one (L := L))
    linarith
  · by_cases hth : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · obtain ⟨-, w2⟩ := L.win_thick j h1 h2' τ hth
      linarith
    · have hthin : D.host.IsThin (D.eTau τ : D.R.GG) := ⟨(D.eTau τ).2, hnt, hth⟩
      obtain ⟨-, w2⟩ := L.win_thin j h1 h2' τ hthin
      have hw := w''_le (L := L) hN
      linarith

/- English proof (translation)
Use `⟨hx16, ?_⟩` and prove the remaining obligations. Establish `heps` using `L.sc.eps_pos`. Use `set c := 48 * (max L.Ct 5 + 3) / L.sc.eps + 6 / L.sc.eps + 2 with hc`. Establish `hc0 : 0 ≤ c`. Use `le_max_right L.Ct 5` as an intermediate fact.

Establish `: 0 ≤ 48 * (max L.Ct 5 + 3) / L.sc.eps` using `div_nonneg (by linarith) heps.le`. Establish `: 0 ≤ 6 / L.sc.eps` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : (c ^ (6 / L.sc.eps)) ^ (L.sc.eps / 6) ≤ L.sc.x ^ (L.sc.eps / 6)` using `Real.rpow_le_rpow (Real.rpow_nonneg hc0 _) hx (by positivity)`. Establish `h2 : (c ^ (6 / L.sc.eps)) ^ (L.sc.eps / 6) = c`.

Rewrite using `[← Real.rpow_mul hc0, show 6 / L.sc.eps * (L.sc.eps / 6) = 1 by field_simp, Real.rpow_one]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bigX_of (hx16 : 16 ≤ L.sc.x)
    (hx : (48 * (max L.Ct 5 + 3) / L.sc.eps + 6 / L.sc.eps + 2) ^ (6 / L.sc.eps) ≤ L.sc.x) : BigX L := by
  refine ⟨hx16, ?_⟩
  have heps := L.sc.eps_pos
  set c := 48 * (max L.Ct 5 + 3) / L.sc.eps + 6 / L.sc.eps + 2 with hc
  have hc0 : 0 ≤ c := by
    have := le_max_right L.Ct 5
    have : 0 ≤ 48 * (max L.Ct 5 + 3) / L.sc.eps := div_nonneg (by linarith) heps.le
    have : 0 ≤ 6 / L.sc.eps := by positivity
    linarith
  have h1 : (c ^ (6 / L.sc.eps)) ^ (L.sc.eps / 6) ≤ L.sc.x ^ (L.sc.eps / 6) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hc0 _) hx (by positivity)
  have h2 : (c ^ (6 / L.sc.eps)) ^ (L.sc.eps / 6) = c := by
    rw [← Real.rpow_mul hc0, show 6 / L.sc.eps * (L.sc.eps / 6) = 1 by field_simp, Real.rpow_one]
  linarith

end Formalism.L2.DIV.Arith4S

end

noncomputable section

namespace Formalism.L2.DIV.Arith4S

open Formalism.BasicNotions Formalism.L2.DIV Formalism.MainNotions.G

variable {D : D7} (L : SizeData₂ D) (Del h0 : ℕ)

/- English proof (translation)
Establish `e : ((D.eTau (tauPl D z) : D.R.Psi) : D.R.GG) = plGG D z`. Unfold `tauPl`. Rewrite using `[Equiv.apply_symm_apply]`. Rewrite using `[e]`. Unfold `Host.topPlaces`.

Rewrite using `[Finset.mem_image]`. Take `⟨β, t⟩` from `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t', ht', h⟩`. Consider the cases of `β`.

Establish `h2 : D.R.tau1 t' = D.R.tau1 t` using `h`. Establish `h3 : t' = t` using `D.R.toFrame.tau1_injective h2`. Conclude with `⟨rfl, h3 ▸ ht'⟩`. Conclude with `absurd (show D.R.tau1 t' = D.R.tau2 t from h) (D.R.toFrame.ramifiedTau1_ne_ramifiedTau2 t' t)`. Introduce and unpack `⟨h1, h2⟩`.

Establish `h1' : β = false` using `h1`. Substitute `h1'` using the available equality. Conclude with `⟨t, h2, rfl⟩`.
-/
theorem tauPl_top_iff (z : Bool × HH D) :
    ((D.eTau (tauPl D z) : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces ↔
      (z.1 = false ∧ z.2 ∈ D.host.TT) := by
  classical
  have e : ((D.eTau (tauPl D z) : D.R.Psi) : D.R.GG) = plGG D z := by
    unfold tauPl
    rw [Equiv.apply_symm_apply]
  rw [e]
  unfold Host.topPlaces
  rw [Finset.mem_image]
  obtain ⟨β, t⟩ := z
  constructor
  · rintro ⟨t', ht', h⟩
    cases β
    · have h2 : D.R.tau1 t' = D.R.tau1 t := h
      have h3 : t' = t := D.R.toFrame.tau1_injective h2
      exact ⟨rfl, h3 ▸ ht'⟩
    · exact absurd (show D.R.tau1 t' = D.R.tau2 t from h) (D.R.toFrame.ramifiedTau1_ne_ramifiedTau2 t' t)
  · rintro ⟨h1, h2⟩
    have h1' : β = false := h1
    subst h1'
    exact ⟨t, h2, rfl⟩

/- English proof (translation)
Introduce `z i h`. Rewrite using `[ofRecord_uW D L Del h0 hDel u z, ofRecord_uW D L Del h0 hDel u z]`. Establish `hi : i < D.R.k - 1` using `by have : i + 1 < D.R.k := h; omega`. Establish `hs : (ofRecord D L Del h0).sigPar z i = (D.hc (tauPl D z)).v ⟨i, hi⟩`. Unfold `NumDatum.sigPar`.

Rewrite using `[dif_pos hi]`. Rewrite using `[hs]`. Establish `hv : (D.hcW u (tauPl D z)).v = (D.hc (tauPl D z)).v` using `D.hcW_v u _`. Establish `h1` using `(D.hcW u (tauPl D z)).u_gt_v ⟨i, hi⟩`. Establish `h2` using `(D.hcW u (tauPl D z)).v_gt_u ⟨i, hi⟩`.

Rewrite `h1`, `h2` using `[hv]`. Conclude with `⟨h1, h2⟩`.
-/
theorem nf_inter_rec (hDel : D.s.Del = (Del : ℚ)) (u : D.what₂.Word) :
    ∀ z (i : ℕ) (h : i + 1 < (ofRecord D L Del h0).R.k),
      (ofRecord D L Del h0).sigPar z i < (ofRecord D L Del h0).uW (letterOf D L Del h0 u) z ⟨i, by omega⟩ ∧
        (ofRecord D L Del h0).uW (letterOf D L Del h0 u) z ⟨i + 1, h⟩ < (ofRecord D L Del h0).sigPar z i := by
  intro z i h
  rw [ofRecord_uW D L Del h0 hDel u z, ofRecord_uW D L Del h0 hDel u z]
  have hi : i < D.R.k - 1 := by have : i + 1 < D.R.k := h; omega
  have hs : (ofRecord D L Del h0).sigPar z i = (D.hc (tauPl D z)).v ⟨i, hi⟩ := by
    unfold NumDatum.sigPar
    rw [dif_pos hi]
  rw [hs]
  have hv : (D.hcW u (tauPl D z)).v = (D.hc (tauPl D z)).v := D.hcW_v u _
  have h1 := (D.hcW u (tauPl D z)).u_gt_v ⟨i, hi⟩
  have h2 := (D.hcW u (tauPl D z)).v_gt_u ⟨i, hi⟩
  rw [hv] at h1 h2
  exact ⟨h1, h2⟩

def swRec : ℝ := (1 + |L.Cc|) * L.Sc

def constantOneChoice : ℝ := 2 * (1 + |L.Cc|)

/- English proof (translation)
Unfold `NumDatum.Sc`. Rewrite using `[L.Sc_eq, hDel]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem Sc_rec (hDel : D.s.Del = (Del : ℚ)) : (ofRecord D L Del h0).Sc = L.Sc := by
  unfold NumDatum.Sc
  rw [L.Sc_eq, hDel]
  push_cast
  rfl

/- English proof (translation)
Unfold `constantOneChoice`. Use `abs_nonneg L.Cc` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nf_C1two_rec : 2 ≤ constantOneChoice L := by
  unfold constantOneChoice
  have := abs_nonneg L.Cc
  linarith

/- English proof (translation)
Rewrite using `[Sc_rec L Del h0 hDel]`. Unfold `swRec constantOneChoice`. Use polynomial arithmetic with `[L.Sc_pos]`.
-/
theorem nf_C1S_rec (hDel : D.s.Del = (Del : ℚ)) : 2 * swRec L ≤ constantOneChoice L * (ofRecord D L Del h0).Sc := by
  rw [Sc_rec L Del h0 hDel]
  unfold swRec constantOneChoice
  nlinarith [L.Sc_pos]

/- English proof (translation)
Introduce `z hz`. Establish `hk : 5 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`. Establish `hnt : ((D.eTau (tauPl D z) : D.R.Psi) : D.R.GG) ∉ D.host.topPlaces` using `fun h => hz ((tauPl_top_iff z).1 h)`. Use `set τ := tauPl D z with hτ`. Establish `hext` using `P5.uk_extreme τ (by omega) hnt`.

Establish `hv` using `(L.cloud_v τ ⟨D.R.k - 2, by omega⟩).1`. Establish `hv0` using `(L.cloud_v τ ⟨0, by omega⟩).2`. Establish `hg` using `(L.cloud_gap τ (by omega) hnt).2`. Prove the components needed by the constructor for the conclusion. Use `show 0 ≤ (D.hc τ).u ⟨D.R.k - 1, by omega⟩ + ((D.R.k : ℚ) - 1) / 2`.

Rewrite using `[hext]`. Establish `hv' : (0 : ℚ) ≤ (D.hc τ).v ⟨D.R.k - 2, by omega⟩` using `by exact_mod_cast hv`. Establish `hk' : (5 : ℚ) ≤ D.R.k` using `by exact_mod_cast hk`. Combine the linear equalities and inequalities to obtain the conclusion. Use `show ((((D.hc τ).u ⟨0, by omega⟩ - ((D.R.k : ℚ) - 1) / 2 : ℚ)) : ℝ) ≤ swRec L`.

Unfold `swRec`. Move the coercions through the operations in `at hg ⊢`. Establish `hk' : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast hk`. Establish `hS` using `L.Sc_pos`. Establish `hC : L.Cc * L.Sc ≤ |L.Cc| * L.Sc` using `mul_le_mul_of_nonneg_right (le_abs_self _) hS.le`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem nf_off_rec (P5 : ParameterChoice' D L) :
    ∀ z : RPl (ofRecord D L Del h0).R, ¬ (z.1 = false ∧ z.2 ∈ (ofRecord D L Del h0).TT) →
      0 ≤ ((ofRecord D L Del h0).hc z).u ⟨(ofRecord D L Del h0).R.k - 1, by have := (ofRecord D L Del h0).R.m_add_three_le_k; omega⟩ +
          (((ofRecord D L Del h0).R.k : ℚ) - 1) / 2 ∧
        ((((ofRecord D L Del h0).hc z).u ⟨0, by have := (ofRecord D L Del h0).R.m_add_three_le_k; omega⟩ -
          (((ofRecord D L Del h0).R.k : ℚ) - 1) / 2 : ℚ) : ℝ) ≤ swRec L := by
  intro z hz
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hnt : ((D.eTau (tauPl D z) : D.R.Psi) : D.R.GG) ∉ D.host.topPlaces :=
    fun h => hz ((tauPl_top_iff z).1 h)
  set τ := tauPl D z with hτ
  have hext := P5.uk_extreme τ (by omega) hnt
  have hv := (L.cloud_v τ ⟨D.R.k - 2, by omega⟩).1
  have hv0 := (L.cloud_v τ ⟨0, by omega⟩).2
  have hg := (L.cloud_gap τ (by omega) hnt).2
  constructor
  · show 0 ≤ (D.hc τ).u ⟨D.R.k - 1, by omega⟩ + ((D.R.k : ℚ) - 1) / 2
    rw [hext]
    have hv' : (0 : ℚ) ≤ (D.hc τ).v ⟨D.R.k - 2, by omega⟩ := by exact_mod_cast hv
    have hk' : (5 : ℚ) ≤ D.R.k := by exact_mod_cast hk
    linarith
  · show ((((D.hc τ).u ⟨0, by omega⟩ - ((D.R.k : ℚ) - 1) / 2 : ℚ)) : ℝ) ≤ swRec L
    unfold swRec
    push_cast at hg ⊢
    have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
    have hS := L.Sc_pos
    have hC : L.Cc * L.Sc ≤ |L.Cc| * L.Sc := mul_le_mul_of_nonneg_right (le_abs_self _) hS.le
    nlinarith

/- English proof (translation)
Introduce `t ht`. Establish `hk : 5 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`. Establish `hk0 : 0 < D.R.k` using `by omega`. Use `set τ := tauPl D (false, t) with hτ`. Establish `htop : (D.eTau τ : D.R.GG) = D.R.tau1 (⟨t, ht⟩ : D.host.TT)`.

Rewrite using `[hτ]`. Unfold `tauPl`. Rewrite using `[Equiv.apply_symm_apply]`. Both sides reduce to the same expression. Establish `hu` using `L.top_u τ ⟨t, ht⟩ hk0 htop`.

Establish `hv` using `(L.cloud_v τ ⟨D.R.k - 2, by omega⟩).1`. Establish `hv0` using `(L.cloud_v τ ⟨0, by omega⟩).2`. Establish `ha` using `(L.aT_win ⟨t, ht⟩).1`. Establish `hb` using `L.bT_ge ⟨t, ht⟩`. Establish `ha0 : 0 ≤ L.sc.a` using `le_of_lt (mul_pos (lt_trans zero_lt_one L.sc.one_lt_alt) (Real.exp_pos _))`.

Establish `hb0 : 0 ≤ L.sc.b'` using `div_nonneg ha0 (Real.exp_pos _).le`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e` using `ofRecord_aT D L Del h0 ⟨t, ht⟩`. Establish `: (0 : ℝ) ≤ (((ofRecord D L Del h0).aT t : ℚ) : ℝ)` using `by rw [e]; linarith`. Conclude with `this` after adjusting the coercions.

Establish `: (0 : ℝ) ≤ (((ofRecord D L Del h0).bT t : ℚ) : ℝ)`. Unfold `NumDatum.bT`. Use `push_cast`. Establish `hu2 : ((((ofRecord D L Del h0).hc (false, t)).u ⟨(ofRecord D L Del h0).R.k - 1, by show D.R.k - 1 < D.R.k; omega⟩ : ℚ) : ℝ) = -(L.bT ⟨t, ht⟩ : ℝ) - ((D.R.k : ℝ) - 1) / 2` using `hu.2`. Rewrite using `[hu2]`.

Use `show (0 : ℝ) ≤ -(-(L.bT ⟨t, ht⟩ : ℝ) - ((D.R.k : ℝ) - 1) / 2) - ((D.R.k : ℝ) - 1) / 2`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions. Establish `hs : (ofRecord D L Del h0).sigPar (false, t) ((ofRecord D L Del h0).R.k - 2) = (D.hc τ).v ⟨D.R.k - 2, by omega⟩`. Unfold `NumDatum.sigPar`.

Rewrite using `[dif_pos (show (ofRecord D L Del h0).R.k - 2 < (ofRecord D L Del h0).R.k - 1 by show D.R.k - 2 < D.R.k - 1; omega)]`. Rewrite using `[hs]`. Establish `hv' : (0 : ℚ) ≤ (D.hc τ).v ⟨D.R.k - 2, by omega⟩` using `by exact_mod_cast hv`. Establish `hk' : (5 : ℚ) ≤ D.R.k` using `by exact_mod_cast hk`. Use `show 0 ≤ (D.hc τ).v ⟨D.R.k - 2, by omega⟩ + ((D.R.k : ℚ) - 2) / 2`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs : (ofRecord D L Del h0).sigPar (false, t) 0 = (D.hc τ).v ⟨0, by omega⟩`. Unfold `NumDatum.sigPar`. Rewrite using `[dif_pos (show 0 < (ofRecord D L Del h0).R.k - 1 by show 0 < D.R.k - 1; omega)]`. Rewrite using `[hs]`.

Unfold `swRec`. Use `push_cast`. Establish `hk' : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast hk`. Establish `hS` using `L.Sc_pos`. Establish `: 0 ≤ |L.Cc| * L.Sc` using `mul_nonneg (abs_nonneg _) hS.le`.

Use `show (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) - ((D.R.k : ℝ) - 2) / 2 ≤ (1 + |L.Cc|) * L.Sc`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem nf_top_rec :
    ∀ t ∈ (ofRecord D L Del h0).TT, 0 ≤ (ofRecord D L Del h0).aT t ∧ 0 ≤ (ofRecord D L Del h0).bT t ∧
      0 ≤ (ofRecord D L Del h0).sigPar (false, t) ((ofRecord D L Del h0).R.k - 2) +
        (((ofRecord D L Del h0).R.k : ℚ) - 2) / 2 ∧
      ((((ofRecord D L Del h0).sigPar (false, t) 0 - (((ofRecord D L Del h0).R.k : ℚ) - 2) / 2 : ℚ)) : ℝ) ≤ swRec L := by
  intro t ht
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk0 : 0 < D.R.k := by omega
  set τ := tauPl D (false, t) with hτ
  have htop : (D.eTau τ : D.R.GG) = D.R.tau1 (⟨t, ht⟩ : D.host.TT) := by
    rw [hτ]
    unfold tauPl
    rw [Equiv.apply_symm_apply]
    rfl
  have hu := L.top_u τ ⟨t, ht⟩ hk0 htop
  have hv := (L.cloud_v τ ⟨D.R.k - 2, by omega⟩).1
  have hv0 := (L.cloud_v τ ⟨0, by omega⟩).2
  have ha := (L.aT_win ⟨t, ht⟩).1
  have hb := L.bT_ge ⟨t, ht⟩
  have ha0 : 0 ≤ L.sc.a := le_of_lt (mul_pos (lt_trans zero_lt_one L.sc.one_lt_alt) (Real.exp_pos _))
  have hb0 : 0 ≤ L.sc.b' := div_nonneg ha0 (Real.exp_pos _).le
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e := ofRecord_aT D L Del h0 ⟨t, ht⟩
    have : (0 : ℝ) ≤ (((ofRecord D L Del h0).aT t : ℚ) : ℝ) := by rw [e]; linarith
    exact_mod_cast this
  · have : (0 : ℝ) ≤ (((ofRecord D L Del h0).bT t : ℚ) : ℝ) := by
      unfold NumDatum.bT
      push_cast
      have hu2 : ((((ofRecord D L Del h0).hc (false, t)).u ⟨(ofRecord D L Del h0).R.k - 1, by show D.R.k - 1 < D.R.k; omega⟩ : ℚ) : ℝ) =
          -(L.bT ⟨t, ht⟩ : ℝ) - ((D.R.k : ℝ) - 1) / 2 := hu.2
      rw [hu2]
      show (0 : ℝ) ≤ -(-(L.bT ⟨t, ht⟩ : ℝ) - ((D.R.k : ℝ) - 1) / 2) - ((D.R.k : ℝ) - 1) / 2
      linarith
    exact_mod_cast this
  · have hs : (ofRecord D L Del h0).sigPar (false, t) ((ofRecord D L Del h0).R.k - 2) = (D.hc τ).v ⟨D.R.k - 2, by omega⟩ := by
      unfold NumDatum.sigPar
      rw [dif_pos (show (ofRecord D L Del h0).R.k - 2 < (ofRecord D L Del h0).R.k - 1 by
        show D.R.k - 2 < D.R.k - 1; omega)]
    rw [hs]
    have hv' : (0 : ℚ) ≤ (D.hc τ).v ⟨D.R.k - 2, by omega⟩ := by exact_mod_cast hv
    have hk' : (5 : ℚ) ≤ D.R.k := by exact_mod_cast hk
    show 0 ≤ (D.hc τ).v ⟨D.R.k - 2, by omega⟩ + ((D.R.k : ℚ) - 2) / 2
    linarith
  · have hs : (ofRecord D L Del h0).sigPar (false, t) 0 = (D.hc τ).v ⟨0, by omega⟩ := by
      unfold NumDatum.sigPar
      rw [dif_pos (show 0 < (ofRecord D L Del h0).R.k - 1 by show 0 < D.R.k - 1; omega)]
    rw [hs]
    unfold swRec
    push_cast
    have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
    have hS := L.Sc_pos
    have : 0 ≤ |L.Cc| * L.Sc := mul_nonneg (abs_nonneg _) hS.le
    show (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) - ((D.R.k : ℝ) - 2) / 2 ≤ (1 + |L.Cc|) * L.Sc
    nlinarith

section Blocks

variable (N : NumDatum)

/- English proof (translation)
Use `set q := (i - N.R.k) / (N.R.t + 1) with hqdef`. Use `set r := (i - N.R.k) % (N.R.t + 1) with hrdef`. Establish `hdm : (N.R.t + 1) * q + r = i - N.R.k` using `Nat.div_add_mod (i - N.R.k) (N.R.t + 1)`. Establish `hN : N.R.N (j - 1) = N.R.k + (j - 1) * (N.R.t + 1)` using `rfl`. Establish `hlt : i - N.R.k < (j - 1) * (N.R.t + 1)` using `by omega`.

Establish `hq : q < j - 1`. Rewrite using `[hqdef]`. Conclude with `(Nat.div_lt_iff_lt_mul (by omega)).2 hlt`. Use `⟨q, hq, ?_⟩` and prove the remaining obligations. Unfold `NumDatum.nu NumDatum.srcPar NumDatum.eQ`.

Rewrite using `[dif_neg (show ¬ i < N.R.k by omega), dif_pos (show q < N.R.m by omega), dif_pos (show 1 ≤ j ∧ j ≤ N.R.m from ⟨hj1, hjm⟩)]`. Establish `hr : r < N.R.t + 1` using `Nat.mod_lt _ (by omega)`. Establish `hi' : (i : ℚ) = N.R.k + q * ((N.R.t : ℚ) + 1) + r`. Establish `: i = N.R.k + (N.R.t + 1) * q + r` using `by omega`. Rewrite using `[this]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hNj : (N.R.N j : ℚ) = N.R.k + j * ((N.R.t : ℚ) + 1)` using `by show ((N.R.k + j * (N.R.t + 1) : ℕ) : ℚ) = _`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hNj1 : (N.R.N (j - 1) : ℚ) = N.R.k + ((j : ℚ) - 1) * ((N.R.t : ℚ) + 1)`. Rewrite using `[hN]`. Move the coercions through the operations in `[Nat.cast_sub hj1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hjq : (((j - 1 - q : ℕ)) : ℚ) = (j : ℚ) - 1 - q`.

Rewrite using `[Nat.cast_sub (by omega), Nat.cast_sub hj1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hrr : (((r + 1 : ℕ)) : ℚ) = (r : ℚ) + 1` using `by push_cast; ring`. Rewrite using `[hjq, hNj, hNj1, hi']`.

Rewrite `*` using `[← hrdef]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nu_blk_eq (δ : Code N) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ N.R.m) (z : RPl N.R) (i : ℕ) (hik : N.R.k ≤ i)
    (hi : i < N.R.N (j - 1)) :
    ∃ (q : ℕ) (hq : q < j - 1), N.nu δ j z i = (N.hc z).e ⟨j - 1, by omega⟩ - (N.hc z).e ⟨q, by omega⟩ -
      (((j - 1 - q : ℕ) : ℚ)) * ((N.R.t : ℚ) + 1) := by
  set q := (i - N.R.k) / (N.R.t + 1) with hqdef
  set r := (i - N.R.k) % (N.R.t + 1) with hrdef
  have hdm : (N.R.t + 1) * q + r = i - N.R.k := Nat.div_add_mod (i - N.R.k) (N.R.t + 1)
  have hN : N.R.N (j - 1) = N.R.k + (j - 1) * (N.R.t + 1) := rfl
  have hlt : i - N.R.k < (j - 1) * (N.R.t + 1) := by omega
  have hq : q < j - 1 := by
    rw [hqdef]
    exact (Nat.div_lt_iff_lt_mul (by omega)).2 hlt
  refine ⟨q, hq, ?_⟩
  unfold NumDatum.nu NumDatum.srcPar NumDatum.eQ
  rw [dif_neg (show ¬ i < N.R.k by omega), dif_pos (show q < N.R.m by omega),
    dif_pos (show 1 ≤ j ∧ j ≤ N.R.m from ⟨hj1, hjm⟩)]
  have hr : r < N.R.t + 1 := Nat.mod_lt _ (by omega)
  have hi' : (i : ℚ) = N.R.k + q * ((N.R.t : ℚ) + 1) + r := by
    have : i = N.R.k + (N.R.t + 1) * q + r := by omega
    rw [this]
    push_cast
    ring
  have hNj : (N.R.N j : ℚ) = N.R.k + j * ((N.R.t : ℚ) + 1) := by
    show ((N.R.k + j * (N.R.t + 1) : ℕ) : ℚ) = _
    push_cast
    ring
  have hNj1 : (N.R.N (j - 1) : ℚ) = N.R.k + ((j : ℚ) - 1) * ((N.R.t : ℚ) + 1) := by
    rw [hN]
    push_cast [Nat.cast_sub hj1]
    ring
  have hjq : (((j - 1 - q : ℕ)) : ℚ) = (j : ℚ) - 1 - q := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub hj1]
    push_cast
    ring
  have hrr : (((r + 1 : ℕ)) : ℚ) = (r : ℚ) + 1 := by push_cast; ring
  rw [hjq, hNj, hNj1, hi']
  rw [← hrdef] at *
  push_cast
  ring

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro a hb`. Simplify using the standard rewrite rules. Consider the case `succ d ih`.

Introduce `a hb`. Establish `h1` using `ih a (by omega)`. Establish `h2` using `h.gap_be ⟨a + d + 1, hb⟩`. Establish `h3` using `h.gap_eb ⟨a + d, by omega⟩ (by show a + d + 1 < N.R.m; omega)`. Establish `e1 : (⟨a + (d + 1), hb⟩ : Fin N.R.m) = ⟨a + d + 1, hb⟩` using `Fin.ext (by simp; omega)`.

Rewrite using `[e1]`. Use `push_cast`. Establish `e2 : (⟨(⟨a + d, by omega⟩ : Fin N.R.m).1 + 1, (show a + d + 1 < N.R.m by omega)⟩ : Fin N.R.m) = ⟨a + d + 1, hb⟩` using `Fin.ext rfl`. Rewrite `h3` using `[e2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem e_gap (h : HCParam N.R) : ∀ (d a : ℕ) (hb : a + d < N.R.m),
    ((d : ℚ)) * ((N.R.t : ℚ) + 3) ≤ h.e ⟨a + d, hb⟩ - h.e ⟨a, by omega⟩ := by
  intro d
  induction d with
  | zero => intro a hb; simp
  | succ d ih =>
    intro a hb
    have h1 := ih a (by omega)
    have h2 := h.gap_be ⟨a + d + 1, hb⟩
    have h3 := h.gap_eb ⟨a + d, by omega⟩ (by show a + d + 1 < N.R.m; omega)
    have e1 : (⟨a + (d + 1), hb⟩ : Fin N.R.m) = ⟨a + d + 1, hb⟩ := Fin.ext (by simp; omega)
    rw [e1]
    push_cast
    have e2 : (⟨(⟨a + d, by omega⟩ : Fin N.R.m).1 + 1, (show a + d + 1 < N.R.m by omega)⟩ : Fin N.R.m) = ⟨a + d + 1, hb⟩ :=
      Fin.ext rfl
    rw [e2] at h3
    linarith

end Blocks

/- English proof (translation)
Introduce `j hj1 hjm z`. Establish `hbound : ∀ i ∈ Finset.Ico N.R.k (N.R.N (j - 1)), (((N.nu δ j z i : ℚ)) : ℝ) ≤ η`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Ico]`. Take `⟨q, hq, e⟩` from `nu_blk_eq N δ j hj1 hjm z i hi.1 hi.2`.

Rewrite using `[e]`. Establish `hb` using `hbe z ⟨q, by omega⟩ ⟨j - 1, by omega⟩`. Establish `hgap` using `(N.hc z).gap_be ⟨q, by omega⟩`. Establish `hgap' : ((((N.hc z).e ⟨q, by omega⟩ - (N.hc z).b ⟨q, by omega⟩ : ℚ)) : ℝ) ≥ ((N.R.t : ℝ) + 3) / 2`. Establish `h2 : ((((N.R.t : ℚ) + 3) / 2 : ℚ) : ℝ) ≤ (((N.hc z).e ⟨q, by omega⟩ - (N.hc z).b ⟨q, by omega⟩ : ℚ) : ℝ)`.

Conclude with `hgap` after adjusting the coercions. Move the coercions through the operations in `at h2 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht' : (0 : ℝ) ≤ (((j - 1 - q : ℕ)) : ℝ) * ((N.R.t : ℝ) + 1)` using `by positivity`. Establish `ht0 : (0 : ℝ) ≤ N.R.t` using `Nat.cast_nonneg _`.

Move the coercions through the operations in `at hb hgap' ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Use `(Finset.sum_le_sum hbound).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]`. Establish `hN : N.R.N (j - 1) - N.R.k = (j - 1) * (N.R.t + 1)` using `by show N.R.k + (j - 1) * (N.R.t + 1) - N.R.k = _`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hN]`. Move the coercions through the operations in `[Nat.cast_sub hj1]`. Establish `hjm' : (j : ℝ) ≤ (N.R.m : ℝ)` using `by exact_mod_cast hjm`. Establish `ht0 : (0 : ℝ) ≤ N.R.t` using `Nat.cast_nonneg _`.

Establish `: ((j : ℝ) - 1) * ((N.R.t : ℝ) + 1) ≤ (N.R.m : ℝ) * ((N.R.t : ℝ) + 1)` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem blk_of (N : NumDatum) (δ : Code N) (η : ℝ) (hη : 0 ≤ η)
    (hbe : ∀ z (a c : Fin N.R.m), ((((N.hc z).e c - (N.hc z).b a : ℚ)) : ℝ) ≤ η) :
    ∀ j, 1 ≤ j → j ≤ N.R.m → ∀ z,
      (∑ i ∈ Finset.Ico N.R.k (N.R.N (j - 1)), ((N.nu δ j z i : ℚ) : ℝ)) ≤ (N.R.m : ℝ) * ((N.R.t : ℝ) + 1) * η := by
  intro j hj1 hjm z
  have hbound : ∀ i ∈ Finset.Ico N.R.k (N.R.N (j - 1)), (((N.nu δ j z i : ℚ)) : ℝ) ≤ η := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    obtain ⟨q, hq, e⟩ := nu_blk_eq N δ j hj1 hjm z i hi.1 hi.2
    rw [e]
    have hb := hbe z ⟨q, by omega⟩ ⟨j - 1, by omega⟩
    have hgap := (N.hc z).gap_be ⟨q, by omega⟩
    have hgap' : ((((N.hc z).e ⟨q, by omega⟩ - (N.hc z).b ⟨q, by omega⟩ : ℚ)) : ℝ) ≥ ((N.R.t : ℝ) + 3) / 2 := by
      have h2 : ((((N.R.t : ℚ) + 3) / 2 : ℚ) : ℝ) ≤ (((N.hc z).e ⟨q, by omega⟩ - (N.hc z).b ⟨q, by omega⟩ : ℚ) : ℝ) := by
        exact_mod_cast hgap
      push_cast at h2 ⊢
      linarith
    have ht' : (0 : ℝ) ≤ (((j - 1 - q : ℕ)) : ℝ) * ((N.R.t : ℝ) + 1) := by positivity
    have ht0 : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _
    push_cast at hb hgap' ⊢
    linarith
  refine (Finset.sum_le_sum hbound).trans ?_
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hN : N.R.N (j - 1) - N.R.k = (j - 1) * (N.R.t + 1) := by
    show N.R.k + (j - 1) * (N.R.t + 1) - N.R.k = _
    omega
  rw [hN]
  push_cast [Nat.cast_sub hj1]
  have hjm' : (j : ℝ) ≤ (N.R.m : ℝ) := by exact_mod_cast hjm
  have ht0 : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _
  have : ((j : ℝ) - 1) * ((N.R.t : ℝ) + 1) ≤ (N.R.m : ℝ) * ((N.R.t : ℝ) + 1) := by nlinarith
  nlinarith

/- English proof (translation)
Establish `heta : (ofRecord D L Del h0).eta = L.etaSz` using `by rw [hh0]; rfl`. Use `blk_of (ofRecord D L Del h0) (letterOf D L Del h0 u) (ofRecord D L Del h0).eta (by rw [heta]; exact L.etaSz_pos.le) ?_` and prove the remaining obligations. Introduce `z a c`. Rewrite using `[heta]`. Use `(abs_le.1 (L.be_close (tauPl D z) a c)).1` as an intermediate fact.

Use `show ((((D.hc (tauPl D z)).e c - (D.hc (tauPl D z)).b a : ℚ)) : ℝ) ≤ L.etaSz`. Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nf_blk_rec (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)) (u : D.what₂.Word) :
    ∀ j, 1 ≤ j → j ≤ (ofRecord D L Del h0).R.m → ∀ z,
      (∑ i ∈ Finset.Ico (ofRecord D L Del h0).R.k ((ofRecord D L Del h0).R.N (j - 1)),
          (((ofRecord D L Del h0).nu (letterOf D L Del h0 u) j z i : ℚ) : ℝ)) ≤
        ((ofRecord D L Del h0).R.m : ℝ) * (((ofRecord D L Del h0).R.t : ℝ) + 1) * (ofRecord D L Del h0).eta := by
  have heta : (ofRecord D L Del h0).eta = L.etaSz := by rw [hh0]; rfl
  refine blk_of (ofRecord D L Del h0) (letterOf D L Del h0 u) (ofRecord D L Del h0).eta
    (by rw [heta]; exact L.etaSz_pos.le) ?_
  intro z a c
  rw [heta]
  have := (abs_le.1 (L.be_close (tauPl D z) a c)).1
  show ((((D.hc (tauPl D z)).e c - (D.hc (tauPl D z)).b a : ℚ)) : ℝ) ≤ L.etaSz
  push_cast at this ⊢
  linarith

section Sizes

/- English proof (translation)
Distinguish the cases in `h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces`. Conclude with `Or.inl h1`. Distinguish the cases in `h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces`. Conclude with `Or.inr (Or.inl ⟨h1, h2⟩)`. Conclude with `Or.inr (Or.inr ⟨(D.eTau τ).2, h1, h2⟩)`.
-/
theorem place_cases (τ : D.what₂.Tau) :
    (D.eTau τ : D.R.GG) ∈ D.host.topPlaces ∨
      ((D.eTau τ : D.R.GG) ∉ D.host.topPlaces ∧ (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces) ∨
      D.host.IsThin (D.eTau τ : D.R.GG) := by
  by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · exact Or.inl h1
  by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  exact Or.inr (Or.inr ⟨(D.eTau τ).2, h1, h2⟩)

/- English proof (translation)
The claim follows from `le_of_lt (mul_pos (lt_trans zero_lt_one L.sc.one_lt_alt) (Real.exp_pos _))`.
-/
theorem a_nonneg_rec : 0 ≤ L.sc.a := le_of_lt (mul_pos (lt_trans zero_lt_one L.sc.one_lt_alt) (Real.exp_pos _))

/- English proof (translation)
The claim follows from `div_nonneg (a_nonneg_rec L) (Real.exp_pos _).le`.
-/
theorem b'_nonneg_rec : 0 ≤ L.sc.b' := div_nonneg (a_nonneg_rec L) (Real.exp_pos _).le

/- English proof (translation)
Unfold `Host.topPlaces at h`. Take `⟨t, ht, e⟩` from `Finset.mem_image.1 h`. Conclude with `⟨⟨t, ht⟩, e.symm⟩`.
-/
theorem top_of_mem (τ : D.what₂.Tau) (h : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces) :
    ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t := by
  unfold Host.topPlaces at h
  obtain ⟨t, ht, e⟩ := Finset.mem_image.1 h
  exact ⟨⟨t, ht⟩, e.symm⟩

/- English proof (translation)
Introduce `j hj1 hjm τ`. Break down `place_cases τ with h | h | h` into its components or cases. Take `⟨t, ht⟩` from `top_of_mem τ h`. Establish `hw` using `(L.win_top j hj1 hjm τ t ht).1`. Establish `hbt` using `L.bT_ge t`.

Establish `: 0 ≤ L.sc.b' / L.sc.x` using `div_nonneg (b'_nonneg_rec L) (by linarith [L.sc.one_lt_alt])`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear relations using `[(L.win_thick j hj1 hjm τ h.2).1]`. Combine the linear relations using `[(L.win_thin j hj1 hjm τ h).1]`.
-/
theorem wj_ge_rec (X : ℝ) (hb : X ≤ L.sc.b) (hw : X ≤ L.sc.w'' D.R.n) (hb' : X ≤ L.sc.b') :
    ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, X ≤ wj D j τ := by
  intro j hj1 hjm τ
  rcases place_cases τ with h | h | h
  · obtain ⟨t, ht⟩ := top_of_mem τ h
    have hw := (L.win_top j hj1 hjm τ t ht).1
    have hbt := L.bT_ge t
    have : 0 ≤ L.sc.b' / L.sc.x := div_nonneg (b'_nonneg_rec L) (by linarith [L.sc.one_lt_alt])
    linarith
  · linarith [(L.win_thick j hj1 hjm τ h.2).1]
  · linarith [(L.win_thin j hj1 hjm τ h).1]

/- English proof (translation)
Introduce `j hj1 hjm z`. Rewrite using `[ofRecord_w D L Del h0 hj1 z]`. Establish `h` using `wj_ge_rec L _ hb hw hb' j hj1 hjm (tauPl D z)`. Use `le_trans ?_ h` and prove the remaining obligations. Use `show _ ≤ ((D.R.k + D.R.m * (D.R.t + 1) : ℕ) : ℝ)`.

Use `push_cast`. Establish `hjm' : (j : ℝ) ≤ D.R.m` using `by exact_mod_cast hjm`. Establish `hj1' : (1 : ℝ) ≤ j` using `by exact_mod_cast hj1`. Establish `ht : (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`. Establish `hk : (0 : ℝ) ≤ D.R.k` using `Nat.cast_nonneg _`.

Use `show ((D.R.k : ℝ) + (2 * (j : ℝ) - 1) * ((D.R.t : ℝ) + 1)) / 2 ≤ _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem nf_sw_rec (hb : ((ofRecord D L Del h0).Nm : ℝ) ≤ L.sc.b) (hw : ((ofRecord D L Del h0).Nm : ℝ) ≤ L.sc.w'' D.R.n)
    (hb' : ((ofRecord D L Del h0).Nm : ℝ) ≤ L.sc.b') :
    ∀ j, 1 ≤ j → j ≤ (ofRecord D L Del h0).R.m → ∀ z,
      (((ofRecord D L Del h0).R.k : ℝ) + (2 * (j : ℝ) - 1) * (((ofRecord D L Del h0).R.t : ℝ) + 1)) / 2 ≤
        (ofRecord D L Del h0).w j z := by
  intro j hj1 hjm z
  rw [ofRecord_w D L Del h0 hj1 z]
  have h := wj_ge_rec L _ hb hw hb' j hj1 hjm (tauPl D z)
  refine le_trans ?_ h
  show _ ≤ ((D.R.k + D.R.m * (D.R.t + 1) : ℕ) : ℝ)
  push_cast
  have hjm' : (j : ℝ) ≤ D.R.m := by exact_mod_cast hjm
  have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  show ((D.R.k : ℝ) + (2 * (j : ℝ) - 1) * ((D.R.t : ℝ) + 1)) / 2 ≤ _
  nlinarith

/- English proof (translation)
Introduce `j hj1 hjm z i hi`. Distinguish the cases in `hik : (ofRecord D L Del h0).R.k ≤ i`. Take `⟨q, hq, e⟩` from `nu_blk_eq (ofRecord D L Del h0) (letterOf D L Del h0 u) j hj1 hjm z i hik hi`. Rewrite using `[e]`. Establish `hg` using `e_gap (ofRecord D L Del h0) ((ofRecord D L Del h0).hc z) (j - 1 - q) q (by omega)`.

Establish `e1 : (⟨q + (j - 1 - q), by omega⟩ : Fin (ofRecord D L Del h0).R.m) = ⟨j - 1, by omega⟩` using `Fin.ext (by simp; omega)`. Rewrite `hg` using `[e1]`. Establish `: (0 : ℚ) ≤ (((j - 1 - q : ℕ)) : ℚ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hik` using `[not_le]`.

Establish `hik2 : i < D.R.k` using `hik`. Establish `hjm2 : j ≤ D.R.m` using `hjm`. Establish `hk : 5 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`. Use `set τ := tauPl D z with hτ`. Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`.

Establish `hb'0` using `b'_nonneg_rec L`. Establish `hbx : L.sc.b' / L.sc.x ≤ L.sc.b'` using `div_le_self hb'0 hx1.le`. Establish `hbx0 : 0 ≤ L.sc.b' / L.sc.x` using `div_nonneg hb'0 (by linarith)`. Establish `hkR : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast hk`. Establish `hnu : (((ofRecord D L Del h0).nu (letterOf D L Del h0 u) j z i : ℚ) : ℝ) = (((D.hcW u τ).u ⟨i, hik⟩ : ℚ) : ℝ) + wj D j τ - (((D.R.N (j - 1) : ℝ) + D.R.N j - 1 - 2 * (i : ℝ)) / 2)`.

Establish `hw'` using `ofRecord_w D L Del h0 hj1 z`. Unfold `NumDatum.nu NumDatum.srcPar`. Rewrite using `[dif_pos hik, ofRecord_uW D L Del h0 hDel u z]`. Unfold `NumDatum.w at hw'`. Use `push_cast`.

Rewrite using `[hw']`. Both sides reduce to the same expression. Establish `hNs : ((D.R.N (j - 1) : ℝ) + D.R.N j - 1 - 2 * (i : ℝ)) / 2 ≤ ((ofRecord D L Del h0).Nm : ℝ) - 1 / 2`. Establish `h1 : D.R.N (j - 1) ≤ D.R.N D.R.m` using `Nat.add_le_add_left (Nat.mul_le_mul_right (D.R.t + 1) (show j - 1 ≤ D.R.m by omega)) D.R.k`. Establish `h2 : D.R.N j ≤ D.R.N D.R.m` using `Nat.add_le_add_left (Nat.mul_le_mul_right (D.R.t + 1) hjm2) D.R.k`.

Establish `h1' : (D.R.N (j - 1) : ℝ) ≤ D.R.N D.R.m` using `by exact_mod_cast h1`. Establish `h2' : (D.R.N j : ℝ) ≤ D.R.N D.R.m` using `by exact_mod_cast h2`. Establish `hi0 : (0 : ℝ) ≤ i` using `Nat.cast_nonneg _`. Use `show _ ≤ (D.R.N D.R.m : ℝ) - 1 / 2`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `key : ((ofRecord D L Del h0).Nm : ℝ) ≤ (((D.hcW u τ).u ⟨i, hik⟩ : ℚ) : ℝ) + wj D j τ`. Establish `hu_int : i < D.R.k - 1 → (0 : ℝ) ≤ (((D.hcW u τ).u ⟨i, hik⟩ : ℚ) : ℝ)`. Introduce `hi1`. Distinguish the cases in `hi0 : i = 0`. Substitute `hi0` using the available equality.

Establish `e` using `D.hcW_first u τ (by omega)`. Establish `h1` using `(D.hc τ).u_gt_v ⟨0, by omega⟩`. Establish `h2` using `(L.cloud_v τ ⟨0, by omega⟩).1`. Rewrite using `[e]`. Establish `: (0 : ℚ) ≤ (D.hc τ).v ⟨0, by omega⟩` using `by exact_mod_cast h2`.

Establish `: (0 : ℚ) ≤ (D.hc τ).u ⟨0, by omega⟩` using `le_of_lt (lt_of_le_of_lt this h1)`. Conclude with `this` after adjusting the coercions. Conclude with `(L.cloud_u u τ ⟨i, hik⟩ (by show 1 ≤ i; omega) (by show i + 1 < D.R.k; omega)).1`. Break down `place_cases τ with htop | hthick` into its components or cases. Take `⟨t, ht⟩` from `top_of_mem τ htop`.

Establish `hwt` using `(L.win_top j hj1 hjm τ t ht).1`. Establish `hbt` using `L.bT_ge t`. Distinguish the cases in `hil : i = D.R.k - 1`. Substitute `hil` using the available equality. Establish `e` using `D.hcW_last u τ (by omega)`.

Establish `hu` using `(L.top_u τ t (by omega) ht).2`. Establish `e2 : (⟨D.R.k - 1, hik⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩` using `rfl`. Rewrite using `[e2, e, hu]`. Use `show (D.R.N D.R.m : ℝ) ≤ _`. Establish `: ((ofRecord D L Del h0).Nm : ℝ) = D.R.N D.R.m` using `rfl`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h0u` using `hu_int (by omega)`. Establish `: ((ofRecord D L Del h0).Nm : ℝ) = D.R.N D.R.m` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hoff : (D.eTau τ : D.R.GG) ∉ D.host.topPlaces ∧ wj D j τ ≥ ((ofRecord D L Del h0).Nm : ℝ) + 1`.

Break down `hthick with hth | hth` into its components or cases. Conclude with `⟨hth.1, by linarith [(L.win_thick j hj1 hjm τ hth.2).1]⟩`. Conclude with `⟨hth.2.1, by linarith [(L.win_thin j hj1 hjm τ hth).1]⟩`. Distinguish the cases in `hil : i = D.R.k - 1`. Substitute `hil` using the available equality.

Establish `e` using `D.hcW_last u τ (by omega)`. Establish `hext` using `P5.uk_extreme τ (by omega) hoff.1`. Establish `hv` using `(L.cloud_v τ ⟨D.R.k - 2, by omega⟩).1`. Establish `e2 : (⟨D.R.k - 1, hik⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩` using `rfl`. Rewrite using `[e2, e, hext]`.

Use `push_cast`. Combine the linear relations using `[hoff.2]`. Establish `h0u` using `hu_int (by omega)`. Combine the linear relations using `[hoff.2]`. Use `key` as an intermediate fact.

Establish `hfin : (0 : ℝ) ≤ (((ofRecord D L Del h0).nu (letterOf D L Del h0 u) j z i : ℚ) : ℝ)`. Rewrite using `[hnu]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hfin` after adjusting the coercions.
-/
theorem nu_nonneg_from_bounds (hDel : D.s.Del = (Del : ℚ)) (P5 : ParameterChoice' D L) (u : D.what₂.Word)
    (hb : ((ofRecord D L Del h0).Nm : ℝ) + 1 ≤ L.sc.b) (hw : ((ofRecord D L Del h0).Nm : ℝ) + 1 ≤ L.sc.w'' D.R.n)
    (hb' : ((ofRecord D L Del h0).Nm : ℝ) + D.R.k ≤ L.sc.b' / L.sc.x) :
    ∀ j, 1 ≤ j → j ≤ (ofRecord D L Del h0).R.m → ∀ z, ∀ i < (ofRecord D L Del h0).R.N (j - 1),
      0 ≤ (ofRecord D L Del h0).nu (letterOf D L Del h0 u) j z i := by
  intro j hj1 hjm z i hi
  by_cases hik : (ofRecord D L Del h0).R.k ≤ i
  · obtain ⟨q, hq, e⟩ := nu_blk_eq (ofRecord D L Del h0) (letterOf D L Del h0 u) j hj1 hjm z i hik hi
    rw [e]
    have hg := e_gap (ofRecord D L Del h0) ((ofRecord D L Del h0).hc z) (j - 1 - q) q (by omega)
    have e1 : (⟨q + (j - 1 - q), by omega⟩ : Fin (ofRecord D L Del h0).R.m) = ⟨j - 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e1] at hg
    have : (0 : ℚ) ≤ (((j - 1 - q : ℕ)) : ℚ) := Nat.cast_nonneg _
    linarith
  · rw [not_le] at hik
    have hik2 : i < D.R.k := hik
    have hjm2 : j ≤ D.R.m := hjm
    have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
    set τ := tauPl D z with hτ
    have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
    have hb'0 := b'_nonneg_rec L
    have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0 hx1.le
    have hbx0 : 0 ≤ L.sc.b' / L.sc.x := div_nonneg hb'0 (by linarith)
    have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk

    have hnu : (((ofRecord D L Del h0).nu (letterOf D L Del h0 u) j z i : ℚ) : ℝ) =
        (((D.hcW u τ).u ⟨i, hik⟩ : ℚ) : ℝ) + wj D j τ -
          (((D.R.N (j - 1) : ℝ) + D.R.N j - 1 - 2 * (i : ℝ)) / 2) := by
      have hw' := ofRecord_w D L Del h0 hj1 z
      unfold NumDatum.nu NumDatum.srcPar
      rw [dif_pos hik, ofRecord_uW D L Del h0 hDel u z]
      unfold NumDatum.w at hw'
      push_cast
      rw [hw']
      rfl

    have hNs : ((D.R.N (j - 1) : ℝ) + D.R.N j - 1 - 2 * (i : ℝ)) / 2 ≤ ((ofRecord D L Del h0).Nm : ℝ) - 1 / 2 := by
      have h1 : D.R.N (j - 1) ≤ D.R.N D.R.m :=
        Nat.add_le_add_left (Nat.mul_le_mul_right (D.R.t + 1) (show j - 1 ≤ D.R.m by omega)) D.R.k
      have h2 : D.R.N j ≤ D.R.N D.R.m := Nat.add_le_add_left (Nat.mul_le_mul_right (D.R.t + 1) hjm2) D.R.k
      have h1' : (D.R.N (j - 1) : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast h1
      have h2' : (D.R.N j : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast h2
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
      show _ ≤ (D.R.N D.R.m : ℝ) - 1 / 2
      linarith
    have key : ((ofRecord D L Del h0).Nm : ℝ) ≤ (((D.hcW u τ).u ⟨i, hik⟩ : ℚ) : ℝ) + wj D j τ := by
      have hu_int : i < D.R.k - 1 → (0 : ℝ) ≤ (((D.hcW u τ).u ⟨i, hik⟩ : ℚ) : ℝ) := by
        intro hi1
        by_cases hi0 : i = 0
        · subst hi0
          have e := D.hcW_first u τ (by omega)
          have h1 := (D.hc τ).u_gt_v ⟨0, by omega⟩
          have h2 := (L.cloud_v τ ⟨0, by omega⟩).1
          rw [e]
          have : (0 : ℚ) ≤ (D.hc τ).v ⟨0, by omega⟩ := by exact_mod_cast h2
          have : (0 : ℚ) ≤ (D.hc τ).u ⟨0, by omega⟩ := le_of_lt (lt_of_le_of_lt this h1)
          exact_mod_cast this
        · exact (L.cloud_u u τ ⟨i, hik⟩ (by show 1 ≤ i; omega) (by show i + 1 < D.R.k; omega)).1
      rcases place_cases τ with htop | hthick
      · obtain ⟨t, ht⟩ := top_of_mem τ htop
        have hwt := (L.win_top j hj1 hjm τ t ht).1
        have hbt := L.bT_ge t
        by_cases hil : i = D.R.k - 1
        · subst hil
          have e := D.hcW_last u τ (by omega)
          have hu := (L.top_u τ t (by omega) ht).2
          have e2 : (⟨D.R.k - 1, hik⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := rfl
          rw [e2, e, hu]
          show (D.R.N D.R.m : ℝ) ≤ _
          have : ((ofRecord D L Del h0).Nm : ℝ) = D.R.N D.R.m := rfl
          linarith
        · have h0u := hu_int (by omega)
          have : ((ofRecord D L Del h0).Nm : ℝ) = D.R.N D.R.m := rfl
          linarith
      · have hoff : (D.eTau τ : D.R.GG) ∉ D.host.topPlaces ∧ wj D j τ ≥ ((ofRecord D L Del h0).Nm : ℝ) + 1 := by
          rcases hthick with hth | hth
          · exact ⟨hth.1, by linarith [(L.win_thick j hj1 hjm τ hth.2).1]⟩
          · exact ⟨hth.2.1, by linarith [(L.win_thin j hj1 hjm τ hth).1]⟩
        by_cases hil : i = D.R.k - 1
        · subst hil
          have e := D.hcW_last u τ (by omega)
          have hext := P5.uk_extreme τ (by omega) hoff.1
          have hv := (L.cloud_v τ ⟨D.R.k - 2, by omega⟩).1
          have e2 : (⟨D.R.k - 1, hik⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := rfl
          rw [e2, e, hext]
          push_cast
          linarith [hoff.2]
        · have h0u := hu_int (by omega)
          linarith [hoff.2]
    have := key
    have hfin : (0 : ℝ) ≤ (((ofRecord D L Del h0).nu (letterOf D L Del h0 u) j z i : ℚ) : ℝ) := by
      rw [hnu]
      linarith
    exact_mod_cast hfin

end Sizes

section Top

/- English proof (translation)
Establish `h : (4 * N.R.ord : ℝ) ≤ N.rd ^ 2` using `N.H.der.rd_sq_ge`. Establish `ho : (1 : ℝ) ≤ N.R.ord` using `by exact_mod_cast N.R.ord_pos`. Establish `h0 : 0 ≤ N.rd` using `Real.rpow_nonneg (abs_nonneg _) _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem two_le_rd (N : NumDatum) : 2 ≤ N.rd := by
  have h : (4 * N.R.ord : ℝ) ≤ N.rd ^ 2 := N.H.der.rd_sq_ge
  have ho : (1 : ℝ) ≤ N.R.ord := by exact_mod_cast N.R.ord_pos
  have h0 : 0 ≤ N.rd := Real.rpow_nonneg (abs_nonneg _) _
  nlinarith

/- English proof (translation)
Establish `hk : (1 : ℝ) ≤ D.R.k`. Use `D.R.m_add_three_le_k` as an intermediate fact. Conclude with `(show 1 ≤ D.R.k by omega)` after adjusting the coercions. Establish `hS` using `L.Sc_pos`. Establish `h1 : L.Sc ≤ (D.R.k : ℝ) * L.Sc` using `by nlinarith`.

Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hb0 : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hn : (1 : ℝ) ≤ D.R.n`. Establish `: 1 ≤ D.R.n` using `D.R.ord_pos`. Conclude with `this` after adjusting the coercions.

Establish `hX : 1 ≤ L.sc.X'` using `Real.one_le_exp (Real.rpow_nonneg (by linarith) _)`. Establish `hw : L.sc.w'' D.R.n ≤ L.sc.b`. Unfold `Scale.w'' Scale.b' Scale.a`. Establish `hxn : 0 < L.sc.x * D.R.n` using `by positivity`. Rewrite using `[div_div, div_le_iff₀ (by positivity)]`.

Establish `: L.sc.x * L.sc.b ≤ L.sc.x * L.sc.b * (L.sc.X' * D.R.n)`. Establish `h1 : 1 ≤ L.sc.X' * D.R.n` using `by nlinarith`. Conclude with `le_mul_of_one_le_right (by positivity) h1`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear relations using `[P5.kS_le]`.
-/
theorem Sc_le_b (P5 : ParameterChoice' D L) : L.Sc ≤ L.sc.b := by
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (show 1 ≤ D.R.k by omega)
  have hS := L.Sc_pos
  have h1 : L.Sc ≤ (D.R.k : ℝ) * L.Sc := by nlinarith
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hX : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hw : L.sc.w'' D.R.n ≤ L.sc.b := by
    unfold Scale.w'' Scale.b' Scale.a
    have hxn : 0 < L.sc.x * D.R.n := by positivity
    rw [div_div, div_le_iff₀ (by positivity)]
    have : L.sc.x * L.sc.b ≤ L.sc.x * L.sc.b * (L.sc.X' * D.R.n) := by
      have h1 : 1 ≤ L.sc.X' * D.R.n := by nlinarith
      exact le_mul_of_one_le_right (by positivity) h1
    nlinarith
  linarith [P5.kS_le]

/- English proof (translation)
Introduce `j hj1 hjm z`. Establish `h1` using `hw2b j hj1 hjm z`. Establish `hS` using `Sc_le_b L P5`. Establish `hS0` using `L.Sc_pos`. Establish `hrd` using `two_le_rd (ofRecord D L Del h0)`.

Establish `hb0 : 0 < L.sc.b` using `Real.exp_pos _`. Establish `ha : (ofRecord D L Del h0).sc.a = L.sc.x * L.sc.b` using `rfl`. Establish `hbb : (ofRecord D L Del h0).sc.b = L.sc.b` using `rfl`. Rewrite using `[ha]`. Rewrite `h1` using `[hbb]`.

Unfold `swRec`. Establish `hc : (1 + |L.Cc|) * L.Sc ≤ (1 + |L.Cc|) * L.sc.b` using `mul_le_mul_of_nonneg_left hS (by positivity)`. Establish `hxb : (3 + |L.Cc|) * L.sc.b ≤ L.sc.x * L.sc.b` using `mul_le_mul_of_nonneg_right hx hb0.le`. Establish `hxb0 : 0 ≤ L.sc.x * L.sc.b` using `by nlinarith [L.sc.one_lt_alt]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem nf_rowsA_rec (P5 : ParameterChoice' D L) (hx : 3 + |L.Cc| ≤ L.sc.x)
    (hw2b : ∀ j, 1 ≤ j → j ≤ (ofRecord D L Del h0).R.m → ∀ z, (ofRecord D L Del h0).w j z ≤ 2 * (ofRecord D L Del h0).sc.b) :
    ∀ j, 1 ≤ j → j ≤ (ofRecord D L Del h0).R.m → ∀ z,
      (ofRecord D L Del h0).w j z + swRec L ≤ (ofRecord D L Del h0).sc.a * (ofRecord D L Del h0).rd := by
  intro j hj1 hjm z
  have h1 := hw2b j hj1 hjm z
  have hS := Sc_le_b L P5
  have hS0 := L.Sc_pos
  have hrd := two_le_rd (ofRecord D L Del h0)
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have ha : (ofRecord D L Del h0).sc.a = L.sc.x * L.sc.b := rfl
  have hbb : (ofRecord D L Del h0).sc.b = L.sc.b := rfl
  rw [ha]
  rw [hbb] at h1
  unfold swRec
  have hc : (1 + |L.Cc|) * L.Sc ≤ (1 + |L.Cc|) * L.sc.b := mul_le_mul_of_nonneg_left hS (by positivity)
  have hxb : (3 + |L.Cc|) * L.sc.b ≤ L.sc.x * L.sc.b := mul_le_mul_of_nonneg_right hx hb0.le
  have hxb0 : 0 ≤ L.sc.x * L.sc.b := by nlinarith [L.sc.one_lt_alt]
  nlinarith

/- English proof (translation)
Introduce `j hj1 hjm t ht`. Establish `h1` using `hw2b j hj1 hjm (false, t)`. Rewrite using `[ofRecord_aT D L Del h0 ⟨t, ht⟩]`. Establish `haw` using `(L.aT_win ⟨t, ht⟩).2`. Establish `hrd` using `two_le_rd (ofRecord D L Del h0)`.

Establish `hb0 : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `ha : (ofRecord D L Del h0).sc.a = L.sc.x * L.sc.b` using `rfl`. Establish `hbb : (ofRecord D L Del h0).sc.b = L.sc.b` using `rfl`. Rewrite `h1` using `[hbb]`.

Rewrite using `[ha]`. Establish `hk : (1 : ℝ) ≤ D.R.k`. Use `D.R.m_add_three_le_k` as an intermediate fact. Conclude with `(show 1 ≤ D.R.k by omega)` after adjusting the coercions. Establish `hxA : L.sc.x ≤ L.sc.x ^ (Scale.A / 2)`.

Establish `: L.sc.x = L.sc.x ^ (1 : ℝ)` using `(Real.rpow_one _).symm`. Use `conv_lhs => rw [this]`. Conclude with `Real.rpow_le_rpow_of_exponent_le (by linarith) (by unfold Scale.A; norm_num)`. Establish `hden : L.sc.x ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)` using `by nlinarith`. Establish `hfrac : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.b`.

Rewrite using `[div_le_iff₀ (by linarith)]`. Use `show L.sc.x * L.sc.b ≤ L.sc.b * ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2))`. Use the polynomial consequences of the given equalities and inequalities. Establish `hxb : 3 * L.sc.b ≤ L.sc.x * L.sc.b` using `mul_le_mul_of_nonneg_right hx hb0.le`. Establish `ha' : L.sc.a = L.sc.x * L.sc.b` using `rfl`.

Rewrite `haw`, `hfrac` using `[ha']`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem nf_topsA_rec (hx : 3 ≤ L.sc.x)
    (hw2b : ∀ j, 1 ≤ j → j ≤ (ofRecord D L Del h0).R.m → ∀ z, (ofRecord D L Del h0).w j z ≤ 2 * (ofRecord D L Del h0).sc.b) :
    ∀ j, 1 ≤ j → j ≤ (ofRecord D L Del h0).R.m → ∀ t ∈ (ofRecord D L Del h0).TT,
      (((ofRecord D L Del h0).aT t : ℚ) : ℝ) + (ofRecord D L Del h0).w j (false, t) ≤
        (ofRecord D L Del h0).sc.a * (ofRecord D L Del h0).rd := by
  intro j hj1 hjm t ht
  have h1 := hw2b j hj1 hjm (false, t)
  rw [ofRecord_aT D L Del h0 ⟨t, ht⟩]
  have haw := (L.aT_win ⟨t, ht⟩).2
  have hrd := two_le_rd (ofRecord D L Del h0)
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hx0 : 0 < L.sc.x := by linarith
  have ha : (ofRecord D L Del h0).sc.a = L.sc.x * L.sc.b := rfl
  have hbb : (ofRecord D L Del h0).sc.b = L.sc.b := rfl
  rw [hbb] at h1
  rw [ha]
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (show 1 ≤ D.R.k by omega)
  have hxA : L.sc.x ≤ L.sc.x ^ (Scale.A / 2) := by
    have : L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
    conv_lhs => rw [this]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by unfold Scale.A; norm_num)
  have hden : L.sc.x ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) := by nlinarith
  have hfrac : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.b := by
    rw [div_le_iff₀ (by linarith)]
    show L.sc.x * L.sc.b ≤ L.sc.b * ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2))
    nlinarith
  have hxb : 3 * L.sc.b ≤ L.sc.x * L.sc.b := mul_le_mul_of_nonneg_right hx hb0.le
  have ha' : L.sc.a = L.sc.x * L.sc.b := rfl
  rw [ha'] at haw hfrac
  nlinarith

end Top

section Discharge

/- English proof (translation)
Establish `hx0 : 0 < L.sc.x` using `lt_trans zero_lt_one L.sc.one_lt_alt`. Establish `hn : (1 : ℝ) ≤ D.R.n`. Establish `: 1 ≤ D.R.n` using `D.R.ord_pos`. Conclude with `this` after adjusting the coercions. Unfold `Scale.w''`.

Rewrite using `[← div_div]`. Conclude with `div_le_self (div_nonneg (b'_nonneg_rec L) hx0.le) hn`.
-/
theorem w''_le_b'x : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := by
  have hx0 : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  unfold Scale.w''
  rw [← div_div]
  exact div_le_self (div_nonneg (b'_nonneg_rec L) hx0.le) hn

/- English proof (translation)
The claim follows from `div_le_self (b'_nonneg_rec L) L.sc.one_lt_alt.le`.
-/
theorem b'x_le_b' : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self (b'_nonneg_rec L) L.sc.one_lt_alt.le

/- English proof (translation)
Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hb0 : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hn : (1 : ℝ) ≤ D.R.n`. Establish `: 1 ≤ D.R.n` using `D.R.ord_pos`. Conclude with `this` after adjusting the coercions.

Establish `hX : 1 ≤ L.sc.X'` using `Real.one_le_exp (Real.rpow_nonneg (by linarith) _)`. Unfold `Scale.w'' Scale.b' Scale.a`. Establish `hxn : 0 < L.sc.x * D.R.n` using `by positivity`. Rewrite using `[div_div, div_le_iff₀ (by positivity)]`. Establish `: L.sc.x * L.sc.b ≤ L.sc.x * L.sc.b * (L.sc.X' * D.R.n)`.

Establish `h1 : 1 ≤ L.sc.X' * D.R.n` using `by nlinarith`. Conclude with `le_mul_of_one_le_right (by positivity) h1`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem w''_le_b : L.sc.w'' D.R.n ≤ L.sc.b := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hX : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  unfold Scale.w'' Scale.b' Scale.a
  have hxn : 0 < L.sc.x * D.R.n := by positivity
  rw [div_div, div_le_iff₀ (by positivity)]
  have : L.sc.x * L.sc.b ≤ L.sc.x * L.sc.b * (L.sc.X' * D.R.n) := by
    have h1 : 1 ≤ L.sc.X' * D.R.n := by nlinarith
    exact le_mul_of_one_le_right (by positivity) h1
  nlinarith

/- English proof (translation)
Establish `hD1 : (1 : ℝ) ≤ Del`. Establish `h` using `D.s.Del_pos`. Rewrite `h` using `[hDel]`. Establish `: 0 < Del` using `by exact_mod_cast h`. Conclude with `this` after adjusting the coercions.

Establish `hSc : L.Sc = (D.R.k : ℝ) * (4 * (Del : ℝ))`. Rewrite using `[L.Sc_eq, hDel]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hk5 : (5 : ℝ) ≤ D.R.k`.

Use `D.R.m_add_three_le_k` as an intermediate fact. Use `D.R.two_le_m` as an intermediate fact. Conclude with `(show 5 ≤ D.R.k by omega)` after adjusting the coercions. Establish `ht : (11 : ℝ) ≤ D.R.t`. Use `D.R.rank_add_five_le` as an intermediate fact.

Use `D.R.m_add_three_le_k` as an intermediate fact. Use `D.R.two_le_m` as an intermediate fact. Conclude with `(show 11 ≤ D.R.t by omega)` after adjusting the coercions. Establish `hm : (0 : ℝ) ≤ D.R.m` using `Nat.cast_nonneg _`. Establish `hkS` using `P5.kS_le`.

Establish `hmt` using `P5.mteta`. Establish `hte` using `P5.t_le_eta`. Rewrite `hkS` using `[hSc]`. Establish `hNm : ((ofRecord D L Del h0).Nm : ℝ) = D.R.k + D.R.m * ((D.R.t : ℝ) + 1)` using `by show ((D.R.k + D.R.m * (D.R.t + 1) : ℕ) : ℝ) = _`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hNm]`. Establish `h1 : 20 * (D.R.k : ℝ) ≤ L.sc.w'' D.R.n`. Establish `e1 : (D.R.k : ℝ) * 4 ≤ (D.R.k : ℝ) * (4 * (Del : ℝ))` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`. Establish `e2 : (D.R.k : ℝ) * ((D.R.k : ℝ) * 4) ≤ (D.R.k : ℝ) * ((D.R.k : ℝ) * (4 * (Del : ℝ)))` using `mul_le_mul_of_nonneg_left e1 (by linarith)`.

Establish `e3 : 20 * (D.R.k : ℝ) ≤ (D.R.k : ℝ) * ((D.R.k : ℝ) * 4)` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : 11 * ((D.R.m : ℝ) * ((D.R.t : ℝ) + 1)) ≤ L.sc.w'' D.R.n`. Establish `: (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * 11 ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz` using `mul_le_mul_of_nonneg_left (by linarith) (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem Nm_le_w'' (hDel : D.s.Del = (Del : ℚ)) (P5 : ParameterChoice' D L) :
    ((ofRecord D L Del h0).Nm : ℝ) + D.R.k + 1 ≤ L.sc.w'' D.R.n := by
  have hD1 : (1 : ℝ) ≤ Del := by
    have h := D.s.Del_pos
    rw [hDel] at h
    have : 0 < Del := by exact_mod_cast h
    exact_mod_cast this
  have hSc : L.Sc = (D.R.k : ℝ) * (4 * (Del : ℝ)) := by
    rw [L.Sc_eq, hDel]
    push_cast
    rfl
  have hk5 : (5 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k; have := D.R.two_le_m
    exact_mod_cast (show 5 ≤ D.R.k by omega)
  have ht : (11 : ℝ) ≤ D.R.t := by
    have := D.R.rank_add_five_le; have := D.R.m_add_three_le_k; have := D.R.two_le_m
    exact_mod_cast (show 11 ≤ D.R.t by omega)
  have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hkS := P5.kS_le
  have hmt := P5.mteta
  have hte := P5.t_le_eta
  rw [hSc] at hkS
  have hNm : ((ofRecord D L Del h0).Nm : ℝ) = D.R.k + D.R.m * ((D.R.t : ℝ) + 1) := by
    show ((D.R.k + D.R.m * (D.R.t + 1) : ℕ) : ℝ) = _
    push_cast
    ring
  rw [hNm]
  have h1 : 20 * (D.R.k : ℝ) ≤ L.sc.w'' D.R.n := by
    have e1 : (D.R.k : ℝ) * 4 ≤ (D.R.k : ℝ) * (4 * (Del : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e2 : (D.R.k : ℝ) * ((D.R.k : ℝ) * 4) ≤ (D.R.k : ℝ) * ((D.R.k : ℝ) * (4 * (Del : ℝ))) :=
      mul_le_mul_of_nonneg_left e1 (by linarith)
    have e3 : 20 * (D.R.k : ℝ) ≤ (D.R.k : ℝ) * ((D.R.k : ℝ) * 4) := by nlinarith
    linarith
  have h2 : 11 * ((D.R.m : ℝ) * ((D.R.t : ℝ) + 1)) ≤ L.sc.w'' D.R.n := by
    have : (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * 11 ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  nlinarith

/- English proof (translation)
Establish `h` using `Nm_le_w'' L Del h0 hDel P5`. Establish `hk : (0 : ℝ) ≤ D.R.k` using `Nat.cast_nonneg _`. Establish `hw` using `w''_le_b L`. Establish `hw'` using `(w''_le_b'x L).trans (b'x_le_b' L)`. Conclude with `nf_sw_rec L Del h0 (by linarith) (by linarith) (by linarith)`.
-/
theorem nf_sw_rec' (hDel : D.s.Del = (Del : ℚ)) (P5 : ParameterChoice' D L) :
    ∀ j, 1 ≤ j → j ≤ (ofRecord D L Del h0).R.m → ∀ z,
      (((ofRecord D L Del h0).R.k : ℝ) + (2 * (j : ℝ) - 1) * (((ofRecord D L Del h0).R.t : ℝ) + 1)) / 2 ≤
        (ofRecord D L Del h0).w j z := by
  have h := Nm_le_w'' L Del h0 hDel P5
  have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hw := w''_le_b L
  have hw' := (w''_le_b'x L).trans (b'x_le_b' L)
  exact nf_sw_rec L Del h0 (by linarith) (by linarith) (by linarith)

/- English proof (translation)
Establish `h` using `Nm_le_w'' L Del h0 hDel P5`. Establish `hk : (0 : ℝ) ≤ D.R.k` using `Nat.cast_nonneg _`. Establish `hw` using `w''_le_b L`. Establish `hw'` using `w''_le_b'x L`. Conclude with `nu_nonneg_from_bounds L Del h0 hDel P5 u (by linarith) (by linarith) (by linarith)`.
-/
theorem nu_nonneg_from_conditions (hDel : D.s.Del = (Del : ℚ)) (P5 : ParameterChoice' D L) (u : D.what₂.Word) :
    ∀ j, 1 ≤ j → j ≤ (ofRecord D L Del h0).R.m → ∀ z, ∀ i < (ofRecord D L Del h0).R.N (j - 1),
      0 ≤ (ofRecord D L Del h0).nu (letterOf D L Del h0 u) j z i := by
  have h := Nm_le_w'' L Del h0 hDel P5
  have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hw := w''_le_b L
  have hw' := w''_le_b'x L
  exact nu_nonneg_from_bounds L Del h0 hDel P5 u (by linarith) (by linarith) (by linarith)

end Discharge

section Assemble

/- English proof (translation)
The claim follows from `logrd logx := logx Nc0 := Nc0 w2b := w2b Om := Om lam := lam lam0 := hlam0 n2 := n2 n3 := n3 eta := eta kN := kN kS := kS blkW := blkW Nw := Nw bN := bN mkb := mkb c1 := c1 c2 := c2 c3 := c3 c4 := c4 c5 := c5 C1two := nf_C1two_rec L constant_weight_sum_bound := nf_C1S_rec L Del h …`.
-/
theorem numFacts_rows (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)) (P5 : ParameterChoice' D L)
    (u : D.what₂.Word) (hx : 3 + |L.Cc| ≤ L.sc.x) (Nc lam0 C0 ce Ch : ℝ)
    (logrd : Real.log (ofRecord D L Del h0).rd ≤ (ofRecord D L Del h0).sc.L)
    (logx : Real.log (ofRecord D L Del h0).sc.x ≤ (ofRecord D L Del h0).sc.L)
    (Nc0 : 0 ≤ Nc)
    (w2b : ∀ j, 1 ≤ j → j ≤ (ofRecord D L Del h0).R.m → ∀ z, (ofRecord D L Del h0).w j z ≤ 2 * (ofRecord D L Del h0).sc.b)
    (Om : |(ofRecord D L Del h0).logOm| ≤ (ofRecord D L Del h0).La)
    (lam : ((ofRecord D L Del h0).R.m : ℝ) * lam0 ≤ (ofRecord D L Del h0).sc.b)
    (hlam0 : 0 ≤ lam0)
    (n2 : ((ofRecord D L Del h0).Nm : ℝ) ^ 2 ≤ (ofRecord D L Del h0).sc.b)
    (n3 : ((ofRecord D L Del h0).R.m : ℝ) ^ 3 * ((ofRecord D L Del h0).Nm : ℝ) ^ 2 * (ofRecord D L Del h0).sc.L ≤
      (ofRecord D L Del h0).sc.b)
    (eta : ((ofRecord D L Del h0).R.m : ℝ) * (ofRecord D L Del h0).eta * ((ofRecord D L Del h0).Nm : ℝ) *
      (ofRecord D L Del h0).sc.L ≤ (ofRecord D L Del h0).sc.b)
    (kN : ((ofRecord D L Del h0).R.k : ℝ) * ((ofRecord D L Del h0).Nm : ℝ) ≤ (ofRecord D L Del h0).sc.b)
    (kS : ((ofRecord D L Del h0).R.k : ℝ) * (ofRecord D L Del h0).Sc ≤
      (ofRecord D L Del h0).sc.w'' (ofRecord D L Del h0).R.n)
    (blkW : ((ofRecord D L Del h0).R.m : ℝ) * (((ofRecord D L Del h0).R.t : ℝ) + 1) * (ofRecord D L Del h0).eta ≤
      (ofRecord D L Del h0).sc.w'' (ofRecord D L Del h0).R.n)
    (Nw : ((ofRecord D L Del h0).Nm : ℝ) * (ofRecord D L Del h0).sc.w'' (ofRecord D L Del h0).R.n ≤
      (ofRecord D L Del h0).sc.b)
    (bN : (ofRecord D L Del h0).sc.b' * ((ofRecord D L Del h0).Nm : ℝ) ≤ (ofRecord D L Del h0).sc.a)
    (mkb : ((ofRecord D L Del h0).R.m : ℝ) * ((ofRecord D L Del h0).R.k : ℝ) * (ofRecord D L Del h0).sc.b' ≤
      (ofRecord D L Del h0).sc.a)
    (c1 : 1 ≤ C0) (c2 : C0 ≤ ce) (c3 : 0 ≤ Ch) (c4 : Ch ≤ C0)
    (c5 : Ch * (ofRecord D L Del h0).Lp ≤ C0 * (ofRecord D L Del h0).La)
    (constant_succ_le : constantOneChoice L + 1 ≤ C0) :
    (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) Nc lam0 C0 ce Ch (swRec L) (constantOneChoice L) where
  logrd := logrd
  logx := logx
  Nc0 := Nc0
  w2b := w2b
  Om := Om
  lam := lam
  lam0 := hlam0
  n2 := n2
  n3 := n3
  eta := eta
  kN := kN
  kS := kS
  blkW := blkW
  Nw := Nw
  bN := bN
  mkb := mkb
  c1 := c1
  c2 := c2
  c3 := c3
  c4 := c4
  c5 := c5
  C1two := nf_C1two_rec L
  constant_weight_sum_bound := nf_C1S_rec L Del h0 hDel
  constant_succ_le := constant_succ_le
  sw := nf_sw_rec' L Del h0 hDel P5
  rowsA := nf_rowsA_rec L Del h0 P5 hx w2b
  topsA := nf_topsA_rec L Del h0 (by have := abs_nonneg L.Cc; linarith) w2b
  nu0 := nu_nonneg_from_conditions L Del h0 hDel P5 u
  blk := nf_blk_rec L Del h0 hh0 u
  inter := nf_inter_rec L Del h0 hDel u
  off := nf_off_rec L Del h0 P5
  top := nf_top_rec L Del h0

end Assemble

end Formalism.L2.DIV.Arith4S

end

noncomputable section

namespace Formalism.L2.DIV.Arith4S

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
open NumberField IsDedekindDomain
open Formalism.MainNotions.DIV.Proofs Formalism.MainNotions.DIV.Proofs.HHParts

variable {D : D7} (L : SizeData₂ D) (Del h0 : ℕ)

/- English proof (translation)
Unfold `NumDatum.Lp Formalism.BasicNotions.DV.Lprime`. Rewrite using `[ofRecord_rd]`.
-/
theorem Lp_rec : (ofRecord D L Del h0).Lp = Formalism.BasicNotions.DV.Lprime D L := by
  unfold NumDatum.Lp Formalism.BasicNotions.DV.Lprime
  rw [ofRecord_rd]

/- English proof (translation)
Take `⟨Y, hY1, -, hY3, hY4⟩` from `P5.g_Y`. Establish `hb` using `one_le_b L`. Establish `hk3` using `D.R.m_add_three_le_k`. Establish `hk : (1 : ℝ) ≤ D.R.k` using `by exact_mod_cast (show 1 ≤ D.R.k by omega)`. Establish `hkb : 1 ≤ (D.R.k : ℝ) * L.sc.b` using `by nlinarith`.

Establish `hY0 : 1 ≤ Y` using `le_trans (one_le_pow₀ hkb) hY1`. Establish `hg` using `(hY4 i).2`. Establish `hg0 : 0 < (D.host.g i : ℝ)` using `lt_of_lt_of_le (by linarith) (hY4 i).1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem log_g_le (P5 : ParameterChoice' D L) (i : Fin 2) :
    Real.log (D.host.g i : ℝ) ≤ Real.log 2 + P5.CYL * L.sc.L := by
  obtain ⟨Y, hY1, -, hY3, hY4⟩ := P5.g_Y
  have hb := one_le_b L
  have hk3 := D.R.m_add_three_le_k
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (show 1 ≤ D.R.k by omega)
  have hkb : 1 ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
  have hY0 : 1 ≤ Y := le_trans (one_le_pow₀ hkb) hY1
  have hg := (hY4 i).2
  have hg0 : 0 < (D.host.g i : ℝ) := lt_of_lt_of_le (by linarith) (hY4 i).1
  calc Real.log (D.host.g i : ℝ) ≤ Real.log (2 * Y) := Real.log_le_log hg0 hg
    _ = Real.log 2 + Real.log Y := Real.log_mul (by norm_num) (by linarith)
    _ ≤ Real.log 2 + P5.CYL * L.sc.L := by linarith

/- English proof (translation)
Rewrite using `[Lp_rec, ofRecord_La]`. Establish `hN : SizeN L` using `hS.1`. Establish `hK : SizeK L` using `hS.2.2.1`. Establish `hQD : SizeQD L` using `hS.2.2.2.2.2.2.1`. Establish `hr : 1 ≤ D.host.rdE` using `hQD.2.2.2.2.2.2.1`.

Establish `hb` using `one_le_b L`. Establish `hv` using `nV_one hK`. Establish `hx0 : 0 < L.sc.x` using `sc_x_pos L`. Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hL1 : 1 < L.sc.L` using `Real.one_lt_rpow hx1 L.sc.eps_pos`.

Establish `hY` using `P5.CYL_pos`. Establish `hg : ∀ i : Fin 2, 0 < (D.host.g i : ℝ)` using `fun i => by`. Take `⟨Y, hY1, -, -, hY4⟩` from `P5.g_Y`. Establish `hk3` using `D.R.m_add_three_le_k`. Establish `hk : (1 : ℝ) ≤ D.R.k` using `by exact_mod_cast (show 1 ≤ D.R.k by omega)`.

Establish `hkb : 1 ≤ (D.R.k : ℝ) * L.sc.b` using `by nlinarith`. Establish `hY0 : 1 ≤ Y` using `le_trans (one_le_pow₀ hkb) hY1`. Conclude with `lt_of_lt_of_le (by linarith) (hY4 i).1`. Establish `g0` using `log_g_le L P5 0`. Establish `g1` using `log_g_le L P5 1`.

Use `set c : ℝ := max L.Ct 5 + 3 with hc`. Establish `hc8 : 8 ≤ c` using `by have := le_max_right L.Ct 5; linarith`. Establish `hnv : Real.log (D.R.nV : ℝ) ≤ c * Real.log L.sc.x`. Establish `h1 : (D.R.nV : ℝ) ≤ L.sc.x ^ c` using `(nV_le L).trans (szPol_le_rpow hS hx)`. Establish `h2` using `Real.log_le_log (by linarith) h1`.

Rewrite `h2` using `[Real.log_rpow hx0]`. Then use the resulting hypothesis. Establish `lb : Real.log L.sc.b = L.sc.L` using `by unfold Scale.b; exact Real.log_exp _`. Establish `hb0 : 0 < L.sc.b` using `by linarith`. Establish `hr0 : 0 < D.host.rdE` using `by linarith`. Establish `hv0 : 0 < (D.R.nV : ℝ)` using `by linarith`.

Establish `E1 : Formalism.BasicNotions.DV.Lprime D L = L.sc.L + Real.log D.host.rdE + Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ) + Real.log (D.R.nV : ℝ)`. Unfold `Formalism.BasicNotions.DV.Lprime`. Rewrite using `[Real.log_mul (mul_pos (mul_pos hb0 hr0) (mul_pos (hg 0) (hg 1))).ne' hv0.ne', Real.log_mul (mul_pos hb0 hr0).ne' (mul_pos (hg 0) (hg 1)).ne', Real.log_mul hb0.ne' hr0.ne', Real.log_mul (hg 0).ne' (hg 1).ne', lb]`. Expand and normalize the polynomial expressions, which then agree. Establish `E2 : L.La = Real.log L.sc.x + L.sc.L + Real.log D.host.rdE`.

Unfold `SizeData₂.La Scale.a`. Rewrite using `[Real.log_mul (mul_pos hx0 hb0).ne' hr0.ne', Real.log_mul hx0.ne' hb0.ne', lb]`. Rewrite using `[E1, E2]`. Establish `lx : 0 ≤ Real.log L.sc.x` using `Real.log_nonneg hx1.le`. Establish `lr : 0 ≤ Real.log D.host.rdE` using `Real.log_nonneg hr`.

Establish `l2 : Real.log 2 < 1` using `by have := Real.log_two_lt_d9; linarith`. Establish `e1 : P5.CYL * L.sc.L ≤ P5.CYL * (Real.log L.sc.x + L.sc.L + Real.log D.host.rdE)` using `mul_le_mul_of_nonneg_left (by linarith) hY.le`. Establish `e2 : c * Real.log L.sc.x ≤ c * (Real.log L.sc.x + L.sc.L + Real.log D.host.rdE)` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem Lp_le_La (P5 : ParameterChoice' D L) (hS : SizesAt L) (hx : 9 ≤ L.sc.x) :
    (ofRecord D L Del h0).Lp ≤ (3 + 2 * P5.CYL + (max L.Ct 5 + 3)) * (ofRecord D L Del h0).La := by
  rw [Lp_rec, ofRecord_La]
  have hN : SizeN L := hS.1
  have hK : SizeK L := hS.2.2.1
  have hQD : SizeQD L := hS.2.2.2.2.2.2.1
  have hr : 1 ≤ D.host.rdE := hQD.2.2.2.2.2.2.1
  have hb := one_le_b L
  have hv := nV_one hK
  have hx0 : 0 < L.sc.x := sc_x_pos L
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL1 : 1 < L.sc.L := Real.one_lt_rpow hx1 L.sc.eps_pos
  have hY := P5.CYL_pos
  have hg : ∀ i : Fin 2, 0 < (D.host.g i : ℝ) := fun i => by
    obtain ⟨Y, hY1, -, -, hY4⟩ := P5.g_Y
    have hk3 := D.R.m_add_three_le_k
    have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (show 1 ≤ D.R.k by omega)
    have hkb : 1 ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
    have hY0 : 1 ≤ Y := le_trans (one_le_pow₀ hkb) hY1
    exact lt_of_lt_of_le (by linarith) (hY4 i).1
  have g0 := log_g_le L P5 0
  have g1 := log_g_le L P5 1
  set c : ℝ := max L.Ct 5 + 3 with hc
  have hc8 : 8 ≤ c := by have := le_max_right L.Ct 5; linarith

  have hnv : Real.log (D.R.nV : ℝ) ≤ c * Real.log L.sc.x := by
    have h1 : (D.R.nV : ℝ) ≤ L.sc.x ^ c := (nV_le L).trans (szPol_le_rpow hS hx)
    have h2 := Real.log_le_log (by linarith) h1
    rwa [Real.log_rpow hx0] at h2
  have lb : Real.log L.sc.b = L.sc.L := by unfold Scale.b; exact Real.log_exp _
  have hb0 : 0 < L.sc.b := by linarith
  have hr0 : 0 < D.host.rdE := by linarith
  have hv0 : 0 < (D.R.nV : ℝ) := by linarith
  have E1 : Formalism.BasicNotions.DV.Lprime D L = L.sc.L + Real.log D.host.rdE + Real.log (D.host.g 0 : ℝ) +
      Real.log (D.host.g 1 : ℝ) + Real.log (D.R.nV : ℝ) := by
    unfold Formalism.BasicNotions.DV.Lprime
    rw [Real.log_mul (mul_pos (mul_pos hb0 hr0) (mul_pos (hg 0) (hg 1))).ne' hv0.ne',
      Real.log_mul (mul_pos hb0 hr0).ne' (mul_pos (hg 0) (hg 1)).ne', Real.log_mul hb0.ne' hr0.ne',
      Real.log_mul (hg 0).ne' (hg 1).ne', lb]
    ring
  have E2 : L.La = Real.log L.sc.x + L.sc.L + Real.log D.host.rdE := by
    unfold SizeData₂.La Scale.a
    rw [Real.log_mul (mul_pos hx0 hb0).ne' hr0.ne', Real.log_mul hx0.ne' hb0.ne', lb]
  rw [E1, E2]
  have lx : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx1.le
  have lr : 0 ≤ Real.log D.host.rdE := Real.log_nonneg hr
  have l2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have e1 : P5.CYL * L.sc.L ≤ P5.CYL * (Real.log L.sc.x + L.sc.L + Real.log D.host.rdE) :=
    mul_le_mul_of_nonneg_left (by linarith) hY.le
  have e2 : c * Real.log L.sc.x ≤ c * (Real.log L.sc.x + L.sc.L + Real.log D.host.rdE) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith

/- English proof (translation)
Establish `h1` using `Lp_le_La L Del h0 P5 hS hx`. Establish `hLa : 0 ≤ (ofRecord D L Del h0).La`. Rewrite using `[ofRecord_La]`. Conclude with `(La_bounds hS.1 hS.2.2.1 hS.2.2.2.2.2.2.1).1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem constant_mul_Lp_le (P5 : ParameterChoice' D L) (hS : SizesAt L) (hx : 9 ≤ L.sc.x) (Ch C0 : ℝ) (hCh : 0 ≤ Ch)
    (hC0 : Ch * (3 + 2 * P5.CYL + (max L.Ct 5 + 3)) ≤ C0) :
    Ch * (ofRecord D L Del h0).Lp ≤ C0 * (ofRecord D L Del h0).La := by
  have h1 := Lp_le_La L Del h0 P5 hS hx
  have hLa : 0 ≤ (ofRecord D L Del h0).La := by
    rw [ofRecord_La]; exact (La_bounds hS.1 hS.2.2.1 hS.2.2.2.2.2.2.1).1
  calc Ch * (ofRecord D L Del h0).Lp ≤ Ch * ((3 + 2 * P5.CYL + (max L.Ct 5 + 3)) * (ofRecord D L Del h0).La) :=
        mul_le_mul_of_nonneg_left h1 hCh
    _ = (Ch * (3 + 2 * P5.CYL + (max L.Ct 5 + 3))) * (ofRecord D L Del h0).La := by ring
    _ ≤ C0 * (ofRecord D L Del h0).La := mul_le_mul_of_nonneg_right hC0 hLa

/- English proof (translation)
Establish `h1 : 1 ≤ C0` using `(le_max_left _ _).trans hC0`. Establish `h2 : Ch * (3 + 2 * P5.CYL + (max L.Ct 5 + 3)) ≤ C0` using `(le_max_right _ _).trans hC0`. Establish `hY` using `P5.CYL_pos`. Establish `hc : 1 ≤ 3 + 2 * P5.CYL + (max L.Ct 5 + 3)` using `by have := le_max_right L.Ct 5; linarith`. Use `⟨h1, hce, hCh, ?_, constant_mul_Lp_le L Del h0 P5 hS hx Ch C0 hCh h2⟩` and prove the remaining obligations.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem nf_consts_rec (P5 : ParameterChoice' D L) (hS : SizesAt L) (hx : 9 ≤ L.sc.x) (Ch C0 ce : ℝ) (hCh : 0 ≤ Ch)
    (hC0 : max 1 (Ch * (3 + 2 * P5.CYL + (max L.Ct 5 + 3))) ≤ C0) (hce : C0 ≤ ce) :
    1 ≤ C0 ∧ C0 ≤ ce ∧ 0 ≤ Ch ∧ Ch ≤ C0 ∧ Ch * (ofRecord D L Del h0).Lp ≤ C0 * (ofRecord D L Del h0).La := by
  have h1 : 1 ≤ C0 := (le_max_left _ _).trans hC0
  have h2 : Ch * (3 + 2 * P5.CYL + (max L.Ct 5 + 3)) ≤ C0 := (le_max_right _ _).trans hC0
  have hY := P5.CYL_pos
  have hc : 1 ≤ 3 + 2 * P5.CYL + (max L.Ct 5 + 3) := by have := le_max_right L.Ct 5; linarith
  refine ⟨h1, hce, hCh, ?_, constant_mul_Lp_le L Del h0 P5 hS hx Ch C0 hCh h2⟩
  nlinarith

/- English proof (translation)
Use `set N := ⌈(e + 1) / eps⌉₊ with hNdef`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hN : e + 1 ≤ eps * (N : ℝ)`. Use `Nat.le_ceil ((e + 1) / eps)` as an intermediate fact. Rewrite `this` using `[← hNdef, div_le_iff₀ heps]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hF : (0 : ℝ) < (Nat.factorial N : ℝ)` using `by exact_mod_cast Nat.factorial_pos N`. Establish `hxe : 0 ≤ x ^ e` using `Real.rpow_nonneg hx0.le _`. Establish `h1 : (x ^ eps) ^ N / (Nat.factorial N : ℝ) ≤ Real.exp (x ^ eps)` using `Real.pow_div_factorial_le_exp _ (Real.rpow_nonneg hx0.le _) N`. Establish `h2 : (x ^ eps) ^ N = x ^ (eps * (N : ℝ))`.

Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hx0.le]`. Establish `h3 : x ^ (e + 1) ≤ x ^ (eps * (N : ℝ))` using `Real.rpow_le_rpow_of_exponent_le hx1 hN`. Establish `h4 : x ^ (e + 1) = x * x ^ e` using `by rw [Real.rpow_add hx0, Real.rpow_one, mul_comm]`. Distinguish the cases in `hc : c ≤ 0`. Establish `: c * x ^ e ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg hc hxe`.

Combine the linear relations using `[Real.exp_pos (x ^ eps)]`. Use `replace hc : 0 < c := lt_of_not_ge hc`. Establish `h5 : c * x ^ e * (Nat.factorial N : ℝ) ≤ x * x ^ e`. Use `mul_le_mul_of_nonneg_right hxc hxe` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `h6 : c * x ^ e ≤ x ^ (e + 1) / (Nat.factorial N : ℝ)`. Rewrite using `[le_div_iff₀ hF, h4]`. Conclude with `h5`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_rpow_le_exp_rpow {x eps c e : ℝ} (hx1 : 1 ≤ x) (heps : 0 < eps) (he : 0 ≤ e)
    (hxc : c * (Nat.factorial ⌈(e + 1) / eps⌉₊ : ℝ) ≤ x) : c * x ^ e ≤ Real.exp (x ^ eps) := by
  set N := ⌈(e + 1) / eps⌉₊ with hNdef
  have hx0 : 0 < x := by linarith
  have hN : e + 1 ≤ eps * (N : ℝ) := by
    have := Nat.le_ceil ((e + 1) / eps)
    rw [← hNdef, div_le_iff₀ heps] at this
    linarith
  have hF : (0 : ℝ) < (Nat.factorial N : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have hxe : 0 ≤ x ^ e := Real.rpow_nonneg hx0.le _
  have h1 : (x ^ eps) ^ N / (Nat.factorial N : ℝ) ≤ Real.exp (x ^ eps) :=
    Real.pow_div_factorial_le_exp _ (Real.rpow_nonneg hx0.le _) N
  have h2 : (x ^ eps) ^ N = x ^ (eps * (N : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
  have h3 : x ^ (e + 1) ≤ x ^ (eps * (N : ℝ)) := Real.rpow_le_rpow_of_exponent_le hx1 hN
  have h4 : x ^ (e + 1) = x * x ^ e := by rw [Real.rpow_add hx0, Real.rpow_one, mul_comm]
  by_cases hc : c ≤ 0
  · have : c * x ^ e ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hxe
    linarith [Real.exp_pos (x ^ eps)]
  · replace hc : 0 < c := lt_of_not_ge hc
    have h5 : c * x ^ e * (Nat.factorial N : ℝ) ≤ x * x ^ e := by
      have := mul_le_mul_of_nonneg_right hxc hxe
      nlinarith
    have h6 : c * x ^ e ≤ x ^ (e + 1) / (Nat.factorial N : ℝ) := by
      rw [le_div_iff₀ hF, h4]; exact h5
    calc c * x ^ e ≤ x ^ (e + 1) / (Nat.factorial N : ℝ) := h6
      _ ≤ x ^ (eps * (N : ℝ)) / (Nat.factorial N : ℝ) := div_le_div_of_nonneg_right h3 hF.le
      _ = (x ^ eps) ^ N / (Nat.factorial N : ℝ) := by rw [h2]
      _ ≤ Real.exp (x ^ eps) := h1

/- English proof (translation)
The claim follows from `mul_rpow_le_exp_rpow L.sc.one_lt_alt.le L.sc.eps_pos he hxc`.
-/
theorem mul_rpow_le_b {c e : ℝ} (he : 0 ≤ e)
    (hxc : c * (Nat.factorial ⌈(e + 1) / L.sc.eps⌉₊ : ℝ) ≤ L.sc.x) : c * L.sc.x ^ e ≤ L.sc.b :=
  mul_rpow_le_exp_rpow L.sc.one_lt_alt.le L.sc.eps_pos he hxc

section Bound

variable {J Pl : Type} [Fintype J] [Fintype Pl] [DecidableEq Pl]

/- English proof (translation)
Establish `hLa : 0 ≤ R.La` using `(abs_nonneg _).trans R.p23`. Establish `hk` using `R.p16`. Establish `hm` using `R.p14`. Establish `hb : 0 ≤ R.b` using `by rw [R.p4]; exact (Real.exp_pos _).le`. Use `set X := (R.k + R.m) * (2 * R.b) * R.La with hX`.

Establish `hX0 : 0 ≤ X` using `by rw [hX]; have : 0 ≤ R.k + R.m := by linarith`. Check the signs of the components of the expression. Establish `hterm : ∀ j ρ, R.pq j * R.w j ρ * R.logOm ≤ X`. Introduce `j ρ`. Establish `hpq : |R.pq j| ≤ R.k + R.m`.

Use `R.p22 j` as an intermediate fact. Establish `h1 : |R.pq j| ≤ |R.pq j - R.k| + |R.k|`. Use `abs_add_le (R.pq j - R.k) R.k` as an intermediate fact. Simplify using `using this`. Rewrite `h1` using `[abs_of_nonneg (by linarith : (0:ℝ) ≤ R.k)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨hw0, hw1⟩` from `R.p21 j ρ`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul (mul_le_mul hpq hw1 hw0 (by linarith)) R.p23 (abs_nonneg _)` to reduce the goal to its premises. Establish `: 0 ≤ R.k + R.m` using `by linarith`.

Check the signs of the components of the expression. Establish `hρ : ∀ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm ≤ R.f * X`. Introduce `j`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem main_le_RN (R : RecNums J Pl) :
    (∑ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm) ≤ R.m * (R.f * ((R.k + R.m) * (2 * R.b) * R.La)) := by
  have hLa : 0 ≤ R.La := (abs_nonneg _).trans R.p23
  have hk := R.p16
  have hm := R.p14
  have hb : 0 ≤ R.b := by rw [R.p4]; exact (Real.exp_pos _).le
  set X := (R.k + R.m) * (2 * R.b) * R.La with hX
  have hX0 : 0 ≤ X := by rw [hX]; have : 0 ≤ R.k + R.m := by linarith
                         positivity
  have hterm : ∀ j ρ, R.pq j * R.w j ρ * R.logOm ≤ X := by
    intro j ρ
    have hpq : |R.pq j| ≤ R.k + R.m := by
      have := R.p22 j
      have h1 : |R.pq j| ≤ |R.pq j - R.k| + |R.k| := by
        have := abs_add_le (R.pq j - R.k) R.k; simpa using this
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ R.k)] at h1
      linarith
    obtain ⟨hw0, hw1⟩ := R.p21 j ρ
    calc R.pq j * R.w j ρ * R.logOm ≤ |R.pq j * R.w j ρ * R.logOm| := le_abs_self _
      _ = |R.pq j| * R.w j ρ * |R.logOm| := by rw [abs_mul, abs_mul, abs_of_nonneg hw0]
      _ ≤ (R.k + R.m) * (2 * R.b) * R.La := by
        apply mul_le_mul (mul_le_mul hpq hw1 hw0 (by linarith)) R.p23 (abs_nonneg _)
        have : 0 ≤ R.k + R.m := by linarith
        positivity
  have hρ : ∀ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm ≤ R.f * X := by
    intro j
    calc ∑ ρ, R.pq j * R.w j ρ * R.logOm ≤ ∑ _ρ : Pl, X := Finset.sum_le_sum fun ρ _ => hterm j ρ
      _ = (Fintype.card Pl : ℝ) * X := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ R.f * X := mul_le_mul_of_nonneg_right R.p13 hX0
  calc (∑ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm) ≤ ∑ _j : J, R.f * X := Finset.sum_le_sum fun j _ => hρ j
    _ = (Fintype.card J : ℝ) * (R.f * X) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = R.m * (R.f * X) := by rw [R.p12]

end Bound

section BoundBR

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {Nd : NumDatum} {eJz : A3.fam3.base3.J ≃ Fin Nd.R.m} {Nc : ℝ}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}

/- English proof (translation)
Establish `h1` using `levelThree_bound_closed hZ eJ δ Tl lam0 C0 ce Ch Sw C1 H Zs C CH`. Establish `h2` using `error_bound_closed_numbers Nd Nc hZ eJ δ Tl lam0 C0 ce Ch Sw C1 H Zs C CH hC bd dg s c13 cG cD hbd hLam hdg hce`. Unfold `boundBR`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem boundBR_le_closed (hZ : ClosedScale3 A3 Nd eJz Nc Zsc) (eJ : A3.fam3.base3.J ≃ Fin Nd.R.m) (δ : Code Nd) (Tl : ℕ)
    (lam0 C0 ce Ch Sw C1 : ℝ) (H : Nd.NumFacts δ Nc lam0 C0 ce Ch Sw C1) (Zs : DefSub A3.fam3.amb3) (C CH : ℝ)
    {Df0 Df1 : DefSide A3.fam3.base3} {Dc : DefCols Df1} {Sp : SPer Dc}
    (P : IndefCoreR Df0 Df1 Dc Sp ((Zsc Zs).num C CH)) (hC : 0 ≤ C) (bd : A3.fam3.base3.J → ℝ) (dg s : ℕ)
    (c13 cG cD : ℝ) (hbd : ∀ j, bd j ≤ c13 * Nd.unitE Nc)
    (hLam : lam0 + Real.log (s : ℝ) ≤ cG * ((Nd.R.m : ℝ) * Nd.unitE Nc))
    (hdg : Real.log (dg : ℝ) + Real.log (s : ℝ) ≤ cD * Nd.unitE Nc) (hce : C + cG + C + (c13 + cD) + 1 ≤ ce) :
    boundBR P (lgDef (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H) s) 1 (etaSumBound bd dg s) ≤
      (∑ j, ∑ ρ, (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).pq j *
          (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).w j ρ *
          (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).logOm) + 2 * FoOfR P +
        (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).errB := by
  have h1 := levelThree_bound_closed hZ eJ δ Tl lam0 C0 ce Ch Sw C1 H Zs C CH
  have h2 := error_bound_closed_numbers Nd Nc hZ eJ δ Tl lam0 C0 ce Ch Sw C1 H Zs C CH hC bd dg s c13 cG cD hbd hLam hdg hce
  unfold boundBR
  linarith

end BoundBR

section Sizes

/- English proof (translation)
Establish `h1` using `bPol_le hS K 9 hx1`. Establish `he : (0 : ℝ) ≤ ((9 : ℕ) : ℝ) * (max L.Ct 5 + 3) + 1`. Use `le_max_right L.Ct 5` as an intermediate fact. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h2` using `mul_rpow_le_b L (c := 1) (e := ((9 : ℕ) : ℝ) * (max L.Ct 5 + 3) + 1) he (by push_cast; simpa using hx2)`. Establish `hb` using `one_le_b L`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem polyBound_mul_b_le_sq (hS : SizesAt L) (K : ℝ) (hx1 : max 9 K ≤ L.sc.x)
    (hx2 : (Nat.factorial ⌈((9 : ℝ) * (max L.Ct 5 + 3) + 1 + 1) / L.sc.eps⌉₊ : ℝ) ≤ L.sc.x) :
    K * szPol L ^ 9 * L.sc.b ≤ L.sc.b ^ 2 := by
  have h1 := bPol_le hS K 9 hx1
  have he : (0 : ℝ) ≤ ((9 : ℕ) : ℝ) * (max L.Ct 5 + 3) + 1 := by
    have := le_max_right L.Ct 5; push_cast; nlinarith
  have h2 := mul_rpow_le_b L (c := 1) (e := ((9 : ℕ) : ℝ) * (max L.Ct 5 + 3) + 1) he (by push_cast; simpa using hx2)
  have hb := one_le_b L
  calc K * szPol L ^ 9 * L.sc.b ≤ L.sc.x ^ (((9 : ℕ) : ℝ) * (max L.Ct 5 + 3) + 1) * L.sc.b := h1
    _ ≤ L.sc.b * L.sc.b := mul_le_mul_of_nonneg_right (by simpa using h2) (by linarith)
    _ = L.sc.b ^ 2 := (sq _).symm

/- English proof (translation)
Establish `hx0` using `sc_x_pos L`. Establish `hL0` using `(sc_L_pos L).le`. Establish `hb` using `one_le_b L`. Establish `hn : (1 : ℝ) ≤ D.R.n` using `by exact_mod_cast (show 1 ≤ D.R.n from D.R.ord_pos)`. Establish `hT : (D.host.T2.card : ℝ) ≤ D.R.n`.

Establish `: D.host.T2 ⊆ Finset.range D.R.n` using `fun u hu => Finset.mem_range.2 (by`. Establish `h1` using `D.host.second_set_range u hu`. Establish `h2` using `D.host.two_le_Lw`. Establish `h3 : D.R.n0 ≤ D.R.n` using `D.R.cyclic_order_le_exponent`. Use the proof step `nlinarith)`.

Conclude with `(by simpa using Finset.card_le_card this)` after adjusting the coercions. Establish `hxe : L.sc.x ^ (-L.sc.eps) = (L.sc.L)⁻¹`. Rewrite using `[Real.rpow_neg hx0.le]`. Both sides reduce to the same expression. Establish `hLp : 0 < L.sc.L` using `sc_L_pos L`.

Establish `eNc : L.Nc = (D.host.T2.card : ℝ) * D.R.k * L.sc.b * L.sc.L ^ 2 / ((D.R.n : ℝ) ^ 2)`. Unfold `SizeData₂.Nc budgetNc rankBudget bSize`. Rewrite using `[hxe]`. Establish `: L.sc.x ^ L.sc.eps = L.sc.L` using `rfl`. Rewrite using `[this]`.

Establish `hb' : Real.exp L.sc.L = L.sc.b` using `rfl`. Rewrite using `[hb']`. Clear the denominators using the available nonvanishing facts. Rewrite using `[eNc, div_le_iff₀ (by positivity)]`. Establish `hk` using `k_le L`.

Establish `hLP` using `L_le L`. Establish `hP` using `one_le_szPol L`. Establish `hk0 : (0 : ℝ) ≤ D.R.k` using `Nat.cast_nonneg _`. Establish `hT0 : (0 : ℝ) ≤ D.host.T2.card` using `Nat.cast_nonneg _`. Establish `e1 : (D.host.T2.card : ℝ) * D.R.k * L.sc.b * L.sc.L ^ 2 ≤ (D.R.n : ℝ) * (szPol L * L.sc.b * szPol L ^ 2)`.

Establish `a1 : (D.host.T2.card : ℝ) * D.R.k ≤ (D.R.n : ℝ) * szPol L` using `mul_le_mul hT hk hk0 (by linarith)`. Establish `a2 : (D.host.T2.card : ℝ) * D.R.k * L.sc.b ≤ (D.R.n : ℝ) * szPol L * L.sc.b` using `mul_le_mul_of_nonneg_right a1 (by linarith)`. Establish `a3 : L.sc.L ^ 2 ≤ szPol L ^ 2` using `pow_le_pow_left₀ hL0 hLP 2`. Establish `a4 : (D.host.T2.card : ℝ) * D.R.k * L.sc.b * L.sc.L ^ 2 ≤ (D.R.n : ℝ) * szPol L * L.sc.b * szPol L ^ 2` using `mul_le_mul a2 a3 (by positivity) (by positivity)`. Combine the equalities or inequalities in the displayed calculation.

Establish `e2 : (D.R.n : ℝ) * (szPol L * L.sc.b * szPol L ^ 2) ≤ szPol L ^ 3 * L.sc.b * (D.R.n : ℝ) ^ 2`. Establish `: (D.R.n : ℝ) ≤ (D.R.n : ℝ) ^ 2` using `by nlinarith`. Establish `h3 : 0 ≤ szPol L ^ 3 * L.sc.b` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Nc_le_rec : L.Nc ≤ szPol L ^ 3 * L.sc.b := by
  have hx0 := sc_x_pos L
  have hL0 := (sc_L_pos L).le
  have hb := one_le_b L
  have hn : (1 : ℝ) ≤ D.R.n := by exact_mod_cast (show 1 ≤ D.R.n from D.R.ord_pos)
  have hT : (D.host.T2.card : ℝ) ≤ D.R.n := by
    have : D.host.T2 ⊆ Finset.range D.R.n := fun u hu => Finset.mem_range.2 (by
      have h1 := D.host.second_set_range u hu
      have h2 := D.host.two_le_Lw
      have h3 : D.R.n0 ≤ D.R.n := D.R.cyclic_order_le_exponent
      nlinarith)
    exact_mod_cast (by simpa using Finset.card_le_card this)
  have hxe : L.sc.x ^ (-L.sc.eps) = (L.sc.L)⁻¹ := by
    rw [Real.rpow_neg hx0.le]; rfl
  have hLp : 0 < L.sc.L := sc_L_pos L
  have eNc : L.Nc = (D.host.T2.card : ℝ) * D.R.k * L.sc.b * L.sc.L ^ 2 / ((D.R.n : ℝ) ^ 2) := by
    unfold SizeData₂.Nc budgetNc rankBudget bSize
    rw [hxe]
    have : L.sc.x ^ L.sc.eps = L.sc.L := rfl
    rw [this]
    have hb' : Real.exp L.sc.L = L.sc.b := rfl
    rw [hb']
    field_simp
  rw [eNc, div_le_iff₀ (by positivity)]
  have hk := k_le L
  have hLP := L_le L
  have hP := one_le_szPol L
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) ≤ D.host.T2.card := Nat.cast_nonneg _
  have e1 : (D.host.T2.card : ℝ) * D.R.k * L.sc.b * L.sc.L ^ 2 ≤ (D.R.n : ℝ) * (szPol L * L.sc.b * szPol L ^ 2) := by
    have a1 : (D.host.T2.card : ℝ) * D.R.k ≤ (D.R.n : ℝ) * szPol L := mul_le_mul hT hk hk0 (by linarith)
    have a2 : (D.host.T2.card : ℝ) * D.R.k * L.sc.b ≤ (D.R.n : ℝ) * szPol L * L.sc.b :=
      mul_le_mul_of_nonneg_right a1 (by linarith)
    have a3 : L.sc.L ^ 2 ≤ szPol L ^ 2 := pow_le_pow_left₀ hL0 hLP 2
    have a4 : (D.host.T2.card : ℝ) * D.R.k * L.sc.b * L.sc.L ^ 2 ≤ (D.R.n : ℝ) * szPol L * L.sc.b * szPol L ^ 2 :=
      mul_le_mul a2 a3 (by positivity) (by positivity)
    calc _ ≤ (D.R.n : ℝ) * szPol L * L.sc.b * szPol L ^ 2 := a4
      _ = _ := by ring
  have e2 : (D.R.n : ℝ) * (szPol L * L.sc.b * szPol L ^ 2) ≤ szPol L ^ 3 * L.sc.b * (D.R.n : ℝ) ^ 2 := by
    have : (D.R.n : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by nlinarith
    have h3 : 0 ≤ szPol L ^ 3 * L.sc.b := by positivity
    nlinarith
  linarith

/- English proof (translation)
Establish `e : L.B0 = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L` using `rfl`. Rewrite using `[e]`. Establish `hf` using `f_le L`. Establish `hm` using `m_le L`. Establish `hL` using `L_le L`.

Establish `hb` using `one_le_b L`. Establish `h0 : (0:ℝ) ≤ D.R.f` using `Nat.cast_nonneg _`. Establish `h1 : (0:ℝ) ≤ D.R.m` using `Nat.cast_nonneg _`. Establish `hL0` using `(sc_L_pos L).le`. Establish `: (D.R.f : ℝ) * D.R.m * L.sc.L ≤ szPol L * szPol L * szPol L` using `mul_le_mul (mul_le_mul hf hm h1 (by linarith [one_le_szPol L])) hL hL0 (by nlinarith [one_le_szPol L])`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem initialBound_le_cube : L.B0 ≤ szPol L ^ 3 * L.sc.b := by
  have e : L.B0 = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L := rfl
  rw [e]
  have hf := f_le L; have hm := m_le L; have hL := L_le L
  have hb := one_le_b L
  have h0 : (0:ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have h1 : (0:ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hL0 := (sc_L_pos L).le
  have : (D.R.f : ℝ) * D.R.m * L.sc.L ≤ szPol L * szPol L * szPol L :=
    mul_le_mul (mul_le_mul hf hm h1 (by linarith [one_le_szPol L])) hL hL0 (by nlinarith [one_le_szPol L])
  nlinarith

/- English proof (translation)
Establish `e : (ofRecord D L Del h0).unitE L.Nc = L.sc.L * (L.B0 + L.Nc)` using `rfl`. Rewrite using `[e]`. Establish `h1` using `initialBound_le_cube L`. Establish `h2` using `Nc_le_rec L`. Establish `hL` using `L_le L`.

Establish `hL0` using `(sc_L_pos L).le`. Establish `hb` using `one_le_b L`. Establish `hP` using `one_le_szPol L`. Establish `hB0 : 0 ≤ L.B0 + L.Nc`. Establish `: 0 ≤ L.B0` using `by unfold SizeData₂.B0 sizeBudget bSize; have := (sc_x_pos L); positivity`.

Use `Nc_nonneg L` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
theorem unitE_le_rec : (ofRecord D L Del h0).unitE L.Nc ≤ 2 * szPol L ^ 4 * L.sc.b := by
  have e : (ofRecord D L Del h0).unitE L.Nc = L.sc.L * (L.B0 + L.Nc) := rfl
  rw [e]
  have h1 := initialBound_le_cube L; have h2 := Nc_le_rec L
  have hL := L_le L; have hL0 := (sc_L_pos L).le
  have hb := one_le_b L
  have hP := one_le_szPol L
  have hB0 : 0 ≤ L.B0 + L.Nc := by
    have : 0 ≤ L.B0 := by unfold SizeData₂.B0 sizeBudget bSize; have := (sc_x_pos L); positivity
    have := Nc_nonneg L
    linarith
  calc L.sc.L * (L.B0 + L.Nc) ≤ szPol L * (2 * (szPol L ^ 3 * L.sc.b)) :=
        mul_le_mul hL (by linarith) hB0 (by linarith)
    _ = 2 * szPol L ^ 4 * L.sc.b := by ring

end Sizes

section Q

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

/- English proof (translation)
Use `(main_le_RN _).trans ?_` and prove the remaining obligations. Use `show (D.R.m : ℝ) * ((D.R.f : ℝ) * (((D.R.k : ℝ) + D.R.m) * (2 * L.sc.b) * (ofRecord D L Del h0).La)) ≤ _`. Rewrite using `[ofRecord_La]`. Establish `hf` using `f_le L`. Establish `hm` using `m_le L`.

Establish `hk` using `k_le L`. Take `⟨hLa0, hLa⟩` from `La_bounds hS.1 hS.2.2.1 hS.2.2.2.2.2.2.1`. Establish `hb` using `one_le_b L`. Establish `hP` using `one_le_szPol L`. Establish `h0 : (0:ℝ) ≤ D.R.f` using `Nat.cast_nonneg _`.

Establish `h1 : (0:ℝ) ≤ D.R.m` using `Nat.cast_nonneg _`. Establish `h2 : (0:ℝ) ≤ D.R.k` using `Nat.cast_nonneg _`. Establish `a1 : ((D.R.k : ℝ) + D.R.m) * (2 * L.sc.b) * L.La ≤ (2 * szPol L) * (2 * L.sc.b) * (4 * szPol L)` using `mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (by linarith)) hLa hLa0 (by positivity)`. Establish `a2 : (D.R.f : ℝ) * (((D.R.k : ℝ) + D.R.m) * (2 * L.sc.b) * L.La) ≤ szPol L * ((2 * szPol L) * (2 * L.sc.b) * (4 * szPol L))` using `mul_le_mul hf a1 (by positivity) (by positivity)`. Establish `a3 : (D.R.m : ℝ) * ((D.R.f : ℝ) * (((D.R.k : ℝ) + D.R.m) * (2 * L.sc.b) * L.La)) ≤ szPol L * (szPol L * ((2 * szPol L) * (2 * L.sc.b) * (4 * szPol L)))` using `mul_le_mul hm a2 (by positivity) (by positivity)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem main_rec (hS : SizesAt L) {J : Type} [Fintype J] (eJ : J ≃ Fin (ofRecord D L Del h0).R.m)
    (δ : Code (ofRecord D L Del h0)) (Tl : ℕ) (Nc lam0 C0 ce Ch Sw C1 : ℝ)
    (H : (ofRecord D L Del h0).NumFacts δ Nc lam0 C0 ce Ch Sw C1) :
    (∑ j, ∑ ρ, (RecNums.ofNum (ofRecord D L Del h0) eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).pq j *
        (RecNums.ofNum (ofRecord D L Del h0) eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).w j ρ *
        (RecNums.ofNum (ofRecord D L Del h0) eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).logOm) ≤ 16 * szPol L ^ 4 * L.sc.b := by
  refine (main_le_RN _).trans ?_
  show (D.R.m : ℝ) * ((D.R.f : ℝ) * (((D.R.k : ℝ) + D.R.m) * (2 * L.sc.b) * (ofRecord D L Del h0).La)) ≤ _
  rw [ofRecord_La]
  have hf := f_le L; have hm := m_le L; have hk := k_le L
  obtain ⟨hLa0, hLa⟩ := La_bounds hS.1 hS.2.2.1 hS.2.2.2.2.2.2.1
  have hb := one_le_b L
  have hP := one_le_szPol L
  have h0 : (0:ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have h1 : (0:ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have h2 : (0:ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have a1 : ((D.R.k : ℝ) + D.R.m) * (2 * L.sc.b) * L.La ≤ (2 * szPol L) * (2 * L.sc.b) * (4 * szPol L) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (by linarith)) hLa hLa0 (by positivity)
  have a2 : (D.R.f : ℝ) * (((D.R.k : ℝ) + D.R.m) * (2 * L.sc.b) * L.La) ≤
      szPol L * ((2 * szPol L) * (2 * L.sc.b) * (4 * szPol L)) := mul_le_mul hf a1 (by positivity) (by positivity)
  have a3 : (D.R.m : ℝ) * ((D.R.f : ℝ) * (((D.R.k : ℝ) + D.R.m) * (2 * L.sc.b) * L.La)) ≤
      szPol L * (szPol L * ((2 * szPol L) * (2 * L.sc.b) * (4 * szPol L))) := mul_le_mul hm a2 (by positivity) (by positivity)
  calc _ ≤ szPol L * (szPol L * ((2 * szPol L) * (2 * L.sc.b) * (4 * szPol L))) := a3
    _ = 16 * szPol L ^ 4 * L.sc.b := by ring

/- English proof (translation)
Rewrite using `[RecNums.ofNum_errB]`. Establish `hu` using `unitE_le_rec L Del h0`. Establish `hu0 : 0 ≤ (ofRecord D L Del h0).unitE L.Nc`. Use `one_le_unitE (ofRecord D L Del h0) (Nc_nonneg L)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hm` using `m_le L`. Establish `h1 : (0:ℝ) ≤ D.R.m` using `Nat.cast_nonneg _`. Establish `e : (ofRecord D L Del h0).sc.x ^ (ofRecord D L Del h0).sc.eps * ((ofRecord D L Del h0).B0 + L.Nc) = (ofRecord D L Del h0).unitE L.Nc` using `rfl`. Use `show ce * (D.R.m : ℝ) * ((ofRecord D L Del h0).sc.x ^ (ofRecord D L Del h0).sc.eps * ((ofRecord D L Del h0).B0 + L.Nc)) ≤ _`. Rewrite using `[e]`.

Establish `a : (D.R.m : ℝ) * (ofRecord D L Del h0).unitE L.Nc ≤ szPol L * (2 * szPol L ^ 4 * L.sc.b)` using `mul_le_mul hm hu hu0 (by linarith [one_le_szPol L])`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem errB_rec {J : Type} [Fintype J] (eJ : J ≃ Fin (ofRecord D L Del h0).R.m)
    (δ : Code (ofRecord D L Del h0)) (Tl : ℕ) (lam0 C0 ce Ch Sw C1 : ℝ)
    (H : (ofRecord D L Del h0).NumFacts δ L.Nc lam0 C0 ce Ch Sw C1) (hce : 0 ≤ ce) :
    (RecNums.ofNum (ofRecord D L Del h0) eJ δ Tl L.Nc lam0 C0 ce Ch Sw C1 H).errB ≤ 2 * ce * szPol L ^ 5 * L.sc.b := by
  rw [RecNums.ofNum_errB]
  have hu := unitE_le_rec L Del h0
  have hu0 : 0 ≤ (ofRecord D L Del h0).unitE L.Nc := by
    have := one_le_unitE (ofRecord D L Del h0) (Nc_nonneg L); linarith
  have hm := m_le L
  have h1 : (0:ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have e : (ofRecord D L Del h0).sc.x ^ (ofRecord D L Del h0).sc.eps * ((ofRecord D L Del h0).B0 + L.Nc) =
      (ofRecord D L Del h0).unitE L.Nc := rfl
  show ce * (D.R.m : ℝ) * ((ofRecord D L Del h0).sc.x ^ (ofRecord D L Del h0).sc.eps * ((ofRecord D L Del h0).B0 + L.Nc)) ≤ _
  rw [e]
  have a : (D.R.m : ℝ) * (ofRecord D L Del h0).unitE L.Nc ≤ szPol L * (2 * szPol L ^ 4 * L.sc.b) :=
    mul_le_mul hm hu hu0 (by linarith [one_le_szPol L])
  calc ce * (D.R.m : ℝ) * (ofRecord D L Del h0).unitE L.Nc = ce * ((D.R.m : ℝ) * (ofRecord D L Del h0).unitE L.Nc) := by ring
    _ ≤ ce * (szPol L * (2 * szPol L ^ 4 * L.sc.b)) := mul_le_mul_of_nonneg_left a hce
    _ = 2 * ce * szPol L ^ 5 * L.sc.b := by ring

/- English proof (translation)
Establish `h` using `Formalism.L2.DIV.Cons.log_card_le_unitE (G := G) L hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hS.2.2.2.2.2.1 0 0 L.Nc (Nc_nonneg L) hc`. Establish `hu` using `unitE_le_rec L 0 0`. Establish `hm` using `m_le L`. Establish `hu0 : 0 ≤ (ofRecord D L 0 0).unitE L.Nc`. Use `one_le_unitE (ofRecord D L 0 0) (Nc_nonneg L)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `a : (D.R.m : ℝ) * (ofRecord D L 0 0).unitE L.Nc ≤ szPol L * (2 * szPol L ^ 4 * L.sc.b)` using `mul_le_mul hm hu hu0 (by linarith [one_le_szPol L])`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem logG_rec (hS : SizesAt L) (hc : Fintype.card G = D.what₂.restRowsFiniteGroupCard) :
    Real.log (Fintype.card G : ℝ) ≤ 4 * szPol L ^ 5 * L.sc.b := by
  have h := Formalism.L2.DIV.Cons.log_card_le_unitE (G := G) L hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hS.2.2.2.2.2.1
    0 0 L.Nc (Nc_nonneg L) hc
  have hu := unitE_le_rec L 0 0
  have hm := m_le L
  have hu0 : 0 ≤ (ofRecord D L 0 0).unitE L.Nc := by
    have := one_le_unitE (ofRecord D L 0 0) (Nc_nonneg L); linarith
  have a : (D.R.m : ℝ) * (ofRecord D L 0 0).unitE L.Nc ≤ szPol L * (2 * szPol L ^ 4 * L.sc.b) :=
    mul_le_mul hm hu hu0 (by linarith [one_le_szPol L])
  calc _ ≤ 2 * ((D.R.m : ℝ) * (ofRecord D L 0 0).unitE L.Nc) := h
    _ ≤ 2 * (szPol L * (2 * szPol L ^ 4 * L.sc.b)) := by linarith
    _ = 4 * szPol L ^ 5 * L.sc.b := by ring

end Q

section QAll

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

/- English proof (translation)
Establish `hSG : SizeG L` using `hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1`. Establish `hP` using `one_le_szPol L`. Establish `hb` using `one_le_b L`. Establish `hP9b : 0 ≤ szPol L ^ 9 * L.sc.b`. Establish `: 0 ≤ szPol L ^ 9` using `pow_nonneg (by linarith) 9`.

Use the polynomial consequences of the given equalities and inequalities. Use `set K0 : ℝ := 272 + 2 * ce with hK0`. Establish `hKb` using `polyBound_mul_b_le_sq L hS K0 hx1 hx2`. Establish `hmain` using `main_rec L Del h0 hS eJ δ Tl L.Nc lam0 C0 ce Ch Sw C1 H`. Establish `hFo' : L.Fo ≤ 256 * szPol L ^ 9 * L.sc.b` using `Formalism.MainNotions.DIV.HookProducts.HookProductWeightBounds.fo_le_pol hFD hS (Formalism.MainNotions.G.Joints.Lit.mertens_bound _)`.

Establish `herr` using `errB_rec L Del h0 eJ δ Tl lam0 C0 ce Ch Sw C1 H hce0`. Establish `p4 : szPol L ^ 4 * L.sc.b ≤ szPol L ^ 9 * L.sc.b` using `poly_pow_mul_b_le_ninth (by norm_num)`. Establish `p5 : szPol L ^ 5 * L.sc.b ≤ szPol L ^ 9 * L.sc.b` using `poly_pow_mul_b_le_ninth (by norm_num)`. Use `⟨_, boundBR_le_closed hZ eJ δ Tl lam0 C0 ce Ch Sw C1 H Zs C CH P hC bd dg s c13 cG cD hbd hLam hdg hce, ?_⟩` and prove the remaining obligations. Use `hg_of_sizeG L Del h0 hSG hZ Zs C CH _ ?_ ?_ ?_ ?_` and prove the remaining obligations.

Rewrite using `[hFo]`. Establish `e1 : 16 * szPol L ^ 4 * L.sc.b ≤ 16 * (szPol L ^ 9 * L.sc.b)` using `by nlinarith`. Establish `e2 : 2 * ce * szPol L ^ 5 * L.sc.b ≤ 2 * ce * (szPol L ^ 9 * L.sc.b)`. Use `mul_le_mul_of_nonneg_left p5 (by linarith : 0 ≤ 2 * ce); nlinarith` as an intermediate fact. Establish `e3 : K0 * szPol L ^ 9 * L.sc.b = (272 + 2 * ce) * (szPol L ^ 9 * L.sc.b)` using `by rw [hK0]; ring`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h1 : L.sc.x ^ CH ≤ L.sc.x ^ (max CH 0)` using `Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (le_max_left _ _)`. Establish `h2` using `mul_rpow_le_b L (c := 1) (e := max CH 0) (le_max_right _ _) (by simpa using hx3)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h` using `logG_rec L hS hcard`.

Establish `e3 : K0 * szPol L ^ 9 * L.sc.b = (272 + 2 * ce) * (szPol L ^ 9 * L.sc.b)` using `by rw [hK0]; ring`. Use the polynomial consequences of the given equalities and inequalities. Establish `hf` using `f_le L`. Establish `ht` using `t_le L`. Establish `hrt : D.R.r + 5 ≤ D.R.t`.

Use `D.R.rank_add_five_le` as an intermediate fact. Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers. Establish `hr : (D.R.r : ℝ) ≤ szPol L` using `le_trans (by exact_mod_cast (by omega : D.R.r ≤ D.R.t)) ht`. Establish `h0f : (0:ℝ) ≤ D.R.f` using `Nat.cast_nonneg _`.

Establish `h0r : (0:ℝ) ≤ D.R.r` using `Nat.cast_nonneg _`. Establish `a1 : (D.R.f : ℝ) * D.R.r ≤ szPol L * szPol L` using `mul_le_mul hf hr h0r (by linarith)`. Establish `p2 : szPol L ^ 2 * L.sc.b ≤ szPol L ^ 9 * L.sc.b` using `poly_pow_mul_b_le_ninth (by norm_num)`. Establish `a2 : szPol L * szPol L ≤ szPol L ^ 2 * L.sc.b` using `by nlinarith`. Establish `e3 : K0 * szPol L ^ 9 * L.sc.b = (272 + 2 * ce) * (szPol L ^ 9 * L.sc.b)` using `by rw [hK0]; ring`.

Establish `hb2 : L.sc.b ^ 2 ≤ L.sc.b ^ 6` using `pow_le_pow_right₀ hb (by norm_num)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem q_rec (hS : SizesAt L) (hFD : L.FDef)
    {A3 : FamIn3 K G Pl0 I0 Ty T m} {eJz : A3.fam3.base3.J ≃ Fin (ofRecord D L Del h0).R.m}
    {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} (hZ : ClosedScale3 A3 (ofRecord D L Del h0) eJz L.Nc Zsc)
    (eJ : A3.fam3.base3.J ≃ Fin (ofRecord D L Del h0).R.m) (δ : Code (ofRecord D L Del h0)) (Tl : ℕ)
    (lam0 C0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts δ L.Nc lam0 C0 ce Ch Sw C1)
    (Zs : DefSub A3.fam3.amb3) (C CH : ℝ) {Df0 Df1 : DefSide A3.fam3.base3} {Dc : DefCols Df1} {Sp : SPer Dc}
    (P : IndefCoreR Df0 Df1 Dc Sp ((Zsc Zs).num C CH)) (hFo : 2 * FoOfR P = L.Fo)
    (hC : 0 ≤ C) (bd : A3.fam3.base3.J → ℝ) (dg s : ℕ) (c13 cG cD : ℝ)
    (hbd : ∀ j, bd j ≤ c13 * (ofRecord D L Del h0).unitE L.Nc)
    (hLam : lam0 + Real.log (s : ℝ) ≤ cG * (((ofRecord D L Del h0).R.m : ℝ) * (ofRecord D L Del h0).unitE L.Nc))
    (hdg : Real.log (dg : ℝ) + Real.log (s : ℝ) ≤ cD * (ofRecord D L Del h0).unitE L.Nc)
    (hce : C + cG + C + (c13 + cD) + 1 ≤ ce)
    (hcard : Fintype.card G = D.what₂.restRowsFiniteGroupCard) (hce0 : 0 ≤ ce)
    (hx1 : max 9 (272 + 2 * ce) ≤ L.sc.x)
    (hx2 : (Nat.factorial ⌈((9 : ℝ) * (max L.Ct 5 + 3) + 1 + 1) / L.sc.eps⌉₊ : ℝ) ≤ L.sc.x)
    (hx3 : (Nat.factorial ⌈(max CH 0 + 1) / L.sc.eps⌉₊ : ℝ) ≤ L.sc.x) :
    ∃ B : ℝ, boundBR P (lgDef (RecNums.ofNum (ofRecord D L Del h0) eJ δ Tl L.Nc lam0 C0 ce Ch Sw C1 H) s) 1
        (etaSumBound bd dg s) ≤ B ∧
      24 * ((ofRecord D L Del h0).R.f : ℝ) * ((ofRecord D L Del h0).R.r : ℝ) * QOfR B ((Zsc Zs).num C CH) ≤
        (((min ((ofRecord D L Del h0).g 0) ((ofRecord D L Del h0).g 1)) : ℕ) : ℝ) := by
  have hSG : SizeG L := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hP := one_le_szPol L
  have hb := one_le_b L
  have hP9b : 0 ≤ szPol L ^ 9 * L.sc.b := by
    have : 0 ≤ szPol L ^ 9 := pow_nonneg (by linarith) 9
    nlinarith
  set K0 : ℝ := 272 + 2 * ce with hK0
  have hKb := polyBound_mul_b_le_sq L hS K0 hx1 hx2

  have hmain := main_rec L Del h0 hS eJ δ Tl L.Nc lam0 C0 ce Ch Sw C1 H
  have hFo' : L.Fo ≤ 256 * szPol L ^ 9 * L.sc.b :=
    Formalism.MainNotions.DIV.HookProducts.HookProductWeightBounds.fo_le_pol hFD hS (Formalism.MainNotions.G.Joints.Lit.mertens_bound _)
  have herr := errB_rec L Del h0 eJ δ Tl lam0 C0 ce Ch Sw C1 H hce0
  have p4 : szPol L ^ 4 * L.sc.b ≤ szPol L ^ 9 * L.sc.b := poly_pow_mul_b_le_ninth (by norm_num)
  have p5 : szPol L ^ 5 * L.sc.b ≤ szPol L ^ 9 * L.sc.b := poly_pow_mul_b_le_ninth (by norm_num)
  refine ⟨_, boundBR_le_closed hZ eJ δ Tl lam0 C0 ce Ch Sw C1 H Zs C CH P hC bd dg s c13 cG cD hbd hLam hdg hce, ?_⟩
  refine hg_of_sizeG L Del h0 hSG hZ Zs C CH _ ?_ ?_ ?_ ?_
  ·
    rw [hFo]
    have e1 : 16 * szPol L ^ 4 * L.sc.b ≤ 16 * (szPol L ^ 9 * L.sc.b) := by nlinarith
    have e2 : 2 * ce * szPol L ^ 5 * L.sc.b ≤ 2 * ce * (szPol L ^ 9 * L.sc.b) := by
      have := mul_le_mul_of_nonneg_left p5 (by linarith : 0 ≤ 2 * ce); nlinarith
    have e3 : K0 * szPol L ^ 9 * L.sc.b = (272 + 2 * ce) * (szPol L ^ 9 * L.sc.b) := by rw [hK0]; ring
    nlinarith
  ·
    have h1 : L.sc.x ^ CH ≤ L.sc.x ^ (max CH 0) :=
      Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (le_max_left _ _)
    have h2 := mul_rpow_le_b L (c := 1) (e := max CH 0) (le_max_right _ _) (by simpa using hx3)
    linarith
  ·
    have h := logG_rec L hS hcard
    have e3 : K0 * szPol L ^ 9 * L.sc.b = (272 + 2 * ce) * (szPol L ^ 9 * L.sc.b) := by rw [hK0]; ring
    nlinarith
  ·
    have hf := f_le L
    have ht := t_le L
    have hrt : D.R.r + 5 ≤ D.R.t := by
      have := D.R.rank_add_five_le
      unfold Ranks.r
      omega
    have hr : (D.R.r : ℝ) ≤ szPol L := le_trans (by exact_mod_cast (by omega : D.R.r ≤ D.R.t)) ht
    have h0f : (0:ℝ) ≤ D.R.f := Nat.cast_nonneg _
    have h0r : (0:ℝ) ≤ D.R.r := Nat.cast_nonneg _
    have a1 : (D.R.f : ℝ) * D.R.r ≤ szPol L * szPol L := mul_le_mul hf hr h0r (by linarith)
    have p2 : szPol L ^ 2 * L.sc.b ≤ szPol L ^ 9 * L.sc.b := poly_pow_mul_b_le_ninth (by norm_num)
    have a2 : szPol L * szPol L ≤ szPol L ^ 2 * L.sc.b := by nlinarith
    have e3 : K0 * szPol L ^ 9 * L.sc.b = (272 + 2 * ce) * (szPol L ^ 9 * L.sc.b) := by rw [hK0]; ring
    have hb2 : L.sc.b ^ 2 ≤ L.sc.b ^ 6 := pow_le_pow_right₀ hb (by norm_num)
    nlinarith

end QAll

end Formalism.L2.DIV.Arith4S

end

noncomputable section

namespace Formalism.L2.DIV.Arith4S

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV

variable {D : D7} (L : SizeData₂ D) (Del h0 : ℕ)

/- English proof (translation)
Take `⟨c1, c2, c3, c4, c5⟩` from `nf_consts_rec L Del h0 P5 hS hx9 Ch C0 ce hCh hC0 hce`. Conclude with `numFacts_rows L Del h0 hDel hh0 P5 u hx3 L.Nc (Real.log (Fintype.card G)) C0 ce Ch (nf_logrd L Del h0 hS hB) (nf_logx L Del h0 hB) (cloudConstant_nonneg L) (size_le_two_b L Del h0 hS hB) (nf_Om L Del h0 hS hB) (nf_lam L Del h0 G hS hB hc) (logCardGroup_nonneg G) (rank_sq_le_b L D …`.
-/
theorem numFacts_rec (hS : SizesAt L) (hB : BigX L) (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ))
    (P5 : ParameterChoice' D L) (u : D.what₂.Word) (hx3 : 3 + |L.Cc| ≤ L.sc.x) (hx9 : 9 ≤ L.sc.x)
    (G : Type) [Group G] [Fintype G] (hc : Fintype.card G = D.what₂.restRowsFiniteGroupCard) (C0 ce Ch : ℝ) (hCh : 0 ≤ Ch)
    (hC0 : max 1 (Ch * (3 + 2 * P5.CYL + (max L.Ct 5 + 3))) ≤ C0) (hC1 : constantOneChoice L + 1 ≤ C0) (hce : C0 ≤ ce) :
    (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc (Real.log (Fintype.card G)) C0 ce Ch (swRec L) (constantOneChoice L) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := nf_consts_rec L Del h0 P5 hS hx9 Ch C0 ce hCh hC0 hce
  exact numFacts_rows L Del h0 hDel hh0 P5 u hx3 L.Nc (Real.log (Fintype.card G)) C0 ce Ch
    (nf_logrd L Del h0 hS hB) (nf_logx L Del h0 hB) (cloudConstant_nonneg L) (size_le_two_b L Del h0 hS hB) (nf_Om L Del h0 hS hB)
    (nf_lam L Del h0 G hS hB hc) (logCardGroup_nonneg G) (rank_sq_le_b L Del h0 hS hB) (cube_rank_sq_le_b L Del h0 hS hB) (nf_eta L Del h0 hS hh0)
    (nf_kN L Del h0 hS hB) (nf_kS L Del h0 hS hDel) (nf_blkW L Del h0 hS hh0) (nf_Nw L Del h0 hS hB) (nf_bN L Del h0 hS hB)
    (nf_mkb L Del h0 hS hB) c1 c2 c3 c4 c5 hC1

end Formalism.L2.DIV.Arith4S

end

noncomputable section

namespace Formalism.L2.DIV.Arith4S

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
open NumberField IsDedekindDomain

variable {D : D7} (L : SizeData₂ D) (Del h0 : ℕ)

/- English proof (translation)
Establish `hx9 : 9 ≤ L.sc.x` using `(le_max_left _ _).trans hx`. Establish `H` using `numFacts_rec L Del h0 hS hB hDel hh0 P5 u hx3 hx9 G hc C0 ce Ch hCh hC0 hC1 hce0`. Establish `hZ` using `closedScale3_fix A3 P0 ψ0 (ofRecord D L Del h0) eJz L.Nc Ch`. Establish `hbd : ∀ j : Fin m, (fun _ : Fin m => divSize L Ce) j ≤ Ce * (ofRecord D L Del h0).unitE L.Nc` using `fun _ => le_of_eq (divSize_eq_unitE L Del h0 Ce)`. Establish `hLam : Real.log (Fintype.card G) + Real.log ((1 : ℕ) : ℝ) ≤ 2 * (((ofRecord D L Del h0).R.m : ℝ) * (ofRecord D L Del h0).unitE L.Nc)` using `Formalism.L2.DIV.Cons.lamSizeAt_record_one (G := G) L hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hS.2.2.2.2.2.1 Del h0 L.Nc (cloudConstant_nonneg L) hc`.

Establish `hce' : C + 2 + C + (Ce + cD) + 1 ≤ ce` using `hce`. Establish `hce0' : 0 ≤ ce` using `by linarith`. Establish `hFo : 2 * FoOfR Pk.core = L.Fo` using `two_FoOfR_eq_Fo L Pk.core eJz (fixedScale_tied L Del h0 hK hFD A3 P0 ψ0 eJz L.Nc Ch Pk.Zs C CH)`. Take `⟨B, hBB, hg⟩` from `q_rec L Del h0 hS hFD hZ eJz (letterOf D L Del h0 u) ((D.mem u).A.T) (Real.log (Fintype.card G)) C0 ce Ch (swRec L) (constantOneChoice L) H Pk.Zs C CH Pk.core hFo hC (fun _ => divSize L Ce) dg 1 Ce 2 cD hbd hLam hdg hce' hc hce0' hx hx1 hx2`. Conclude with `arithmetic_fixed_scale A3 1 P0 ψ0 P1 ψ1 Dc Sp (ofRecord D L Del h0) eJz L.Nc cf C CH eJz (letterOf D L Del h0 u) ((D.mem u).A.T) (Real.log (Fintype.card G)) C0 ce Ch (swRec L) (constantOneChoice L) H Pk (fun _ => divSize L Ce) dg hC h28 le_rfl Ce 2 cD hbd hLam hdg hce' B hBB hg`.
-/
theorem arithAt_rec (hS : SizesAt L) (hB : BigX L) (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ))
    (P5 : ParameterChoice' D L) (hFD : L.FDef) (hK : DV.KapDef D) (u : D.what₂.Word) (hx3 : 3 + |L.Cc| ≤ L.sc.x)
    {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ} (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m)
    (hc : Fintype.card G = D.what₂.restRowsFiniteGroupCard) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* D.what₂.LLˣ) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
    (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (eJz : A3.fam3.base3.J ≃ Fin D.R.m) (cf : ConvFace A3.fam3.base3)
    (C CH Ch C0 ce Ce : ℝ)
    (Pk : IndefPkgR A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp (ZscFix3 A3 P0 ψ0 (ofRecord D L Del h0) eJz L.Nc Ch))
      cf C CH)
    (dg : ℕ) (cD : ℝ) (hdg : Real.log (dg : ℝ) + Real.log ((1 : ℕ) : ℝ) ≤ cD * (ofRecord D L Del h0).unitE L.Nc)
    (hC : 0 ≤ C) (hCh : 0 ≤ Ch) (h28 : 28 ≤ C0) (hC1 : constantOneChoice L + 1 ≤ C0)
    (hC0 : max 1 (Ch * (3 + 2 * P5.CYL + (max L.Ct 5 + 3))) ≤ C0) (hce0 : C0 ≤ ce)
    (hce : C + 2 + C + (Ce + cD) + 1 ≤ ce)
    (hx : max 9 (272 + 2 * ce) ≤ L.sc.x)
    (hx1 : (⌈(9 * (max L.Ct 5 + 3) + 1 + 1) / L.sc.eps⌉₊.factorial : ℝ) ≤ L.sc.x)
    (hx2 : (⌈(max CH 0 + 1) / L.sc.eps⌉₊.factorial : ℝ) ≤ L.sc.x) :
    ArithAt A3 1 P0 ψ0 P1 ψ1 Dc Sp (ZscFix3 A3 P0 ψ0 (ofRecord D L Del h0) eJz L.Nc Ch) cf C CH Pk
      (RecNums.ofNum (ofRecord D L Del h0) eJz (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc (Real.log (Fintype.card G))
        C0 ce Ch (swRec L) (constantOneChoice L)
        (numFacts_rec L Del h0 hS hB hDel hh0 P5 u hx3 ((le_max_left _ _).trans hx) G hc C0 ce Ch hCh hC0 hC1 hce0))
      (fun _ => divSize L Ce) dg := by
  have hx9 : 9 ≤ L.sc.x := (le_max_left _ _).trans hx
  have H := numFacts_rec L Del h0 hS hB hDel hh0 P5 u hx3 hx9 G hc C0 ce Ch hCh hC0 hC1 hce0
  have hZ := closedScale3_fix A3 P0 ψ0 (ofRecord D L Del h0) eJz L.Nc Ch
  have hbd : ∀ j : Fin m, (fun _ : Fin m => divSize L Ce) j ≤ Ce * (ofRecord D L Del h0).unitE L.Nc :=
    fun _ => le_of_eq (divSize_eq_unitE L Del h0 Ce)
  have hLam : Real.log (Fintype.card G) + Real.log ((1 : ℕ) : ℝ) ≤
      2 * (((ofRecord D L Del h0).R.m : ℝ) * (ofRecord D L Del h0).unitE L.Nc) :=
    Formalism.L2.DIV.Cons.lamSizeAt_record_one (G := G) L hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hS.2.2.2.2.2.1 Del h0 L.Nc
      (cloudConstant_nonneg L) hc
  have hce' : C + 2 + C + (Ce + cD) + 1 ≤ ce := hce
  have hce0' : 0 ≤ ce := by linarith
  have hFo : 2 * FoOfR Pk.core = L.Fo :=
    two_FoOfR_eq_Fo L Pk.core eJz (fixedScale_tied L Del h0 hK hFD A3 P0 ψ0 eJz L.Nc Ch Pk.Zs C CH)
  obtain ⟨B, hBB, hg⟩ := q_rec L Del h0 hS hFD hZ eJz (letterOf D L Del h0 u) ((D.mem u).A.T) (Real.log (Fintype.card G))
    C0 ce Ch (swRec L) (constantOneChoice L) H Pk.Zs C CH Pk.core hFo hC (fun _ => divSize L Ce) dg 1 Ce 2 cD hbd hLam hdg hce' hc
    hce0' hx hx1 hx2
  exact arithmetic_fixed_scale A3 1 P0 ψ0 P1 ψ1 Dc Sp (ofRecord D L Del h0) eJz L.Nc cf C CH eJz (letterOf D L Del h0 u)
    ((D.mem u).A.T) (Real.log (Fintype.card G)) C0 ce Ch (swRec L) (constantOneChoice L) H Pk (fun _ => divSize L Ce) dg hC h28
    le_rfl Ce 2 cD hbd hLam hdg hce' B hBB hg

end Formalism.L2.DIV.Arith4S

end
