import Formalism.GaussJetBounds.OneLetterRadius
import Formalism.GaussJetBounds.StatementG

noncomputable section
open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

/- English proof (translation)
Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hl.one_lt`. Establish `hpi0 : 0 < ‖(l : K)‖` using `norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)`. Use `set L : ℝ := Real.logb l (a : ℝ) + 1 with hL`. Establish `hL0 : 0 ≤ L`. Establish `: 0 ≤ Real.logb l (a : ℝ)` using `Real.logb_nonneg hl1 (by exact_mod_cast ha)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcoord : ∀ i ∈ κ.support, ‖(((κ i).factorial : ℕ) : K)‖ ≤ ‖(l : K)‖ ^ ((κ i : ℝ) / ((l : ℝ) - 1) - L)`. Introduce `i hi`. Establish `hki : 1 ≤ κ i` using `Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)`. Establish `hb` using `(Formalism.IncomingBounds.padicValFactorialBounds l hl (κ i) hki).1`.

Establish `hlog : Real.logb l (κ i : ℝ) ≤ Real.logb l (a : ℝ)` using `Real.logb_le_logb_of_le hl1 (by exact_mod_cast hki) (by exact_mod_cast hκa i)`. Rewrite using `[norm_natCast_eq_pow_padicValNat hl hlt (Nat.factorial_ne_zero _), ← Real.rpow_natCast]`. Conclude with `Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le (by rw [hL]; linarith)`. Establish `hmf : ((mfact κ : ℕ) : K) = ∏ i ∈ κ.support, (((κ i).factorial : ℕ) : K)`. Rewrite using `[mfact, Finsupp.prod, Nat.cast_prod]`.

Rewrite using `[hmf, norm_prod]`. Combine the equalities or inequalities in the displayed calculation. Apply `Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le` to reduce the goal to its premises. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]`. Establish `hsum : ∑ i ∈ κ.support, (κ i : ℝ) / ((l : ℝ) - 1) = ∑ i, (κ i : ℝ) / ((l : ℝ) - 1)`.

Apply `Finset.sum_subset (Finset.subset_univ _)` to reduce the goal to its premises. Introduce `i _ hi`. Rewrite using `[Finsupp.notMem_support_iff.mp hi]`. Simplify using the standard rewrite rules. Establish `hcard : (κ.support.card : ℝ) ≤ (Fintype.card ι : ℝ)`.

Conclude with `Finset.card_le_univ _` after adjusting the coercions. Rewrite using `[hsum]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem factValA {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ}
    (hl : l.Prime) (hlt : ‖(l : K)‖ < 1) {ι : Type v} [Fintype ι] (κ : ι →₀ ℕ) {a : ℕ}
    (ha : 1 ≤ a) (hκa : ∀ i, κ i ≤ a) :
    ‖((mfact κ : ℕ) : K)‖ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) -
        (Fintype.card ι : ℝ) * (Real.logb l (a : ℝ) + 1)) := by
  classical
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  set L : ℝ := Real.logb l (a : ℝ) + 1 with hL
  have hL0 : 0 ≤ L := by
    have : 0 ≤ Real.logb l (a : ℝ) := Real.logb_nonneg hl1 (by exact_mod_cast ha)
    linarith
  have hcoord : ∀ i ∈ κ.support, ‖(((κ i).factorial : ℕ) : K)‖ ≤
      ‖(l : K)‖ ^ ((κ i : ℝ) / ((l : ℝ) - 1) - L) := by
    intro i hi
    have hki : 1 ≤ κ i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    have hb := (Formalism.IncomingBounds.padicValFactorialBounds l hl (κ i) hki).1
    have hlog : Real.logb l (κ i : ℝ) ≤ Real.logb l (a : ℝ) :=
      Real.logb_le_logb_of_le hl1 (by exact_mod_cast hki) (by exact_mod_cast hκa i)
    rw [norm_natCast_eq_pow_padicValNat hl hlt (Nat.factorial_ne_zero _), ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le (by rw [hL]; linarith)
  have hmf : ((mfact κ : ℕ) : K) = ∏ i ∈ κ.support, (((κ i).factorial : ℕ) : K) := by
    rw [mfact, Finsupp.prod, Nat.cast_prod]
  rw [hmf, norm_prod]
  calc ∏ i ∈ κ.support, ‖(((κ i).factorial : ℕ) : K)‖
      ≤ ∏ i ∈ κ.support, ‖(l : K)‖ ^ ((κ i : ℝ) / ((l : ℝ) - 1) - L) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) hcoord
    _ = ‖(l : K)‖ ^ (∑ i ∈ κ.support, ((κ i : ℝ) / ((l : ℝ) - 1) - L)) :=
        (Real.rpow_sum_of_pos hpi0 _ _).symm
    _ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) - (Fintype.card ι : ℝ) * L) := by
        apply Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        have hsum : ∑ i ∈ κ.support, (κ i : ℝ) / ((l : ℝ) - 1) =
            ∑ i, (κ i : ℝ) / ((l : ℝ) - 1) := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi
          rw [Finsupp.notMem_support_iff.mp hi]; simp
        have hcard : (κ.support.card : ℝ) ≤ (Fintype.card ι : ℝ) := by
          exact_mod_cast Finset.card_le_univ _
        rw [hsum]
        nlinarith

/- English proof (translation)
Introduce `K _ _ _ l d N0 N1 _ hl hodd hd hde hpi K0 hK0 ζ hζ be hbe ι _ _ lt M hM1 hMlt g hg0 hg U hU ε hε sig hsig κ a ha hκa hκ`. Establish `hl2 : (2 : ℝ) ≤ l` using `by exact_mod_cast hl.two_le`. Establish `h0 : 0 < ‖(l : K)‖` using `norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)`. Establish `h1 : ‖(l : K)‖ ≤ 1` using `hpi.le`. Establish `hrho : 0 ≤ rho l`.

Unfold `rho`. Apply `div_nonneg zero_le_one` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `hrg : gam l = 1 / ((l : ℝ) - 1) - rho l`. Establish `ha : (l : ℝ) - 1 ≠ 0` using `by linarith`.

Establish `hb : (l : ℝ) ^ 2 - 1 ≠ 0` using `by nlinarith`. Unfold `gam rho`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨hS1, hS2⟩` from `hS K l d hl hodd hd hde hpi K0 hK0 ζ hζ be hbe`.

Establish `hbe0 : MvPowerSeries.constantCoeff be = 0`. Assume the negation of the conclusion as `h`. Establish `h' : MvPowerSeries.coeff 0 be ≠ 0`. Rewrite using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply]` and apply the resulting hypothesis. Use `(hbe.2.2.1 0 h').1` as an intermediate fact.

Simplify using `[degE] at this`. Take `⟨hP1, hP2⟩` from `hP K l d N0 N1 hl hpi ι M hM1 be hbe0 hS1 hS2`. Establish `hlin0 : ∀ x, MvPowerSeries.constantCoeff (linSub M x) = 0`. Introduce `x`. Simplify using `[linSub]`.

Establish `hbS0 : MvPowerSeries.constantCoeff (bSum M be) = 0`. Unfold `bSum`. Rewrite using `[map_sum]`. Use `Finset.sum_eq_zero fun ab _ => ?_` and prove the remaining obligations. Conclude with `MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => hlin0 _) (fun s => hlin0 _) hbe0`.

Establish `hr : ∀ i, (fun _ : ι => rho l) i ≤ (fun i => rho l + sig i) i` using `fun i => by`. Simplify using `only`. Combine the linear relations using `[hsig i]`. Establish `hBw : WtGeLe ‖(l : K)‖ (fun i => rho l + sig i) (1 / ((l : ℝ) - 1)) κ (ε • bSum M be)`. Introduce `n hn`.

Apply the tactic sequence `have hεn : ‖ε‖ = 1 := by rcases hε with h | h <;> simp [h]`. Establish `hc : MvPowerSeries.coeff n (ε • bSum M be) = ε * MvPowerSeries.coeff n (bSum M be)`. Rewrite using `[map_smul, smul_eq_mul]`. Rewrite using `[monoWtGe_iff, hc, norm_mul, hεn, one_mul]`. Distinguish the cases in `hp : ∃ (i j : ι) (α β : ℕ), n = pureMon l i j α β`.

Take `⟨i, j, α, β, rfl⟩` from `hp`. Distinguish the cases in `hw : MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β) (MvPowerSeries.coeff (pureMon l i j α β) (bSum M be))`. Conclude with `asmR_monoWtGe_rad h0 h1 hr hw`. Establish `hs1` using `hκ i j α β hn hw`. Establish `hlow` using `hP1 (pureMon l i j α β)`.

Rewrite `hlow` using `[monoWtGe_iff]`. Use `le_trans hlow (Real.rpow_le_rpow_of_exponent_ge h0 h1 ?_)` and prove the remaining obligations. Rewrite using `[asmR_dot_add_right, asmR_dot_pureMon l i j α β sig]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `asmR_monoWtGe_rad h0 h1 hr (hP2 n hp)`.

Establish `hBc : MvPowerSeries.constantCoeff (ε • bSum M be) = 0`. Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_smul, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hbS0, smul_zero]`. Establish `hExp` using `hE K l hl hpi ι (fun i => rho l + sig i) κ (ε • bSum M be) hBc hBw`. Establish `hU0 : WtGe ‖(l : K)‖ (fun _ : ZV d N0 N1 => rho l) 0 U`. Introduce `n`.

Rewrite using `[monoWtGe_iff]`. Use `le_trans (hU n) (Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 ?_)` and prove the remaining obligations. Combine the linear relations using `[asmR_dot_nonneg n (r := fun _ : ZV d N0 N1 => rho l) fun _ => hrho]`. Establish `hg' : ∀ x, MvPowerSeries.subst g (genLog (K` using `K) l (fun y : ZV d N0 N1 => (y.1 - 2, y.2.1, y.2.2)) x) = MvPowerSeries.X x := by`. Introduce `x`.

Rewrite using `[← (hB K l d N0 N1).2.1 x]`. Conclude with `hg x`. Establish `hgw` using `hG K l hl hpi (ZV d N0 N1) (fun y : ZV d N0 N1 => (y.1 - 2, y.2.1, y.2.2)) g hg0 hg'`. Establish `hgU : WtGe ‖(l : K)‖ (fun _ : ZV d N0 N1 => rho l) 0 (MvPowerSeries.subst g U)` using `hW0 K ‖(l : K)‖ h0 hpi (ZV d N0 N1) (ZV d N0 N1) g (fun _ => rho l) (fun _ => rho l) 0 U hg0 hgw hU0`. Establish `hlinw : ∀ x, WtGe ‖(l : K)‖ (fun _ : ι => rho l) (rho l) (linSub M x)`.

Introduce `x n`. Rewrite using `[monoWtGe_iff]`. Simplify using `only [linSub, map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _) fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with h`.

Substitute `h` using the available equality. Rewrite using `[mul_one, asmR_dot_single]`. Simplify using `using hM1 x i`. Simplify using `using Real.rpow_nonneg h0.le _`. Establish `hY : WtGe ‖(l : K)‖ (fun _ : ι => rho l) 0 (MvPowerSeries.subst (linSub M) (MvPowerSeries.subst g U))` using `hW1 K ‖(l : K)‖ h0 hpi (ZV d N0 N1) ι (linSub M) (fun _ => rho l) (fun _ => rho l) 0 _ hlin0 hlinw hgU`.

Establish `hY1 : WtGeLe ‖(l : K)‖ (fun i => rho l + sig i) 0 κ (MvPowerSeries.subst (linSub M) (MvPowerSeries.subst g U))` using `(hRM K ‖(l : K)‖ h0 hpi ι (fun _ => rho l) (fun i => rho l + sig i) 0 hr).2 κ _ fun n _ => hY n`. Establish `hk` using `hMW K ‖(l : K)‖ h0 ι (fun i => rho l + sig i) 0 0 κ _ _ hY1 hExp κ le_rfl`. Rewrite `hk` using `[monoWtGe_iff]`. Establish `hf` using `factValA (K := K) hl hpi κ ha hκa`. Rewrite using `[norm_mul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_add h0]`. Use `congr 1`. Rewrite using `[asmR_dot_fintype, hrg]`. Establish `key : ∑ i, (κ i : ℝ) * (1 / ((l : ℝ) - 1) - rho l - sig i) = (∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) - ∑ i, (κ i : ℝ) * (rho l + sig i)`.

Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lemmaRA_of (hS : LemmaS.{u}) (hG : GenLogWeight.{u, 0}) (hB : LogBridges.{u})
    (hW1 : SubstWt.{u, 0, v}) (hW0 : SubstWt.{u, 0, 0}) (hRM : RadMono.{u, v})
    (hMW : MulWtLe.{u, v}) (hE : ExpWtLe.{u, v})
    (hP : PureCross.{u, v}) : LemmaRA.{u, v} := by
  intro K _ _ _ l d N0 N1 _ hl hodd hd hde hpi K0 hK0 ζ hζ be hbe ι _ _ lt M hM1 hMlt g hg0 hg
    U hU ε hε sig hsig κ a ha hκa hκ
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have h0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  have h1 : ‖(l : K)‖ ≤ 1 := hpi.le
  have hrho : 0 ≤ rho l := by
    unfold rho
    apply div_nonneg zero_le_one
    nlinarith
  have hrg : gam l = 1 / ((l : ℝ) - 1) - rho l := by
    have ha : (l : ℝ) - 1 ≠ 0 := by linarith
    have hb : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    unfold gam rho
    field_simp
    ring
  obtain ⟨hS1, hS2⟩ := hS K l d hl hodd hd hde hpi K0 hK0 ζ hζ be hbe
  have hbe0 : MvPowerSeries.constantCoeff be = 0 := by
    by_contra h
    have h' : MvPowerSeries.coeff 0 be ≠ 0 := by
      rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    have := (hbe.2.2.1 0 h').1
    simp [degE] at this
  obtain ⟨hP1, hP2⟩ := hP K l d N0 N1 hl hpi ι M hM1 be hbe0 hS1 hS2
  have hlin0 : ∀ x, MvPowerSeries.constantCoeff (linSub M x) = 0 := by
    intro x
    simp [linSub]
  have hbS0 : MvPowerSeries.constantCoeff (bSum M be) = 0 := by
    unfold bSum
    rw [map_sum]
    refine Finset.sum_eq_zero fun ab _ => ?_
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => hlin0 _) (fun s => hlin0 _) hbe0
  have hr : ∀ i, (fun _ : ι => rho l) i ≤ (fun i => rho l + sig i) i := fun i => by
    simp only
    linarith [hsig i]

  have hBw : WtGeLe ‖(l : K)‖ (fun i => rho l + sig i) (1 / ((l : ℝ) - 1)) κ
      (ε • bSum M be) := by
    intro n hn
    have hεn : ‖ε‖ = 1 := by rcases hε with h | h <;> simp [h]
    have hc : MvPowerSeries.coeff n (ε • bSum M be) = ε * MvPowerSeries.coeff n (bSum M be) := by
      rw [map_smul, smul_eq_mul]
    rw [monoWtGe_iff, hc, norm_mul, hεn, one_mul]
    by_cases hp : ∃ (i j : ι) (α β : ℕ), n = pureMon l i j α β
    · obtain ⟨i, j, α, β, rfl⟩ := hp
      by_cases hw : MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
          (MvPowerSeries.coeff (pureMon l i j α β) (bSum M be))
      · exact asmR_monoWtGe_rad h0 h1 hr hw
      · have hs1 := hκ i j α β hn hw
        have hlow := hP1 (pureMon l i j α β)
        rw [monoWtGe_iff] at hlow
        refine le_trans hlow (Real.rpow_le_rpow_of_exponent_ge h0 h1 ?_)
        rw [asmR_dot_add_right, asmR_dot_pureMon l i j α β sig]
        linarith
    · exact asmR_monoWtGe_rad h0 h1 hr (hP2 n hp)
  have hBc : MvPowerSeries.constantCoeff (ε • bSum M be) = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_smul,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hbS0, smul_zero]
  have hExp := hE K l hl hpi ι (fun i => rho l + sig i) κ (ε • bSum M be) hBc hBw

  have hU0 : WtGe ‖(l : K)‖ (fun _ : ZV d N0 N1 => rho l) 0 U := by
    intro n
    rw [monoWtGe_iff]
    refine le_trans (hU n) (Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 ?_)
    linarith [asmR_dot_nonneg n (r := fun _ : ZV d N0 N1 => rho l) fun _ => hrho]
  have hg' : ∀ x, MvPowerSeries.subst g (genLog (K := K) l
      (fun y : ZV d N0 N1 => (y.1 - 2, y.2.1, y.2.2)) x) = MvPowerSeries.X x := by
    intro x
    rw [← (hB K l d N0 N1).2.1 x]
    exact hg x
  have hgw := hG K l hl hpi (ZV d N0 N1) (fun y : ZV d N0 N1 => (y.1 - 2, y.2.1, y.2.2)) g hg0 hg'
  have hgU : WtGe ‖(l : K)‖ (fun _ : ZV d N0 N1 => rho l) 0 (MvPowerSeries.subst g U) :=
    hW0 K ‖(l : K)‖ h0 hpi (ZV d N0 N1) (ZV d N0 N1) g (fun _ => rho l) (fun _ => rho l) 0 U
      hg0 hgw hU0
  have hlinw : ∀ x, WtGe ‖(l : K)‖ (fun _ : ι => rho l) (rho l) (linSub M x) := by
    intro x n
    rw [monoWtGe_iff]
    simp only [linSub, map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _)
      fun i _ => ?_
    split_ifs with h
    · subst h
      rw [mul_one, asmR_dot_single]
      simpa using hM1 x i
    · simpa using Real.rpow_nonneg h0.le _
  have hY : WtGe ‖(l : K)‖ (fun _ : ι => rho l) 0
      (MvPowerSeries.subst (linSub M) (MvPowerSeries.subst g U)) :=
    hW1 K ‖(l : K)‖ h0 hpi (ZV d N0 N1) ι (linSub M) (fun _ => rho l) (fun _ => rho l) 0 _
      hlin0 hlinw hgU
  have hY1 : WtGeLe ‖(l : K)‖ (fun i => rho l + sig i) 0 κ
      (MvPowerSeries.subst (linSub M) (MvPowerSeries.subst g U)) :=
    (hRM K ‖(l : K)‖ h0 hpi ι (fun _ => rho l) (fun i => rho l + sig i) 0 hr).2 κ _
      fun n _ => hY n
  have hk := hMW K ‖(l : K)‖ h0 ι (fun i => rho l + sig i) 0 0 κ _ _ hY1 hExp κ le_rfl
  rw [monoWtGe_iff] at hk
  have hf := factValA (K := K) hl hpi κ ha hκa
  rw [norm_mul]
  calc _ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) -
          (Fintype.card ι : ℝ) * (Real.logb l (a : ℝ) + 1)) *
        ‖(l : K)‖ ^ (0 + 0 - dot κ (fun i => rho l + sig i)) :=
        mul_le_mul hf hk (norm_nonneg _) (Real.rpow_nonneg h0.le _)
    _ = _ := by
      rw [← Real.rpow_add h0]
      congr 1
      rw [asmR_dot_fintype, hrg]
      have key : ∑ i, (κ i : ℝ) * (1 / ((l : ℝ) - 1) - rho l - sig i) =
          (∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) - ∑ i, (κ i : ℝ) * (rho l + sig i) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      linarith

/- English proof (translation)
The claim follows from `lemmaRA_of lemmaS generalized_log_weight logarithm_weight_comparison substitution_weight_bound substitution_weight_bound radical_weight_monotone multiplicative_weight_le exponential_weight_le pure_cross_term_weight`.
-/
theorem lemma_R_log_loss : LemmaRA.{u, v} :=
  lemmaRA_of lemmaS generalized_log_weight logarithm_weight_comparison substitution_weight_bound substitution_weight_bound radical_weight_monotone
    multiplicative_weight_le exponential_weight_le pure_cross_term_weight

end Formalism.DworkPowerSeriesWeights
