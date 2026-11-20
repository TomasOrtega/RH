import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeWeightFormula
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Establish `h0 : 0 ≤ ⨆ k : Ψ × Fin N, |lam k.1 k.2|` using `Real.iSup_nonneg fun _ => abs_nonneg _`. Use `(pi_norm_le_iff_of_nonneg h0).2 fun τ => (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs]`. Conclude with `le_ciSup (f := fun k : Ψ × Fin N => |lam k.1 k.2|) (Set.finite_range _).bddAbove (τ, i)`.

Use `Real.iSup_le (fun k => ?_) (norm_nonneg _)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_wt_eq_iSup {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam : Top.Wt Ψ N) :
    ‖lam‖ = ⨆ k : Ψ × Fin N, |lam k.1 k.2| := by
  apply le_antisymm
  · have h0 : 0 ≤ ⨆ k : Ψ × Fin N, |lam k.1 k.2| := Real.iSup_nonneg fun _ => abs_nonneg _
    refine (pi_norm_le_iff_of_nonneg h0).2 fun τ => (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact le_ciSup (f := fun k : Ψ × Fin N => |lam k.1 k.2|) (Set.finite_range _).bddAbove (τ, i)
  · refine Real.iSup_le (fun k => ?_) (norm_nonneg _)
    calc |lam k.1 k.2| = ‖lam k.1 k.2‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖lam k.1‖ := norm_le_pi_norm _ _
      _ ≤ ‖lam‖ := norm_le_pi_norm _ _

/- English proof (translation)
Rewrite using `[(Top.flagDeg_eq_weyl Ψ N lam).1, mul_assoc, GlobalTheory.CompHt.vdm, ← Finset.prod_mul_distrib]`. Use `congr 1`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `hI : Finset.Ioi i = Finset.univ.filter (fun k => i < k)` using `by ext; simp`. Rewrite using `[hI, Finset.prod_filter, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[div_eq_inv_mul]`.

Simplify using the standard rewrite rules.
-/
theorem flagDeg_eq_const_mul_vdm {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (lam : Top.Wt Ψ N) :
    Top.flagDeg lam = (((Top.dimFl Ψ N).factorial : ℝ) *
      ∏ _τ : Ψ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then ((k : ℝ) - (i : ℝ))⁻¹ else 1)) *
        GlobalTheory.CompHt.vdm lam := by
  rw [(Top.flagDeg_eq_weyl Ψ N lam).1, mul_assoc, GlobalTheory.CompHt.vdm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hI : Finset.Ioi i = Finset.univ.filter (fun k => i < k) := by ext; simp
  rw [hI, Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs
  · rw [div_eq_inv_mul]
  · simp

/- English proof (translation)
Rewrite using `[flagDeg_eq_const_mul_vdm lam, flagDeg_eq_const_mul_vdm mu]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem flagDeg_mul_vdm {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (lam mu : Top.Wt Ψ N) :
    Top.flagDeg lam * GlobalTheory.CompHt.vdm mu = Top.flagDeg mu * GlobalTheory.CompHt.vdm lam := by
  rw [flagDeg_eq_const_mul_vdm lam, flagDeg_eq_const_mul_vdm mu]
  ring

/- English proof (translation)
Take `rfl` from `Subsingleton.elim i₁ i₂`. Simplify using `[GlobalTheory.CompHt.vdm]`.
-/
theorem vdm_cast {ι : Type} (i₁ i₂ : Fintype ι) {N : ℕ} (w : ι → Fin N → ℤ) :
    ((@GlobalTheory.CompHt.vdm ι i₁ N ℤ _ w : ℤ) : ℝ) = @GlobalTheory.CompHt.vdm ι i₂ N ℝ _ fun τ i => (w τ i : ℝ) := by
  obtain rfl := Subsingleton.elim i₁ i₂
  simp [GlobalTheory.CompHt.vdm]

section Entries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

/- English proof (translation)
Use function extensionality and compare the values at `τ n`. Simplify using `only [towerWt, reW]`. Use `split_ifs with hn`. Rewrite using `[GlobalTheory.AllWt.wtOf_big (Dw := Dw) u 0 τ n hn]`. Simplify using the standard rewrite rules.

Establish `hn'` using `n.isLt`. Establish `hq : Dw.p + Dw.q - 1 - (n : ℕ) < Dw.q` using `by omega`. Rewrite using `[GlobalTheory.AllWt.wtOf_small (Dw := Dw) u 0 τ _ hq]`. Establish `hf : (⟨Dw.p + (Dw.q - 1 - (Dw.p + Dw.q - 1 - (n : ℕ))), by omega⟩ : Fin (Dw.p + Dw.q)) = n` using `Fin.ext (by simp only; omega)`. Rewrite using `[hf]`.

Simplify using the standard rewrite rules.
-/
theorem towerWt_wtOf (Dw : Datum H) (u : GlobalTheory.AllWt.Weight Dw) :
    towerWt Dw (GlobalTheory.AllWt.wtOf Dw u 0).1 = reW u := by
  funext τ n
  simp only [towerWt, reW]
  split_ifs with hn
  · rw [GlobalTheory.AllWt.wtOf_big (Dw := Dw) u 0 τ n hn]
    simp
  · have hn' := n.isLt
    have hq : Dw.p + Dw.q - 1 - (n : ℕ) < Dw.q := by omega
    rw [GlobalTheory.AllWt.wtOf_small (Dw := Dw) u 0 τ _ hq]
    have hf : (⟨Dw.p + (Dw.q - 1 - (Dw.p + Dw.q - 1 - (n : ℕ))), by omega⟩ : Fin (Dw.p + Dw.q)) = n :=
      Fin.ext (by simp only; omega)
    rw [hf]
    simp

/- English proof (translation)
Establish `h1 : Dw.p - 1 < Dw.p + Dw.q` using `by omega`. Establish `h2 : Dw.p < Dw.p + Dw.q` using `by omega`. Simplify using `only [Top.gap, Top.ent, dif_pos h1, dif_pos h2, reW]`.
-/
theorem gap_reW {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (τ : CMType H) (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) :
    Top.gap Dw.p (reW u) τ = (u τ ⟨Dw.p - 1, by omega⟩ : ℝ) - u τ ⟨Dw.p, by omega⟩ := by
  have h1 : Dw.p - 1 < Dw.p + Dw.q := by omega
  have h2 : Dw.p < Dw.p + Dw.q := by omega
  simp only [Top.gap, Top.ent, dif_pos h1, dif_pos h2, reW]

/- English proof (translation)
Introduce `τ _ _ hab` and use `by simp only [reW] exact_mod_cast h τ hab`.
-/
theorem regDominant_reW {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (h : ∀ τ, StrictAnti (u τ)) :
    Top.RegDominant (reW u) := fun τ _ _ hab => by
  simp only [reW]
  exact_mod_cast h τ hab

/- English proof (translation)
Use `⟨one_pos, regDominant_reW u h, fun τ => ?_, fun τ a b _ hab => ?_⟩` and prove the remaining obligations. Rewrite using `[gap_reW u τ hp hq]`. Establish `hlt : (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) < ⟨Dw.p, by omega⟩` using `Fin.mk_lt_mk.2 (by omega)`. Establish `h1` using `h τ hlt`. Establish `h2 : u τ ⟨Dw.p, by omega⟩ + 1 ≤ u τ ⟨Dw.p - 1, by omega⟩` using `h1`.

Establish `h3 : ((u τ ⟨Dw.p, by omega⟩ : ℝ)) + 1 ≤ u τ ⟨Dw.p - 1, by omega⟩` using `by exact_mod_cast h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hne : u τ a - u τ b ≠ 0` using `sub_ne_zero.2 fun e => hab ((h τ).injective e)`. Establish `h1 : (1 : ℤ) ≤ |u τ a - u τ b|` using `Int.one_le_abs hne`. Simplify using `only [reW]`.

Conclude with `h1` after adjusting the coercions.
-/
theorem weightHyp_reW_one {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q)
    (h : ∀ τ, StrictAnti (u τ)) : Top.WeightHyp Dw.p (reW u) 1 := by
  refine ⟨one_pos, regDominant_reW u h, fun τ => ?_, fun τ a b _ hab => ?_⟩
  · rw [gap_reW u τ hp hq]
    have hlt : (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) < ⟨Dw.p, by omega⟩ :=
      Fin.mk_lt_mk.2 (by omega)
    have h1 := h τ hlt
    have h2 : u τ ⟨Dw.p, by omega⟩ + 1 ≤ u τ ⟨Dw.p - 1, by omega⟩ := h1
    have h3 : ((u τ ⟨Dw.p, by omega⟩ : ℝ)) + 1 ≤ u τ ⟨Dw.p - 1, by omega⟩ := by exact_mod_cast h2
    linarith
  · have hne : u τ a - u τ b ≠ 0 := sub_ne_zero.2 fun e => hab ((h τ).injective e)
    have h1 : (1 : ℤ) ≤ |u τ a - u τ b| := Int.one_le_abs hne
    simp only [reW]
    exact_mod_cast h1

/- English proof (translation)
Take `⟨hg0, hanti, hdist⟩` from `hg`. Establish `hp : 1 ≤ Dw.p` using `by omega`. Use `⟨hg0, regDominant_reW u hanti, fun τ => ?_, fun τ a b ha hab => ?_⟩` and prove the remaining obligations. Rewrite using `[gap_reW u τ hp hq]`. Establish `hlt : (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) < ⟨Dw.p, by omega⟩` using `Fin.mk_lt_mk.2 (by omega)`.

Establish `h1` using `hdist τ ⟨Dw.p, by omega⟩ ⟨Dw.p - 1, by omega⟩ (le_refl _) (ne_of_gt hlt)`. Establish `h2 : (u τ ⟨Dw.p, by omega⟩ : ℝ) < u τ ⟨Dw.p - 1, by omega⟩`. Conclude with `hanti τ hlt` after adjusting the coercions. Rewrite `h1` using `[abs_sub_comm, abs_of_pos (sub_pos.2 h2)]`. Conclude with `h1`.

Establish `ha' : Dw.p ≤ (a : ℕ)`. Establish `hn : ¬ Dw.p ≤ Dw.p + Dw.q - Dw.p` using `by omega`. Simplify `ha` using `only [Top.InSmall, if_neg hn]`. Conclude with `hdist τ a b ha' hab`.
-/
theorem weightHyp_reW_of_wtGap {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ) (hq : 1 ≤ Dw.q)
    (hqp : Dw.q < Dw.p) (hg : GlobalTheory.CovHt.WtGap u g) : Top.WeightHyp Dw.p (reW u) g := by
  obtain ⟨hg0, hanti, hdist⟩ := hg
  have hp : 1 ≤ Dw.p := by omega
  refine ⟨hg0, regDominant_reW u hanti, fun τ => ?_, fun τ a b ha hab => ?_⟩
  · rw [gap_reW u τ hp hq]
    have hlt : (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) < ⟨Dw.p, by omega⟩ :=
      Fin.mk_lt_mk.2 (by omega)
    have h1 := hdist τ ⟨Dw.p, by omega⟩ ⟨Dw.p - 1, by omega⟩ (le_refl _) (ne_of_gt hlt)
    have h2 : (u τ ⟨Dw.p, by omega⟩ : ℝ) < u τ ⟨Dw.p - 1, by omega⟩ := by
      exact_mod_cast hanti τ hlt
    rw [abs_sub_comm, abs_of_pos (sub_pos.2 h2)] at h1
    exact h1
  · have ha' : Dw.p ≤ (a : ℕ) := by
      have hn : ¬ Dw.p ≤ Dw.p + Dw.q - Dw.p := by omega
      simpa only [Top.InSmall, if_neg hn] using ha
    exact hdist τ a b ha' hab

/- English proof (translation)
Simplify using `only [GlobalTheory.CovHt.bndB, Top.bigB0, norm_wt_eq_iSup, reW]`. Rewrite using `[Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]`.
-/
theorem bound_eq_root_weight_bound {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ) :
    GlobalTheory.CovHt.bndB u g = Top.bigB0 (reW u) g := by
  simp only [GlobalTheory.CovHt.bndB, Top.bigB0, norm_wt_eq_iSup, reW]
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]

/- English proof (translation)
Unfold `GlobalTheory.CovHt.l1 Top.l1 reW`. Use `congr!`.
-/
theorem covHt_l1_eq_l1_reW {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) : GlobalTheory.CovHt.l1 u = Top.l1 (reW u) := by
  unfold GlobalTheory.CovHt.l1 Top.l1 reW
  congr!

end Entries

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c RM _ u`. Use `⟨towerWt_wtOf Dw u, ?_, fun n => ?_, ?_, covHt_l1_eq_l1_reW u, ?_, fun v => ?_, weightHyp_reW_one u, fun g => ⟨bound_eq_root_weight_bound u g, fun hq hqp hg => weightHyp_reW_of_wtGap u g hq hqp hg⟩⟩` and prove the remaining obligations. Conclude with `Prod.ext rfl (by simp [GlobalTheory.AllWt.wtOf_snd])`. Rewrite using `[GlobalTheory.CompHt.nsmul_wtOf, smul_zero]`. Introduce and unpack `(_ | r)`.

Simplify using `[nOf, Top.RootModel.coef]`. Simplify using `[nOf, Top.RootModel.coef, reW]`. Simplify using `only [GlobalTheory.CompHt.dimFlag, Formalism.DegreeFormula.dimFl, Top.dimFl]`. Rewrite using `[Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]`. Establish `e : ∀ w : GlobalTheory.AllWt.Weight Dw, ((GlobalTheory.CompHt.vdm w : ℤ) : ℝ) = GlobalTheory.CompHt.vdm (reW w)` using `fun w => vdm_cast _ _ w`.

Rewrite using `[e, e]`. Conclude with `flagDeg_mul_vdm (reW u) (reW v)`.
-/
theorem integer_weights_vocab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) [DecidableEq (CMType H)] (u : GlobalTheory.AllWt.Weight Dw), towerWt Dw (GlobalTheory.AllWt.wtOf Dw u 0).1 = reW u ∧ (GlobalTheory.AllWt.wtOf Dw u 0) = ((GlobalTheory.AllWt.wtOf Dw u 0).1, 0) ∧ (∀ n : ℕ, n • (GlobalTheory.AllWt.wtOf Dw u 0) = GlobalTheory.AllWt.wtOf Dw (n • u) 0) ∧ (∀ j, (nOf u j : ℝ) = RM.coef (reW u) 0 j) ∧ GlobalTheory.CovHt.l1 u = Top.l1 (reW u) ∧ GlobalTheory.CompHt.dimFlag Dw = (Top.dimFl (CMType H) (Dw.p + Dw.q)) ∧ (∀ v : GlobalTheory.AllWt.Weight Dw, Top.flagDeg (reW u) * ((GlobalTheory.CompHt.vdm v : ℤ) : ℝ) = Top.flagDeg (reW v) * ((GlobalTheory.CompHt.vdm u : ℤ) : ℝ)) ∧ (1 ≤ Dw.p → 1 ≤ Dw.q → (∀ τ, StrictAnti (u τ)) → Top.WeightHyp Dw.p (reW u) 1) ∧ ∀ g : ℝ, GlobalTheory.CovHt.bndB u g = Top.bigB0 (reW u) g ∧ (1 ≤ Dw.q → Dw.q < Dw.p → GlobalTheory.CovHt.WtGap u g → Top.WeightHyp Dw.p (reW u) g) := by
  intro E _ _ _ H Dw l Xo c RM _ u
  refine ⟨towerWt_wtOf Dw u, ?_, fun n => ?_, ?_, covHt_l1_eq_l1_reW u, ?_, fun v => ?_, weightHyp_reW_one u,
    fun g => ⟨bound_eq_root_weight_bound u g, fun hq hqp hg => weightHyp_reW_of_wtGap u g hq hqp hg⟩⟩
  · exact Prod.ext rfl (by simp [GlobalTheory.AllWt.wtOf_snd])
  · rw [GlobalTheory.CompHt.nsmul_wtOf, smul_zero]
  · rintro (_ | r)
    · simp [nOf, Top.RootModel.coef]
    · simp [nOf, Top.RootModel.coef, reW]
  · simp only [GlobalTheory.CompHt.dimFlag, Formalism.DegreeFormula.dimFl, Top.dimFl]
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  · have e : ∀ w : GlobalTheory.AllWt.Weight Dw, ((GlobalTheory.CompHt.vdm w : ℤ) : ℝ) = GlobalTheory.CompHt.vdm (reW w) :=
      fun w => vdm_cast _ _ w
    rw [e, e]
    exact flagDeg_mul_vdm (reW u) (reW v)

end GlobalTheory.CompanionTheory.Ar.Plug
