import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtBasisMapGood
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsExpEqOfSubstLg
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TypicalBasisCoordinates
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChainLemmaMultivariatePowerSeriesCoordinateForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBasisChangeInvariaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthIntegralCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeFormalGroupDeterminantPowDepthOfRadiiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypicalCurveBasisAdaptedToSaturatedFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdGeExpOfLogSumTwoRadiiStatement

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth.InertBound

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

/- English proof (translation)
Establish `hex` using `isExp_expOf G`. Establish `hL' : HasSubst L` using `hasSubst_of_constantCoeff_zero hL`. Establish `hexs : HasSubst (expOf G)` using `hasSubst_of_constantCoeff_zero hex.1`. Use `set E : Fin d → MvPowerSeries (Fin M) C := fun k => subst L (expOf G k) with hE`. Establish `hE0 : ∀ k, constantCoeff (E k) = 0` using `fun k => constantCoeff_subst_eq_zero hL' hL (hex.1 k)`.

Establish `hEs : HasSubst E` using `hasSubst_of_constantCoeff_zero hE0`. Use `⟨fun a => subst E (Ψ a), fun a => constantCoeff_subst_eq_zero hEs hE0 (hΨ0 a), ?_⟩` and prove the remaining obligations. Introduce `e`. Establish `hΨs : HasSubst Ψ` using `hasSubst_of_constantCoeff_zero hΨ0`. Establish `hΦs : HasSubst Φ` using `hasSubst_of_constantCoeff_zero hΦ0`.

Establish `h1 : ∀ k, subst (fun a => subst E (Ψ a)) (Φ k) = E k`. Introduce `k`. Rewrite using `[← subst_comp_subst_apply hΨs hEs, hΨΦ, subst_X hEs]`. Rewrite using `[subst_comp_subst_apply hΦs (hasSubst_of_constantCoeff_zero (fun a => constantCoeff_subst_eq_zero hEs hE0 (hΨ0 a)))]`. Simplify using `only [h1]`.

Rewrite using `[hE, ← subst_comp_subst_apply hexs hL', hex.2 e, subst_X hL']`.
-/
theorem exists_chart_coords {d M : ℕ} (G : LogFGL v d) (Φ Ψ : Fin d → MvPowerSeries (Fin d) C)
    (hΦ0 : ∀ a, constantCoeff (Φ a) = 0) (hΨ0 : ∀ a, constantCoeff (Ψ a) = 0)
    (hΨΦ : ∀ a, subst Ψ (Φ a) = X a) (L : Fin d → MvPowerSeries (Fin M) C)
    (hL : ∀ k, constantCoeff (L k) = 0) :
    ∃ t : Fin d → MvPowerSeries (Fin M) C, (∀ a, constantCoeff (t a) = 0) ∧
      ∀ e, subst t (subst Φ (G.lg e)) = L e := by
  have hex := isExp_expOf G
  have hL' : HasSubst L := hasSubst_of_constantCoeff_zero hL
  have hexs : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hex.1
  set E : Fin d → MvPowerSeries (Fin M) C := fun k => subst L (expOf G k) with hE
  have hE0 : ∀ k, constantCoeff (E k) = 0 := fun k =>
    constantCoeff_subst_eq_zero hL' hL (hex.1 k)
  have hEs : HasSubst E := hasSubst_of_constantCoeff_zero hE0
  refine ⟨fun a => subst E (Ψ a), fun a => constantCoeff_subst_eq_zero hEs hE0 (hΨ0 a), ?_⟩
  intro e
  have hΨs : HasSubst Ψ := hasSubst_of_constantCoeff_zero hΨ0
  have hΦs : HasSubst Φ := hasSubst_of_constantCoeff_zero hΦ0
  have h1 : ∀ k, subst (fun a => subst E (Ψ a)) (Φ k) = E k := by
    intro k
    rw [← subst_comp_subst_apply hΨs hEs, hΨΦ, subst_X hEs]
  rw [subst_comp_subst_apply hΦs (hasSubst_of_constantCoeff_zero
    (fun a => constantCoeff_subst_eq_zero hEs hE0 (hΨ0 a)))]
  simp only [h1]
  rw [hE, ← subst_comp_subst_apply hexs hL', hex.2 e, subst_X hL']

/- English proof (translation)
Use extensionality with `α`. Simplify using `only [lgSum, map_sum, coeff_smul, smul_eq_mul]`. Use `show (∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, (∑ e, c a n e * N e b) * coeff α (t a ^ p ^ n)) = ∑ e, N e b * (∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n e * coeff α (t a ^ p ^ n))`. Simplify using `only [Finset.sum_mul, Finset.mul_sum]`. Use `conv_rhs => rw [Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by ring` and prove the remaining obligations.
-/
theorem lgSum_mulMatrix {d M : ℕ} (p : ℕ) (c : Fin d → ℕ → Fin d → C)
    (t : Fin d → MvPowerSeries (Fin M) C) (N : Matrix (Fin d) (Fin d) C) (b : Fin d) :
    lgSum p (fun a n b => ∑ e, c a n e * N e b) t b = ∑ e, N e b • lgSum p c t e := by
  ext α
  simp only [lgSum, map_sum, coeff_smul, smul_eq_mul]
  show (∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, (∑ e, c a n e * N e b) * coeff α (t a ^ p ^ n))
    = ∑ e, N e b * (∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n e * coeff α (t a ^ p ^ n))
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by ring

end

end GlobalTheory.FGDepth.InertBound

namespace GlobalTheory.FGDepth.InertBound

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs), finsum_eq_sum_of_support_subset (s := (Finset.range (Finsupp.degree α + 1)).image fun n => p ^ n), Finset.sum_image fun x _ y _ hxy => Nat.pow_right_injective hp hxy]`. Both sides reduce to the same expression. Introduce `m hm`. Rewrite `hm` using `[Function.mem_support, smul_eq_mul]`. Choose the witnesses or unpack the hypotheses as in `⟨n, rfl⟩ : ∃ n, m = p ^ n := by`.

Assume the negation of the conclusion as `hne`. Conclude with `hm (by rw [hf m (fun n e => hne ⟨n, e⟩), zero_mul])`. Establish `hle : p ^ n ≤ Finsupp.degree α`. Assume the negation of the conclusion as `hlt`. Conclude with `hm (by rw [GlobalTheory.ChainCoord.coeff_pow_eq_zero hs α (not_le.1 hlt), mul_zero])`.

Establish `hn : n < p ^ n` using `Nat.lt_pow_self hp`. Conclude with `Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (by omega), rfl⟩)`.
-/
theorem coeff_subst_typical {M p : ℕ} (hp : 2 ≤ p) (f : PowerSeries C)
    (hf : ∀ m, (∀ n, m ≠ p ^ n) → PowerSeries.coeff m f = 0)
    (s : MvPowerSeries (Fin M) C) (hs : constantCoeff s = 0) (α : Fin M →₀ ℕ) :
    coeff α (PowerSeries.subst s f) = ∑ n ∈ Finset.range (Finsupp.degree α + 1),
      PowerSeries.coeff (p ^ n) f * coeff α (s ^ (p ^ n)) := by
  classical
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs),
    finsum_eq_sum_of_support_subset
      (s := (Finset.range (Finsupp.degree α + 1)).image fun n => p ^ n),
    Finset.sum_image fun x _ y _ hxy => Nat.pow_right_injective hp hxy]
  · rfl
  · intro m hm
    rw [Function.mem_support, smul_eq_mul] at hm
    obtain ⟨n, rfl⟩ : ∃ n, m = p ^ n := by
      by_contra hne
      exact hm (by rw [hf m (fun n e => hne ⟨n, e⟩), zero_mul])
    have hle : p ^ n ≤ Finsupp.degree α := by
      by_contra hlt
      exact hm (by rw [GlobalTheory.ChainCoord.coeff_pow_eq_zero hs α (not_le.1 hlt), mul_zero])
    have hn : n < p ^ n := Nat.lt_pow_self hp
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (by omega), rfl⟩)

/- English proof (translation)
Establish `hts : HasSubst t` using `hasSubst_of_constantCoeff_zero ht`. Establish `h1 : ∀ a (f : PowerSeries C),`. Substitute `t (PowerSeries.subst (X a : MvPowerSeries (Fin d) C) f) = PowerSeries.subst (t a) f := by` using the available equality. Introduce `a f`. Rewrite using `[PowerSeries.subst_def, PowerSeries.subst_def, subst_comp_subst_apply (ptOn_hs a) hts]`.

Simplify using `only [subst_X hts]`. Rewrite using `[← coe_substAlgHom hts, map_sum]`. Simplify using `only [coe_substAlgHom, h1]`. Use extensionality with `α`. Rewrite using `[map_sum]`.

Use `show _ = ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, G.lc p (γ a) n b * coeff α (t a ^ (p ^ n))`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => coeff_subst_typical hp _ (hγ a b) (t a) (ht a) α`.
-/
theorem subst_sum_lgCurve {d M : ℕ} (G : LogFGL v d) {p : ℕ} (hp : 2 ≤ p)
    (γ : Fin d → Fin d → PowerSeries C) (hγ : ∀ a, G.IsPTypical p (γ a))
    (t : Fin d → MvPowerSeries (Fin M) C) (ht : ∀ a, constantCoeff (t a) = 0) (b : Fin d) :
    subst t (∑ a, PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve (γ a) b)) =
      lgSum p (fun a n e => G.lc p (γ a) n e) t b := by
  have hts : HasSubst t := hasSubst_of_constantCoeff_zero ht
  have h1 : ∀ a (f : PowerSeries C),
      subst t (PowerSeries.subst (X a : MvPowerSeries (Fin d) C) f) = PowerSeries.subst (t a) f := by
    intro a f
    rw [PowerSeries.subst_def, PowerSeries.subst_def, subst_comp_subst_apply (ptOn_hs a) hts]
    simp only [subst_X hts]
  rw [← coe_substAlgHom hts, map_sum]
  simp only [coe_substAlgHom, h1]
  ext α
  rw [map_sum]
  show _ = ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a,
    G.lc p (γ a) n b * coeff α (t a ^ (p ^ n))
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => coeff_subst_typical hp _ (hγ a b) (t a) (ht a) α

/- English proof (translation)
Establish `hp1 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `hA : 0 ≤ 2 / ((p : ℝ) * (p - 1))` using `div_nonneg zero_le_two (mul_nonneg (by linarith) (by linarith))`. Establish `hB : 0 ≤ 2 / ((p : ℝ) - 1)` using `div_nonneg zero_le_two (by linarith)`. Generalize the expression as in `2 / ((p : ℝ) * (p - 1)) = A at hA ⊢`. Generalize the expression as in `2 / ((p : ℝ) - 1) = B at hB ⊢`.

Establish `hcard : (Finset.univ.filter fun a : Fin i => a.val < j).card ≤ j`. Combine the equalities or inequalities in the displayed calculation. Take `⟨a, ha, rfl⟩` from `Finset.mem_map.1 hx`. Conclude with `Finset.mem_range.2 (Finset.mem_filter.1 ha).2`. Use `_ = j := Finset.card_range j`.

Combine the equalities or inequalities in the displayed calculation. Distinguish the cases in `hj : a.val < j`. Apply the tactic sequence `rw [if_pos hj] split_ifs <;> linarith`. Rewrite using `[if_neg hj, if_pos (hgood a (not_lt.1 hj)), add_zero]`. Use `_ = i * A + (Finset.univ.filter fun a : Fin i => a.val < j).card * B := by`.

Rewrite using `[Finset.sum_add_distrib, ← Finset.sum_filter]`. Simplify using the standard rewrite rules. Use `_ ≤ _ := by`. Establish `: ((Finset.univ.filter fun a : Fin i => a.val < j).card : ℝ) ≤ j`. Conclude with `hcard` after adjusting the coercions.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right this hB]`.
-/
theorem sum_radii_le {i d j : ℕ} (p : ℕ) (hp : 2 ≤ p) (r : Fin i → Fin d) (good : Fin d → Prop)
    [DecidablePred good] (hgood : ∀ a : Fin i, j ≤ a.val → good (r a)) :
    (∑ a, (if good (r a) then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1))) ≤
      i * (2 / ((p : ℝ) * (p - 1))) + j * (2 / ((p : ℝ) - 1)) := by
  have hp1 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hA : 0 ≤ 2 / ((p : ℝ) * (p - 1)) :=
    div_nonneg zero_le_two (mul_nonneg (by linarith) (by linarith))
  have hB : 0 ≤ 2 / ((p : ℝ) - 1) := div_nonneg zero_le_two (by linarith)
  generalize 2 / ((p : ℝ) * (p - 1)) = A at hA ⊢
  generalize 2 / ((p : ℝ) - 1) = B at hB ⊢
  have hcard : (Finset.univ.filter fun a : Fin i => a.val < j).card ≤ j := by
    calc _ = ((Finset.univ.filter fun a : Fin i => a.val < j).map Fin.valEmbedding).card :=
          (Finset.card_map _).symm
      _ ≤ (Finset.range j).card := Finset.card_le_card fun x hx => by
          obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
          exact Finset.mem_range.2 (Finset.mem_filter.1 ha).2
      _ = j := Finset.card_range j
  calc _ ≤ ∑ a : Fin i, (A + if a.val < j then B else 0) := Finset.sum_le_sum fun a _ => by
        by_cases hj : a.val < j
        · rw [if_pos hj]
          split_ifs <;> linarith
        · rw [if_neg hj, if_pos (hgood a (not_lt.1 hj)), add_zero]
    _ = i * A + (Finset.univ.filter fun a : Fin i => a.val < j).card * B := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp
    _ ≤ _ := by
        have : ((Finset.univ.filter fun a : Fin i => a.val < j).card : ℝ) ≤ j := by
          exact_mod_cast hcard
        nlinarith [mul_le_mul_of_nonneg_right this hB]

end

end GlobalTheory.FGDepth.InertBound

namespace GlobalTheory.FGDepth.InertBound

open GlobalTheory.ChainCoord in

/- English proof (translation)
Introduce `C _ _ _ v p hp hv d h hh ty G μ τ j i c hcard u hu hsupp`. Take `⟨γ, r, g, hB, -, hgdet, htan, hgood⟩` from `GlobalTheory.T.exists_typicalCurve_basis_adapted_to_saturated_frame C v p hp hv d h hh ty G μ τ j i hcard u hu hsupp`. Take `⟨hγ, hγty, hdet⟩` from `hB`. Establish `e1 : detDepth G u c = detDepth G (fun a => tangent (γ (r a))) c`. Rewrite using `[← GlobalTheory.T.formalGroupDeterminantPowDepth_basis_change_invariant C v i d c G u g hgdet]`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Conclude with `(htan a).symm`. Take `⟨Ψ, hΨi, hΨ0, hΨΦ, hΦΨ⟩` from `ptBasisMap_inv G hγ hdet`. Establish `hΦg` using `ptBasisMap_good G hγ`.

Use `set T : Matrix (Fin d) (Fin d) C := Matrix.of fun a b => tangent (γ a) b with hT`. Take `⟨hTu, hTinv⟩` from `pt_inv_int (M := T) (fun a b => (hγ a b).2 1) hdet`. Use `set L : Fin d → MvPowerSeries (Fin i) C := fun e => ∑ a, tangent (γ (r a)) e • X a with hLdef`. Establish `hL0 : ∀ e, constantCoeff (L e) = 0` using `by intro e; simp [L]`. Take `⟨t, ht0, htL⟩` from `exists_chart_coords G (ptBasisMap G γ) Ψ (fun a => (hΦg a).1) hΨ0 hΨΦ L hL0`.

Establish `hp2 : 2 ≤ p` using `hp.two_le`. Establish `hlg : ∀ b, lgSum p (fun a n e => G.lc p (γ a) n e) t b = L b`. Introduce `b`. Rewrite using `[← htL b, ptBasisMap_lg G hγ b, subst_sum_lgCurve G hp2 γ (fun a => (hγty a).1) t ht0 b]`. Use `set c' : Fin d → ℕ → Fin d → C := fun a n b => ∑ e, G.lc p (γ a) n e * T⁻¹ e b with hc'`.

Use `set z' : Fin d → MvPowerSeries (Fin i) C := fun b => ∑ e, T⁻¹ e b • L e with hz'`. Establish `hlg' : ∀ b, lgSum p c' t b = z' b`. Introduce `b`. Rewrite using `[hc', lgSum_mulMatrix]`. Simplify using `only [hlg, hz']`.

Use `set good : Fin d → Prop := fun b => G.lc p (γ b) 1 = 0 with hgoodDef`. Use `set rad : Fin d → ℝ := fun b => if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1) with hrad`. Use `set ρ : Fin i → ℝ := fun a => rad (r a) with hρ`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.one_lt`. Establish `hrad0 : ∀ b, 0 ≤ rad b`.

Introduce `b`. Simplify using `only [hrad]`. Use `split_ifs`. Conclude with `div_nonneg zero_le_two (mul_nonneg (by linarith) (by linarith))`. Conclude with `div_nonneg zero_le_two (by linarith)`.

Establish `hTT : T * T⁻¹ = 1` using `Matrix.mul_nonsing_inv T hTu`. Establish `hc0 : ∀ a, c' a 0 = Pi.single a 1`. Introduce `a`. Use function extensionality and compare the values at `b`. Establish `hte : ∀ e, G.lc p (γ a) 0 e = T a e` using `fun e => by`.

Simplify using `only [hT, Matrix.of_apply]`. Conclude with `(congrFun (ReciprocityTheory.ChartRestriction.G.Sh.PTb.tangent_eq_lc_zero G p (fun e => (hγ a e).1)) e).symm`. Simplify using `only [hc', hte]`. Rewrite using `[← Matrix.mul_apply, hTT, Matrix.one_apply, Pi.single_apply]`. Distinguish the cases in `hab : b = a`.

Simplify using `[hab]`. Simplify using `[hab, Ne.symm hab]`. Establish `hcn : ∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c' a n b)`. Introduce `a n b`. Use `v.map_le_sum fun e _ => ?_` and prove the remaining obligations.

Rewrite using `[v.map_mul]`. Conclude with `le_add_of_le_of_nonneg ((pt5v' C v p hp hv d h ty G γ ⟨hγ, hγty, hdet⟩ a).1 n e) (hTinv e b)`. Establish `hcg : ∀ a, good a → ∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c' a n b)`. Introduce `a ha n b hn`. Use `v.map_le_sum fun e _ => ?_` and prove the remaining obligations.

Rewrite using `[v.map_mul]`. Conclude with `le_add_of_le_of_nonneg ((pt5v' C v p hp hv d h ty G γ ⟨hγ, hγty, hdet⟩ a).2 ha n e hn) (hTinv e b)`. Establish `hzeq : ∀ b, z' b = ∑ a, ((1 : Matrix (Fin d) (Fin d) C) (r a) b) • (X a : MvPowerSeries (Fin i) C)`. Introduce `b`. Rewrite using `[← hTT]`.

Simplify using `only [hz', hLdef, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Simplify using `only [hT, Matrix.of_apply]`. Put the polynomial expressions in normal form.

Establish `hz : ∀ b, OrdGe v ρ (z' b) (rad b)`. Introduce `b`. Rewrite using `[hzeq b]`. Use `ord_sum _ fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.one_apply]`.

Use `split_ifs with hab`. Rewrite using `[one_smul]`. Introduce `α`. Rewrite using `[coeff_X]`. Use `split_ifs with hα`.

Substitute `hα` using the available equality. Establish `hs : ∑ m, ρ m * ((Finsupp.single a 1 : Fin i →₀ ℕ) m : ℝ) = ρ a`. Simplify using `[Finsupp.single_apply]`. Rewrite using `[hs, v.map_one, ← hab]`. Use `show ((rad (r a) - rad (r a) : ℝ) : WithTop ℝ) ≤ 0`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite using `[zero_smul]`. Conclude with `ord_zero _`. Establish `hD` using `GlobalTheory.T.ordGe_exp_of_logSum_two_radii C v p hp hv d i good c' hc0 hcn hcg ρ z' t hz ht0 hlg'`.

Establish `htord : ∀ b, OrdGe v ρ (t b) 0` using `fun b => ord_mono (hD b) (hrad0 b)`. Establish `e2` using `GlobalTheory.T.differentialOperatorDepth_integral_coordinates C v i d c G (fun a => tangent (γ (r a))) (basisMap G γ) Ψ (fun a => by`. Rewrite using `[basisMap_eq_ptBasisMap]`. Conclude with `⟨(hΦg a).2, (hΦg a).1, hΨi a, hΨ0 a⟩)`. Use the proof step `(fun a => by rw [basisMap_eq_ptBasisMap]; exact ⟨hΨΦ a, hΦΨ a⟩) t ht0`.

Use the proof step `(fun e => by rw [basisMap_eq_ptBasisMap]; exact htL e)`. Rewrite using `[e1]`. Establish `hS : (c : ℝ) * ∑ a, ρ a ≤ 2 * i * c / ((p : ℝ) * (p - 1)) + 2 * j * c / ((p : ℝ) - 1)`. Use `sum_radii_le (d := d) p hp2 r good hgood` as an intermediate fact. Establish `hc : (0 : ℝ) ≤ c` using `Nat.cast_nonneg c`.

Combine the equalities or inequalities in the displayed calculation. Establish `hlowAll : ∀ B : ℝ, (∀ α ∈ (detPow C i c).support, ((B + (c : ℝ) * ∑ a, ρ a : ℝ) : WithTop ℝ) ≤ v ((detPow C i c).coeff α * mfact α)) → (B : EReal) ≤ detDepth G (fun a => tangent (γ (r a))) c`. Introduce `B hB`. Rewrite using `[e2]`. Use `le_iInf fun f => ?_` and prove the remaining obligations.

Use `GlobalTheory.T.le_formalGroupDeterminantPowDepth_of_radii C v i d c ρ t B ht0 htord hB f.1 f.2` as an intermediate fact. Conclude with `WithBot.coe_le_coe.2 this`. Distinguish the cases in `hfin : ∃ α ∈ (detPow C i c).support, v ((detPow C i c).coeff α * mfact α) ≠ ⊤`. Take `⟨α1, hα1, hne⟩` from `hfin`. Take `⟨α0, hα0, hmin⟩` from `(detPow C i c).support.exists_min_image (fun α => v ((detPow C i c).coeff α * mfact α)) ⟨α1, hα1⟩`.

Establish `hne0 : v ((detPow C i c).coeff α0 * mfact α0) ≠ ⊤` using `ne_top_of_le_ne_top hne (hmin α1 hα1)`. Take `⟨κ, hκ⟩` from `WithTop.ne_top_iff_exists.1 hne0`. Establish `hlow` using `hlowAll (κ - (c : ℝ) * ∑ a, ρ a) (fun α hα => by`. Rewrite using `[sub_add_cancel, hκ]`. Conclude with `hmin α hα)`.

Establish `hcont : content v (detPow C i c) ≤ (κ : EReal)`. Unfold `content`. Use `(iInf₂_le α0 hα0).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[← hκ]`. Both sides reduce to the same expression.

Use `hcont.trans ?_` and prove the remaining obligations. Establish `e3 : (κ : EReal) = ((κ - (c : ℝ) * ∑ a, ρ a : ℝ) : EReal) + (((c : ℝ) * ∑ a, ρ a : ℝ) : EReal)`. Rewrite using `[← EReal.coe_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e3]`. Conclude with `add_le_add hlow (EReal.coe_le_coe_iff.2 hS)`. Use `push_neg at hfin`. Establish `htop : detDepth G (fun a => tangent (γ (r a))) c = ⊤`. Use `(EReal.eq_top_iff_forall_lt _).2 fun y => ?_` and prove the remaining obligations.

Use `lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (lt_add_one y)) (hlowAll (y + 1) fun α hα => ?_)` and prove the remaining obligations. Rewrite using `[hfin α hα]`. Conclude with `le_top`. Rewrite using `[htop, EReal.top_add_coe]`. Conclude with `le_top`.
-/
theorem content_le_detDepth_add :
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
      p.Prime → v (p : C) = 1 → ∀ (d h : ℕ), 0 < h → ∀ (ty : Fin d → ZMod h) (G : LogFGL v d),
        MuAction G p h ty → ∀ (τ : ZMod h) (j i c : ℕ),
          (Finset.univ.filter fun a => ty a = τ + 1).card ≤ j →
          ∀ u : Fin i → Fin d → C, IsSatFrame v u → (∀ a e, ty e ≠ τ → u a e = 0) →
            content v (detPow C i c) ≤ detDepth G u c +
              ((2 * i * c / ((p : ℝ) * (p - 1)) + 2 * j * c / ((p : ℝ) - 1) : ℝ) : EReal) := by
  intro C _ _ _ v p hp hv d h hh ty G μ τ j i c hcard u hu hsupp
  classical
  obtain ⟨γ, r, g, hB, -, hgdet, htan, hgood⟩ :=
    GlobalTheory.T.exists_typicalCurve_basis_adapted_to_saturated_frame C v p hp hv d h hh ty G μ τ j i hcard u hu hsupp
  obtain ⟨hγ, hγty, hdet⟩ := hB
  have e1 : detDepth G u c = detDepth G (fun a => tangent (γ (r a))) c := by
    rw [← GlobalTheory.T.formalGroupDeterminantPowDepth_basis_change_invariant C v i d c G u g hgdet]
    congr 1
    funext a
    exact (htan a).symm
  obtain ⟨Ψ, hΨi, hΨ0, hΨΦ, hΦΨ⟩ := ptBasisMap_inv G hγ hdet
  have hΦg := ptBasisMap_good G hγ
  set T : Matrix (Fin d) (Fin d) C := Matrix.of fun a b => tangent (γ a) b with hT
  obtain ⟨hTu, hTinv⟩ := pt_inv_int (M := T) (fun a b => (hγ a b).2 1) hdet
  set L : Fin d → MvPowerSeries (Fin i) C := fun e => ∑ a, tangent (γ (r a)) e • X a with hLdef
  have hL0 : ∀ e, constantCoeff (L e) = 0 := by intro e; simp [L]
  obtain ⟨t, ht0, htL⟩ :=
    exists_chart_coords G (ptBasisMap G γ) Ψ (fun a => (hΦg a).1) hΨ0 hΨΦ L hL0
  have hp2 : 2 ≤ p := hp.two_le
  have hlg : ∀ b, lgSum p (fun a n e => G.lc p (γ a) n e) t b = L b := by
    intro b
    rw [← htL b, ptBasisMap_lg G hγ b,
      subst_sum_lgCurve G hp2 γ (fun a => (hγty a).1) t ht0 b]
  set c' : Fin d → ℕ → Fin d → C := fun a n b => ∑ e, G.lc p (γ a) n e * T⁻¹ e b with hc'
  set z' : Fin d → MvPowerSeries (Fin i) C := fun b => ∑ e, T⁻¹ e b • L e with hz'
  have hlg' : ∀ b, lgSum p c' t b = z' b := by
    intro b
    rw [hc', lgSum_mulMatrix]
    simp only [hlg, hz']
  set good : Fin d → Prop := fun b => G.lc p (γ b) 1 = 0 with hgoodDef
  set rad : Fin d → ℝ := fun b => if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1)
    with hrad
  set ρ : Fin i → ℝ := fun a => rad (r a) with hρ
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hrad0 : ∀ b, 0 ≤ rad b := by
    intro b
    simp only [hrad]
    split_ifs
    · exact div_nonneg zero_le_two (mul_nonneg (by linarith) (by linarith))
    · exact div_nonneg zero_le_two (by linarith)
  have hTT : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hTu
  have hc0 : ∀ a, c' a 0 = Pi.single a 1 := by
    intro a
    funext b
    have hte : ∀ e, G.lc p (γ a) 0 e = T a e := fun e => by
      simp only [hT, Matrix.of_apply]
      exact (congrFun (ReciprocityTheory.ChartRestriction.G.Sh.PTb.tangent_eq_lc_zero G p (fun e => (hγ a e).1)) e).symm
    simp only [hc', hte]
    rw [← Matrix.mul_apply, hTT, Matrix.one_apply, Pi.single_apply]
    by_cases hab : b = a
    · simp [hab]
    · simp [hab, Ne.symm hab]
  have hcn : ∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c' a n b) := by
    intro a n b
    refine v.map_le_sum fun e _ => ?_
    rw [v.map_mul]
    exact le_add_of_le_of_nonneg ((pt5v' C v p hp hv d h ty G γ ⟨hγ, hγty, hdet⟩ a).1 n e)
      (hTinv e b)
  have hcg : ∀ a, good a → ∀ (n : ℕ) b, 1 ≤ n →
      ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c' a n b) := by
    intro a ha n b hn
    refine v.map_le_sum fun e _ => ?_
    rw [v.map_mul]
    exact le_add_of_le_of_nonneg
      ((pt5v' C v p hp hv d h ty G γ ⟨hγ, hγty, hdet⟩ a).2 ha n e hn) (hTinv e b)
  have hzeq : ∀ b, z' b = ∑ a, ((1 : Matrix (Fin d) (Fin d) C) (r a) b) • (X a : MvPowerSeries (Fin i) C) := by
    intro b
    rw [← hTT]
    simp only [hz', hLdef, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    simp only [hT, Matrix.of_apply]
    ring_nf
  have hz : ∀ b, OrdGe v ρ (z' b) (rad b) := by
    intro b
    rw [hzeq b]
    refine ord_sum _ fun a _ => ?_
    rw [Matrix.one_apply]
    split_ifs with hab
    · rw [one_smul]
      intro α
      rw [coeff_X]
      split_ifs with hα
      · subst hα
        have hs : ∑ m, ρ m * ((Finsupp.single a 1 : Fin i →₀ ℕ) m : ℝ) = ρ a := by
          simp [Finsupp.single_apply]
        rw [hs, v.map_one, ← hab]
        show ((rad (r a) - rad (r a) : ℝ) : WithTop ℝ) ≤ 0
        simp
      · simp
    · rw [zero_smul]
      exact ord_zero _
  have hD := GlobalTheory.T.ordGe_exp_of_logSum_two_radii C v p hp hv d i good c' hc0 hcn hcg ρ z' t hz ht0 hlg'
  have htord : ∀ b, OrdGe v ρ (t b) 0 := fun b => ord_mono (hD b) (hrad0 b)
  have e2 := GlobalTheory.T.differentialOperatorDepth_integral_coordinates C v i d c G (fun a => tangent (γ (r a))) (basisMap G γ) Ψ
    (fun a => by
      rw [basisMap_eq_ptBasisMap]
      exact ⟨(hΦg a).2, (hΦg a).1, hΨi a, hΨ0 a⟩)
    (fun a => by rw [basisMap_eq_ptBasisMap]; exact ⟨hΨΦ a, hΦΨ a⟩) t ht0
    (fun e => by rw [basisMap_eq_ptBasisMap]; exact htL e)
  rw [e1]
  have hS : (c : ℝ) * ∑ a, ρ a ≤ 2 * i * c / ((p : ℝ) * (p - 1)) + 2 * j * c / ((p : ℝ) - 1) := by
    have := sum_radii_le (d := d) p hp2 r good hgood
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    calc (c : ℝ) * ∑ a, ρ a ≤ c * (i * (2 / ((p : ℝ) * (p - 1))) + j * (2 / ((p : ℝ) - 1))) :=
          mul_le_mul_of_nonneg_left this hc
      _ = _ := by ring
  have hlowAll : ∀ B : ℝ, (∀ α ∈ (detPow C i c).support, ((B + (c : ℝ) * ∑ a, ρ a : ℝ) : WithTop ℝ) ≤
      v ((detPow C i c).coeff α * mfact α)) →
      (B : EReal) ≤ detDepth G (fun a => tangent (γ (r a))) c := by
    intro B hB
    rw [e2]
    refine le_iInf fun f => ?_
    have := GlobalTheory.T.le_formalGroupDeterminantPowDepth_of_radii C v i d c ρ t B ht0 htord hB f.1 f.2
    exact WithBot.coe_le_coe.2 this
  by_cases hfin : ∃ α ∈ (detPow C i c).support, v ((detPow C i c).coeff α * mfact α) ≠ ⊤
  · obtain ⟨α1, hα1, hne⟩ := hfin
    obtain ⟨α0, hα0, hmin⟩ := (detPow C i c).support.exists_min_image
      (fun α => v ((detPow C i c).coeff α * mfact α)) ⟨α1, hα1⟩
    have hne0 : v ((detPow C i c).coeff α0 * mfact α0) ≠ ⊤ := ne_top_of_le_ne_top hne (hmin α1 hα1)
    obtain ⟨κ, hκ⟩ := WithTop.ne_top_iff_exists.1 hne0
    have hlow := hlowAll (κ - (c : ℝ) * ∑ a, ρ a) (fun α hα => by
      rw [sub_add_cancel, hκ]; exact hmin α hα)
    have hcont : content v (detPow C i c) ≤ (κ : EReal) := by
      unfold content
      refine (iInf₂_le α0 hα0).trans (le_of_eq ?_)
      rw [← hκ]
      rfl
    refine hcont.trans ?_
    have e3 : (κ : EReal) = ((κ - (c : ℝ) * ∑ a, ρ a : ℝ) : EReal) + (((c : ℝ) * ∑ a, ρ a : ℝ) : EReal) := by
      rw [← EReal.coe_add]; congr 1; ring
    rw [e3]
    exact add_le_add hlow (EReal.coe_le_coe_iff.2 hS)
  · push_neg at hfin
    have htop : detDepth G (fun a => tangent (γ (r a))) c = ⊤ := by
      refine (EReal.eq_top_iff_forall_lt _).2 fun y => ?_
      refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (lt_add_one y)) (hlowAll (y + 1) fun α hα => ?_)
      rw [hfin α hα]
      exact le_top
    rw [htop, EReal.top_add_coe]
    exact le_top

end GlobalTheory.FGDepth.InertBound
