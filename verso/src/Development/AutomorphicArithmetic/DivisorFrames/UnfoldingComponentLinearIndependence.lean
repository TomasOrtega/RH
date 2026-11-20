import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfContinuousReading
import Development.AutomorphicArithmetic.DivisorFrames.UnfoldingChartLinearIndependence
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

open Module GlobalTheory GlobalTheory.SecDivision GlobalTheory.Reg GlobalTheory.GenericFrames GlobalTheory.FlatLine GlobalTheory.FlagTan GlobalTheory.FlatCore in
/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c r σ U hσ hU Z m ε hε e e' f g hf hfZ hf0 hg hgZ q hq hfg j`. Take `⟨-, -, h, -⟩` from `evLaws_genFr_atlas E H Dw l Xo c`. Establish `off : ∀ {u : Rul Xo c}, u ∈ suppOn Z → ∀ Z', Z' ≠ Z → genVal Z' u = 0` using `fun hu Z' hZ => by`. Rewrite using `[genVal_apply h]`. Conclude with `evC_eq_zero h hZ hu`.

Establish `hfz : genVal Z f ≠ 0` using `fun h0 => hf0 (secZ_eq_zero_of_genVal hf fun Z' => by`. Distinguish the cases in `hZ : Z' = Z`. Rewrite using `[hZ, h0]`. Conclude with `off hfZ Z' hZ)`. Take `⟨s, hs, hsv⟩` from `GlobalTheory.SecGlueInt.exists_secZ_of_regular E H Dw l Xo c h (e' - e) (fun Z' => genVal Z' (g j) / genVal Z' f) fun C => by`.

Distinguish the cases in `hZ : C.Z = Z`. Use `swap`. Rewrite using `[off (hgZ j) _ hZ, zero_div, mul_zero]`. Conclude with `zero_mem _`. Substitute `hZ` using the available equality.

Take `⟨a, ha1, ha2⟩` from `GlobalTheory.DegCmp.fChart_exists_val C hf`. Use `choose b hb1 hb2 using fun j => GlobalTheory.DegCmp.fChart_exists_val C (hg j)`. Establish `ha0 : (a : Om C.Z) ≠ 0` using `by rw [ha1]; exact mul_ne_zero (Units.ne_zero _) hfz`. Take `⟨u, hu⟩` from `UpperTheory.unfolding_chart_linear_independence E H Dw l Xo c r σ U hσ hU h C m ε hε e e' f g hf hg q hq hfg a b (fun h0 => ha0 (by rw [h0]; rfl)) (ha2 _) (fun j => hb2 j _) j`. Establish `hu' : (b j : Om C.Z) = a * u` using `by rw [hu]; rfl`.

Establish `hp : (∏ i, C.t i ^ e' i) = (∏ i, C.t i ^ (e' - e) i) * ∏ i, C.t i ^ e i`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun i _ => by rw [← zpow_add, Pi.sub_apply, sub_add_cancel]`. Establish `: ((∏ i, C.t i ^ (e' - e) i : (Om C.Z)ˣ) : Om C.Z) * (genVal C.Z (g j) / genVal C.Z f) = u`. Use `mul_left_cancel₀ ha0 ?_` and prove the remaining obligations.

Rewrite using `[← hu', ha1, hb1, hp, Units.val_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `u.2`. Establish `hsv' : ∀ Z' : Comp Xo c, genVal Z' s = genVal Z' (g j) / genVal Z' f` using `fun Z' => (genVal_apply h Z' s).trans (hsv Z')`.

Establish `h1 : idem Z * s = s` using `sub_eq_zero.1 (secZ_eq_zero_of_genVal (sub_mem (idem_mul_mem Z hs).1 hs) fun Z' => by`. Rewrite using `[map_sub, map_mul]`. Distinguish the cases in `hZ : Z' = Z`. Rewrite using `[hZ, GlobalTheory.DegCmp.genVal_idem_self, one_mul, sub_self]`. Rewrite using `[hsv', off (hgZ j) _ hZ, zero_div, mul_zero, sub_self])`.

Use `⟨s, hs, ?_, sub_eq_zero.1 (secZ_eq_zero_of_genVal (sub_mem (sub_add_cancel e' e ▸ mul_mem_secZ hs hf) (hg j)) fun Z' => ?_)⟩` and prove the remaining obligations. Rewrite using `[← h1, mul_comm]`. Conclude with `mul_mem_suppOn s (idem_mem_suppOn Z)`. Rewrite using `[map_sub, map_mul, hsv']`. Distinguish the cases in `hZ : Z' = Z`.

Rewrite using `[hZ, div_mul_cancel₀ _ hfz, sub_self]`. Rewrite using `[off (hgZ j) _ hZ, zero_div, zero_mul, sub_self]`.
-/
theorem UpperTheory.unfolding_component_linear_independence :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (Z : Comp Xo c) (m : ℕ) (ε : Fin m → ℂ), (∀ a : Fin m → c.F, ∑ j, σ (a j) * ε j = 0 → a = 0) → ∀ (e e' : Formalism.L2.Pj.Ix Dw → ℤ) (f : Rul Xo c) (g : Fin m → Rul Xo c), f ∈ secZ Xo c e → f ∈ suppOn Z → f ≠ 0 → (∀ j, g j ∈ secZ Xo c e') → (∀ j, g j ∈ suppOn Z) → ∀ q : FDSec U.X, (∀ k, ContinuousOn (q k) (U.X k).dom) → (∀ z ∈ framesOn U Z, ∑ j, ε j * rdU U (g j) z.1 z.2 = q z.1 z.2 * rdU U f z.1 z.2) → ∀ j, ∃ s ∈ secZ Xo c (e' - e), s ∈ suppOn Z ∧ s * f = g j := by
  intro E _ _ _ H Dw l Xo c r σ U hσ hU Z m ε hε e e' f g hf hfZ hf0 hg hgZ q hq hfg j
  obtain ⟨-, -, h, -⟩ := evLaws_genFr_atlas E H Dw l Xo c
  have off : ∀ {u : Rul Xo c}, u ∈ suppOn Z → ∀ Z', Z' ≠ Z → genVal Z' u = 0 := fun hu Z' hZ => by
    rw [genVal_apply h]; exact evC_eq_zero h hZ hu
  have hfz : genVal Z f ≠ 0 := fun h0 => hf0 (secZ_eq_zero_of_genVal hf fun Z' => by
    by_cases hZ : Z' = Z
    · rw [hZ, h0]
    · exact off hfZ Z' hZ)
  obtain ⟨s, hs, hsv⟩ := GlobalTheory.SecGlueInt.exists_secZ_of_regular E H Dw l Xo c h (e' - e)
    (fun Z' => genVal Z' (g j) / genVal Z' f) fun C => by
      by_cases hZ : C.Z = Z
      swap
      · rw [off (hgZ j) _ hZ, zero_div, mul_zero]; exact zero_mem _
      subst hZ
      obtain ⟨a, ha1, ha2⟩ := GlobalTheory.DegCmp.fChart_exists_val C hf
      choose b hb1 hb2 using fun j => GlobalTheory.DegCmp.fChart_exists_val C (hg j)
      have ha0 : (a : Om C.Z) ≠ 0 := by rw [ha1]; exact mul_ne_zero (Units.ne_zero _) hfz
      obtain ⟨u, hu⟩ := UpperTheory.unfolding_chart_linear_independence E H Dw l Xo c r σ U hσ hU h C m ε hε e e' f g hf hg q hq hfg a b
        (fun h0 => ha0 (by rw [h0]; rfl)) (ha2 _) (fun j => hb2 j _) j
      have hu' : (b j : Om C.Z) = a * u := by rw [hu]; rfl
      have hp : (∏ i, C.t i ^ e' i) = (∏ i, C.t i ^ (e' - e) i) * ∏ i, C.t i ^ e i := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => by rw [← zpow_add, Pi.sub_apply, sub_add_cancel]
      have : ((∏ i, C.t i ^ (e' - e) i : (Om C.Z)ˣ) : Om C.Z) * (genVal C.Z (g j) / genVal C.Z f) = u := by
        refine mul_left_cancel₀ ha0 ?_
        rw [← hu', ha1, hb1, hp, Units.val_mul]
        field_simp
      rw [this]
      exact u.2
  have hsv' : ∀ Z' : Comp Xo c, genVal Z' s = genVal Z' (g j) / genVal Z' f :=
    fun Z' => (genVal_apply h Z' s).trans (hsv Z')
  have h1 : idem Z * s = s :=
    sub_eq_zero.1 (secZ_eq_zero_of_genVal (sub_mem (idem_mul_mem Z hs).1 hs) fun Z' => by
      rw [map_sub, map_mul]
      by_cases hZ : Z' = Z
      · rw [hZ, GlobalTheory.DegCmp.genVal_idem_self, one_mul, sub_self]
      · rw [hsv', off (hgZ j) _ hZ, zero_div, mul_zero, sub_self])
  refine ⟨s, hs, ?_,
    sub_eq_zero.1 (secZ_eq_zero_of_genVal (sub_mem (sub_add_cancel e' e ▸ mul_mem_secZ hs hf) (hg j)) fun Z' => ?_)⟩
  · rw [← h1, mul_comm]
    exact mul_mem_suppOn s (idem_mem_suppOn Z)
  · rw [map_sub, map_mul, hsv']
    by_cases hZ : Z' = Z
    · rw [hZ, div_mul_cancel₀ _ hfz, sub_self]
    · rw [off (hgZ j) _ hZ, zero_div, zero_mul, sub_self]
