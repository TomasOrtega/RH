import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairOmSumSameDatumLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormTerminalDeterminantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairDefiniteThetaLatticeLeFixedIndexBoundStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

/- English proof (translation)
Rewrite using `[← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]`. Use `ENNReal.tsum_le_tsum fun a => ?_` and prove the remaining obligations. Use `split_ifs with hq`. Take `⟨p, hp, hr⟩` from `h a hq`. Use `le_trans ?_ (Finset.single_le_sum (f := fun p => if R p a then f a else 0) (fun _ _ => zero_le) hp)` and prove the remaining obligations.

Simplify using `[hr]`. Conclude with `zero_le`.
-/
theorem tsum_ite_le_sum_fibres {α β : Type*} (Q : α → Prop) (R : β → α → Prop) (f : α → ℝ≥0∞) (S : Finset β)
    [∀ a, Decidable (Q a)] [∀ p a, Decidable (R p a)]
    (h : ∀ a, Q a → ∃ p ∈ S, R p a) :
    (∑' a, if Q a then f a else 0) ≤ ∑ p ∈ S, ∑' a, if R p a then f a else 0 := by
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun a => ?_
  split_ifs with hq
  · obtain ⟨p, hp, hr⟩ := h a hq
    refine le_trans ?_ (Finset.single_le_sum (f := fun p => if R p a then f a else 0)
      (fun _ _ => zero_le) hp)
    simp [hr]
  · exact zero_le

/- English proof (translation)
Establish `h : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ)` using `by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)`. Use `Real.logb_nonneg (b := 2) (by norm_num) h` as an intermediate fact. Unfold `cf`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cf_nonneg_of_numberField (K : Type) [Field K] [NumberField K] : 0 ≤ cf K := by
  have h : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have := Real.logb_nonneg (b := 2) (by norm_num) h
  unfold cf
  linarith

/- English proof (translation)
Establish `h0 : (0 : ℝ) ≤ (i : ℝ) * b` using `by positivity`. Establish `h1 : ((i : ℝ) * b) ^ 2 ≤ D / G`. Rewrite using `[le_div_iff₀ hG]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : ((i : ℝ) * b) ^ k ≤ (D / G) ^ ((k : ℝ) / 2)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_natCast _ 2, ← Real.rpow_mul h0, ← Real.rpow_natCast]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ _ := Real.rpow_le_rpow (by positivity) h1 (by positivity)`. Establish `h3 : (i : ℝ) ^ c ≤ D ^ c` using `Real.rpow_le_rpow (by positivity) hi hc`. Establish `h4 : 0 ≤ (D / G) ^ ((k : ℝ) / 2)` using `le_trans (by positivity) h2`. Use `gcongr`.
-/
theorem index_pair_bound {G D c X : ℝ} (k i b : ℕ) (hG : 0 < G) (hc : 0 ≤ c) (hX : 0 ≤ X)
    (h : G * (i : ℝ) ^ 2 * (b : ℝ) ^ 2 ≤ D) (hi : (i : ℝ) ≤ D) :
    ((i : ℝ) * b) ^ k * (i : ℝ) ^ c * X ≤ (D / G) ^ ((k : ℝ) / 2) * D ^ c * X := by
  have h0 : (0 : ℝ) ≤ (i : ℝ) * b := by positivity
  have h1 : ((i : ℝ) * b) ^ 2 ≤ D / G := by
    rw [le_div_iff₀ hG]; nlinarith
  have h2 : ((i : ℝ) * b) ^ k ≤ (D / G) ^ ((k : ℝ) / 2) := by
    calc ((i : ℝ) * b) ^ k = (((i : ℝ) * b) ^ 2) ^ ((k : ℝ) / 2) := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul h0, ← Real.rpow_natCast]
          congr 1; push_cast; ring
      _ ≤ _ := Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have h3 : (i : ℝ) ^ c ≤ D ^ c := Real.rpow_le_rpow (by positivity) hi hc
  have h4 : 0 ≤ (D / G) ^ ((k : ℝ) / 2) := le_trans (by positivity) h2
  gcongr

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ`. Take `⟨-, hG, hI, -, hGI, -⟩` from `GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ hg hΛ`. Establish `hG1 : (1 : ℝ) ≤ N.gI g Λ` using `by exact_mod_cast hG`. Establish `hI1 : (1 : ℝ) ≤ N.iI g Λ` using `by exact_mod_cast hI`. Establish `hD : 1 ≤ N.Del` using `le_trans (by nlinarith) hGI`.

Establish `hnD : ∀ l, 0 ≤ N.nD l` using `fun l => by`. Unfold `NF.nD`. Use `split_ifs`. Check the signs of the components of the expression. Conclude with `le_rfl`.

Establish `hDb : 0 ≤ N.Db` using `Finset.prod_nonneg fun l _ => hnD l`. Establish `hNT : 0 ≤ N.NT` using `by unfold NF.NT; positivity`. Establish `hX : 0 ≤ (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)` using `by positivity`. Use `set X := (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3) with hXdef`. Use `set S : Finset (ℕ × ℕ) := (Finset.Icc 1 ⌊N.Del⌋₊ ×ˢ Finset.Icc 1 ⌊N.Del⌋₊).filter (fun p => (N.gI g Λ : ℝ) * (p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2 ≤ N.Del) with hS`.

Establish `hcard : (S.card : ℝ) ≤ N.Del ^ 2`. Establish `h1 : S.card ≤ ⌊N.Del⌋₊ * ⌊N.Del⌋₊`. Use `(Finset.card_filter_le _ _).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `h2 : (⌊N.Del⌋₊ : ℝ) ≤ N.Del` using `Nat.floor_le (by linarith)`.

Combine the equalities or inequalities in the displayed calculation. Establish `hcover : ∀ Λ' : Submodule (𝓞 K) V, N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' → ∃ p ∈ S, N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = p.1 ∧ N.bI Λ' = p.2`. Introduce and unpack `Λ' ⟨h1, h2⟩`. Use `⟨(N.iI g Λ', N.bI Λ'), ?_, h1, h2, rfl, rfl⟩` and prove the remaining obligations. Take `⟨-, -, hI', hb, -⟩` from `GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ' hg h1`.

Establish `hb0` using `(GlobalTheory.T.normal_form_terminal_determinant K V H hK r N g Λ' hg h1).1`. Establish `hgg : N.gI g Λ' = N.gI g Λ`. Unfold `NF.gI flagPairDefinitePartLattice latLa`. Rewrite using `[h2.1, h2.2.2]`. Rewrite `hb` using `[hgg]`.

Establish `hi1 : (1 : ℝ) ≤ N.iI g Λ'` using `by exact_mod_cast hI'`. Establish `hb1 : (1 : ℝ) ≤ N.bI Λ'` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb0`. Establish `hi2 : (N.iI g Λ' : ℝ) ≤ (N.iI g Λ' : ℝ) ^ 2` using `by nlinarith`. Establish `hb2 : (N.bI Λ' : ℝ) ≤ (N.bI Λ' : ℝ) ^ 2` using `by nlinarith`. Rewrite using `[hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]`.

Use `⟨⟨⟨hI', Nat.le_floor ?_⟩, Nat.one_le_iff_ne_zero.2 hb0, Nat.le_floor ?_⟩, hb⟩` and prove the remaining obligations. Use `le_trans ?_ hb` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `le_trans ?_ hb` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `hc` using `cf_nonneg_of_numberField K`. Establish `hY : 0 ≤ (N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ cf K * X`. Establish `: 0 ≤ N.Del` using `by linarith`. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation.

Unfold `NF.omSum`. Conclude with `@tsum_ite_le_sum_fibres _ _ _ _ _ S (fun _ => Classical.propDecidable _) (fun _ _ => Classical.propDecidable _) fun o ho => hcover _ ho`. Use `_ ≤ ∑ _p ∈ S, ENNReal.ofReal ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ cf K * X) := by`. Use `Finset.sum_le_sum fun p hp => ?_` and prove the remaining obligations. Use `(GlobalTheory.T.hermFramePair_omSum_same_datum_le K V H hK r N g Λ hg hΛ p.1 p.2).trans (ENNReal.ofReal_le_ofReal ?_)` and prove the remaining obligations.

Rewrite `hp` using `[hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]`. Use `index_pair_bound _ _ _ (by linarith) hc hX hp.2 ?_` and prove the remaining obligations. Conclude with `le_trans (by exact_mod_cast hp.1.1.2) (Nat.floor_le (by linarith : 0 ≤ N.Del))`. Use `_ = ENNReal.ofReal (S.card * ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ cf K * X)) := by`. Rewrite using `[Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]`.

Use `_ ≤ _ := by`. Use `ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right hcard hY).trans (le_of_eq ?_))` and prove the remaining obligations. Rewrite using `[Real.rpow_add (by linarith), Real.rpow_two]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem omSum_sameDat_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ') ≤ ENNReal.ofReal ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  obtain ⟨-, hG, hI, -, hGI, -⟩ := GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ hg hΛ
  have hG1 : (1 : ℝ) ≤ N.gI g Λ := by exact_mod_cast hG
  have hI1 : (1 : ℝ) ≤ N.iI g Λ := by exact_mod_cast hI
  have hD : 1 ≤ N.Del := le_trans (by nlinarith) hGI
  have hnD : ∀ l, 0 ≤ N.nD l := fun l => by
    unfold NF.nD
    split_ifs
    · positivity
    · exact le_rfl
  have hDb : 0 ≤ N.Db := Finset.prod_nonneg fun l _ => hnD l
  have hNT : 0 ≤ N.NT := by unfold NF.NT; positivity
  have hX : 0 ≤ (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3) := by positivity
  set X := (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3) with hXdef
  set S : Finset (ℕ × ℕ) := (Finset.Icc 1 ⌊N.Del⌋₊ ×ˢ Finset.Icc 1 ⌊N.Del⌋₊).filter
    (fun p => (N.gI g Λ : ℝ) * (p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2 ≤ N.Del) with hS
  have hcard : (S.card : ℝ) ≤ N.Del ^ 2 := by
    have h1 : S.card ≤ ⌊N.Del⌋₊ * ⌊N.Del⌋₊ := by
      refine (Finset.card_filter_le _ _).trans ?_
      simp
    have h2 : (⌊N.Del⌋₊ : ℝ) ≤ N.Del := Nat.floor_le (by linarith)
    calc (S.card : ℝ) ≤ (⌊N.Del⌋₊ : ℝ) * ⌊N.Del⌋₊ := by exact_mod_cast h1
      _ ≤ N.Del * N.Del := by gcongr
      _ = _ := by ring
  have hcover : ∀ Λ' : Submodule (𝓞 K) V, N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' →
      ∃ p ∈ S, N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = p.1 ∧ N.bI Λ' = p.2 := by
    rintro Λ' ⟨h1, h2⟩
    refine ⟨(N.iI g Λ', N.bI Λ'), ?_, h1, h2, rfl, rfl⟩
    obtain ⟨-, -, hI', hb, -⟩ := GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ' hg h1
    have hb0 := (GlobalTheory.T.normal_form_terminal_determinant K V H hK r N g Λ' hg h1).1
    have hgg : N.gI g Λ' = N.gI g Λ := by
      unfold NF.gI flagPairDefinitePartLattice latLa
      rw [h2.1, h2.2.2]
    rw [hgg] at hb
    have hi1 : (1 : ℝ) ≤ N.iI g Λ' := by exact_mod_cast hI'
    have hb1 : (1 : ℝ) ≤ N.bI Λ' := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb0
    have hi2 : (N.iI g Λ' : ℝ) ≤ (N.iI g Λ' : ℝ) ^ 2 := by nlinarith
    have hb2 : (N.bI Λ' : ℝ) ≤ (N.bI Λ' : ℝ) ^ 2 := by nlinarith
    rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨hI', Nat.le_floor ?_⟩, Nat.one_le_iff_ne_zero.2 hb0, Nat.le_floor ?_⟩, hb⟩
    · refine le_trans ?_ hb
      calc (N.iI g Λ' : ℝ) = 1 * (N.iI g Λ' : ℝ) * 1 := by ring
        _ ≤ _ := by gcongr; linarith
    · refine le_trans ?_ hb
      calc (N.bI Λ' : ℝ) = 1 * 1 * (N.bI Λ' : ℝ) := by ring
        _ ≤ _ := by gcongr; linarith
  have hc := cf_nonneg_of_numberField K
  have hY : 0 ≤ (N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ cf K * X := by
    have : 0 ≤ N.Del := by linarith
    positivity
  calc N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ')
      ≤ ∑ p ∈ S, N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = p.1 ∧ N.bI Λ' = p.2) := by
        unfold NF.omSum
        exact @tsum_ite_le_sum_fibres _ _ _ _ _ S (fun _ => Classical.propDecidable _)
          (fun _ _ => Classical.propDecidable _) fun o ho => hcover _ ho
    _ ≤ ∑ _p ∈ S, ENNReal.ofReal
          ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ cf K * X) := by
        refine Finset.sum_le_sum fun p hp => ?_
        refine (GlobalTheory.T.hermFramePair_omSum_same_datum_le K V H hK r N g Λ hg hΛ p.1 p.2).trans (ENNReal.ofReal_le_ofReal ?_)
        rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        refine index_pair_bound _ _ _ (by linarith) hc hX hp.2 ?_
        exact le_trans (by exact_mod_cast hp.1.1.2) (Nat.floor_le (by linarith : 0 ≤ N.Del))
    _ = ENNReal.ofReal (S.card *
          ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ cf K * X)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right hcard hY).trans (le_of_eq ?_))
        rw [Real.rpow_add (by linarith), Real.rpow_two]
        ring

end GlobalTheory.DegCnt
