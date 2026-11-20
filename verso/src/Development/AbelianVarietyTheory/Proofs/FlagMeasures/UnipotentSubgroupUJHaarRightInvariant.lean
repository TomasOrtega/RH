import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHaarMeasureOfSigmaFinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJHaarEntryBoundedPolynomialGrowthStatement
open MeasureTheory

noncomputable section

open scoped ENNReal NNReal

namespace GlobalTheory.UJUnimod

variable {n : ℕ}

def Bd (a : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) : Prop := ∀ i j, ‖a i j‖ ≤ R

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `: ∀ l ∈ (Finset.univ : Finset (Fin n)), ‖a i l * b l j‖ ≤ R * R'` using `fun l _ => by`. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul (ha i l) (hb l j) (norm_nonneg _) ((norm_nonneg _).trans (ha i l))`. Simplify using `using Finset.sum_le_card_nsmul _ _ _ this`.
-/
theorem Bd.mul {a b : Matrix (Fin n) (Fin n) ℂ} {R R' : ℝ} (ha : Bd a R) (hb : Bd b R') :
    Bd (a * b) ((n : ℝ) * (R * R')) := by
  intro i j
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ l ∈ (Finset.univ : Finset (Fin n)), ‖a i l * b l j‖ ≤ R * R' := fun l _ => by
    rw [norm_mul]
    exact mul_le_mul (ha i l) (hb l j) (norm_nonneg _) ((norm_nonneg _).trans (ha i l))
  simpa using Finset.sum_le_card_nsmul _ _ _ this

/- English proof (translation)
Use `set X := g - 1 with hX`. Establish `e : g = X + 1` using `by simp [hX]`. Use `⟨∑ l ∈ Finset.range m, ∑ i, ∑ j, ‖(X ^ l) i j‖, by positivity, fun p i j => ?_⟩` and prove the remaining obligations. Use `set B := ∑ l ∈ Finset.range m, ∑ i, ∑ j, ‖(X ^ l) i j‖ with hB`. Establish `hB0 : 0 ≤ B` using `by positivity`.

Rewrite using `[e, (Commute.one_right X).add_pow, Matrix.sum_apply]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `: ∀ l ∈ Finset.range (p + 1), ‖(X ^ l * 1 ^ (p - l) * (p.choose l : Matrix (Fin n) (Fin n) ℂ)) i j‖ ≤ B * ((p : ℝ) + 1) ^ m` using `fun l _ => by`. Distinguish the cases in `hl : l < m`. Establish `h1 : ‖(X ^ l) i j‖ ≤ B` using `((Finset.single_le_sum (f := fun j => ‖(X ^ l) i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖(X ^ l) i j‖) (fun _ _ => by positivity) (Finset.mem_univ i))).trans (Finset.single_le_sum (f := fun l => ∑ i, ∑ j, ‖(X ^ l) i j‖) …`.

Establish `h2 : (p.choose l : ℝ) ≤ ((p : ℝ) + 1) ^ m`. Establish `h3 : (p.choose l : ℝ) ≤ (p : ℝ) ^ l` using `by exact_mod_cast Nat.choose_le_pow p l`. Establish `h4 : (0 : ℝ) ≤ p` using `Nat.cast_nonneg p`. Conclude with `h3.trans ((pow_le_pow_left₀ h4 (by linarith) l).trans (pow_le_pow_right₀ (by linarith) hl.le))`. Rewrite using `[one_pow, mul_one, ← nsmul_eq_mul', Matrix.smul_apply, nsmul_eq_mul, norm_mul, Complex.norm_natCast, mul_comm]`.

Conclude with `mul_le_mul h1 h2 (Nat.cast_nonneg _) hB0`. Rewrite using `[pow_eq_zero_of_le (not_lt.1 hl) hg]`. Simplify using `only [zero_mul, Matrix.zero_apply, norm_zero]`. Check the signs of the components of the expression. Use `(Finset.sum_le_card_nsmul _ _ _ this).trans (le_of_eq ?_)` and prove the remaining obligations.

Simplify using `only [Finset.card_range, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bd_pow {g : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} (hg : (g - 1) ^ m = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℕ, Bd (g ^ j) (B * ((j : ℝ) + 1) ^ (m + 1)) := by
  set X := g - 1 with hX
  have e : g = X + 1 := by simp [hX]
  refine ⟨∑ l ∈ Finset.range m, ∑ i, ∑ j, ‖(X ^ l) i j‖, by positivity, fun p i j => ?_⟩
  set B := ∑ l ∈ Finset.range m, ∑ i, ∑ j, ‖(X ^ l) i j‖ with hB
  have hB0 : 0 ≤ B := by positivity
  rw [e, (Commute.one_right X).add_pow, Matrix.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ l ∈ Finset.range (p + 1), ‖(X ^ l * 1 ^ (p - l) * (p.choose l : Matrix (Fin n) (Fin n) ℂ)) i j‖ ≤
      B * ((p : ℝ) + 1) ^ m := fun l _ => by
    by_cases hl : l < m
    · have h1 : ‖(X ^ l) i j‖ ≤ B :=
        ((Finset.single_le_sum (f := fun j => ‖(X ^ l) i j‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)).trans
          (Finset.single_le_sum (f := fun i => ∑ j, ‖(X ^ l) i j‖) (fun _ _ => by positivity)
            (Finset.mem_univ i))).trans
          (Finset.single_le_sum (f := fun l => ∑ i, ∑ j, ‖(X ^ l) i j‖) (fun _ _ => by positivity)
            (Finset.mem_range.2 hl))
      have h2 : (p.choose l : ℝ) ≤ ((p : ℝ) + 1) ^ m := by
        have h3 : (p.choose l : ℝ) ≤ (p : ℝ) ^ l := by exact_mod_cast Nat.choose_le_pow p l
        have h4 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
        exact h3.trans ((pow_le_pow_left₀ h4 (by linarith) l).trans (pow_le_pow_right₀ (by linarith) hl.le))
      rw [one_pow, mul_one, ← nsmul_eq_mul', Matrix.smul_apply, nsmul_eq_mul, norm_mul, Complex.norm_natCast,
        mul_comm]
      exact mul_le_mul h1 h2 (Nat.cast_nonneg _) hB0
    · rw [pow_eq_zero_of_le (not_lt.1 hl) hg]
      simp only [zero_mul, Matrix.zero_apply, norm_zero]
      positivity
  refine (Finset.sum_le_card_nsmul _ _ _ this).trans (le_of_eq ?_)
  simp only [Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.UJUnimod

namespace GlobalTheory.UJUnimod

/- English proof (translation)
Introduce `n ε m S hS hu μ hμ`. Take `⟨hσ, h0, hc, hl⟩` from `hμ`. Establish `hce : Topology.IsClosedEmbedding S.subtype` using `hS.isClosedEmbedding_subtypeVal`. Establish `hφ : MeasurableEmbedding S.subtype` using `hce.measurableEmbedding`. Use `haveI : LocallyCompactSpace S := hce.locallyCompactSpace`.

Use `haveI : SecondCountableTopology S := hce.isEmbedding.secondCountableTopology`. Establish `h2 : (μ.comap S.subtype).map S.subtype = μ`. Rewrite using `[hφ.map_comap]`. Use `Measure.restrict_eq_self_of_ae_mem ?_` and prove the remaining obligations. Establish `: Set.range S.subtype = (S : Set (Formalism.REAL.UJ ε))` using `Subtype.range_coe`.

Rewrite using `[this]`. Conclude with `hc`. Use `set ν : Measure S := μ.comap S.subtype with hν`. Use `haveI : SigmaFinite ν := SigmaFinite.of_map _ hφ.measurable.aemeasurable (by rwa [h2])`. Use `haveI : ν.IsMulLeftInvariant := ⟨fun g => by`.

Apply `hφ.map_injective` to reduce the goal to its premises. Establish `hm : Measurable fun x : Formalism.REAL.UJ ε => (g : Formalism.REAL.UJ ε) * x` using `measurable_const_mul _`. Rewrite using `[Measure.map_map hφ.measurable (measurable_const_mul g), h2]`. Use `conv_rhs => rw [← hl g g.2, ← h2, Measure.map_map hm hφ.measurable]`. Use the proof step `rfl⟩`.

Use `haveI : ν.IsHaarMeasure := GlobalTheory.SnMass.ProdQuot.isHaarMeasure_of_sigmaFinite ν fun h => h0 (by rw [← h2, h, Measure.map_zero])`. Establish `hfin : IsFiniteMeasureOnCompacts μ` using `⟨fun K hK => by`. Rewrite using `[← h2, hφ.map_apply]`. Conclude with `(hce.isCompact_preimage hK).measure_lt_top⟩`. Establish `hmod : ∀ s : S, μ.map (fun x => x * (s : Formalism.REAL.UJ ε)) = (Measure.modularCharacter s : ℝ≥0∞) • μ`.

Introduce `s`. Establish `e1 : ν.map (· * s) = (Measure.modularCharacter s : ℝ≥0∞) • ν`. Rewrite using `[show (Measure.modularCharacter s : ℝ≥0) = Measure.modularCharacterFun s from rfl, Measure.modularCharacterFun_eq_haarScalarFactor ν s]`. Conclude with `Measure.isMulLeftInvariant_eq_smul _ ν`. Use `conv_lhs => rw [← h2]`.

Rewrite using `[Measure.map_map (measurable_mul_const _) hφ.measurable]`. Establish `: (fun x : Formalism.REAL.UJ ε => x * (s : Formalism.REAL.UJ ε)) ∘ S.subtype = S.subtype ∘ (· * s)`. Use function extensionality and compare the values at `x`. Both sides reduce to the same expression. Rewrite using `[this, ← Measure.map_map hφ.measurable (measurable_mul_const _), e1, Measure.map_smul, h2]`.

Establish `key : ∀ s : S, Measure.modularCharacter s ≤ 1`. Introduce `s`. Use `set Δ := Measure.modularCharacter s with hΔ`. Take `⟨C, D, hgr⟩` from `GlobalTheory.T.unitaryJ_haar_entryBounded_polynomial_growth ε S hS μ ⟨hσ, h0, hc, hl⟩ hfin`. Take `⟨B, hB, hpow⟩` from `bd_pow (hu _ (S.inv_mem s.2))`.

Set `Bx : ℝ → Set (Formalism.REAL.UJ ε)` to `fun R => {g | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R}`. Take `⟨ρ, hρ⟩ : ∃ ρ : ℕ, μ (Bx ((ρ : ℝ) + 1)) ≠ 0` from `by by_contra! h`. Apply `h0` to reduce the goal to its premises. Rewrite using `[← Measure.measure_univ_eq_zero]`. Establish `: (Set.univ : Set (Formalism.REAL.UJ ε)) = ⋃ ρ : ℕ, Bx ((ρ : ℝ) + 1)`.

Use extensionality with `g`. Simplify using `only [Set.mem_univ, Set.mem_iUnion, true_iff]`. Take `⟨N, hN⟩` from `exists_nat_ge (∑ i, ∑ j, ‖Formalism.MainNotions.S.uMat g i j‖)`. Use `⟨N, fun i j => ?_⟩` and prove the remaining obligations. Use `(Finset.single_le_sum (f := fun j => ‖Formalism.MainNotions.S.uMat g i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖Formalism.MainNotions.S.uMat g i j‖) (fun _ _ => by positivity) (Finset.mem_univ i))` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[this]`. Conclude with `measure_iUnion_null h`. Use `set ρ' : ℝ := (ρ : ℝ) + 1 with hρ'`. Establish `hρ1 : 1 ≤ ρ'` using `by rw [hρ']; linarith [Nat.cast_nonneg (α := ℝ) ρ]`.

Choose the witnesses or unpack the hypotheses as in `⟨C', hC', hgr'⟩ : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ R : ℝ, 1 ≤ R → (μ (Bx R)).toReal ≤ C' * R ^ D ∧ μ (Bx R) < ⊤ := by`. Use `⟨max C 0, le_max_right _ _, fun R hR => ?_⟩` and prove the remaining obligations. Establish `h1 : μ (Bx R) ≤ ENNReal.ofReal (max C 0 * R ^ D)` using `(hgr R hR).trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))`. Use `⟨?_, h1.trans_lt ENNReal.ofReal_lt_top⟩` and prove the remaining obligations. Use `ENNReal.toReal_mono ENNReal.ofReal_ne_top h1` as an intermediate fact.

Rewrite `this` using `[ENNReal.toReal_ofReal (by positivity)]`. Then use the resulting hypothesis. Establish `hv : 0 < (μ (Bx ρ')).toReal` using `ENNReal.toReal_pos hρ (hgr' ρ' hρ1).2.ne`. Use `set K : ℝ := ((n : ℝ) + 1) * ρ' * (B + 1) with hK`. Establish `hK1 : 1 ≤ K`. Rewrite using `[hK]`.

Establish `: (1 : ℝ) ≤ (n : ℝ) + 1` using `by linarith [Nat.cast_nonneg (α := ℝ) n]`. Establish `h2 : (1 : ℝ) ≤ B + 1` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Establish `hU : ∀ (a : Formalism.REAL.UJ ε) (j : ℕ), Formalism.MainNotions.S.uMat (a ^ j) = Formalism.MainNotions.S.uMat a ^ j` using `fun a j => map_pow ((Units.coeHom (Matrix (Fin n) (Fin n) ℂ)).comp (Formalism.REAL.UJ ε).subtype) a j`. Establish `em : ∀ j : ℕ, μ.map (fun x => x * ((s : Formalism.REAL.UJ ε) ^ j)) = ((Δ : ℝ≥0∞) ^ j) • μ`.

Introduce `j`. Use `hmod (s ^ j)` as an intermediate fact. Rewrite `this` using `[map_pow]`. Simplify using `using this`. Establish `key2 : ∀ j : ℕ, (Δ : ℝ) ^ j * (μ (Bx ρ')).toReal ≤ C' * K ^ D * ((j : ℝ) + 1) ^ ((m + 1) * D)`.

Introduce `j`. Establish `ht : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ (m + 1)` using `one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) j])`. Establish `hme : MeasurableEmbedding (fun x : Formalism.REAL.UJ ε => x * ((s : Formalism.REAL.UJ ε) ^ j))` using `(Homeomorph.mulRight ((s : Formalism.REAL.UJ ε) ^ j)).measurableEmbedding`. Establish `h1 : (((Δ : ℝ≥0∞) ^ j) • μ) (Bx ρ') ≤ μ (Bx (K * ((j : ℝ) + 1) ^ (m + 1)))`. Rewrite using `[← em, hme.map_apply]`.

Use `measure_mono fun x hx => ?_` and prove the remaining obligations. Establish `hx' : x = (x * (s : Formalism.REAL.UJ ε) ^ j) * ((s : Formalism.REAL.UJ ε)⁻¹) ^ j`. Rewrite using `[mul_assoc, inv_pow, mul_inv_cancel, mul_one]`. Establish `h2` using `(show Bd (Formalism.MainNotions.S.uMat (x * (s : Formalism.REAL.UJ ε) ^ j)) ρ' from hx).mul (hpow j)`. Establish `h3 : Formalism.MainNotions.S.uMat x = Formalism.MainNotions.S.uMat (x * (s : Formalism.REAL.UJ ε) ^ j) * Formalism.MainNotions.S.uMat (((s : S)⁻¹ : S) : Formalism.REAL.UJ ε) ^ j`.

Rewrite using `[← hU]`. Use `conv_lhs => rw [hx']`. Both sides reduce to the same expression. Introduce `i k`. Rewrite using `[h3]`.

Use `(h2 i k).trans ?_` and prove the remaining obligations. Rewrite using `[hK]`. Establish `hB' : B ≤ B + 1` using `by linarith`. Establish `hn' : (n : ℝ) ≤ (n : ℝ) + 1` using `by linarith`. Establish `h0ρ : 0 ≤ ρ'` using `by linarith`.

Combine the equalities or inequalities in the displayed calculation. Establish `hR1 : 1 ≤ K * ((j : ℝ) + 1) ^ (m + 1)` using `by nlinarith`. Establish `h2` using `(ENNReal.toReal_mono (hgr' _ hR1).2.ne h1).trans (hgr' _ hR1).1`. Rewrite `h2` using `[Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, mul_pow, ← pow_mul, ← mul_assoc]`. Simplify using `using h2`.

Use `by_contra! h1`. Establish `h2 : 1 < (Δ : ℝ)` using `by exact_mod_cast h1`. Establish `h3` using `((tendsto_pow_const_div_const_pow_of_one_lt ((m + 1) * D) h2).comp (Filter.tendsto_add_atTop_nat 1)).const_mul (C' * K ^ D * (Δ : ℝ))`. Rewrite `h3` using `[mul_zero]`. Take `⟨j, hj⟩` from `(h3.eventually (gt_mem_nhds hv)).exists`.

Establish `h4` using `key2 j`. Establish `h5 : 0 < (Δ : ℝ) ^ j` using `by positivity`. Simplify using `only [Function.comp_apply, Nat.cast_add, Nat.cast_one] at hj`. Establish `h6 : C' * K ^ D * (Δ : ℝ) * (((j : ℝ) + 1) ^ ((m + 1) * D) / (Δ : ℝ) ^ (j + 1)) = C' * K ^ D * ((j : ℝ) + 1) ^ ((m + 1) * D) / (Δ : ℝ) ^ j`. Establish `: (Δ : ℝ) ≠ 0` using `by positivity`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite `hj` using `[h6, div_lt_iff₀ h5]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `s hs`.

Establish `e1` using `key ⟨s, hs⟩`. Establish `e2` using `key (⟨s, hs⟩ : S)⁻¹`. Establish `e3 : Measure.modularCharacter (⟨s, hs⟩ : S) = 1`. Use `map_mul Measure.modularCharacter (⟨s, hs⟩ : S) (⟨s, hs⟩ : S)⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, map_one]`.

Use `le_antisymm e1 ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `hmod ⟨s, hs⟩` as an intermediate fact. Rewrite `this` using `[e3]`. Simplify using `using this`.
-/
theorem unimodular_of_unipotent : ∀ {n : ℕ} (ε : Fin n → Bool) (m : ℕ) (S : Subgroup (Formalism.REAL.UJ ε)),
    IsClosed (S : Set (Formalism.REAL.UJ ε)) → (∀ g ∈ S, (Formalism.MainNotions.S.uMat g - 1) ^ m = 0) →
    ∀ μ : Measure (Formalism.REAL.UJ ε), Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ →
    ∀ s ∈ S, μ.map (fun x => x * s) = μ := by
  intro n ε m S hS hu μ hμ
  obtain ⟨hσ, h0, hc, hl⟩ := hμ
  have hce : Topology.IsClosedEmbedding S.subtype := hS.isClosedEmbedding_subtypeVal
  have hφ : MeasurableEmbedding S.subtype := hce.measurableEmbedding
  haveI : LocallyCompactSpace S := hce.locallyCompactSpace
  haveI : SecondCountableTopology S := hce.isEmbedding.secondCountableTopology
  have h2 : (μ.comap S.subtype).map S.subtype = μ := by
    rw [hφ.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    have : Set.range S.subtype = (S : Set (Formalism.REAL.UJ ε)) := Subtype.range_coe
    rw [this]
    exact hc
  set ν : Measure S := μ.comap S.subtype with hν
  haveI : SigmaFinite ν := SigmaFinite.of_map _ hφ.measurable.aemeasurable (by rwa [h2])
  haveI : ν.IsMulLeftInvariant := ⟨fun g => by
    apply hφ.map_injective
    have hm : Measurable fun x : Formalism.REAL.UJ ε => (g : Formalism.REAL.UJ ε) * x := measurable_const_mul _
    rw [Measure.map_map hφ.measurable (measurable_const_mul g), h2]
    conv_rhs => rw [← hl g g.2, ← h2, Measure.map_map hm hφ.measurable]
    rfl⟩
  haveI : ν.IsHaarMeasure :=
    GlobalTheory.SnMass.ProdQuot.isHaarMeasure_of_sigmaFinite ν fun h => h0 (by rw [← h2, h, Measure.map_zero])
  have hfin : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => by
    rw [← h2, hφ.map_apply]
    exact (hce.isCompact_preimage hK).measure_lt_top⟩

  have hmod : ∀ s : S, μ.map (fun x => x * (s : Formalism.REAL.UJ ε)) =
      (Measure.modularCharacter s : ℝ≥0∞) • μ := by
    intro s
    have e1 : ν.map (· * s) = (Measure.modularCharacter s : ℝ≥0∞) • ν := by
      rw [show (Measure.modularCharacter s : ℝ≥0) = Measure.modularCharacterFun s from rfl,
        Measure.modularCharacterFun_eq_haarScalarFactor ν s]
      exact Measure.isMulLeftInvariant_eq_smul _ ν
    conv_lhs => rw [← h2]
    rw [Measure.map_map (measurable_mul_const _) hφ.measurable]
    have : (fun x : Formalism.REAL.UJ ε => x * (s : Formalism.REAL.UJ ε)) ∘ S.subtype = S.subtype ∘ (· * s) := by
      funext x; rfl
    rw [this, ← Measure.map_map hφ.measurable (measurable_mul_const _), e1, Measure.map_smul, h2]

  have key : ∀ s : S, Measure.modularCharacter s ≤ 1 := by
    intro s
    set Δ := Measure.modularCharacter s with hΔ
    obtain ⟨C, D, hgr⟩ := GlobalTheory.T.unitaryJ_haar_entryBounded_polynomial_growth ε S hS μ ⟨hσ, h0, hc, hl⟩ hfin
    obtain ⟨B, hB, hpow⟩ := bd_pow (hu _ (S.inv_mem s.2))
    let Bx : ℝ → Set (Formalism.REAL.UJ ε) := fun R => {g | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R}
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ, μ (Bx ((ρ : ℝ) + 1)) ≠ 0 := by
      by_contra! h
      apply h0
      rw [← Measure.measure_univ_eq_zero]
      have : (Set.univ : Set (Formalism.REAL.UJ ε)) = ⋃ ρ : ℕ, Bx ((ρ : ℝ) + 1) := by
        ext g
        simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
        obtain ⟨N, hN⟩ := exists_nat_ge (∑ i, ∑ j, ‖Formalism.MainNotions.S.uMat g i j‖)
        refine ⟨N, fun i j => ?_⟩
        have := (Finset.single_le_sum (f := fun j => ‖Formalism.MainNotions.S.uMat g i j‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖Formalism.MainNotions.S.uMat g i j‖)
          (fun _ _ => by positivity) (Finset.mem_univ i))
        linarith
      rw [this]
      exact measure_iUnion_null h
    set ρ' : ℝ := (ρ : ℝ) + 1 with hρ'
    have hρ1 : 1 ≤ ρ' := by rw [hρ']; linarith [Nat.cast_nonneg (α := ℝ) ρ]
    obtain ⟨C', hC', hgr'⟩ : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ R : ℝ, 1 ≤ R → (μ (Bx R)).toReal ≤ C' * R ^ D ∧ μ (Bx R) < ⊤ := by
      refine ⟨max C 0, le_max_right _ _, fun R hR => ?_⟩
      have h1 : μ (Bx R) ≤ ENNReal.ofReal (max C 0 * R ^ D) :=
        (hgr R hR).trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))
      refine ⟨?_, h1.trans_lt ENNReal.ofReal_lt_top⟩
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have hv : 0 < (μ (Bx ρ')).toReal := ENNReal.toReal_pos hρ (hgr' ρ' hρ1).2.ne
    set K : ℝ := ((n : ℝ) + 1) * ρ' * (B + 1) with hK
    have hK1 : 1 ≤ K := by
      rw [hK]
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have h2 : (1 : ℝ) ≤ B + 1 := by linarith
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ _ := by gcongr
    have hU : ∀ (a : Formalism.REAL.UJ ε) (j : ℕ), Formalism.MainNotions.S.uMat (a ^ j) = Formalism.MainNotions.S.uMat a ^ j := fun a j =>
      map_pow ((Units.coeHom (Matrix (Fin n) (Fin n) ℂ)).comp (Formalism.REAL.UJ ε).subtype) a j
    have em : ∀ j : ℕ, μ.map (fun x => x * ((s : Formalism.REAL.UJ ε) ^ j)) = ((Δ : ℝ≥0∞) ^ j) • μ := by
      intro j
      have := hmod (s ^ j)
      rw [map_pow] at this
      simpa using this
    have key2 : ∀ j : ℕ, (Δ : ℝ) ^ j * (μ (Bx ρ')).toReal ≤ C' * K ^ D * ((j : ℝ) + 1) ^ ((m + 1) * D) := by
      intro j
      have ht : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ (m + 1) := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) j])
      have hme : MeasurableEmbedding (fun x : Formalism.REAL.UJ ε => x * ((s : Formalism.REAL.UJ ε) ^ j)) :=
        (Homeomorph.mulRight ((s : Formalism.REAL.UJ ε) ^ j)).measurableEmbedding
      have h1 : (((Δ : ℝ≥0∞) ^ j) • μ) (Bx ρ') ≤ μ (Bx (K * ((j : ℝ) + 1) ^ (m + 1))) := by
        rw [← em, hme.map_apply]
        refine measure_mono fun x hx => ?_
        have hx' : x = (x * (s : Formalism.REAL.UJ ε) ^ j) * ((s : Formalism.REAL.UJ ε)⁻¹) ^ j := by
          rw [mul_assoc, inv_pow, mul_inv_cancel, mul_one]
        have h2 := (show Bd (Formalism.MainNotions.S.uMat (x * (s : Formalism.REAL.UJ ε) ^ j)) ρ' from hx).mul (hpow j)
        have h3 : Formalism.MainNotions.S.uMat x = Formalism.MainNotions.S.uMat (x * (s : Formalism.REAL.UJ ε) ^ j) *
            Formalism.MainNotions.S.uMat (((s : S)⁻¹ : S) : Formalism.REAL.UJ ε) ^ j := by
          rw [← hU]
          conv_lhs => rw [hx']
          rfl
        intro i k
        rw [h3]
        refine (h2 i k).trans ?_
        rw [hK]
        have hB' : B ≤ B + 1 := by linarith
        have hn' : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
        have h0ρ : 0 ≤ ρ' := by linarith
        calc (n : ℝ) * (ρ' * (B * ((j : ℝ) + 1) ^ (m + 1))) = (n : ℝ) * ρ' * B * ((j : ℝ) + 1) ^ (m + 1) := by ring
          _ ≤ ((n : ℝ) + 1) * ρ' * (B + 1) * ((j : ℝ) + 1) ^ (m + 1) := by gcongr
      have hR1 : 1 ≤ K * ((j : ℝ) + 1) ^ (m + 1) := by nlinarith
      have h2 := (ENNReal.toReal_mono (hgr' _ hR1).2.ne h1).trans (hgr' _ hR1).1
      rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, mul_pow, ← pow_mul,
        ← mul_assoc] at h2
      simpa using h2
    by_contra! h1
    have h2 : 1 < (Δ : ℝ) := by exact_mod_cast h1
    have h3 := ((tendsto_pow_const_div_const_pow_of_one_lt ((m + 1) * D) h2).comp
      (Filter.tendsto_add_atTop_nat 1)).const_mul (C' * K ^ D * (Δ : ℝ))
    rw [mul_zero] at h3
    obtain ⟨j, hj⟩ := (h3.eventually (gt_mem_nhds hv)).exists
    have h4 := key2 j
    have h5 : 0 < (Δ : ℝ) ^ j := by positivity
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one] at hj
    have h6 : C' * K ^ D * (Δ : ℝ) * (((j : ℝ) + 1) ^ ((m + 1) * D) / (Δ : ℝ) ^ (j + 1)) =
        C' * K ^ D * ((j : ℝ) + 1) ^ ((m + 1) * D) / (Δ : ℝ) ^ j := by
      have : (Δ : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    rw [h6, div_lt_iff₀ h5] at hj
    linarith
  intro s hs
  have e1 := key ⟨s, hs⟩
  have e2 := key (⟨s, hs⟩ : S)⁻¹
  have e3 : Measure.modularCharacter (⟨s, hs⟩ : S) = 1 := by
    have := map_mul Measure.modularCharacter (⟨s, hs⟩ : S) (⟨s, hs⟩ : S)⁻¹
    rw [mul_inv_cancel, map_one] at this
    refine le_antisymm e1 ?_
    calc (1 : ℝ≥0) = _ := this
      _ ≤ Measure.modularCharacter (⟨s, hs⟩ : S) * 1 := mul_le_mul_of_nonneg_left e2 zero_le
      _ = _ := mul_one _
  have := hmod ⟨s, hs⟩
  rw [e3] at this
  simpa using this

end GlobalTheory.UJUnimod
