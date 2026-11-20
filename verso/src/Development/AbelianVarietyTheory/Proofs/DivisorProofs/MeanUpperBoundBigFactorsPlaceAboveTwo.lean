import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import Development.AutomorphicArithmetic.CMTraceForms.Places
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartColengthBoundPrimeTwo
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ColengthBoundSplitPlaceChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFlagCharactersLeadingMinorsColength
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyClosedValuedExtensionOfCDVR
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagStepCharactersOfColengthStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c`. Use `letI := H.starRing`. Introduce `p hp F vd hTP T io y h2 hy`. Take `⟨Ch, -⟩` from `(@GlobalTheory.IntChartExists.intChart_exists E _ _ _ H Dw l Xo c H.starRing).2.2 (fun _ => rfl) T io y`. Take `⟨X⟩` from `GlobalTheory.CharDepth.nonempty_valExt T p h2`.

Take `⟨xs, hAF, hprod⟩` from `GlobalTheory.CharDepth.colength_bound_at_two p (GlobalTheory.ChF.colength_bound_split_place_chart p) E H Dw l Xo c T io y Ch X hy F vd hTP`. Use `set v2 : ℝ := (X.v ((p : ℕ) : X.C) : ℝ) with hv2`. Use `set B : ℝ := (F : ℝ) * Dw.q * (1 + vd / 2) with hB`. Establish `hv2pos : 0 < v2`. Rewrite using `[hv2, NNReal.coe_pos, pos_iff_ne_zero, Ne, map_eq_zero]`.

Conclude with `Nat.cast_ne_zero.2 hp.out.ne_zero`. Establish `hv2lt : v2 < 1`. Establish `h2C : algebraMap X.O X.C ((p : ℕ) : X.O) = ((p : ℕ) : X.C)` using `map_natCast _ _`. Establish `hle` using `X.ints.map_le_one ((p : ℕ) : X.O)`. Establish `hne : X.v (algebraMap X.O X.C ((p : ℕ) : X.O)) ≠ 1` using `fun h => X.nonunit.out ((X.ints.isUnit_iff_valuation_eq_one).2 h)`.

Rewrite `hle`, `hne` using `[h2C]`. Rewrite using `[hv2]`. Conclude with `lt_of_le_of_ne hle hne` after adjusting the coercions. Establish `hlogv : Real.log v2 < 0` using `Real.log_neg hv2pos hv2lt`. Establish `hpos : ∀ τ, InPsi H τ → 0 < (xs τ : ℝ)`.

Introduce `τ hτ`. Establish `hP : 0 < ∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ)` using `lt_of_lt_of_le (Real.rpow_pos_of_pos hv2pos _) hprod`. Break down `(NNReal.coe_nonneg (xs τ)).lt_or_eq with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction.

Establish `: ∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ) = 0` using `Finset.prod_eq_zero (Finset.mem_filter.2 ⟨Finset.mem_univ _, hτ⟩) h.symm`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hle1 : ∀ τ, InPsi H τ → (xs τ : ℝ) ≤ 1`. Introduce `τ hτ`. Establish `hne : xs τ ≠ 0` using `fun h => by have := hpos τ hτ; rw [h] at this; simp at this`.

Conclude with `(GlobalTheory.CharDepth.exists_flag_characters X.C X.v X.O X.ints _ _ _ _ _ (hAF τ hτ) hne).1` after adjusting the coercions. Set `len : (E →+* ℂ) → ℝ` to `fun τ => if InPsi H τ then Real.log (xs τ) / Real.log v2 else 0`. Establish `hlen_pow : ∀ τ, InPsi H τ → v2 ^ len τ = (xs τ : ℝ)`. Introduce `τ hτ`. Simplify using `only [len, if_pos hτ]`.

Rewrite using `[Real.rpow_def_of_pos hv2pos, mul_div_cancel₀ _ hlogv.ne, Real.exp_log (hpos τ hτ)]`. Use `⟨len, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `τ`. Distinguish the cases in `hτ : InPsi H τ`. Simplify using `only [len, if_pos hτ]`.

Conclude with `div_nonneg_of_nonpos (Real.log_nonpos (NNReal.coe_nonneg _) (hle1 τ hτ)) hlogv.le`. Simplify using `[len, if_neg hτ]`. Introduce `τ hτ`. Simplify using `[len, if_neg hτ]`. Establish `hsum : ∑ τ, len τ = (∑ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), Real.log (xs τ)) / Real.log v2`.

Rewrite using `[Finset.sum_div, Finset.sum_filter]`. Establish `hlogP : Real.log (∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ)) = ∑ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), Real.log (xs τ)` using `Real.log_prod fun τ hτ => (hpos τ (Finset.mem_filter.1 hτ).2).ne'`. Establish `hlb : B * Real.log v2 ≤ ∑ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), Real.log (xs τ)`. Rewrite using `[← hlogP, ← Real.log_rpow hv2pos]`. Conclude with `Real.log_le_log (Real.rpow_pos_of_pos hv2pos _) hprod`.

Rewrite using `[hsum, div_le_iff_of_neg hlogv]`. Conclude with `hlb`. Introduce `f k hf`. Establish `hr : (X.v ((p : ℕ) : X.C) : ℝ) ^ len f.1 ≤ xs f.1` using `(hlen_pow f.1 hf).le`. Conclude with `(GlobalTheory.T.flagStep_characters_of_colength E H Dw l Xo c p T io y Ch X f (xs f.1) (len f.1) (hAF f.1 hf) hr).2 k`.
-/
theorem mean_bound_big_factors_at_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (F : ℕ) (vd : ℝ), UpperTheory.Depth.SplitPlaces p H F vd → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ¬ IsUnit ((p : ℕ) : T.V) → y.IsAlg → ∃ len : (E →+* ℂ) → ℝ, (∀ τ, 0 ≤ len τ) ∧ (∀ τ, ¬ InPsi H τ → len τ = 0) ∧ ∑ τ, len τ ≤ F * Dw.q * (1 + vd / 2) ∧ ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → nuFac p y f k ≤ ((k * len f.1 : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p hp F vd hTP T io y h2 hy
  classical
  obtain ⟨Ch, -⟩ := (@GlobalTheory.IntChartExists.intChart_exists E _ _ _ H Dw l Xo c H.starRing).2.2 (fun _ => rfl) T io y
  obtain ⟨X⟩ := GlobalTheory.CharDepth.nonempty_valExt T p h2
  obtain ⟨xs, hAF, hprod⟩ := GlobalTheory.CharDepth.colength_bound_at_two p (GlobalTheory.ChF.colength_bound_split_place_chart p)
    E H Dw l Xo c T io y Ch X hy F vd hTP
  set v2 : ℝ := (X.v ((p : ℕ) : X.C) : ℝ) with hv2
  set B : ℝ := (F : ℝ) * Dw.q * (1 + vd / 2) with hB

  have hv2pos : 0 < v2 := by
    rw [hv2, NNReal.coe_pos, pos_iff_ne_zero, Ne, map_eq_zero]
    exact Nat.cast_ne_zero.2 hp.out.ne_zero
  have hv2lt : v2 < 1 := by
    have h2C : algebraMap X.O X.C ((p : ℕ) : X.O) = ((p : ℕ) : X.C) := map_natCast _ _
    have hle := X.ints.map_le_one ((p : ℕ) : X.O)
    have hne : X.v (algebraMap X.O X.C ((p : ℕ) : X.O)) ≠ 1 := fun h =>
      X.nonunit.out ((X.ints.isUnit_iff_valuation_eq_one).2 h)
    rw [h2C] at hle hne
    rw [hv2]
    exact_mod_cast lt_of_le_of_ne hle hne
  have hlogv : Real.log v2 < 0 := Real.log_neg hv2pos hv2lt

  have hpos : ∀ τ, InPsi H τ → 0 < (xs τ : ℝ) := by
    intro τ hτ
    have hP : 0 < ∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ) :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos hv2pos _) hprod
    rcases (NNReal.coe_nonneg (xs τ)).lt_or_eq with h | h
    · exact h
    · exfalso
      have : ∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ) = 0 :=
        Finset.prod_eq_zero (Finset.mem_filter.2 ⟨Finset.mem_univ _, hτ⟩) h.symm
      linarith
  have hle1 : ∀ τ, InPsi H τ → (xs τ : ℝ) ≤ 1 := by
    intro τ hτ
    have hne : xs τ ≠ 0 := fun h => by have := hpos τ hτ; rw [h] at this; simp at this
    exact_mod_cast (GlobalTheory.CharDepth.exists_flag_characters X.C X.v X.O X.ints _ _ _ _ _ (hAF τ hτ) hne).1
  let len : (E →+* ℂ) → ℝ := fun τ => if InPsi H τ then Real.log (xs τ) / Real.log v2 else 0
  have hlen_pow : ∀ τ, InPsi H τ → v2 ^ len τ = (xs τ : ℝ) := by
    intro τ hτ
    simp only [len, if_pos hτ]
    rw [Real.rpow_def_of_pos hv2pos, mul_div_cancel₀ _ hlogv.ne, Real.exp_log (hpos τ hτ)]
  refine ⟨len, ?_, ?_, ?_, ?_⟩
  · intro τ
    by_cases hτ : InPsi H τ
    · simp only [len, if_pos hτ]
      exact div_nonneg_of_nonpos (Real.log_nonpos (NNReal.coe_nonneg _) (hle1 τ hτ)) hlogv.le
    · simp [len, if_neg hτ]
  · intro τ hτ
    simp [len, if_neg hτ]
  · have hsum : ∑ τ, len τ = (∑ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), Real.log (xs τ)) / Real.log v2 := by
      rw [Finset.sum_div, Finset.sum_filter]
    have hlogP : Real.log (∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ)) =
        ∑ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), Real.log (xs τ) :=
      Real.log_prod fun τ hτ => (hpos τ (Finset.mem_filter.1 hτ).2).ne'
    have hlb : B * Real.log v2 ≤ ∑ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), Real.log (xs τ) := by
      rw [← hlogP, ← Real.log_rpow hv2pos]
      exact Real.log_le_log (Real.rpow_pos_of_pos hv2pos _) hprod
    rw [hsum, div_le_iff_of_neg hlogv]
    exact hlb
  · intro f k hf
    have hr : (X.v ((p : ℕ) : X.C) : ℝ) ^ len f.1 ≤ xs f.1 := (hlen_pow f.1 hf).le
    exact (GlobalTheory.T.flagStep_characters_of_colength E H Dw l Xo c p T io y Ch X f (xs f.1) (len f.1) (hAF f.1 hf) hr).2 k

end GlobalTheory.RefSum
