import Formalism.HarderNarasimhan.StatementFrame
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PlaceSplit
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNSlopes
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNExtreme
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNStep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermod
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.RatioMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FinSup
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.TwistFinrankEq
import Formalism.CorankShare.CorankShareProofs.LayerCakeFormula
import Formalism.CorankShare.CorankShareProofs.SumNormSqLeHilbertSchmidt

open Module NumberField Finset Formalism.CorankShareLayerCake.FR

noncomputable section

namespace Formalism.HN

/- English proof (translation)
Establish `hone : ∀ i, ∑ j, x i j ≤ ((univ.filter (fun j => x i j < s - τ)).card : ℝ) * (s - τ) + ((m i : ℝ) - (univ.filter (fun j => x i j < s - τ)).card) * (s + u)`. Introduce `i`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not univ (fun j => x i j < s - τ)]`. Establish `hc` using `Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (m i)))) (fun j => x i j < s - τ)`. Rewrite `hc` using `[Finset.card_univ, Fintype.card_fin]`.

Establish `hc' : ((m i : ℝ) - (univ.filter (fun j => x i j < s - τ)).card) = ((univ.filter (fun j => ¬ x i j < s - τ)).card : ℝ)`. Establish `hc2 : ((univ.filter (fun j => x i j < s - τ)).card : ℝ) + ((univ.filter (fun j => ¬ x i j < s - τ)).card : ℝ) = (m i : ℝ)` using `by exact_mod_cast hc`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hc']`. Establish `h1 : ∑ j ∈ univ.filter (fun j => x i j < s - τ), x i j ≤ ∑ _j ∈ univ.filter (fun j => x i j < s - τ), (s - τ)` using `Finset.sum_le_sum fun j hj => (Finset.mem_filter.1 hj).2.le`.

Establish `h2 : ∑ j ∈ univ.filter (fun j => ¬ x i j < s - τ), x i j ≤ ∑ _j ∈ univ.filter (fun j => ¬ x i j < s - τ), (s + u)` using `Finset.sum_le_sum fun j _ => hle i j`. Rewrite `h1`, `h2` using `[Finset.sum_const, nsmul_eq_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `htot` using `Finset.sum_le_sum fun i (_ : i ∈ (univ : Finset I)) => hone i`. Establish `hexp : ∑ i, (((univ.filter (fun j => x i j < s - τ)).card : ℝ) * (s - τ) + ((m i : ℝ) - (univ.filter (fun j => x i j < s - τ)).card) * (s + u)) = (∑ i, (m i : ℝ)) * (s + u) - (∑ i, ((univ.filter (fun j => x i j < s - τ)).card : ℝ)) * (u + τ)`.

Rewrite using `[Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite `htot` using `[hexp]`. Establish `hut : 0 < u + τ` using `by linarith`.

Rewrite using `[mul_div_assoc', le_div_iff₀ hut]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem frameB_share {I : Type} [Fintype I] (m : I → ℕ) (x : ∀ i, Fin (m i) → ℝ) (s u τ : ℝ)
    (hu : 0 < u) (hτ : 0 ≤ τ) (hsum : (∑ i, (m i : ℝ)) * s ≤ ∑ i, ∑ j, x i j)
    (hle : ∀ i j, x i j ≤ s + u) :
    (∑ i, ((univ.filter (fun j => x i j < s - τ)).card : ℝ)) ≤ (∑ i, (m i : ℝ)) * (u / (u + τ)) := by
  have hone : ∀ i, ∑ j, x i j ≤ ((univ.filter (fun j => x i j < s - τ)).card : ℝ) * (s - τ) +
      ((m i : ℝ) - (univ.filter (fun j => x i j < s - τ)).card) * (s + u) := by
    intro i
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun j => x i j < s - τ)]
    have hc := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (m i))))
      (fun j => x i j < s - τ)
    rw [Finset.card_univ, Fintype.card_fin] at hc
    have hc' : ((m i : ℝ) - (univ.filter (fun j => x i j < s - τ)).card) =
        ((univ.filter (fun j => ¬ x i j < s - τ)).card : ℝ) := by
      have hc2 : ((univ.filter (fun j => x i j < s - τ)).card : ℝ) +
          ((univ.filter (fun j => ¬ x i j < s - τ)).card : ℝ) = (m i : ℝ) := by exact_mod_cast hc
      linarith
    rw [hc']
    have h1 : ∑ j ∈ univ.filter (fun j => x i j < s - τ), x i j ≤
        ∑ _j ∈ univ.filter (fun j => x i j < s - τ), (s - τ) :=
      Finset.sum_le_sum fun j hj => (Finset.mem_filter.1 hj).2.le
    have h2 : ∑ j ∈ univ.filter (fun j => ¬ x i j < s - τ), x i j ≤
        ∑ _j ∈ univ.filter (fun j => ¬ x i j < s - τ), (s + u) :=
      Finset.sum_le_sum fun j _ => hle i j
    rw [Finset.sum_const, nsmul_eq_mul] at h1 h2
    linarith
  have htot := Finset.sum_le_sum fun i (_ : i ∈ (univ : Finset I)) => hone i
  have hexp : ∑ i, (((univ.filter (fun j => x i j < s - τ)).card : ℝ) * (s - τ) +
      ((m i : ℝ) - (univ.filter (fun j => x i j < s - τ)).card) * (s + u)) =
      (∑ i, (m i : ℝ)) * (s + u) - (∑ i, ((univ.filter (fun j => x i j < s - τ)).card : ℝ)) * (u + τ) := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hexp] at htot
  have hut : 0 < u + τ := by linarith
  rw [mul_div_assoc', le_div_iff₀ hut]
  nlinarith

/- English proof (translation)
Establish `h2` using `(polygon_slopes_characterization R V E ρ L hL).2.1 θ`. Establish `h3` using `Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (rk ρ L)))) (fun j => θ ≤ slopeList ρ L j)`. Simplify using `only [not_le, Finset.card_univ, Fintype.card_fin] at h3`. Establish `h4 : ((univ.filter (fun j => θ ≤ slopeList ρ L j)).card : ℝ) + ((univ.filter (fun j => slopeList ρ L j < θ)).card : ℝ) = (rk ρ L : ℝ)`. Conclude with `h3` after adjusting the coercions.

Rewrite `h4` using `[h2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem frameB_count_lt {R V E : Type} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E)
    (L : Submodule R V) (hL : IsLat ρ L) (θ : ℝ) :
    ((univ.filter (fun j => slopeList ρ L j < θ)).card : ℝ) =
      (rk ρ L : ℝ) - rk ρ (hnStep ρ L θ) := by
  have h2 := (polygon_slopes_characterization R V E ρ L hL).2.1 θ
  have h3 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (rk ρ L))))
    (fun j => θ ≤ slopeList ρ L j)
  simp only [not_le, Finset.card_univ, Fintype.card_fin] at h3
  have h4 : ((univ.filter (fun j => θ ≤ slopeList ρ L j)).card : ℝ) +
      ((univ.filter (fun j => slopeList ρ L j < θ)).card : ℝ) = (rk ρ L : ℝ) := by
    exact_mod_cast h3
  rw [h2] at h4
  linarith

/- English proof (translation)
The claim follows from `hnStep_of degree_supermodular slope_characterization maximal_slope_ratio finite_supremum_slopes real_saturation_property saturation_basic_properties`.
-/
theorem frameB_hnStep : HNStep.{0, 0, 0} :=
  hnStep_of degree_supermodular slope_characterization maximal_slope_ratio finite_supremum_slopes real_saturation_property saturation_basic_properties

def slopeNormalisingConstant (K : Type) [Field K] [NumberField K] : ℝ :=
  -Real.log 2 + logDisc K / (Module.finrank ℚ K : ℝ)

section Herm

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Unfold `muDef slopeNormalisingConstant`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem frameB_muDef (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) :
    muDef b X L = 2 * slope (Formalism.HermitianLatticesTheory.realize b X) L + slopeNormalisingConstant K := by
  unfold muDef slopeNormalisingConstant; ring

/- English proof (translation)
Unfold `muMaxDef slopeNormalisingConstant`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem frameB_muMaxDef (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) :
    muMaxDef b X L = 2 * muMax (Formalism.HermitianLatticesTheory.realize b X) L + slopeNormalisingConstant K := by
  unfold muMaxDef slopeNormalisingConstant; ring

/- English proof (translation)
Unfold `muMinDef slopeNormalisingConstant`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem frameB_muMinDef (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) :
    muMinDef b X L = 2 * muMin (Formalism.HermitianLatticesTheory.realize b X) L + slopeNormalisingConstant K := by
  unfold muMinDef slopeNormalisingConstant; ring

/- English proof (translation)
Unfold `rkK`. Rewrite using `[hL, finrank_top, Module.finrank_eq_card_basis b]`.
-/
theorem frameB_rkK_top (b : Basis ι K V) (L : Submodule (𝓞 K) V)
    (hL : Submodule.span K (L : Set V) = ⊤) : rkK L = Fintype.card ι := by
  unfold rkK
  rw [hL, finrank_top, Module.finrank_eq_card_basis b]

/- English proof (translation)
Introduce `h0`. Rewrite `hL` using `[h0, Submodule.bot_coe, Submodule.span_zero_singleton]`. Conclude with `bot_ne_top hL`.
-/
theorem frameB_ne_bot [Nontrivial V] (L : Submodule (𝓞 K) V)
    (hL : Submodule.span K (L : Set V) = ⊤) : L ≠ ⊥ := by
  intro h0
  rw [h0, Submodule.bot_coe, Submodule.span_zero_singleton] at hL
  exact bot_ne_top hL

end Herm

/- English proof (translation)
Rewrite using `[Finset.sum_add_distrib, ← Finset.mul_sum, (polygon_slopes_characterization R V E ρ L hL).2.2.1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Establish `hs : slope ρ L = deg ρ L / rk ρ L` using `rfl`. Establish `hr' : (rk ρ L : ℝ) ≠ 0` using `by exact_mod_cast hr`. Rewrite using `[hs]`. Clear the denominators using the available nonvanishing facts.
-/
theorem frameB_sum_sl {R V E : Type} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E)
    (L : Submodule R V) (hL : IsLat ρ L) (hr : rk ρ L ≠ 0) (a : ℝ) :
    ∑ j, (2 * slopeList ρ L j + a) = (rk ρ L : ℝ) * (2 * slope ρ L + a) := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, (polygon_slopes_characterization R V E ρ L hL).2.2.1,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hs : slope ρ L = deg ρ L / rk ρ L := rfl
  have hr' : (rk ρ L : ℝ) ≠ 0 := by exact_mod_cast hr
  rw [hs]
  field_simp

/- English proof (translation)
Establish `h1 : ∫ τ in (0:ℝ)..HH, (u + τ)⁻¹ = Real.log ((u + HH) / u)`. Use `intervalIntegral.integral_comp_add_left (fun x : ℝ => x⁻¹) (a := 0) (b := HH) u` as an intermediate fact. Rewrite using `[this, integral_inv_of_pos (by linarith) (by linarith)]`. Simplify using the standard rewrite rules. Establish `h2 : (1 + HH / u) = (u + HH) / u` using `by field_simp`.

Rewrite using `[h2, ← h1, ← intervalIntegral.integral_const_mul]`. Use `congr 1`. Use extensionality with `τ`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem frameB_integral (u HH : ℝ) (hu : 0 < u) (hH : 0 ≤ HH) :
    ∫ τ in (0:ℝ)..HH, 4 * (u / (u + τ)) = 4 * u * Real.log (1 + HH / u) := by
  have h1 : ∫ τ in (0:ℝ)..HH, (u + τ)⁻¹ = Real.log ((u + HH) / u) := by
    have := intervalIntegral.integral_comp_add_left (fun x : ℝ => x⁻¹) (a := 0) (b := HH) u
    rw [this, integral_inv_of_pos (by linarith) (by linarith)]
    simp
  have h2 : (1 + HH / u) = (u + HH) / u := by field_simp
  rw [h2, ← h1, ← intervalIntegral.integral_const_mul]
  congr 1; ext τ; ring

end Formalism.HN
