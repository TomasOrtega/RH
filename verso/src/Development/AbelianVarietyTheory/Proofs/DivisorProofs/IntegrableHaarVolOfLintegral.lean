import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section
namespace GlobalTheory.GJTransfer

/- English proof (translation)
Set `Y : Matrix (Fin n) (Fin n) 𝒪[k]` to `fun i j => ⟨X i j, hX i j⟩`. Establish `e : X.det = (𝒪[k].subtype.mapMatrix Y).det` using `rfl`. Rewrite using `[e, ← RingHom.map_det]`. Conclude with `(Y.det).2`.
-/
theorem det_mem_integer {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (X : Matrix (Fin n) (Fin n) k)
    (hX : X ∈ intM k (Fin n) (Fin n)) : valuation k X.det ≤ 1 := by
  let Y : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨X i j, hX i j⟩
  have e : X.det = (𝒪[k].subtype.mapMatrix Y).det := rfl
  rw [e, ← RingHom.map_det]
  exact (Y.det).2

/- English proof (translation)
Take `⟨_, _⟩` from `Model.secondCountable_and_t2_local_field (k := k)`. Establish `: BorelSpace (GL (Fin n) k)` using `borel_GL`. Establish `hE` using `Model.measurableEmbedding_val (k := k) (Fin n)`. Establish `hd` using `continuous_density_volGL (k := k) (n := Fin n)`. Establish `hn : IsLocallyConstant fun g : GL (Fin n) k => nabs k (GeneralLinearGroup.det g)` using `(isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det`.

Establish `hO : IsClopen (intM k (Fin n) (Fin n))` using `⟨isCompact_intMatrix.isClosed, isOpen_intMatrix⟩`. Establish `hind : IsLocallyConstant fun g : GL (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val` using `(LocallyConstant.indicator (1 : LocallyConstant _ ℝ) hO).isLocallyConstant.comp_continuous Units.continuous_val`. Use `set F : GL (Fin n) k → ℝ := fun g => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val * nabs k (gdet g) ^ σ with hF`. Establish `hFc : Continuous F` using `hind.continuous.mul (hn.comp fun r : ℝ => r ^ σ).continuous`. Use `⟨hFc.aestronglyMeasurable, ?_⟩` and prove the remaining obligations.

Use `set I : Matrix (Fin n) (Fin n) k → ENNReal := (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) with hIdef`. Establish `hpt : ∀ g : GL (Fin n) k, ENNReal.ofReal (nabs k (GeneralLinearGroup.det g) ^ (-(Fintype.card (Fin n) : ℝ))) * ‖F g‖ₑ ≤ I g.val`. Introduce `g`. Establish `hp` using `nabs_pos' (GeneralLinearGroup.det g)`. Use `set a := nabs k (GeneralLinearGroup.det g) with ha`.

Distinguish the cases in `hg : g.val ∈ intM k (Fin n) (Fin n)`. Establish `h0 : (g.val).det ≠ 0` using `g.det_ne_zero`. Establish `hu : Units.mk0 (g.val).det h0 = GeneralLinearGroup.det g` using `Units.ext rfl`. Establish `hle : a ≤ 1`. Rewrite using `[ha, ← hu]`.

Conclude with `Model.nabs_le_one _ (det_mem_integer _ hg)`. Rewrite using `[hIdef, Set.indicator_of_mem hg, dif_neg h0, hu, ← ha, ENNReal.ofReal_rpow_of_pos hp]`. Establish `hFg : F g = a ^ σ`. Rewrite using `[hF]`. Simplify using `only [Set.indicator_of_mem hg, one_mul]`.

Both sides reduce to the same expression. Rewrite using `[hFg, Real.enorm_of_nonneg (Real.rpow_nonneg hp.le _), ← ENNReal.ofReal_mul (Real.rpow_nonneg hp.le _), ← Real.rpow_add hp, Fintype.card_fin]`. Use `ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hp hle ?_)` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hFg : F g = 0`.

Rewrite using `[hF]`. Simplify using `only [Set.indicator_of_notMem hg, zero_mul]`. Rewrite using `[hFg]`. Simplify using the standard rewrite rules. Unfold `HasFiniteIntegral volGL`.

Use `erw [lintegral_withDensity_eq_lintegral_mul _ hd.measurable hFc.enorm.measurable]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem integrable_volGL_of_lintegral {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure]
    (n : ℕ) (σ s : ℝ) (hs : s ≤ σ - n)
    (hI : ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal
      (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X ∂(volM μ (Fin n) (Fin n)) < ⊤) :
    Integrable (fun g : GL (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val *
      nabs k (gdet g) ^ σ) (volGL μ (Fin n)) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (GL (Fin n) k) := borel_GL
  have hE := Model.measurableEmbedding_val (k := k) (Fin n)
  have hd := continuous_density_volGL (k := k) (n := Fin n)
  have hn : IsLocallyConstant fun g : GL (Fin n) k => nabs k (GeneralLinearGroup.det g) :=
    (isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det
  have hO : IsClopen (intM k (Fin n) (Fin n)) := ⟨isCompact_intMatrix.isClosed, isOpen_intMatrix⟩
  have hind : IsLocallyConstant fun g : GL (Fin n) k =>
      (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val :=
    (LocallyConstant.indicator (1 : LocallyConstant _ ℝ) hO).isLocallyConstant.comp_continuous
      Units.continuous_val
  set F : GL (Fin n) k → ℝ := fun g => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val *
      nabs k (gdet g) ^ σ with hF
  have hFc : Continuous F :=
    hind.continuous.mul (hn.comp fun r : ℝ => r ^ σ).continuous
  refine ⟨hFc.aestronglyMeasurable, ?_⟩
  set I : Matrix (Fin n) (Fin n) k → ENNReal := (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal
      (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) with hIdef
  have hpt : ∀ g : GL (Fin n) k, ENNReal.ofReal (nabs k (GeneralLinearGroup.det g) ^ (-(Fintype.card (Fin n) : ℝ)))
      * ‖F g‖ₑ ≤ I g.val := by
    intro g
    have hp := nabs_pos' (GeneralLinearGroup.det g)
    set a := nabs k (GeneralLinearGroup.det g) with ha
    by_cases hg : g.val ∈ intM k (Fin n) (Fin n)
    · have h0 : (g.val).det ≠ 0 := g.det_ne_zero
      have hu : Units.mk0 (g.val).det h0 = GeneralLinearGroup.det g := Units.ext rfl
      have hle : a ≤ 1 := by
        rw [ha, ← hu]
        exact Model.nabs_le_one _ (det_mem_integer _ hg)
      rw [hIdef, Set.indicator_of_mem hg, dif_neg h0, hu, ← ha, ENNReal.ofReal_rpow_of_pos hp]
      have hFg : F g = a ^ σ := by
        rw [hF]; simp only [Set.indicator_of_mem hg, one_mul]; rfl
      rw [hFg, Real.enorm_of_nonneg (Real.rpow_nonneg hp.le _),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hp.le _), ← Real.rpow_add hp, Fintype.card_fin]
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hp hle ?_)
      linarith
    · have hFg : F g = 0 := by
        rw [hF]; simp only [Set.indicator_of_notMem hg, zero_mul]
      rw [hFg]; simp
  unfold HasFiniteIntegral volGL
  erw [lintegral_withDensity_eq_lintegral_mul _ hd.measurable hFc.enorm.measurable]
  calc _ ≤ ∫⁻ g : GL (Fin n) k, I g.val ∂((volM μ (Fin n) (Fin n)).comap fun g : GL (Fin n) k => g.val) :=
        lintegral_mono fun g => hpt g
    _ = ∫⁻ X, I X ∂(((volM μ (Fin n) (Fin n)).comap fun g : GL (Fin n) k => g.val).map
          fun g : GL (Fin n) k => g.val) := (hE.lintegral_map I).symm
    _ = ∫⁻ X, I X ∂((volM μ (Fin n) (Fin n)).restrict (Set.range fun g : GL (Fin n) k => g.val)) := by
        erw [hE.map_comap]; rfl
    _ ≤ ∫⁻ X, I X ∂(volM μ (Fin n) (Fin n)) := lintegral_mono' Measure.restrict_le_self le_rfl
    _ < ⊤ := hI

/- English proof (translation)
Take `⟨_, _⟩` from `Model.secondCountable_and_t2_local_field (k := k)`. Establish `: BorelSpace (GL (Fin n) k)` using `borel_GL`. Establish `: SecondCountableTopology (GL (Fin n) k)` using `secondCountable_GL`. Establish `: (volGL (Measure.addHaar : Measure k) (Fin n)).IsHaarMeasure` using `isHaarMeasure_volGL _`. Establish `: (haarVol (KO k (Fin n))).IsHaarMeasure` using `isHaarMeasure_haarVol_KO`.

Rewrite using `[Measure.isMulLeftInvariant_eq_smul (haarVol (KO k (Fin n))) (volGL (Measure.addHaar : Measure k) (Fin n))]`. Conclude with `(integrable_volGL_of_lintegral _ n σ s hs hI).smul_measure_nnreal`.
-/
theorem integrable_haarVol_of_lintegral {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (σ s : ℝ) (hs : s ≤ σ - n)
    (hI : ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal
      (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X
        ∂(volM (Measure.addHaar : Measure k) (Fin n) (Fin n)) < ⊤) :
    Integrable (fun g : GL (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val *
      nabs k (gdet g) ^ σ) (haarVol (KO k (Fin n))) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (GL (Fin n) k) := borel_GL
  have : SecondCountableTopology (GL (Fin n) k) := secondCountable_GL
  have : (volGL (Measure.addHaar : Measure k) (Fin n)).IsHaarMeasure := isHaarMeasure_volGL _
  have : (haarVol (KO k (Fin n))).IsHaarMeasure := isHaarMeasure_haarVol_KO
  rw [Measure.isMulLeftInvariant_eq_smul (haarVol (KO k (Fin n))) (volGL (Measure.addHaar : Measure k) (Fin n))]
  exact (integrable_volGL_of_lintegral _ n σ s hs hI).smul_measure_nnreal

end GlobalTheory.GJTransfer
