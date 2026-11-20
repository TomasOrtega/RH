import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableZetaIntegralMatrixSchwartzStatement

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

noncomputable section
namespace GlobalTheory.GJForm

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

/- English proof (translation)
Take `⟨_, _⟩` from `Model.secondCountable_and_t2_local_field (k := k)`. Establish `: BorelSpace (GL (Fin n) k)` using `borel_GL`. Establish `: MeasurableMul (GL (Fin n) k)` using `inferInstance`. Establish `: (haarVol (KO k (Fin n))).IsHaarMeasure` using `isHaarMeasure_haarVol_KO`. Use `⟨fun φ hφ φ' hφ' => ?_, fun c φ hφ => ?_, fun g₁ g₂ φ hφ => ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[← integral_add (GlobalTheory.T.integrable_zeta_integral_matrix_schwartz k n ν z hν hz φ hφ) (GlobalTheory.T.integrable_zeta_integral_matrix_schwartz k n ν z hν hz φ' hφ')]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Simplify using `only [Pi.add_apply]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `g`.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `set F : GL (Fin n) k → ℂ := fun g => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z with hF set d := gdet g₁ * gdet g₂ with hd'`. Establish `hd : (ν d : ℂ) * apow d z ≠ 0` using `mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)`. Establish `key : ∀ g : GL (Fin n) k, φ (g₁.val * g.val * g₂.val) * (ν (gdet g) : ℂ) * apow (gdet g) z = ((ν d : ℂ) * apow d z)⁻¹ * F (g₁ * (g * g₂))`.

Introduce `g`. Establish `e : gdet (g₁ * (g * g₂)) = gdet g * d`. Rewrite using `[gdet_mul, gdet_mul, hd', mul_left_comm]`. Establish `ha` using `apow_ne_zero d z`. Establish `hn : (ν d : ℂ) ≠ 0` using `Units.ne_zero _`.

Simplify using `only [hF, e, map_mul, Units.val_mul, apow_mul, Matrix.mul_assoc]`. Clear the denominators using the available nonvanishing facts. Repeatedly rewrite using `[key]`. Rewrite using `[integral_const_mul]`. Establish `h1 : ∫ g, F (g₁ * (g * g₂)) ∂(haarVol (KO k (Fin n))) = ∫ g, F g ∂(haarVol (KO k (Fin n)))`.

Establish `h2` using `integral_mul_right_eq_self (μ := haarVol (KO k (Fin n))) (fun g => F (g₁ * g)) g₂`. Conclude with `h2.trans (integral_mul_left_eq_self (μ := haarVol (KO k (Fin n))) F g₁)`. Rewrite using `[h1, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]`.
-/
theorem isEqv_integral (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ) (hν : IsSmU ν) (hz : (n : ℝ) - 1 < z.re) :
    IsEqv ν z (fun φ : Matrix (Fin n) (Fin n) k → ℂ =>
      ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n)))) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (GL (Fin n) k) := borel_GL
  have : MeasurableMul (GL (Fin n) k) := inferInstance
  have : (haarVol (KO k (Fin n))).IsHaarMeasure := isHaarMeasure_haarVol_KO
  refine ⟨fun φ hφ φ' hφ' => ?_, fun c φ hφ => ?_, fun g₁ g₂ φ hφ => ?_⟩
  · dsimp only
    rw [← integral_add (GlobalTheory.T.integrable_zeta_integral_matrix_schwartz k n ν z hν hz φ hφ) (GlobalTheory.T.integrable_zeta_integral_matrix_schwartz k n ν z hν hz φ' hφ')]
    congr 1; funext g; simp only [Pi.add_apply]; ring
  · dsimp only
    rw [← integral_const_mul]; congr 1; funext g; simp only [Pi.smul_apply, smul_eq_mul]; ring
  · set F : GL (Fin n) k → ℂ := fun g => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z with hF
    set d := gdet g₁ * gdet g₂ with hd'
    have hd : (ν d : ℂ) * apow d z ≠ 0 := mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
    have key : ∀ g : GL (Fin n) k, φ (g₁.val * g.val * g₂.val) * (ν (gdet g) : ℂ) * apow (gdet g) z
        = ((ν d : ℂ) * apow d z)⁻¹ * F (g₁ * (g * g₂)) := by
      intro g
      have e : gdet (g₁ * (g * g₂)) = gdet g * d := by
        rw [gdet_mul, gdet_mul, hd', mul_left_comm]
      have ha := apow_ne_zero d z
      have hn : (ν d : ℂ) ≠ 0 := Units.ne_zero _
      simp only [hF, e, map_mul, Units.val_mul, apow_mul, Matrix.mul_assoc]
      field_simp
    simp_rw [key]
    rw [integral_const_mul]
    have h1 : ∫ g, F (g₁ * (g * g₂)) ∂(haarVol (KO k (Fin n))) = ∫ g, F g ∂(haarVol (KO k (Fin n))) := by
      have h2 := integral_mul_right_eq_self (μ := haarVol (KO k (Fin n))) (fun g => F (g₁ * g)) g₂
      exact h2.trans (integral_mul_left_eq_self (μ := haarVol (KO k (Fin n))) F g₁)
    rw [h1, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]

/- English proof (translation)
Take `⟨_, _⟩` from `Model.secondCountable_and_t2_local_field (k := k)`. Establish `: BorelSpace (GL (Fin n) k)` using `borel_GL`. Establish `: MeasurableMul (GL (Fin n) k)` using `inferInstance`. Establish `: (haarVol (KO k (Fin n))).IsHaarMeasure` using `isHaarMeasure_haarVol_KO`. Use `set H : Subgroup (GL (Fin n) k) := KO k (Fin n) ⊓ (ν.comp Matrix.GeneralLinearGroup.det).ker with hH`.

Establish `hHo : IsOpen (H : Set (GL (Fin n) k))`. Rewrite using `[hH, Subgroup.coe_inf]`. Conclude with `isOpen_KO.inter (hν.1.preimage Matrix.GeneralLinearGroup.continuous_det)`. Establish `hHc : IsCompact (H : Set (GL (Fin n) k))` using `isCompact_KO.of_isClosed_subset (H.isClosed_of_isOpen hHo) fun x hx => hx.1`. Establish `hemb : Topology.IsOpenEmbedding (fun g : GL (Fin n) k => g.val)`.

Use `{ toIsEmbedding := isEmbedding_val_GL, isOpen_range := ?_ }` and prove the remaining obligations. Establish `e : Set.range (fun g : GL (Fin n) k => g.val) = {A | A.det ≠ 0}`. Use extensionality with `A`. Use `⟨?_, fun h => ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A h, rfl⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨g, rfl⟩`.

Conclude with `g.det_ne_zero`. Rewrite using `[e]`. Conclude with `isOpen_ne_fun (continuous_id.matrix_det) continuous_const`. Use `set S : Set (Matrix (Fin n) (Fin n) k) := (fun g : GL (Fin n) k => g.val) '' H with hS`. Establish `hSc : IsCompact S` using `hHc.image Units.continuous_val`.

Establish `hSo : IsClopen S` using `⟨hSc.isClosed, hemb.isOpenMap _ hHo⟩`. Use `⟨S.indicator 1, ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hSo).isLocallyConstant, HasCompactSupport.intro hSc fun x hx => Set.indicator_of_notMem hx _⟩, ?_⟩` and prove the remaining obligations. Establish `hfun : (fun g : GL (Fin n) k => S.indicator 1 g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) = (H : Set (GL (Fin n) k)).indicator (fun _ => (1 : ℂ))`. Use function extensionality and compare the values at `g`. Distinguish the cases in `hg : g ∈ H`.

Establish `h1 : g.val ∈ S` using `⟨g, hg, rfl⟩`. Establish `h2 : ν (gdet g) = 1` using `hg.2`. Rewrite using `[Set.indicator_of_mem h1, Set.indicator_of_mem (show g ∈ (H : Set _) from hg), h2, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg.1)]`. Simplify using the standard rewrite rules. Establish `h1 : g.val ∉ S`.

Introduce and unpack `⟨g', hg', e⟩`. Conclude with `hg (Units.ext e ▸ hg')`. Rewrite using `[Set.indicator_of_notMem h1, Set.indicator_of_notMem (show g ∉ (H : Set _) from hg)]`. Simplify using the standard rewrite rules. Simplify using `only [hfun]`.

Establish `hI` using `integral_indicator_const (μ := haarVol (KO k (Fin n))) (1 : ℂ) hHo.measurableSet`. Establish `hpos` using `hHo.measure_pos (haarVol (KO k (Fin n))) ⟨1, H.one_mem⟩`. Establish `hfin` using `hHc.measure_lt_top (μ := haarVol (KO k (Fin n)))`. Use `erw [hI]`. Rewrite using `[Complex.real_smul, mul_one, Complex.ofReal_ne_zero, measureReal_def]`.

Conclude with `(ENNReal.toReal_pos hpos.ne' hfin.ne).ne'`.
-/
theorem exists_integral_ne_zero (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ) (hν : IsSmU ν) :
    ∃ φ ∈ SB (Matrix (Fin n) (Fin n) k),
      ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n))) ≠ 0 := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (GL (Fin n) k) := borel_GL
  have : MeasurableMul (GL (Fin n) k) := inferInstance
  have : (haarVol (KO k (Fin n))).IsHaarMeasure := isHaarMeasure_haarVol_KO
  set H : Subgroup (GL (Fin n) k) := KO k (Fin n) ⊓ (ν.comp Matrix.GeneralLinearGroup.det).ker with hH
  have hHo : IsOpen (H : Set (GL (Fin n) k)) := by
    rw [hH, Subgroup.coe_inf]
    exact isOpen_KO.inter (hν.1.preimage Matrix.GeneralLinearGroup.continuous_det)
  have hHc : IsCompact (H : Set (GL (Fin n) k)) :=
    isCompact_KO.of_isClosed_subset (H.isClosed_of_isOpen hHo) fun x hx => hx.1
  have hemb : Topology.IsOpenEmbedding (fun g : GL (Fin n) k => g.val) := by
    refine { toIsEmbedding := isEmbedding_val_GL, isOpen_range := ?_ }
    have e : Set.range (fun g : GL (Fin n) k => g.val) = {A | A.det ≠ 0} := by
      ext A
      refine ⟨?_, fun h => ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A h, rfl⟩⟩
      rintro ⟨g, rfl⟩
      exact g.det_ne_zero
    rw [e]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  set S : Set (Matrix (Fin n) (Fin n) k) := (fun g : GL (Fin n) k => g.val) '' H with hS
  have hSc : IsCompact S := hHc.image Units.continuous_val
  have hSo : IsClopen S := ⟨hSc.isClosed, hemb.isOpenMap _ hHo⟩
  refine ⟨S.indicator 1, ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hSo).isLocallyConstant,
    HasCompactSupport.intro hSc fun x hx => Set.indicator_of_notMem hx _⟩, ?_⟩
  have hfun : (fun g : GL (Fin n) k => S.indicator 1 g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) =
      (H : Set (GL (Fin n) k)).indicator (fun _ => (1 : ℂ)) := by
    funext g
    by_cases hg : g ∈ H
    · have h1 : g.val ∈ S := ⟨g, hg, rfl⟩
      have h2 : ν (gdet g) = 1 := hg.2
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem (show g ∈ (H : Set _) from hg), h2,
        apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg.1)]
      simp
    · have h1 : g.val ∉ S := by
        rintro ⟨g', hg', e⟩
        exact hg (Units.ext e ▸ hg')
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (show g ∉ (H : Set _) from hg)]
      simp
  simp only [hfun]
  have hI := integral_indicator_const (μ := haarVol (KO k (Fin n))) (1 : ℂ) hHo.measurableSet
  have hpos := hHo.measure_pos (haarVol (KO k (Fin n))) ⟨1, H.one_mem⟩
  have hfin := hHc.measure_lt_top (μ := haarVol (KO k (Fin n)))
  erw [hI]
  rw [Complex.real_smul, mul_one, Complex.ofReal_ne_zero, measureReal_def]
  exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ n ν z hν hz` and use `⟨isEqv_integral n ν z hν hz, exists_integral_ne_zero n ν z hν⟩`.
-/
theorem isEqv_integral_and_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ), IsSmU ν → (n : ℝ) - 1 < z.re →
    IsEqv ν z (fun φ : Matrix (Fin n) (Fin n) k → ℂ => ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n)))) ∧
    ∃ φ ∈ SB (Matrix (Fin n) (Fin n) k), ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n))) ≠ 0 :=
  fun _ _ _ _ _ _ _ n ν z hν hz => ⟨isEqv_integral n ν z hν hz, exists_integral_ne_zero n ν z hν⟩

end GlobalTheory.GJForm
