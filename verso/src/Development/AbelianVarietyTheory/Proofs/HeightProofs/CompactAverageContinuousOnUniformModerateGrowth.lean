import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSubLeOfDerivIcc
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExpSecondKindCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasFDerivAtDerFamProdExpStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DerFamExpandWordsStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeasurableDerFamCompStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AvgDerFamGrowthStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOnAvgRightTranslatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open MeasureTheory Filter Topology

namespace GlobalTheory.KAvgGrowth

/- English proof (translation)
Introduce `n ε f hf hU e he`. Take `⟨N, F, hF0, hFd, hFg⟩` from `hU`. Use `⟨GlobalTheory.T.continuousOn_integral_mul_right_translate_toMK n ε f hf e he, ?_⟩` and prove the remaining obligations. Set `B` to `Module.finBasis ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))`. Set `b : Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))) → Mx n` to `fun i => (B i : Mx n)`.

Establish `hb : ∀ i, b i ∈ lieSet ε` using `fun i => by rw [lieSet_eq_lie]; exact (B i).2`. Set `c : Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))) → Mx n → ℝ` to `fun i Z => if h : Z ∈ lieSet ε then B.repr ⟨Z, by rwa [lieSet_eq_lie] at h⟩ i else 0`. Establish `hsum : ∀ Z ∈ lieSet ε, Z = ∑ i, c i Z • b i`. Introduce `Z hZ`. Establish `hZ' : Z ∈ GlobalTheory.LowTypeDetermined.lie (Jm ε)` using `by rwa [lieSet_eq_lie] at hZ`.

Use `congrArg Subtype.val (B.sum_repr ⟨Z, hZ'⟩)` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at this`. Simplify using `only [c, dif_pos hZ]`. Conclude with `this.symm`.

Establish `hli : LinearIndependent ℝ b` using `B.linearIndependent.map' (GlobalTheory.LowTypeDetermined.lie (Jm ε)).subtype (Submodule.ker_subtype _)`. Establish `hC : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ Z ∈ lieSet ε, ∀ g ∈ UJset ε, F (Z :: l) g = ∑ i, (c i Z : ℂ) * F (b i :: l) g`. Introduce `l hl Z hZ g hg`. Take `⟨τ, hτ0, hτ, hev⟩` from `GlobalTheory.T.exp_second_kind_coordinates n ε _ b hb hli (fun Z hZ => ⟨fun i => c i Z, hsum Z hZ⟩) (fun i => c i Z)`. Establish `h2` using `GlobalTheory.T.hasFDerivAt_derFam_mul_prod_exp_smul_zero n ε N F hFd hFg l hl _ b hb g hg`.

Rewrite `h2` using `[← hτ0]`. Establish `h3` using `h2.comp_hasDerivAt (0 : ℝ) hτ`. Establish `h4 : HasDerivAt (fun t : ℝ => F l (g * NormedSpace.exp (t • Z))) (F (Z :: l) g) 0` using `hFd l hl Z hZ g hg`. Establish `h5 : (fun t : ℝ => F l (g * NormedSpace.exp (t • Z))) =ᶠ[nhds 0] ((fun t : Fin _ → ℝ => F l (g * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod)) ∘ τ)` using `by filter_upwards [hev] with t ht`. Rewrite `ht` using `[← hsum Z hZ]`.

Simplify using `only [Function.comp_apply, ht]`. Establish `h6` using `h4.unique (h3.congr_of_eventuallyEq h5)`. Rewrite using `[h6]`. Simplify using `only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, Complex.real_smul]`. Establish `hD` using `GlobalTheory.T.derFam_ofFn_eq_sum_prod_coeff_of_expand n ε F hFd _ b c hb hC`.

Establish `hK : ∀ k : ↥(KG ε), toMK k ∈ UJset ε` using `fun k => K_le_UJ (toMK_mem_K k)`. Establish `had : ∀ (k : ↥(KG ε)) (X : Mx n), X ∈ lieSet ε → (toMK k)⁻¹ * X * toMK k ∈ lieSet ε`. Introduce `k X hX`. Rewrite `hX`, the goal using `[lieSet_eq_lie]`. Conclude with `GlobalTheory.LowTypeDetermined.conj_mem_lie (isUnit_Jm ε) (hK k) hX`.

Establish `hinvc : Continuous fun k : ↥(KG ε) => (toMK k)⁻¹`. Establish `e1 : (fun k : ↥(KG ε) => (toMK k)⁻¹) = fun k => toMK k⁻¹`. Use function extensionality and compare the values at `k`. Conclude with `(Matrix.coe_units_inv _).symm`. Rewrite using `[e1]`.

Conclude with `(continuous_toMK ε).comp continuous_inv`. Establish `hcc : ∀ i (X : Mx n), X ∈ lieSet ε → Continuous fun k : ↥(KG ε) => c i ((toMK k)⁻¹ * X * toMK k)`. Introduce `i X hX`. Establish `hX' : ∀ k : ↥(KG ε), (toMK k)⁻¹ * X * toMK k ∈ GlobalTheory.LowTypeDetermined.lie (Jm ε)` using `fun k => by`. Use `had k X hX` as an intermediate fact.

Rewrite `this` using `[lieSet_eq_lie]`. Then use the resulting hypothesis. Establish `e1 : (fun k : ↥(KG ε) => c i ((toMK k)⁻¹ * X * toMK k)) = fun k => B.repr ⟨(toMK k)⁻¹ * X * toMK k, hX' k⟩ i`. Use function extensionality and compare the values at `k`. Simplify using `only [c, dif_pos (had k X hX)]`. Rewrite using `[e1]`.

Establish `hm : Continuous fun k : ↥(KG ε) => (⟨(toMK k)⁻¹ * X * toMK k, hX' k⟩ : GlobalTheory.LowTypeDetermined.lie (Jm ε))` using `((hinvc.matrix_mul continuous_const).matrix_mul (continuous_toMK ε)).subtype_mk _`. Conclude with `((B.coord i).continuous_of_finiteDimensional).comp hm`. Establish `e1 : ∀ (l : List (Mx n)) (k : ↥(KG ε)), (l.map fun X => (toMK k)⁻¹ * X * toMK k) = List.ofFn fun j => (toMK k)⁻¹ * l.get j * toMK k`. Introduce `l k`. Use `conv_lhs => rw [← List.ofFn_get l]`.

Rewrite using `[List.map_ofFn]`. Both sides reduce to the same expression. Establish `hbw : ∀ {m : ℕ} (J : Fin m → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε)))), ∀ Y ∈ List.ofFn (fun j => b (J j)), Y ∈ lieSet ε`. Introduce `m J Y hY`. Take `⟨j, rfl⟩` from `(List.mem_ofFn' _ _).1 hY`.

Conclude with `hb _`. Establish `hUb : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∃ C : ℝ, ∀ k : ↥(KG ε), ∀ g ∈ UJset ε, ‖F (l.map fun X => (toMK k)⁻¹ * X * toMK k) g‖ ≤ C * (1 + hs g) ^ N`. Introduce `l hl`. Establish `hcb : ∀ i (j : Fin l.length), ∃ M : ℝ, ∀ k : ↥(KG ε), |c i ((toMK k)⁻¹ * l.get j * toMK k)| ≤ M`. Introduce `i j`.

Take `⟨M, hM⟩` from `(isCompact_univ.image (hcc i _ (hl _ (List.get_mem l j)))).isBounded.exists_norm_le`. Conclude with `⟨M, fun k => by simpa [Real.norm_eq_abs] using hM _ ⟨k, Set.mem_univ _, rfl⟩⟩`. Use `choose M hM using hcb`. Establish `hCJ : ∀ J : Fin l.length → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))), ∃ C : ℝ, ∀ g ∈ UJset ε, ‖F (List.ofFn fun j => b (J j)) g‖ ≤ C * (1 + hs g) ^ N` using `fun J => hFg _ (hbw J)`. Use `choose CJ hCJ using hCJ`.

Use `⟨∑ J : Fin l.length → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))), (∏ j, |M (J j) j|) * |CJ J|, fun k g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[e1, hD _ _ (fun j => had k _ (hl _ (List.get_mem l j))) g hg, Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun J _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_prod, mul_assoc]`. Establish `hw : 0 ≤ (1 + hs g) ^ N` using `pow_nonneg (by linarith [hs_nonneg g]) _`.

Use `mul_le_mul (Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => ?_) ?_ (norm_nonneg _) (Finset.prod_nonneg fun j _ => abs_nonneg _)` and prove the remaining obligations. Rewrite using `[Complex.norm_real, Real.norm_eq_abs]`. Conclude with `(hM _ _ k).trans (le_abs_self _)`. Conclude with `(hCJ J g hg).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hw)`. Establish `hF0c : ContinuousOn (F []) (UJset ε)` using `hf.congr fun g hg => hF0 g hg`.

Establish `hMs : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ z ∈ UJset ε, AEStronglyMeasurable (fun k : ↥(KG ε) => F (l.map fun X => (toMK k)⁻¹ * X * toMK k) (z * toMK k)) (muK ε)`. Introduce `l hl z hz`. Use `Measurable.aestronglyMeasurable ?_` and prove the remaining obligations. Establish `e2 : (fun k : ↥(KG ε) => F (l.map fun X => (toMK k)⁻¹ * X * toMK k) (z * toMK k)) = fun k => ∑ J : Fin l.length → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))), (∏ j, (c (J j) ((toMK k)⁻¹ * l.get j * toMK k) : ℂ)) * F (List.ofFn fun j => b (J j)) (z * toMK k)`. Use function extensionality and compare the values at `k`.

Rewrite using `[e1, hD _ _ (fun j => had k _ (hl _ (List.get_mem l j))) _ (mul_mem_UJ hz (hK k))]`. Rewrite using `[e2]`. Use `Finset.measurable_sum _ fun J _ => Measurable.mul ?_ ?_` and prove the remaining obligations. Conclude with `Finset.measurable_prod _ fun j _ => Complex.measurable_ofReal.comp (hcc _ _ (hl _ (List.get_mem l j))).measurable`. Conclude with `GlobalTheory.T.measurable_derFam_comp_continuous_of_mem_UJset n ε F hFd hF0c _ (hbw J) (↥(KG ε)) (fun k => z * toMK k) (continuous_const.matrix_mul (continuous_toMK ε)) fun k => mul_mem_UJ hz (hK k)`.

Take `⟨hA, hB⟩` from `GlobalTheory.T.avg_derFam_growth_alt n ε N F hFd hUb hMs e he`. Use `⟨N, _, fun y hy => ?_, hA, hB⟩` and prove the remaining obligations. Simplify using `only [List.map_nil]`. Use `integral_congr_ae (Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[hF0 _ (mul_mem_UJ hy (hK k))]`.
-/
theorem continuousOn_and_umg_kAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (f : GlobalTheory.TypeSum.Mx n → ℂ), ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    ContinuousOn (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (UJset ε) ∧
    GlobalTheory.TypeSum.UMG ε (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) := by
  classical
  intro n ε f hf hU e he
  obtain ⟨N, F, hF0, hFd, hFg⟩ := hU
  refine ⟨GlobalTheory.T.continuousOn_integral_mul_right_translate_toMK n ε f hf e he, ?_⟩
  let B := Module.finBasis ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))
  let b : Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))) → Mx n := fun i => (B i : Mx n)
  have hb : ∀ i, b i ∈ lieSet ε := fun i => by rw [lieSet_eq_lie]; exact (B i).2
  let c : Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))) → Mx n → ℝ := fun i Z =>
    if h : Z ∈ lieSet ε then B.repr ⟨Z, by rwa [lieSet_eq_lie] at h⟩ i else 0
  have hsum : ∀ Z ∈ lieSet ε, Z = ∑ i, c i Z • b i := by
    intro Z hZ
    have hZ' : Z ∈ GlobalTheory.LowTypeDetermined.lie (Jm ε) := by rwa [lieSet_eq_lie] at hZ
    have := congrArg Subtype.val (B.sum_repr ⟨Z, hZ'⟩)
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    simp only [c, dif_pos hZ]
    exact this.symm
  have hli : LinearIndependent ℝ b :=
    B.linearIndependent.map' (GlobalTheory.LowTypeDetermined.lie (Jm ε)).subtype (Submodule.ker_subtype _)
  have hC : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ Z ∈ lieSet ε, ∀ g ∈ UJset ε,
      F (Z :: l) g = ∑ i, (c i Z : ℂ) * F (b i :: l) g := by
    intro l hl Z hZ g hg
    obtain ⟨τ, hτ0, hτ, hev⟩ := GlobalTheory.T.exp_second_kind_coordinates n ε _ b hb hli (fun Z hZ => ⟨fun i => c i Z, hsum Z hZ⟩) (fun i => c i Z)
    have h2 := GlobalTheory.T.hasFDerivAt_derFam_mul_prod_exp_smul_zero n ε N F hFd hFg l hl _ b hb g hg
    rw [← hτ0] at h2
    have h3 := h2.comp_hasDerivAt (0 : ℝ) hτ
    have h4 : HasDerivAt (fun t : ℝ => F l (g * NormedSpace.exp (t • Z))) (F (Z :: l) g) 0 := hFd l hl Z hZ g hg
    have h5 : (fun t : ℝ => F l (g * NormedSpace.exp (t • Z))) =ᶠ[nhds 0]
        ((fun t : Fin _ → ℝ => F l (g * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod)) ∘ τ) := by
      filter_upwards [hev] with t ht
      rw [← hsum Z hZ] at ht
      simp only [Function.comp_apply, ht]
    have h6 := h4.unique (h3.congr_of_eventuallyEq h5)
    rw [h6]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, Complex.real_smul]
  have hD := GlobalTheory.T.derFam_ofFn_eq_sum_prod_coeff_of_expand n ε F hFd _ b c hb hC
  have hK : ∀ k : ↥(KG ε), toMK k ∈ UJset ε := fun k => K_le_UJ (toMK_mem_K k)
  have had : ∀ (k : ↥(KG ε)) (X : Mx n), X ∈ lieSet ε → (toMK k)⁻¹ * X * toMK k ∈ lieSet ε := by
    intro k X hX
    rw [lieSet_eq_lie] at hX ⊢
    exact GlobalTheory.LowTypeDetermined.conj_mem_lie (isUnit_Jm ε) (hK k) hX
  have hinvc : Continuous fun k : ↥(KG ε) => (toMK k)⁻¹ := by
    have e1 : (fun k : ↥(KG ε) => (toMK k)⁻¹) = fun k => toMK k⁻¹ := by
      funext k
      exact (Matrix.coe_units_inv _).symm
    rw [e1]
    exact (continuous_toMK ε).comp continuous_inv
  have hcc : ∀ i (X : Mx n), X ∈ lieSet ε → Continuous fun k : ↥(KG ε) => c i ((toMK k)⁻¹ * X * toMK k) := by
    intro i X hX
    have hX' : ∀ k : ↥(KG ε), (toMK k)⁻¹ * X * toMK k ∈ GlobalTheory.LowTypeDetermined.lie (Jm ε) := fun k => by
      have := had k X hX; rwa [lieSet_eq_lie] at this
    have e1 : (fun k : ↥(KG ε) => c i ((toMK k)⁻¹ * X * toMK k)) =
        fun k => B.repr ⟨(toMK k)⁻¹ * X * toMK k, hX' k⟩ i := by
      funext k
      simp only [c, dif_pos (had k X hX)]
    rw [e1]
    have hm : Continuous fun k : ↥(KG ε) => (⟨(toMK k)⁻¹ * X * toMK k, hX' k⟩ : GlobalTheory.LowTypeDetermined.lie (Jm ε)) :=
      ((hinvc.matrix_mul continuous_const).matrix_mul (continuous_toMK ε)).subtype_mk _
    exact ((B.coord i).continuous_of_finiteDimensional).comp hm
  have e1 : ∀ (l : List (Mx n)) (k : ↥(KG ε)), (l.map fun X => (toMK k)⁻¹ * X * toMK k) =
      List.ofFn fun j => (toMK k)⁻¹ * l.get j * toMK k := by
    intro l k
    conv_lhs => rw [← List.ofFn_get l]
    rw [List.map_ofFn]; rfl
  have hbw : ∀ {m : ℕ} (J : Fin m → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε)))),
      ∀ Y ∈ List.ofFn (fun j => b (J j)), Y ∈ lieSet ε := by
    intro m J Y hY
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hY
    exact hb _
  have hUb : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∃ C : ℝ, ∀ k : ↥(KG ε), ∀ g ∈ UJset ε,
      ‖F (l.map fun X => (toMK k)⁻¹ * X * toMK k) g‖ ≤ C * (1 + hs g) ^ N := by
    intro l hl
    have hcb : ∀ i (j : Fin l.length), ∃ M : ℝ, ∀ k : ↥(KG ε), |c i ((toMK k)⁻¹ * l.get j * toMK k)| ≤ M := by
      intro i j
      obtain ⟨M, hM⟩ := (isCompact_univ.image (hcc i _ (hl _ (List.get_mem l j)))).isBounded.exists_norm_le
      exact ⟨M, fun k => by simpa [Real.norm_eq_abs] using hM _ ⟨k, Set.mem_univ _, rfl⟩⟩
    choose M hM using hcb
    have hCJ : ∀ J : Fin l.length → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))), ∃ C : ℝ,
        ∀ g ∈ UJset ε, ‖F (List.ofFn fun j => b (J j)) g‖ ≤ C * (1 + hs g) ^ N := fun J => hFg _ (hbw J)
    choose CJ hCJ using hCJ
    refine ⟨∑ J : Fin l.length → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))),
      (∏ j, |M (J j) j|) * |CJ J|, fun k g hg => ?_⟩
    rw [e1, hD _ _ (fun j => had k _ (hl _ (List.get_mem l j))) g hg, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun J _ => ?_)
    rw [norm_mul, norm_prod, mul_assoc]
    have hw : 0 ≤ (1 + hs g) ^ N := pow_nonneg (by linarith [hs_nonneg g]) _
    refine mul_le_mul (Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => ?_) ?_ (norm_nonneg _)
      (Finset.prod_nonneg fun j _ => abs_nonneg _)
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact (hM _ _ k).trans (le_abs_self _)
    · exact (hCJ J g hg).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hw)
  have hF0c : ContinuousOn (F []) (UJset ε) := hf.congr fun g hg => hF0 g hg
  have hMs : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ z ∈ UJset ε,
      AEStronglyMeasurable (fun k : ↥(KG ε) =>
        F (l.map fun X => (toMK k)⁻¹ * X * toMK k) (z * toMK k)) (muK ε) := by
    intro l hl z hz
    refine Measurable.aestronglyMeasurable ?_
    have e2 : (fun k : ↥(KG ε) => F (l.map fun X => (toMK k)⁻¹ * X * toMK k) (z * toMK k)) =
        fun k => ∑ J : Fin l.length → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))),
          (∏ j, (c (J j) ((toMK k)⁻¹ * l.get j * toMK k) : ℂ)) * F (List.ofFn fun j => b (J j)) (z * toMK k) := by
      funext k
      rw [e1, hD _ _ (fun j => had k _ (hl _ (List.get_mem l j))) _ (mul_mem_UJ hz (hK k))]
    rw [e2]
    refine Finset.measurable_sum _ fun J _ => Measurable.mul ?_ ?_
    · exact Finset.measurable_prod _ fun j _ =>
        Complex.measurable_ofReal.comp (hcc _ _ (hl _ (List.get_mem l j))).measurable
    · exact GlobalTheory.T.measurable_derFam_comp_continuous_of_mem_UJset n ε F hFd hF0c _ (hbw J) (↥(KG ε)) (fun k => z * toMK k)
        (continuous_const.matrix_mul (continuous_toMK ε)) fun k => mul_mem_UJ hz (hK k)
  obtain ⟨hA, hB⟩ := GlobalTheory.T.avg_derFam_growth_alt n ε N F hFd hUb hMs e he
  refine ⟨N, _, fun y hy => ?_, hA, hB⟩
  simp only [List.map_nil]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only
  rw [hF0 _ (mul_mem_UJ hy (hK k))]

end GlobalTheory.KAvgGrowth
