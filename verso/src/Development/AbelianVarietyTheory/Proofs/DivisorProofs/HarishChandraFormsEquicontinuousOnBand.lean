import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraExistsReproducingTestFunctionGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeSupWiderBandGenCentralEigenformsStatement
import GroundTheory.AutomorphicForms.AdelicGLn

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology Pointwise

namespace GlobalTheory.HCF.Equi

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Use `Continuous.units_map _ ?_` and prove the remaining obligations. Establish `hs : Continuous (sInf E : Cinf E → Ad E)` using `(continuous_infEq E).prodMk continuous_const`. Conclude with `continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)`.
-/
theorem continuous_infGL' : Continuous (infGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) := (continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

/- English proof (translation)
The claim follows from `continuous_pi fun w => ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)).comp continuous_fst`.
-/
theorem continuous_pInf' : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

/- English proof (translation)
The claim follows from `Continuous.units_map _ (continuous_id.matrix_map continuous_pInf')`.
-/
theorem continuous_mapInf : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf')

omit [IsTotallyComplex E] in
/- English proof (translation)
The claim follows from `Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))`.
-/
theorem continuous_mapFin : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))

omit [IsTotallyComplex E] in

/- English proof (translation)
Unfold `absDetA`. Conclude with `GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E) _`.
-/
theorem absDetA_eq (g : GA E a) :
    absDetA g = (GroundTheory.Global.IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det g) : ℝ) := by
  unfold absDetA
  exact GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E) _

omit [IsTotallyComplex E] in

/- English proof (translation)
Rewrite using `[absDetA_eq, absDetA_eq, absDetA_eq, map_mul, map_mul, Positive.val_mul]`.
-/
theorem absDetA_mul (g h : GA E a) : absDetA (g * h) = absDetA g * absDetA h := by
  rw [absDetA_eq, absDetA_eq, absDetA_eq, map_mul, map_mul, Positive.val_mul]

omit [IsTotallyComplex E] in

/- English proof (translation)
Establish `e : (absDetA (E` using `E) (a := a)) = fun g => (GroundTheory.Global.IdeleGroup.ideleModule E (GroundTheory.Automorphic.AdelicGLn.det E a g) : ℝ) :=`. Use function extensionality and compare the values at `absDetA_eq`. Rewrite using `[e]`. Conclude with `continuous_subtype_val.comp (GroundTheory.Global.IdeleGroup.continuous_ideleModule.comp (GroundTheory.Automorphic.AdelicGLn.continuous_det E a))`.
-/
theorem continuous_absDetA : Continuous (absDetA (E := E) (a := a)) := by
  have e : (absDetA (E := E) (a := a)) =
      fun g => (GroundTheory.Global.IdeleGroup.ideleModule E (GroundTheory.Automorphic.AdelicGLn.det E a g) : ℝ) :=
    funext absDetA_eq
  rw [e]
  exact continuous_subtype_val.comp (GroundTheory.Global.IdeleGroup.continuous_ideleModule.comp
    (GroundTheory.Automorphic.AdelicGLn.continuous_det E a))

/- English proof (translation)
Establish `h` using `(ψ.2 g).continuousOn`. Establish `h2 : Continuous fun z : GL (Fin a) (Cinf E) => chart ψ.1 g (toL z.val)` using `h.comp_continuous (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E)) : _) fun z => val_mem_invSet z`. Conclude with `h2.congr fun z => chart_val ψ.1 g z`.
-/
theorem continuous_along (ψ : Sm E a) (g : GA E a) : Continuous fun z : GL (Fin a) (Cinf E) => ψ.1 (g * infGL E a z) := by
  have h := (ψ.2 g).continuousOn
  have h2 : Continuous fun z : GL (Fin a) (Cinf E) => chart ψ.1 g (toL z.val) :=
    h.comp_continuous (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E)) : _) fun z => val_mem_invSet z
  exact h2.congr fun z => chart_val ψ.1 g z

/- English proof (translation)
Introduce `E _ _ _ a L hL W hW X hX N ε hε`. Use `letI : MeasurableSpace (GL (Fin a) (Cinf E)) := borel _`. Use `haveI : BorelSpace (GL (Fin a) (Cinf E)) := ⟨rfl⟩`. Use `haveI : LocallyCompactSpace (GL (Fin a) (Cinf E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace`. Use `set μ : Measure (GL (Fin a) (Cinf E)) := Measure.haar`.

Take `⟨α, hαc, hαs, hα⟩` from `GlobalTheory.T.harishChandra_exists_reproducing_testFunction_GL E a L hL W hW X hX N μ inferInstance`. Establish `hint : ∀ (ψ : Sm E a) (g : GA E a), Integrable (fun y => ψ.1 (g * infGL E a y) * α y) μ` using `fun ψ g => ((continuous_along ψ g).mul hαc).integrable_of_hasCompactSupport hαs.mul_left`. Establish `hrep : ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ g, ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g`. Introduce `φ hφ`. Proceed by induction on `hφ using Submodule.span_induction with`.

Consider the case `mem x hx => exact hα x hx`. Consider the case `zero => intro g`. Express the relevant statement in the definitionally equal form `∫ z, (0 : ℂ) * α z ∂μ = 0`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`.

Introduce `g`. Express the relevant statement in the definitionally equal form `∫ z, (x.1 (g * infGL E a z) + y.1 (g * infGL E a z)) * α z ∂μ = x.1 g + y.1 g`. Repeatedly rewrite using `[add_mul]`. Rewrite using `[integral_add (hint x g) (hint y g), hx, hy]`. Consider the case `smul c x _ hx`.

Introduce `g`. Express the relevant statement in the definitionally equal form `∫ z, (c * x.1 (g * infGL E a z)) * α z ∂μ = c * x.1 g`. Repeatedly rewrite using `[mul_assoc]`. Rewrite using `[integral_const_mul, hx]`. Establish `hfix : ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ k ∈ L, ∀ x, φ.1 (x * finGL E a k) = φ.1 x`.

Introduce `φ hφ k hk x`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem ψ hψ => exact congrArg (fun f : Sm E a => f.1 x) (hψ.2.1 k hk)`. Consider the case `zero => rfl`. Consider the case `add ψ χ _ _ h1 h2`.

Express the relevant statement in the definitionally equal form `ψ.1 (x * finGL E a k) + χ.1 (x * finGL E a k) = ψ.1 x + χ.1 x`. Rewrite using `[h1, h2]`. Consider the case `smul c ψ _ h`. Express the relevant statement in the definitionally equal form `c * ψ.1 (x * finGL E a k) = c * ψ.1 x`. Rewrite using `[h]`.

Take `⟨V, hVc, hV1⟩` from `exists_compact_mem_nhds (1 : GL (Fin a) (Cinf E))`. Establish `hKc : IsCompact (tsupport α)` using `hαs`. Use `set K' := V * tsupport α with hK'`. Establish `hK'c : IsCompact K'` using `hVc.mul hKc`. Establish `hK'm : MeasurableSet K'` using `hK'c.measurableSet`.

Establish `hfc : Continuous fun z : GL (Fin a) (Cinf E) => absDetA (infGL E a z)` using `continuous_absDetA.comp continuous_infGL'`. Take `⟨B₁, hB₁⟩` from `hK'c.exists_bound_of_continuousOn hfc.continuousOn`. Take `⟨B₂, hB₂⟩` from `hK'c.exists_bound_of_continuousOn (hfc.inv₀ fun z => (absDetA_pos _).ne').continuousOn`. Use `set c := max 1 (max B₁ B₂) with hc`. Establish `hc1 : 1 ≤ c` using `le_max_left _ _`.

Establish `hcK : ∀ z ∈ K', c⁻¹ ≤ absDetA (infGL E a z) ∧ absDetA (infGL E a z) ≤ c`. Introduce `z hz`. Establish `hp` using `absDetA_pos (infGL E a z)`. Establish `h1` using `hB₁ z hz`. Establish `h2 : ‖(absDetA (infGL E a z))⁻¹‖ ≤ B₂` using `hB₂ z hz`.

Rewrite `h1` using `[Real.norm_of_nonneg hp.le]`. Rewrite `h2` using `[Real.norm_of_nonneg (inv_nonneg.2 hp.le)]`. Use `⟨?_, h1.trans ((le_max_left _ _).trans (le_max_right _ _))⟩` and prove the remaining obligations. Rewrite using `[inv_le_comm₀ (by positivity) hp]`. Conclude with `h2.trans ((le_max_right _ _).trans (le_max_right _ _))`.

Take `⟨C, hC⟩` from `GlobalTheory.T.norm_le_sup_wider_band_genCentralEigenforms E a L hL W hW X hX N c hc1`. Use `set C' := |C| + 1 with hC'`. Establish `hC'0 : 0 < C'` using `by positivity`. Use `set m := μ.real K' with hm`. Establish `hm0 : 0 ≤ m` using `measureReal_nonneg`.

Use `set δ := ε / (C' * (m + 1)) with hδ`. Establish `hδ0 : 0 < δ` using `by positivity`. Establish `hδe : C' * δ * (m + 1) = ε` using `by rw [hδ]; field_simp`. Take `⟨v, hv, hvK⟩` from `hK'c.mem_uniformity_of_prod (f := fun p x => α (p⁻¹ * x)) (s := Set.univ) (q := 1) (by exact (hαc.comp (continuous_fst.inv.mul continuous_snd)).continuousOn) (Set.mem_univ _) (Metric.dist_mem_uniformity hδ0)`. Rewrite `hv` using `[nhdsWithin_univ]`.

Use `⟨{u | Matrix.GeneralLinearGroup.map (pInf E) u ∈ v ∩ V ∧ Matrix.GeneralLinearGroup.map (pFin E) u ∈ L}, ?_, ?_⟩` and prove the remaining obligations. Use `Filter.inter_mem ?_ ?_` and prove the remaining obligations. Conclude with `continuous_mapInf.continuousAt.preimage_mem_nhds (by rw [map_one]; exact Filter.inter_mem hv hV1)`. Conclude with `continuous_mapFin.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hL.mem_nhds L.one_mem)`. Introduce `φ hφ M hM g hg u hu _`.

Establish `hM0 : 0 ≤ M` using `(norm_nonneg _).trans (hM 1 one_mem_band)`. Use `set y := Matrix.GeneralLinearGroup.map (pInf E) u with hy`. Use `set k := Matrix.GeneralLinearGroup.map (pFin E) u with hk`. Establish `hyv : y ∈ v` using `hu.1.1`. Establish `hyV : y ∈ V` using `hu.1.2`.

Establish `hkL : k ∈ L` using `hu.2`. Establish `hgu : φ.1 (g * u) = φ.1 (g * infGL E a y)`. Rewrite using `[← infGL_mul_finGL u, ← mul_assoc, hfix φ hφ k hkL]`. Rewrite using `[hgu]`. Establish `e1 : φ.1 (g * infGL E a y) = ∫ z, φ.1 (g * infGL E a z) * α (y⁻¹ * z) ∂μ`.

Rewrite using `[← hrep φ hφ (g * infGL E a y), ← integral_mul_left_eq_self (fun z => φ.1 (g * infGL E a z) * α (y⁻¹ * z)) y]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [map_mul, mul_assoc, inv_mul_cancel_left]`. Establish `hi1 : Integrable (fun z => φ.1 (g * infGL E a z) * α (y⁻¹ * z)) μ` using `((continuous_along φ g).mul (hαc.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport (HasCompactSupport.mul_left (hαs.comp_homeomorph (Homeomorph.mulLeft y⁻¹)))`.

Establish `e2 : φ.1 (g * infGL E a y) - φ.1 g = ∫ z, φ.1 (g * infGL E a z) * (α (y⁻¹ * z) - α z) ∂μ`. Rewrite using `[e1, ← hrep φ hφ g, ← integral_sub hi1 (hint φ g)]`. Repeatedly rewrite using `[mul_sub]`. Rewrite using `[e2]`. Establish `hpt : ∀ z, ‖φ.1 (g * infGL E a z) * (α (y⁻¹ * z) - α z)‖ ≤ K'.indicator (fun _ => C' * M * δ) z`.

Introduce `z`. Distinguish the cases in `hz : z ∈ K'`. Rewrite using `[Set.indicator_of_mem hz, norm_mul]`. Establish `hd` using `hcK z hz`. Establish `hg'` using `hg`.

Take `⟨hg1, hg2⟩` from `hg'`. Establish `hb1 : c⁻¹ ≤ absDetA (g * infGL E a z)`. Rewrite using `[absDetA_mul]`. Use `absDetA_pos (infGL E a z)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `hb2 : absDetA (g * infGL E a z) ≤ 2 * c`. Rewrite using `[absDetA_mul]`. Use `absDetA_pos (infGL E a z)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `h1 : ‖φ.1 (g * infGL E a z)‖ ≤ C' * M` using `(hC φ hφ M hM _ hb1 hb2).trans (mul_le_mul_of_nonneg_right (by rw [hC']; linarith [le_abs_self C]) hM0)`.

Establish `h2 : ‖α (y⁻¹ * z) - α z‖ ≤ δ`. Use `hvK y hyv z hz` as an intermediate fact. Simplify using `only [inv_one, one_mul, Set.mem_setOf_eq] at this`. Rewrite using `[← dist_eq_norm]`. Conclude with `this.le`.

Conclude with `mul_le_mul h1 h2 (norm_nonneg _) (by positivity)`. Rewrite using `[Set.indicator_of_notMem hz]`. Establish `hz1 : α z = 0` using `image_eq_zero_of_notMem_tsupport fun h => hz ⟨1, mem_of_mem_nhds hV1, z, h, one_mul z⟩`. Establish `hz2 : α (y⁻¹ * z) = 0` using `image_eq_zero_of_notMem_tsupport fun h => hz ⟨y, hyV, y⁻¹ * z, h, mul_inv_cancel_left y z⟩`. Simplify using `[hz1, hz2]`.

Establish `hint' : Integrable (K'.indicator (fun _ => C' * M * δ)) μ` using `(integrableOn_const (C := C' * M * δ) hK'c.measure_lt_top.ne).integrable_indicator hK'm`. Use `(norm_integral_le_of_norm_le hint' (Filter.Eventually.of_forall hpt)).trans ?_` and prove the remaining obligations. Rewrite using `[integral_indicator_const _ hK'm, smul_eq_mul, ← hm]`. Establish `: 0 ≤ C' * M * δ` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem equicontinuous_band : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ),
    FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ U ∈ 𝓝 (1 : GA E a), ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) →
      ∀ g ∈ band E a, ∀ u ∈ U, g * u ∈ band E a → ‖φ.1 (g * u) - φ.1 g‖ ≤ ε * M := by
  intro E _ _ _ a L hL W hW X hX N ε hε
  letI : MeasurableSpace (GL (Fin a) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin a) (Cinf E)) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GL (Fin a) (Cinf E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  set μ : Measure (GL (Fin a) (Cinf E)) := Measure.haar
  obtain ⟨α, hαc, hαs, hα⟩ := GlobalTheory.T.harishChandra_exists_reproducing_testFunction_GL E a L hL W hW X hX N μ inferInstance
  have hint : ∀ (ψ : Sm E a) (g : GA E a), Integrable (fun y => ψ.1 (g * infGL E a y) * α y) μ := fun ψ g =>
    ((continuous_along ψ g).mul hαc).integrable_of_hasCompactSupport hαs.mul_left

  have hrep : ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ g,
      ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hα x hx
    | zero => intro g; change ∫ z, (0 : ℂ) * α z ∂μ = 0; simp
    | add x y _ _ hx hy =>
      intro g
      change ∫ z, (x.1 (g * infGL E a z) + y.1 (g * infGL E a z)) * α z ∂μ = x.1 g + y.1 g
      simp_rw [add_mul]
      rw [integral_add (hint x g) (hint y g), hx, hy]
    | smul c x _ hx =>
      intro g
      change ∫ z, (c * x.1 (g * infGL E a z)) * α z ∂μ = c * x.1 g
      simp_rw [mul_assoc]
      rw [integral_const_mul, hx]

  have hfix : ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ k ∈ L, ∀ x, φ.1 (x * finGL E a k) = φ.1 x := by
    intro φ hφ k hk x
    induction hφ using Submodule.span_induction with
    | mem ψ hψ => exact congrArg (fun f : Sm E a => f.1 x) (hψ.2.1 k hk)
    | zero => rfl
    | add ψ χ _ _ h1 h2 =>
      change ψ.1 (x * finGL E a k) + χ.1 (x * finGL E a k) = ψ.1 x + χ.1 x
      rw [h1, h2]
    | smul c ψ _ h =>
      change c * ψ.1 (x * finGL E a k) = c * ψ.1 x
      rw [h]

  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : GL (Fin a) (Cinf E))
  have hKc : IsCompact (tsupport α) := hαs
  set K' := V * tsupport α with hK'
  have hK'c : IsCompact K' := hVc.mul hKc
  have hK'm : MeasurableSet K' := hK'c.measurableSet

  have hfc : Continuous fun z : GL (Fin a) (Cinf E) => absDetA (infGL E a z) :=
    continuous_absDetA.comp continuous_infGL'
  obtain ⟨B₁, hB₁⟩ := hK'c.exists_bound_of_continuousOn hfc.continuousOn
  obtain ⟨B₂, hB₂⟩ := hK'c.exists_bound_of_continuousOn
    (hfc.inv₀ fun z => (absDetA_pos _).ne').continuousOn
  set c := max 1 (max B₁ B₂) with hc
  have hc1 : 1 ≤ c := le_max_left _ _
  have hcK : ∀ z ∈ K', c⁻¹ ≤ absDetA (infGL E a z) ∧ absDetA (infGL E a z) ≤ c := by
    intro z hz
    have hp := absDetA_pos (infGL E a z)
    have h1 := hB₁ z hz
    have h2 : ‖(absDetA (infGL E a z))⁻¹‖ ≤ B₂ := hB₂ z hz
    rw [Real.norm_of_nonneg hp.le] at h1
    rw [Real.norm_of_nonneg (inv_nonneg.2 hp.le)] at h2
    refine ⟨?_, h1.trans ((le_max_left _ _).trans (le_max_right _ _))⟩
    rw [inv_le_comm₀ (by positivity) hp]
    exact h2.trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨C, hC⟩ := GlobalTheory.T.norm_le_sup_wider_band_genCentralEigenforms E a L hL W hW X hX N c hc1
  set C' := |C| + 1 with hC'
  have hC'0 : 0 < C' := by positivity
  set m := μ.real K' with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  set δ := ε / (C' * (m + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδe : C' * δ * (m + 1) = ε := by rw [hδ]; field_simp

  obtain ⟨v, hv, hvK⟩ := hK'c.mem_uniformity_of_prod (f := fun p x => α (p⁻¹ * x)) (s := Set.univ) (q := 1)
    (by exact (hαc.comp (continuous_fst.inv.mul continuous_snd)).continuousOn) (Set.mem_univ _)
    (Metric.dist_mem_uniformity hδ0)
  rw [nhdsWithin_univ] at hv

  refine ⟨{u | Matrix.GeneralLinearGroup.map (pInf E) u ∈ v ∩ V ∧ Matrix.GeneralLinearGroup.map (pFin E) u ∈ L}, ?_, ?_⟩
  · refine Filter.inter_mem ?_ ?_
    · exact continuous_mapInf.continuousAt.preimage_mem_nhds (by rw [map_one]; exact Filter.inter_mem hv hV1)
    · exact continuous_mapFin.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hL.mem_nhds L.one_mem)
  intro φ hφ M hM g hg u hu _
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1 one_mem_band)
  set y := Matrix.GeneralLinearGroup.map (pInf E) u with hy
  set k := Matrix.GeneralLinearGroup.map (pFin E) u with hk
  have hyv : y ∈ v := hu.1.1
  have hyV : y ∈ V := hu.1.2
  have hkL : k ∈ L := hu.2
  have hgu : φ.1 (g * u) = φ.1 (g * infGL E a y) := by
    rw [← infGL_mul_finGL u, ← mul_assoc, hfix φ hφ k hkL]
  rw [hgu]

  have e1 : φ.1 (g * infGL E a y) = ∫ z, φ.1 (g * infGL E a z) * α (y⁻¹ * z) ∂μ := by
    rw [← hrep φ hφ (g * infGL E a y),
      ← integral_mul_left_eq_self (fun z => φ.1 (g * infGL E a z) * α (y⁻¹ * z)) y]
    congr 1
    funext x
    simp only [map_mul, mul_assoc, inv_mul_cancel_left]
  have hi1 : Integrable (fun z => φ.1 (g * infGL E a z) * α (y⁻¹ * z)) μ :=
    ((continuous_along φ g).mul (hαc.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (hαs.comp_homeomorph (Homeomorph.mulLeft y⁻¹)))
  have e2 : φ.1 (g * infGL E a y) - φ.1 g = ∫ z, φ.1 (g * infGL E a z) * (α (y⁻¹ * z) - α z) ∂μ := by
    rw [e1, ← hrep φ hφ g, ← integral_sub hi1 (hint φ g)]
    simp_rw [mul_sub]
  rw [e2]

  have hpt : ∀ z, ‖φ.1 (g * infGL E a z) * (α (y⁻¹ * z) - α z)‖ ≤ K'.indicator (fun _ => C' * M * δ) z := by
    intro z
    by_cases hz : z ∈ K'
    · rw [Set.indicator_of_mem hz, norm_mul]
      have hd := hcK z hz
      have hg' := hg
      obtain ⟨hg1, hg2⟩ := hg'
      have hb1 : c⁻¹ ≤ absDetA (g * infGL E a z) := by
        rw [absDetA_mul]
        have := absDetA_pos (infGL E a z)
        nlinarith
      have hb2 : absDetA (g * infGL E a z) ≤ 2 * c := by
        rw [absDetA_mul]
        have := absDetA_pos (infGL E a z)
        nlinarith
      have h1 : ‖φ.1 (g * infGL E a z)‖ ≤ C' * M :=
        (hC φ hφ M hM _ hb1 hb2).trans (mul_le_mul_of_nonneg_right (by rw [hC']; linarith [le_abs_self C]) hM0)
      have h2 : ‖α (y⁻¹ * z) - α z‖ ≤ δ := by
        have := hvK y hyv z hz
        simp only [inv_one, one_mul, Set.mem_setOf_eq] at this
        rw [← dist_eq_norm]; exact this.le
      exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    · rw [Set.indicator_of_notMem hz]
      have hz1 : α z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz ⟨1, mem_of_mem_nhds hV1, z, h, one_mul z⟩
      have hz2 : α (y⁻¹ * z) = 0 := image_eq_zero_of_notMem_tsupport fun h =>
        hz ⟨y, hyV, y⁻¹ * z, h, mul_inv_cancel_left y z⟩
      simp [hz1, hz2]
  have hint' : Integrable (K'.indicator (fun _ => C' * M * δ)) μ :=
    (integrableOn_const (C := C' * M * δ) hK'c.measure_lt_top.ne).integrable_indicator hK'm
  refine (norm_integral_le_of_norm_le hint' (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_indicator_const _ hK'm, smul_eq_mul, ← hm]
  have : 0 ≤ C' * M * δ := by positivity
  calc m * (C' * M * δ) ≤ (m + 1) * (C' * M * δ) := by nlinarith
    _ = ε * M := by rw [← hδe]; ring

end GlobalTheory.HCF.Equi
