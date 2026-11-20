import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorPropertiesStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.SelfDualLat

/- English proof (translation)
Introduce `B`. Rewrite using `[Set.indicator_preimage, Set.ite]`. Use `(IsOpen.inter ?_ h.isOpen).union ?_` and prove the remaining obligations. Apply the tactic sequence `rw [Set.preimage_const]; split_ifs <;> simp`. Rewrite using `[Set.diff_eq]`.

Use `IsOpen.inter ?_ h.isClosed.isOpen_compl` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsOpen ((fun _ : X => (0:ℂ)) ⁻¹' B)`. Apply the tactic sequence `rw [Set.preimage_const]; split_ifs <;> simp`.
-/
theorem isLC_indicator_one {X : Type} [TopologicalSpace X] (s : Set X) (h : IsClopen s) :
    IsLocallyConstant (s.indicator (fun _ => (1 : ℂ))) := by
  classical
  intro B
  rw [Set.indicator_preimage, Set.ite]
  refine (IsOpen.inter ?_ h.isOpen).union ?_
  · rw [Set.preimage_const]; split_ifs <;> simp
  · rw [Set.diff_eq]
    refine IsOpen.inter ?_ h.isClosed.isOpen_compl
    change IsOpen ((fun _ : X => (0:ℂ)) ⁻¹' B)
    rw [Set.preimage_const]; split_ifs <;> simp

/- English proof (translation)
Introduce `F E _ _ _ _ _ V _ _ _ _ _`. Use `haveI := (inferInstance : Unram F E).lcF`. Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`. Use `haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V`. Use `haveI : ContinuousNeg V := ⟨by`.

Use `IsModuleTopology.continuous_of_linearMap (R := F) (A := V) (B := V) (-LinearMap.id)` as an intermediate fact. Conclude with `this⟩`. Set `e : V ≃ₗ[F] (Fin (Module.finrank F V) → F)` to `(Module.finBasis F V).equivFun`. Establish `hc : Continuous e` using `IsModuleTopology.continuous_of_linearMap e.toLinearMap`. Establish `hc' : Continuous e.symm` using `IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap`.

Set `h : V ≃ₜ (Fin (Module.finrank F V) → F)` to `⟨e.toEquiv, hc, hc'⟩`. Conclude with `⟨h.isOpenEmbedding.locallyCompactSpace, h.isEmbedding.secondCountableTopology, h.isEmbedding.t2Space, IsTopologicalAddGroup.mk⟩`.
-/
theorem topo : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V], LocallyCompactSpace V ∧ SecondCountableTopology V ∧ T2Space V ∧ IsTopologicalAddGroup V := by
  intro F E _ _ _ _ _ V _ _ _ _ _
  haveI := (inferInstance : Unram F E).lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V
  haveI : ContinuousNeg V := ⟨by
    have := IsModuleTopology.continuous_of_linearMap (R := F) (A := V) (B := V) (-LinearMap.id)
    exact this⟩
  let e : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := (Module.finBasis F V).equivFun
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc' : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : V ≃ₜ (Fin (Module.finrank F V) → F) := ⟨e.toEquiv, hc, hc'⟩
  exact ⟨h.isOpenEmbedding.locallyCompactSpace, h.isEmbedding.secondCountableTopology, h.isEmbedding.t2Space,
    IsTopologicalAddGroup.mk⟩
/- English proof (translation)
Introduce `F E _ _ _ _ _ ψ hψ V _ _ _ _ _ _ _ _ β μ hμ M hMo hMc y`. Distinguish the cases in `hy : y ∈ {y | ∀ x ∈ M, ψ (β x y) = 1}`. Rewrite using `[Set.indicator_of_mem hy, setIntegral_congr_fun hMo.measurableSet (fun x hx => hy x hx)]`. Simplify using `[Measure.real]`. Rewrite using `[Set.indicator_of_notMem hy]`.

Simplify using `only [Set.mem_setOf_eq, not_forall] at hy`. Take `⟨x0, hx0, hne⟩` from `hy`. Establish `ht` using `integral_add_left_eq_self (μ := μ) (fun x => (M : Set V).indicator (fun x => ψ (β x y)) x) x0`. Establish `hpt : ∀ x, (M : Set V).indicator (fun x => ψ (β x y)) (x0 + x) = ψ (β x0 y) * (M : Set V).indicator (fun x => ψ (β x y)) x`. Introduce `x`.

Distinguish the cases in `hx : x ∈ M`. Establish `: x0 + x ∈ M` using `M.add_mem hx0 hx`. Simplify using `[Set.indicator_of_mem (show x0 + x ∈ (M : Set V) from this), Set.indicator_of_mem (show x ∈ (M : Set V) from hx), map_add, AddChar.map_add_eq_mul]`. Establish `: x0 + x ∉ M` using `fun h => hx (by simpa using M.sub_mem h hx0)`. Simplify using `[Set.indicator_of_notMem (show x0 + x ∉ (M : Set V) from this), Set.indicator_of_notMem (show x ∉ (M : Set V) from hx)]`.

Rewrite `ht` using `[hpt]`. Rewrite `ht` using `[integral_const_mul, integral_indicator hMo.measurableSet]`. Establish `h0 : (ψ (β x0 y) - 1) * ∫ x in (M : Set V), ψ (β x y) ∂μ = 0` using `by rw [sub_mul, one_mul, ht, sub_self]`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h) hne`.

Conclude with `h`.
-/
theorem orth : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] [IsTopologicalAddGroup V] (β : LinearMap.BilinForm F V) (μ : Measure V), μ.IsAddHaarMeasure → ∀ M : AddSubgroup V, IsOpen (M : Set V) → IsCompact (M : Set V) → ∀ y, ∫ x in (M : Set V), ψ (β x y) ∂μ = Set.indicator {y | ∀ x ∈ M, ψ (β x y) = 1} (fun _ => ((μ M).toReal : ℂ)) y := by
  intro F E _ _ _ _ _ ψ hψ V _ _ _ _ _ _ _ _ β μ hμ M hMo hMc y
  classical
  by_cases hy : y ∈ {y | ∀ x ∈ M, ψ (β x y) = 1}
  · rw [Set.indicator_of_mem hy, setIntegral_congr_fun hMo.measurableSet (fun x hx => hy x hx)]
    simp [Measure.real]
  · rw [Set.indicator_of_notMem hy]
    simp only [Set.mem_setOf_eq, not_forall] at hy
    obtain ⟨x0, hx0, hne⟩ := hy
    have ht := integral_add_left_eq_self (μ := μ) (fun x => (M : Set V).indicator (fun x => ψ (β x y)) x) x0
    have hpt : ∀ x, (M : Set V).indicator (fun x => ψ (β x y)) (x0 + x) =
        ψ (β x0 y) * (M : Set V).indicator (fun x => ψ (β x y)) x := by
      intro x
      by_cases hx : x ∈ M
      · have : x0 + x ∈ M := M.add_mem hx0 hx
        simp [Set.indicator_of_mem (show x0 + x ∈ (M : Set V) from this),
          Set.indicator_of_mem (show x ∈ (M : Set V) from hx), map_add, AddChar.map_add_eq_mul]
      · have : x0 + x ∉ M := fun h => hx (by simpa using M.sub_mem h hx0)
        simp [Set.indicator_of_notMem (show x0 + x ∉ (M : Set V) from this),
          Set.indicator_of_notMem (show x ∉ (M : Set V) from hx)]
    simp_rw [hpt] at ht
    rw [integral_const_mul, integral_indicator hMo.measurableSet] at ht
    have h0 : (ψ (β x0 y) - 1) * ∫ x in (M : Set V), ψ (β x y) ∂μ = 0 := by rw [sub_mul, one_mul, ht, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
/- English proof (translation)
Introduce `F E _ _ _ _ _ ψ hψ V _ _ _ _ _ _ _ _ _ _ _ β hβs hβn μ hsd f hf`. Use `haveI := hsd.1`. Establish `hψ'` using `(GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ`. Establish `hI` using `GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ V β hβs hβn`. Use `set B : V → V → ℂ := fun x y => ψ (β x y) with hB`.

Use `set g := fourB μ B f with hgdef`. Establish `hg : IsTest g` using `hI.2 μ hsd.1 f hf`. Establish `hψc : Continuous (fun t : F => ψ t)` using `hψ'.1.continuous`. Establish `hβc : Continuous (fun p : V × V => β p.1 p.2)` using `IsModuleTopology.continuous_bilinear_of_finite_left β`. Establish `hfc : Continuous f` using `hf.1.continuous`.

Establish `hgc : Continuous g` using `hg.1.continuous`. Establish `hfi : Integrable f μ` using `hfc.integrable_of_hasCompactSupport hf.2`. Establish `hgi : Integrable g μ` using `hgc.integrable_of_hasCompactSupport hg.2`. Establish `key : ∀ h : V → ℂ, ((∫ y, ‖h y‖ ^ 2 ∂μ : ℝ) : ℂ) = ∫ y, h y * (starRingEnd ℂ) (h y) ∂μ`. Introduce `h`.

Rewrite using `[← integral_complex_ofReal]`. Use `congr 1`. Use extensionality with `y`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Establish `hconj : ∀ t : F, (starRingEnd ℂ) (ψ t) = ψ (-t)`.

Introduce `t`. Rewrite using `[AddChar.map_neg_eq_inv]`. Establish `h1 : ‖ψ t‖ = 1` using `hψ'.2.1 t`. Establish `h0 : ψ t ≠ 0` using `by intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1`. Rewrite using `[Complex.inv_def, Complex.normSq_eq_norm_sq, h1]`.

Simplify using the standard rewrite rules. Establish `hinner : ∀ x, ∫ y, ψ (β x y) * (starRingEnd ℂ) (g y) ∂μ = (starRingEnd ℂ) (f x)`. Introduce `x`. Use `hsd.2 f hf (-x)` as an intermediate fact. Rewrite `this` using `[neg_neg]`.

Rewrite using `[← this]`. Use `show _ = (starRingEnd ℂ) (∫ y, g y * B y (-x) ∂μ)`. Rewrite using `[← integral_conj]`. Use `congr 1`. Use extensionality with `y`.

Rewrite using `[map_mul, hconj]`. Simplify using `only [map_neg, neg_neg, hβs.eq x y]`. Expand and normalize the polynomial expressions, which then agree. Establish `hint : Integrable (Function.uncurry fun y x => f x * ψ (β x y) * (starRingEnd ℂ) (g y)) (μ.prod μ)`. Use `Integrable.mono' ((hgi.norm).mul_prod hfi.norm) ?_ ?_` and prove the remaining obligations.

Use `Continuous.aestronglyMeasurable ?_` and prove the remaining obligations. Conclude with `((hfc.comp continuous_snd).mul (hψc.comp (hβc.comp continuous_swap))).mul (Complex.continuous_conj.comp (hgc.comp continuous_fst))`. Use `Filter.Eventually.of_forall (fun z => ?_)` and prove the remaining obligations. Simplify using `only [Function.uncurry, norm_mul, hψ'.2.1, mul_one, Complex.norm_conj]`. Rewrite using `[mul_comm]`.

Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[key, key]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use extensionality with `y`.

Rewrite using `[hgdef]`. Unfold `fourB`. Rewrite using `[← integral_mul_const]`. Use `_ = ∫ x, ∫ y, f x * ψ (β x y) * (starRingEnd ℂ) (g y) ∂μ ∂μ := integral_integral_swap hint`. Use `_ = ∫ x, f x * (starRingEnd ℂ) (f x) ∂μ := by`.

Use `congr 1`. Use extensionality with `x`. Repeatedly rewrite using `[mul_assoc]`. Rewrite using `[integral_const_mul, hinner]`.
-/
theorem planch : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [IsTopologicalAddGroup V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → ∀ μ : Measure V, SelfDual μ (fun x y => ψ (β x y)) → ∀ f, IsTest f → ∫ y, ‖fourB μ (fun x y => ψ (β x y)) f y‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ ψ hψ V _ _ _ _ _ _ _ _ _ _ _ β hβs hβn μ hsd f hf
  haveI := hsd.1
  have hψ' := (GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ
  have hI := GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ V β hβs hβn
  set B : V → V → ℂ := fun x y => ψ (β x y) with hB
  set g := fourB μ B f with hgdef
  have hg : IsTest g := hI.2 μ hsd.1 f hf
  have hψc : Continuous (fun t : F => ψ t) := hψ'.1.continuous
  have hβc : Continuous (fun p : V × V => β p.1 p.2) := IsModuleTopology.continuous_bilinear_of_finite_left β
  have hfc : Continuous f := hf.1.continuous
  have hgc : Continuous g := hg.1.continuous
  have hfi : Integrable f μ := hfc.integrable_of_hasCompactSupport hf.2
  have hgi : Integrable g μ := hgc.integrable_of_hasCompactSupport hg.2
  have key : ∀ h : V → ℂ, ((∫ y, ‖h y‖ ^ 2 ∂μ : ℝ) : ℂ) = ∫ y, h y * (starRingEnd ℂ) (h y) ∂μ := by
    intro h
    rw [← integral_complex_ofReal]
    congr 1; ext y
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hconj : ∀ t : F, (starRingEnd ℂ) (ψ t) = ψ (-t) := by
    intro t
    rw [AddChar.map_neg_eq_inv]
    have h1 : ‖ψ t‖ = 1 := hψ'.2.1 t
    have h0 : ψ t ≠ 0 := by intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1]; simp
  have hinner : ∀ x, ∫ y, ψ (β x y) * (starRingEnd ℂ) (g y) ∂μ = (starRingEnd ℂ) (f x) := by
    intro x
    have := hsd.2 f hf (-x)
    rw [neg_neg] at this
    rw [← this]
    show _ = (starRingEnd ℂ) (∫ y, g y * B y (-x) ∂μ)
    rw [← integral_conj]
    congr 1; ext y
    rw [map_mul, hconj]
    simp only [map_neg, neg_neg, hβs.eq x y]
    ring
  have hint : Integrable (Function.uncurry fun y x => f x * ψ (β x y) * (starRingEnd ℂ) (g y)) (μ.prod μ) := by
    refine Integrable.mono' ((hgi.norm).mul_prod hfi.norm) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      exact ((hfc.comp continuous_snd).mul (hψc.comp (hβc.comp continuous_swap))).mul
        (Complex.continuous_conj.comp (hgc.comp continuous_fst))
    · refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [Function.uncurry, norm_mul, hψ'.2.1, mul_one, Complex.norm_conj]
      rw [mul_comm]
  apply Complex.ofReal_injective
  rw [key, key]
  calc ∫ y, g y * (starRingEnd ℂ) (g y) ∂μ
      = ∫ y, ∫ x, f x * ψ (β x y) * (starRingEnd ℂ) (g y) ∂μ ∂μ := by
        congr 1; ext y
        rw [hgdef]; unfold fourB
        rw [← integral_mul_const]
    _ = ∫ x, ∫ y, f x * ψ (β x y) * (starRingEnd ℂ) (g y) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ x, f x * (starRingEnd ℂ) (f x) ∂μ := by
        congr 1; ext x
        simp_rw [mul_assoc]
        rw [integral_const_mul, hinner]

end GlobalTheory.JR.SelfDualLat

open GlobalTheory.JR.SelfDualLat in
/- English proof (translation)
Introduce `F E _ _ _ _ _ ψ hψ V _ _ _ _ _ _ _ β hβs hβn μ hμ`. Take `⟨hLC, hSC, hT2, hTG⟩` from `topo F E V`. Use `haveI := hLC`. Use `haveI := hSC`. Use `haveI := hT2`.

Use `haveI := hTG`. Establish `hI` using `GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ V β hβs hβn`. Establish `fwd : ∀ ν : Measure V, SelfDual ν (fun x y => ψ (β x y)) → ∀ M : AddSubgroup V, IsOpen (M : Set V) → IsCompact (M : Set V) → ν M * ν {y | ∀ x ∈ M, ψ (β x y) = 1} = 1`. Introduce `ν hν M hMo hMc`. Use `haveI := hν.1`.

Use `set P : Set V := {y | ∀ x ∈ M, ψ (β x y) = 1} with hP`. Use `set g : V → ℂ := (M : Set V).indicator (fun _ => 1) with hg`. Establish `hMcl : IsClosed (M : Set V)` using `AddSubgroup.isClosed_of_isOpen M hMo`. Establish `hgt : IsTest g` using `⟨isLC_indicator_one _ ⟨hMcl, hMo⟩, HasCompactSupport.intro hMc (fun x hx => Set.indicator_of_notMem hx _)⟩`. Establish `h1 : ∀ x, fourB ν (fun x y => ψ (β x y)) g x = P.indicator (fun _ => ((ν M).toReal : ℂ)) x`.

Introduce `x`. Rewrite using `[← orth F E ψ hψ V β ν hν.1 M hMo hMc x]`. Unfold `fourB`. Rewrite using `[← integral_indicator hMo.measurableSet]`. Use `congr 1`.

Use extensionality with `t`. Apply the tactic sequence `by_cases ht : t ∈ (M : Set V) <;> simp [hg, ht]`. Establish `hc : ((ν M).toReal : ℂ) ≠ 0`. Establish `h0 : ν M ≠ 0` using `(hMo.measure_pos ν ⟨0, M.zero_mem⟩).ne'`. Establish `ht : ν M ≠ ⊤` using `hMc.measure_lt_top.ne`.

Conclude with `(ENNReal.toReal_pos h0 ht).ne'` after adjusting the coercions. Establish `hft` using `hI.2 ν hν.1 g hgt`. Establish `hPm : MeasurableSet P`. Establish `: P = (fourB ν (fun x y => ψ (β x y)) g) ⁻¹' {((ν M).toReal : ℂ)}`. Use extensionality with `y`.

Use `show y ∈ P ↔ fourB ν (fun x y => ψ (β x y)) g y = ((ν M).toReal : ℂ)`. Rewrite using `[h1]`. Distinguish the cases in `hy : y ∈ P`. Simplify using `[Set.indicator_of_mem hy, hy]`. Rewrite using `[Set.indicator_of_notMem hy]`.

Conclude with `⟨fun h => absurd h hy, fun h => absurd h.symm hc⟩`. Rewrite using `[this]`. Conclude with `(hft.1.isOpen_fiber _).measurableSet`. Establish `h2` using `hν.2 g hgt 0`. Rewrite `h2` using `[neg_zero, show g 0 = 1 by simp [hg, M.zero_mem]]`.

Establish `h3 : fourB ν (fun x y => ψ (β x y)) (fourB ν (fun x y => ψ (β x y)) g) 0 = (ν P).toReal * (ν M).toReal` using `by show ∫ x, fourB ν (fun x y => ψ (β x y)) g x * ψ (β x 0) ∂ν = _`. Repeatedly rewrite using `[h1, map_zero, AddChar.map_zero_eq_one, mul_one]`. Rewrite using `[integral_indicator_const _ hPm]`. Simplify using `[Measure.real]`. Rewrite `h2` using `[h3]`.

Rewrite using `[← ENNReal.toReal_eq_one_iff, ENNReal.toReal_mul]`. Establish `h4 : (((ν M).toReal * (ν P).toReal : ℝ) : ℂ) = 1` using `by push_cast; linear_combination h2`. Conclude with `h4` after adjusting the coercions. Use `⟨fun M hMo hMc => ⟨⟨fun hsd => fwd μ hsd M hMo hMc, fun h => ?_⟩, orth F E ψ hψ V β μ hμ M hMo hMc⟩, fun hsd f hf => planch F E ψ hψ V β hβs hβn μ hsd f hf⟩` and prove the remaining obligations. Take `⟨⟨μ0, hμ0, -⟩, -⟩` from `hI`.

Use `haveI := hμ0.1`. Establish `hsc : μ = Measure.addHaarScalarFactor μ μ0 • μ0` using `Measure.isAddLeftInvariant_eq_smul μ μ0`. Use `set c := Measure.addHaarScalarFactor μ μ0 with hcdef`. Establish `h0` using `fwd μ0 hμ0 M hMo hMc`. Rewrite `h` using `[hsc]`.

Simplify using `only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h`. Establish `hcc : ((c * c : NNReal) : ENNReal) = 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h0, mul_one, ENNReal.coe_mul]`. Use `_ = (c : ENNReal) * μ0 M * ((c : ENNReal) * μ0 {y | ∀ x ∈ M, ψ (β x y) = 1}) := by ring`.

Use `_ = 1 := h`. Establish `hcc' : (c : ℝ) * c = 1` using `by exact_mod_cast (ENNReal.coe_eq_one.1 hcc)`. Establish `hc1 : c = 1`. Establish `: (c : ℝ) = 1` using `by nlinarith [c.2]`. Conclude with `this` after adjusting the coercions.

Establish `: μ = μ0` using `by rw [hsc, hc1, one_smul]`. Rewrite using `[this]`. Conclude with `hμ0`.
-/
theorem GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → ∀ μ : Measure V, μ.IsAddHaarMeasure → (∀ M : AddSubgroup V, IsOpen (M : Set V) → IsCompact (M : Set V) → (SelfDual μ (fun x y => ψ (β x y)) ↔ μ M * μ {y | ∀ x ∈ M, ψ (β x y) = 1} = 1) ∧ ∀ y, ∫ x in (M : Set V), ψ (β x y) ∂μ = Set.indicator {y | ∀ x ∈ M, ψ (β x y) = 1} (fun _ => ((μ M).toReal : ℂ)) y) ∧ (SelfDual μ (fun x y => ψ (β x y)) → ∀ f, IsTest f → ∫ y, ‖fourB μ (fun x y => ψ (β x y)) f y‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) := by
  intro F E _ _ _ _ _ ψ hψ V _ _ _ _ _ _ _ β hβs hβn μ hμ
  obtain ⟨hLC, hSC, hT2, hTG⟩ := topo F E V
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hTG
  have hI := GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ V β hβs hβn
  have fwd : ∀ ν : Measure V, SelfDual ν (fun x y => ψ (β x y)) → ∀ M : AddSubgroup V, IsOpen (M : Set V) →
      IsCompact (M : Set V) → ν M * ν {y | ∀ x ∈ M, ψ (β x y) = 1} = 1 := by
    intro ν hν M hMo hMc
    haveI := hν.1
    set P : Set V := {y | ∀ x ∈ M, ψ (β x y) = 1} with hP
    set g : V → ℂ := (M : Set V).indicator (fun _ => 1) with hg
    have hMcl : IsClosed (M : Set V) := AddSubgroup.isClosed_of_isOpen M hMo
    have hgt : IsTest g := ⟨isLC_indicator_one _ ⟨hMcl, hMo⟩,
      HasCompactSupport.intro hMc (fun x hx => Set.indicator_of_notMem hx _)⟩
    have h1 : ∀ x, fourB ν (fun x y => ψ (β x y)) g x = P.indicator (fun _ => ((ν M).toReal : ℂ)) x := by
      intro x
      rw [← orth F E ψ hψ V β ν hν.1 M hMo hMc x]
      unfold fourB
      rw [← integral_indicator hMo.measurableSet]
      congr 1; ext t
      by_cases ht : t ∈ (M : Set V) <;> simp [hg, ht]
    have hc : ((ν M).toReal : ℂ) ≠ 0 := by
      have h0 : ν M ≠ 0 := (hMo.measure_pos ν ⟨0, M.zero_mem⟩).ne'
      have ht : ν M ≠ ⊤ := hMc.measure_lt_top.ne
      exact_mod_cast (ENNReal.toReal_pos h0 ht).ne'
    have hft := hI.2 ν hν.1 g hgt
    have hPm : MeasurableSet P := by
      have : P = (fourB ν (fun x y => ψ (β x y)) g) ⁻¹' {((ν M).toReal : ℂ)} := by
        ext y
        show y ∈ P ↔ fourB ν (fun x y => ψ (β x y)) g y = ((ν M).toReal : ℂ)
        rw [h1]
        by_cases hy : y ∈ P
        · simp [Set.indicator_of_mem hy, hy]
        · rw [Set.indicator_of_notMem hy]; exact ⟨fun h => absurd h hy, fun h => absurd h.symm hc⟩
      rw [this]; exact (hft.1.isOpen_fiber _).measurableSet
    have h2 := hν.2 g hgt 0
    rw [neg_zero, show g 0 = 1 by simp [hg, M.zero_mem]] at h2
    have h3 : fourB ν (fun x y => ψ (β x y)) (fourB ν (fun x y => ψ (β x y)) g) 0 =
        (ν P).toReal * (ν M).toReal := by
      show ∫ x, fourB ν (fun x y => ψ (β x y)) g x * ψ (β x 0) ∂ν = _
      simp_rw [h1, map_zero, AddChar.map_zero_eq_one, mul_one]
      rw [integral_indicator_const _ hPm]
      simp [Measure.real]
    rw [h3] at h2
    rw [← ENNReal.toReal_eq_one_iff, ENNReal.toReal_mul]
    have h4 : (((ν M).toReal * (ν P).toReal : ℝ) : ℂ) = 1 := by push_cast; linear_combination h2
    exact_mod_cast h4
  refine ⟨fun M hMo hMc => ⟨⟨fun hsd => fwd μ hsd M hMo hMc, fun h => ?_⟩, orth F E ψ hψ V β μ hμ M hMo hMc⟩,
    fun hsd f hf => planch F E ψ hψ V β hβs hβn μ hsd f hf⟩
  obtain ⟨⟨μ0, hμ0, -⟩, -⟩ := hI
  haveI := hμ0.1
  have hsc : μ = Measure.addHaarScalarFactor μ μ0 • μ0 := Measure.isAddLeftInvariant_eq_smul μ μ0
  set c := Measure.addHaarScalarFactor μ μ0 with hcdef
  have h0 := fwd μ0 hμ0 M hMo hMc
  rw [hsc] at h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
  have hcc : ((c * c : NNReal) : ENNReal) = 1 := by
    calc ((c * c : NNReal) : ENNReal) = (c : ENNReal) * c * (μ0 M * μ0 {y | ∀ x ∈ M, ψ (β x y) = 1}) := by
          rw [h0, mul_one, ENNReal.coe_mul]
      _ = (c : ENNReal) * μ0 M * ((c : ENNReal) * μ0 {y | ∀ x ∈ M, ψ (β x y) = 1}) := by ring
      _ = 1 := h
  have hcc' : (c : ℝ) * c = 1 := by exact_mod_cast (ENNReal.coe_eq_one.1 hcc)
  have hc1 : c = 1 := by
    have : (c : ℝ) = 1 := by nlinarith [c.2]
    exact_mod_cast this
  have : μ = μ0 := by rw [hsc, hc1, one_smul]
  rw [this]; exact hμ0
