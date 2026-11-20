import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLinearCombination
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieDerivativeConvolutionKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModerateGrowthConvolutionIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2ConvolutionLocallyCompactMemStatement

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section
namespace GlobalTheory.CompanionTheory.StableMod

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Use `open GlobalTheory.CuspStab in`. Take `⟨hA, hC⟩` from `h`. Use `⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ.1 (ratGL E a γ * g * finGL E a k) = φ.1 (g * finGL E a k)`. Rewrite using `[mul_assoc, hA.left]`.

Establish `e : {k' | finRep E a k' (finRep E a k φ) = finRep E a k φ} = (fun k' => k⁻¹ * k' * k) ⁻¹' {k' | finRep E a k' φ = φ}`. Use extensionality with `k'`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, map_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `e`.

Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, e, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Introduce `e`. Use `congrArg (finRep E a k) e` as an intermediate fact. Rewrite `this` using `[Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (finRep E a k), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Then use the resulting hypothesis. Express the relevant statement in the definitionally equal form `IsOpen {k' | finRep E a k' (finRep E a k φ) = finRep E a k φ}`.

Rewrite using `[e]`. Conclude with `hA.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)`. Use `hA.kfin` as an intermediate fact. Use `Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun c => cptRep E a c φ)).map (finRep E a k)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨c, rfl⟩`.

Conclude with `⟨_, Submodule.subset_span ⟨c, rfl⟩, (LinearMap.congr_fun (fin_cpt_comm k c) φ)⟩`. Conclude with `zfin_of_comm _ (fun z hz => zalg_comm_fin k hz) hA.zfin`. Take `⟨C, N, h1⟩` from `hA.growth (g * finGL E a k)`. Use `⟨C, N, fun y => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖φ.1 (g * infGL E a y * finGL E a k)‖ ≤ _`.

Rewrite using `[mul_assoc, infGL_comm, ← mul_assoc]`. Conclude with `h1 y`. Introduce `r h0 h1 _ _ μ 𝓕 hμ hF g`. Express the relevant statement in the definitionally equal form `∫ x in 𝓕, φ.1 (unip x * g * finGL E a k) ∂μ = 0`. Repeatedly rewrite using `[mul_assoc]`.

Conclude with `hC r h0 h1 μ 𝓕 hμ hF (g * finGL E a k)`.
-/
theorem isCuspForm_fin (k : GL (Fin a) (Af E)) {φ : Sm E a} (h : IsCuspForm φ) : IsCuspForm (finRep E a k φ) := by
  open GlobalTheory.CuspStab in
  obtain ⟨hA, hC⟩ := h
  refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, ?_⟩
  · change φ.1 (ratGL E a γ * g * finGL E a k) = φ.1 (g * finGL E a k)
    rw [mul_assoc, hA.left]
  · have e : {k' | finRep E a k' (finRep E a k φ) = finRep E a k φ} =
        (fun k' => k⁻¹ * k' * k) ⁻¹' {k' | finRep E a k' φ = φ} := by
      ext k'
      simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul]
      constructor
      · intro e
        rw [Module.End.mul_apply, Module.End.mul_apply, e, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
          map_one, Module.End.one_apply]
      · intro e
        have := congrArg (finRep E a k) e
        rwa [Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (finRep E a k), ← map_mul,
          mul_inv_cancel, map_one, Module.End.one_apply] at this
    change IsOpen {k' | finRep E a k' (finRep E a k φ) = finRep E a k φ}
    rw [e]
    exact hA.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · have := hA.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun c => cptRep E a c φ)).map
      (finRep E a k)) (Submodule.span_le.2 ?_)
    rintro _ ⟨c, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨c, rfl⟩, (LinearMap.congr_fun (fin_cpt_comm k c) φ)⟩
  · exact zfin_of_comm _ (fun z hz => zalg_comm_fin k hz) hA.zfin
  · obtain ⟨C, N, h1⟩ := hA.growth (g * finGL E a k)
    refine ⟨C, N, fun y => ?_⟩
    change ‖φ.1 (g * infGL E a y * finGL E a k)‖ ≤ _
    rw [mul_assoc, infGL_comm, ← mul_assoc]
    exact h1 y
  · intro r h0 h1 _ _ μ 𝓕 hμ hF g
    change ∫ x in 𝓕, φ.1 (unip x * g * finGL E a k) ∂μ = 0
    simp_rw [mul_assoc]
    exact hC r h0 h1 μ 𝓕 hμ hF (g * finGL E a k)

/- English proof (translation)
Use `open GlobalTheory.CuspStab in`. Take `⟨hA, hC⟩` from `h`. Use `⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ.1 (ratGL E a γ * g * infGL E a (Unitary.toUnits c)) = φ.1 (g * infGL E a (Unitary.toUnits c))`. Rewrite using `[mul_assoc, hA.left]`.

Conclude with `level_of_le hA.level fun k hk => by`. Express the relevant statement in the definitionally equal form `finRep E a k (cptRep E a c φ) = cptRep E a c φ`. Rewrite using `[← Module.End.mul_apply, fin_cpt_comm, Module.End.mul_apply, hk]`. Use `hA.kfin` as an intermediate fact. Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun c => cptRep E a c φ)) (Submodule.span_le.2 ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨c', rfl⟩`. Use `Submodule.subset_span ⟨c' * c, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = (cptRep E a c' * cptRep E a c) φ`. Rewrite using `[← map_mul]`. Conclude with `zfin_of_comm _ (fun z hz => GlobalTheory.T.mem_zalg_commute_compactRep E a c z hz) hA.zfin`.

Take `⟨C, N, h1⟩` from `growth_mul (Unitary.toUnits c) (hA.growth g)`. Use `⟨C, N, fun y => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖φ.1 (g * infGL E a y * infGL E a (Unitary.toUnits c))‖ ≤ _`. Rewrite using `[mul_assoc, ← map_mul]`. Conclude with `h1 y`.

Introduce `r h0 h1 _ _ μ 𝓕 hμ hF g`. Express the relevant statement in the definitionally equal form `∫ x in 𝓕, φ.1 (unip x * g * infGL E a (Unitary.toUnits c)) ∂μ = 0`. Repeatedly rewrite using `[mul_assoc]`. Conclude with `hC r h0 h1 μ 𝓕 hμ hF (g * infGL E a (Unitary.toUnits c))`.
-/
theorem isCuspForm_cpt (c : Kinf E a) {φ : Sm E a} (h : IsCuspForm φ) : IsCuspForm (cptRep E a c φ) := by
  open GlobalTheory.CuspStab in
  obtain ⟨hA, hC⟩ := h
  refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, ?_⟩
  · change φ.1 (ratGL E a γ * g * infGL E a (Unitary.toUnits c)) = φ.1 (g * infGL E a (Unitary.toUnits c))
    rw [mul_assoc, hA.left]
  · exact level_of_le hA.level fun k hk => by
      change finRep E a k (cptRep E a c φ) = cptRep E a c φ
      rw [← Module.End.mul_apply, fin_cpt_comm, Module.End.mul_apply, hk]
  · have := hA.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun c => cptRep E a c φ))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨c', rfl⟩
    refine Submodule.subset_span ⟨c' * c, ?_⟩
    change _ = (cptRep E a c' * cptRep E a c) φ
    rw [← map_mul]
  · exact zfin_of_comm _ (fun z hz => GlobalTheory.T.mem_zalg_commute_compactRep E a c z hz) hA.zfin
  · obtain ⟨C, N, h1⟩ := growth_mul (Unitary.toUnits c) (hA.growth g)
    refine ⟨C, N, fun y => ?_⟩
    change ‖φ.1 (g * infGL E a y * infGL E a (Unitary.toUnits c))‖ ≤ _
    rw [mul_assoc, ← map_mul]
    exact h1 y
  · intro r h0 h1 _ _ μ 𝓕 hμ hF g
    change ∫ x in 𝓕, φ.1 (unip x * g * infGL E a (Unitary.toUnits c)) ∂μ = 0
    simp_rw [mul_assoc]
    exact hC r h0 h1 μ 𝓕 hμ hF (g * infGL E a (Unitary.toUnits c))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `lieD X φ.1 (u * g) = lieD X φ.1 g`. Establish `e : chart φ.1 (u * g) = chart φ.1 g`. Use function extensionality and compare the values at `x`. Unfold `chart`. Use `split_ifs`.

Rewrite using `[mul_assoc, hu]`. Both sides reduce to the same expression. Unfold `lieD`. Rewrite using `[e]`.
-/
theorem lieD_left {φ : Sm E a} (X : Lie E a) {u : GA E a} (hu : ∀ g, φ.1 (u * g) = φ.1 g) (g : GA E a) :
    (lie E a X φ).1 (u * g) = (lie E a X φ).1 g := by
  change lieD X φ.1 (u * g) = lieD X φ.1 g
  have e : chart φ.1 (u * g) = chart φ.1 g := by
    funext x
    unfold chart
    split_ifs
    · rw [mul_assoc, hu]
    · rfl
  unfold lieD
  rw [e]

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (H : Submodule ℂ (L2 (latticeGL E a) μ))

def formSpace (hH : IsSubrep (R (latticeGL E a) μ) H) : Submodule ℂ (Sm E a) where
  carrier := {φ | IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
    ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H}
  zero_mem' := by
    refine ⟨⟨isAutForm_const (zero_mem _), fun r _ _ _ _ _ _ _ _ _ => integral_zero _ _⟩, fun _ _ => rfl, ?_⟩
    have h : MemL2Quotient (latticeGL E a) μ (0 : Sm E a).1 := ⟨fun _ _ _ => rfl, MemLp.zero⟩
    refine ⟨h, ?_⟩
    have : h.toL2 = 0 := MemLp.toLp_zero _
    rw [this]
    exact zero_mem _
  add_mem' := by
    rintro φ ψ ⟨h1, h2, h3, h4⟩ ⟨h5, h6, h7, h8⟩
    have e := GlobalTheory.CuspFormLin.isCuspForm_smul_add E a 1 φ ψ h1 h5
    rw [one_smul] at e
    refine ⟨e, fun t g => ?_, ?_⟩
    · exact congrArg₂ (· + ·) (h2 t g) (h6 t g)
    · have h : MemL2Quotient (latticeGL E a) μ (φ + ψ).1 := ⟨fun γ hγ g => congrArg₂ (· + ·) (h3.1 γ hγ g) (h7.1 γ hγ g), h3.2.add h7.2⟩
      refine ⟨h, ?_⟩
      have : h.toL2 = h3.toL2 + h7.toL2 := MemLp.toLp_add h3.2 h7.2
      rw [this]
      exact add_mem h4 h8
  smul_mem' := by
    rintro c φ ⟨h1, h2, h3, h4⟩
    have hz : IsCuspForm (0 : Sm E a) :=
      ⟨isAutForm_const (zero_mem _), fun r _ _ _ _ _ _ _ _ _ => integral_zero _ _⟩
    have e := GlobalTheory.CuspFormLin.isCuspForm_smul_add E a c φ 0 h1 hz
    rw [add_zero] at e
    refine ⟨e, fun t g => congrArg (c • ·) (h2 t g), ?_⟩
    have h : MemL2Quotient (latticeGL E a) μ (c • φ).1 := ⟨fun γ hγ g => congrArg (c • ·) (h3.1 γ hγ g), h3.2.const_smul c⟩
    refine ⟨h, ?_⟩
    have : h.toL2 = c • h3.toL2 := MemLp.toLp_const_smul c h3.2
    rw [this]
    exact H.smul_mem c h4

open GroundTheory.Automorphic in

/- English proof (translation)
Establish `hS : IsSubrep (R (latticeGL E a) μ) H` using `hi.1`. Use `⟨formSpace μ H hS, fun φ => Iff.rfl, ?_⟩` and prove the remaining obligations. Introduce and unpack `o φ ⟨h1, h2, h3, h4⟩`. Consider the cases of `o with`. Consider the case `fin k`.

Use `⟨isCuspForm_fin k h1, fun t g => ?_, h3.mul_right (finGL E a k), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ.1 (splitCentre E a t * g * finGL E a k) = φ.1 (g * finGL E a k)`. Rewrite using `[mul_assoc, h2]`. Conclude with `(right_translate_toL2 h3 _) ▸ hS.2 _ _ h4`. Consider the case `cpt k`.

Use `⟨isCuspForm_cpt k h1, fun t g => ?_, h3.mul_right (infGL E a (Unitary.toUnits k)), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ.1 (splitCentre E a t * g * infGL E a (Unitary.toUnits k)) = φ.1 (g * infGL E a (Unitary.toUnits k))`. Rewrite using `[mul_assoc, h2]`. Conclude with `(right_translate_toL2 h3 _) ▸ hS.2 _ _ h4`. Consider the case `lie X`.

Use `letI : MeasurableSpace (AutomorphicForm.archGroup E a) := borel _`. Use `haveI : BorelSpace (AutomorphicForm.archGroup E a) := ⟨rfl⟩`. Take `⟨D, hD, hDc, hrep⟩` from `GlobalTheory.T.lie_derivative_convolution_kernel E a (Measure.haar : Measure (AutomorphicForm.archGroup E a)) φ h1.1 X`. Establish `hc : Continuous φ.1` using `ContAut.continuous_of_isOpen_stab E a φ h1.1.level`. Take `⟨h', hW⟩` from `GlobalTheory.T.l2_convolution_locally_compact_mem (latticeGL E a) μ (Measure.haar : Measure (AutomorphicForm.archGroup E a)) (AutomorphicForm.infEmb E a) AutomorphicForm.continuous_infEmb D hD hDc φ.1 (lie E a X φ).1 hc h3 hrep`.

Use `⟨⟨⟨fun γ g => lieD_left X (h1.1.left γ) g, ?_, GlobalTheory.T.finiteDimensional_span_compact_orbit_lieDerivative E a X φ h1.1.kfin, GlobalTheory.CuspStab.zfin_of_comm _ (fun z hz => GlobalTheory.T.mem_zalg_commute_lie_action E a X z hz) h1.1.zfin, GlobalTheory.T.moderate_growth_c …` and prove the remaining obligations. Conclude with `GlobalTheory.CuspStab.level_of_le h1.1.level fun k hk => by`. Express the relevant statement in the definitionally equal form `finRep E a k (lie E a X φ) = lie E a X φ`. Express the relevant statement in the definitionally equal form `(rt E a (finGL E a k) * lie E a X) φ = _`. Rewrite using `[← lie_rt_fin, Module.End.mul_apply]`.

Conclude with `congrArg (lie E a X) hk`.
-/
theorem exists_stable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)) (_ : H ≤ L2cusp μ)
    (hi : IsIrredSubrep (R (latticeGL E a) μ) H) :
    ∃ V : Submodule ℂ (Sm E a), (∀ φ, φ ∈ V ↔ IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
      ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) ∧ IsStable V := by
  have hS : IsSubrep (R (latticeGL E a) μ) H := hi.1
  refine ⟨formSpace μ H hS, fun φ => Iff.rfl, ?_⟩
  rintro o φ ⟨h1, h2, h3, h4⟩
  cases o with
  | fin k =>
    refine ⟨isCuspForm_fin k h1, fun t g => ?_, h3.mul_right (finGL E a k), ?_⟩
    · change φ.1 (splitCentre E a t * g * finGL E a k) = φ.1 (g * finGL E a k)
      rw [mul_assoc, h2]
    · exact (right_translate_toL2 h3 _) ▸ hS.2 _ _ h4
  | cpt k =>
    refine ⟨isCuspForm_cpt k h1, fun t g => ?_, h3.mul_right (infGL E a (Unitary.toUnits k)), ?_⟩
    · change φ.1 (splitCentre E a t * g * infGL E a (Unitary.toUnits k)) = φ.1 (g * infGL E a (Unitary.toUnits k))
      rw [mul_assoc, h2]
    · exact (right_translate_toL2 h3 _) ▸ hS.2 _ _ h4
  | lie X =>
    letI : MeasurableSpace (AutomorphicForm.archGroup E a) := borel _
    haveI : BorelSpace (AutomorphicForm.archGroup E a) := ⟨rfl⟩
    obtain ⟨D, hD, hDc, hrep⟩ := GlobalTheory.T.lie_derivative_convolution_kernel E a (Measure.haar : Measure (AutomorphicForm.archGroup E a)) φ h1.1 X
    have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ h1.1.level
    obtain ⟨h', hW⟩ := GlobalTheory.T.l2_convolution_locally_compact_mem (latticeGL E a) μ (Measure.haar : Measure (AutomorphicForm.archGroup E a))
      (AutomorphicForm.infEmb E a) AutomorphicForm.continuous_infEmb D hD hDc φ.1 (lie E a X φ).1 hc h3 hrep
    refine ⟨⟨⟨fun γ g => lieD_left X (h1.1.left γ) g, ?_, GlobalTheory.T.finiteDimensional_span_compact_orbit_lieDerivative E a X φ h1.1.kfin,
      GlobalTheory.CuspStab.zfin_of_comm _ (fun z hz => GlobalTheory.T.mem_zalg_commute_lie_action E a X z hz) h1.1.zfin,
      GlobalTheory.T.moderate_growth_convolution_integral E a _ φ.1 _ hc h1.1.growth D hD hDc hrep⟩, GlobalTheory.T.isCuspidal_lieAction_of_isCuspForm E a X φ h1⟩,
      fun t g => lieD_left X (h2 t) g, h', hW H hS h4⟩
    exact GlobalTheory.CuspStab.level_of_le h1.1.level fun k hk => by
      change finRep E a k (lie E a X φ) = lie E a X φ
      change (rt E a (finGL E a k) * lie E a X) φ = _
      rw [← lie_rt_fin, Module.End.mul_apply]
      exact congrArg (lie E a X) hk

end GlobalTheory.CompanionTheory.StableMod
