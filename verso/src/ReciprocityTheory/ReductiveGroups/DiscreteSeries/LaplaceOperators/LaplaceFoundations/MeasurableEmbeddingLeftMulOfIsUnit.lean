import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

variable {k r : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/- English proof (translation)
Take `⟨u, rfl⟩` from `hg`. Set `e : Formalism.QuantumDeterminants.Mt k r ≃ₜ Formalism.QuantumDeterminants.Mt k r` to `{ toFun := Formalism.QuantumDeterminants.lmulM (u : Matrix _ _ ℂ) invFun := Formalism.QuantumDeterminants.lmulM ((u⁻¹ : (Matrix _ _ ℂ)ˣ) : Matrix _ _ ℂ) left_inv := fun x => by`. Express the relevant statement in the definitionally equal form `((u⁻¹ : (Matrix _ _ ℂ)ˣ) : Matrix _ _ ℂ) * ((u : Matrix _ _ ℂ) * Matrix.of x) = Matrix.of x`. Rewrite using `[← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]`. Use `right_inv := fun x => by`.

Express the relevant statement in the definitionally equal form `(u : Matrix _ _ ℂ) * (((u⁻¹ : (Matrix _ _ ℂ)ˣ) : Matrix _ _ ℂ) * Matrix.of x) = Matrix.of x`. Rewrite using `[← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]`. Use `continuous_toFun := by`. Unfold `Formalism.QuantumDeterminants.lmulM`. Conclude with `continuous_const.matrix_mul continuous_id`.

Use `continuous_invFun := by`. Unfold `Formalism.QuantumDeterminants.lmulM`. Conclude with `continuous_const.matrix_mul continuous_id }`. Conclude with `e.toMeasurableEquiv.measurableEmbedding`.
-/
theorem measurableEmbedding_leftMul_of_isUnit {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : IsUnit g) :
    MeasurableEmbedding (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) g) := by
  obtain ⟨u, rfl⟩ := hg
  let e : Formalism.QuantumDeterminants.Mt k r ≃ₜ Formalism.QuantumDeterminants.Mt k r :=
    { toFun := Formalism.QuantumDeterminants.lmulM (u : Matrix _ _ ℂ)
      invFun := Formalism.QuantumDeterminants.lmulM ((u⁻¹ : (Matrix _ _ ℂ)ˣ) : Matrix _ _ ℂ)
      left_inv := fun x => by
        change ((u⁻¹ : (Matrix _ _ ℂ)ˣ) : Matrix _ _ ℂ) * ((u : Matrix _ _ ℂ) * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun x => by
        change (u : Matrix _ _ ℂ) * (((u⁻¹ : (Matrix _ _ ℂ)ˣ) : Matrix _ _ ℂ) * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      continuous_toFun := by
        unfold Formalism.QuantumDeterminants.lmulM
        exact continuous_const.matrix_mul continuous_id
      continuous_invFun := by
        unfold Formalism.QuantumDeterminants.lmulM
        exact continuous_const.matrix_mul continuous_id }
  exact e.toMeasurableEquiv.measurableEmbedding

/- English proof (translation)
Set `L : V →ₗᵢ[ℂ] V` to `{ toLinearMap := (A : V →ₗ[ℂ] V), norm_map' := hA }`. Use extensionality with `v`. Use `ext_inner_left ℂ fun y => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]`. Conclude with `L.inner_map_map y v`.
-/
theorem adjoint_comp_self_of_isometry (A : V →L[ℂ] V) (hA : ∀ v, ‖A v‖ = ‖v‖) :
    (ContinuousLinearMap.adjoint A).comp A = 1 := by
  let L : V →ₗᵢ[ℂ] V := { toLinearMap := (A : V →ₗ[ℂ] V), norm_map' := hA }
  ext v
  refine ext_inner_left ℂ fun y => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  exact L.inner_map_map y v

/- English proof (translation)
The claim follows from `ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [hA, one_mul]`.
-/
theorem opNorm_le_one_of_isometry_alt (A : V →L[ℂ] V) (hA : ∀ v, ‖A v‖ = ‖v‖) : ‖A‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [hA, one_mul]

/- English proof (translation)
Use `set A : V →L[ℂ] V := (innerSL ℂ u').smulRight u with hA`. Use `set F : Formalism.QuantumDeterminants.Mt k r → (V →L[ℂ] V) := fun x => (σ (Matrix.of x)).comp (A.comp (ContinuousLinearMap.adjoint (σ (Matrix.of x)))) with hF`. Establish `hae : ∀ᵐ x ∂μ, Matrix.of x ∈ G`. Rewrite using `[ae_iff]`. Simplify using `using hG0`.

Establish `hFm : AEStronglyMeasurable F μ`. Establish `hc : Continuous (fun S : V →L[ℂ] V => S.comp (A.comp (ContinuousLinearMap.adjoint S)))` using `continuous_id.clm_comp (continuous_const.clm_comp (ContinuousLinearMap.adjoint : (V →L[ℂ] V) ≃ₗᵢ⋆[ℂ] (V →L[ℂ] V)).continuous)`. Conclude with `hc.comp_aestronglyMeasurable hmeas`. Establish `hFb : ∀ᵐ x ∂μ, ‖F x‖ ≤ ‖A‖` using `hae.mono fun x hx => by`. Establish `h1` using `opNorm_le_one_of_isometry_alt _ (hunit _ hx)`.

Establish `h2 : ‖ContinuousLinearMap.adjoint (σ (Matrix.of x))‖ ≤ 1`. Rewrite using `[LinearIsometryEquiv.norm_map]`. Conclude with `h1`. Combine the equalities or inequalities in the displayed calculation. Establish `hFi : Integrable F μ` using `Integrable.of_bound hFm ‖A‖ hFb`.

Establish `hFzi : ∀ z, Integrable (fun x => F x z) μ` using `fun z => hFi.apply_continuousLinearMap z`. Use `set B : V →L[ℂ] V := ∫ x, F x ∂μ with hB`. Establish `happ : ∀ z, B z = ∫ x, F x z ∂μ` using `fun z => ContinuousLinearMap.integral_apply hFi z`. Apply the tactic sequence `have hadj : ∀ g ∈ G, (ContinuousLinearMap.adjoint (σ g)).comp (σ g) = 1 := fun g hg => adjoint_comp_self_of_isometry _ (hunit g hg)`. Establish `hcomm : ∀ g ∈ G, ∀ z, σ g (B z) = B (σ g z)`.

Introduce `g hg z`. Rewrite using `[happ, happ, ← ContinuousLinearMap.integral_comp_comm _ (hFzi z)]`. Establish `key : ∀ᵐ x ∂μ, σ g (F x z) = F (Formalism.QuantumDeterminants.lmulM g x) (σ g z)` using `hae.mono fun x hx => by`. Establish `e : Matrix.of (Formalism.QuantumDeterminants.lmulM g x) = g * Matrix.of x` using `rfl`. Simplify using `only [hF, e, hmul g hg _ hx]`.

Rewrite using `[ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp]`. Simplify using `only [ContinuousLinearMap.comp_apply]`. Use `congrArg (fun T : V →L[ℂ] V => T z) (hadj g hg)` as an intermediate fact. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this`. Rewrite using `[this]`.

Rewrite using `[integral_congr_ae key]`. Use `conv_rhs => rw [← hinv g hg]`. Rewrite using `[(measurableEmbedding_leftMul_of_isUnit (hGu g hg)).integral_map]`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : ℂ, ∀ z, B z = c • z := by`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue (B : Module.End ℂ V)`.

Use `⟨c, fun z => ?_⟩` and prove the remaining obligations. Establish `hS : ∀ g ∈ G, ∀ v ∈ Module.End.eigenspace (B : Module.End ℂ V) c, σ g v ∈ Module.End.eigenspace (B : Module.End ℂ V) c`. Introduce `g hg v hv`. Rewrite `hv`, the goal using `[Module.End.mem_eigenspace_iff]`. Express the relevant statement in the definitionally equal form `B (σ g v) = c • σ g v`.

Rewrite using `[← hcomm g hg]`. Express the relevant statement in the definitionally equal form `σ g ((B : Module.End ℂ V) v) = c • σ g v`. Rewrite using `[hv, map_smul]`. Break down `hirr _ hS with h | h` into its components or cases. It suffices to derive a contradiction.

Take `⟨v, hv⟩` from `hc.exists_hasEigenvector`. Establish `hv1` using `hv.apply_eq_smul`. Establish `hv0` using `hv.2`. Establish `: v ∈ Module.End.eigenspace (B : Module.End ℂ V) c` using `Module.End.mem_eigenspace_iff.2 hv1`. Rewrite `this` using `[h, Submodule.mem_bot]`.

Conclude with `hv0 this`. Establish `: z ∈ Module.End.eigenspace (B : Module.End ℂ V) c` using `h ▸ Submodule.mem_top`. Conclude with `Module.End.mem_eigenspace_iff.1 this`. Establish `hd0 : (Module.finrank ℂ V : ℂ) ≠ 0`. Conclude with `(Module.finrank_pos (R := ℂ) (M := V)).ne'` after adjusting the coercions.

Establish `htr : c * (Module.finrank ℂ V : ℂ) = ⟪u', u⟫_ℂ`. Set `tr : (V →L[ℂ] V) →L[ℂ] ℂ` to `LinearMap.toContinuousLinearMap ((LinearMap.trace ℂ V).comp (ContinuousLinearMap.coeLM ℂ))`. Establish `htrv : ∀ T : V →L[ℂ] V, tr T = LinearMap.trace ℂ V (T : V →ₗ[ℂ] V)` using `fun T => rfl`. Establish `h1 : tr B = ∫ x, tr (F x) ∂μ` using `(ContinuousLinearMap.integral_comp_comm tr hFi).symm`. Establish `h2 : ∀ᵐ x ∂μ, tr (F x) = ⟪u', u⟫_ℂ` using `hae.mono fun x hx => by`.

Rewrite using `[htrv]`. Establish `e1 : ((F x : V →L[ℂ] V) : V →ₗ[ℂ] V) = ((σ (Matrix.of x)).comp A : V →ₗ[ℂ] V) ∘ₗ (ContinuousLinearMap.adjoint (σ (Matrix.of x)) : V →ₗ[ℂ] V)` using `rfl`. Rewrite using `[e1, LinearMap.trace_comp_comm']`. Establish `e2 : (ContinuousLinearMap.adjoint (σ (Matrix.of x)) : V →ₗ[ℂ] V) ∘ₗ ((σ (Matrix.of x)).comp A : V →ₗ[ℂ] V) = (A : V →ₗ[ℂ] V)`. Use `hadj _ hx` as an intermediate fact.

Use extensionality with `y`. Establish `h3` using `congrArg (fun T : V →L[ℂ] V => T (A y)) this`. Simplify using `using h3`. Rewrite using `[e2]`. Establish `e3 : (A : V →ₗ[ℂ] V) = ((innerSL ℂ u' : V →L[ℂ] ℂ) : V →ₗ[ℂ] ℂ).smulRight u`.

Use extensionality with `y`. Both sides reduce to the same expression. Rewrite using `[e3, LinearMap.trace_smulRight]`. Both sides reduce to the same expression. Establish `h3 : tr B = c * (Module.finrank ℂ V : ℂ)`.

Establish `eB : B = c • (1 : V →L[ℂ] V)` using `by ext z; simp [hc z]`. Rewrite using `[htrv, eB]`. Simplify using `[LinearMap.trace_one]`. Rewrite using `[← h3, h1, integral_congr_ae h2, integral_const]`. Simplify using the standard rewrite rules.

Establish `hfin : ⟪v', B v⟫_ℂ = ∫ x, ⟪v', σ (Matrix.of x) u⟫_ℂ * ⟪σ (Matrix.of x) u', v⟫_ℂ ∂μ`. Rewrite using `[happ, ← integral_inner (hFzi v)]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [hF, hA, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_smul, inner_smul_right, ContinuousLinearMap.adjoint_inner_right]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← hfin, hc, inner_smul_right]`. Establish `hc' : c = ⟪u', u⟫_ℂ / (Module.finrank ℂ V : ℂ)`. Rewrite using `[← htr]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hc']`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem schur_orthogonality_unitary_rep (G : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) [IsProbabilityMeasure μ]
    (hG0 : μ {x | Matrix.of x ∉ G} = 0) (hGu : ∀ g ∈ G, IsUnit g)
    (hinv : ∀ g ∈ G, μ.map (Formalism.QuantumDeterminants.lmulM g) = μ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (V →L[ℂ] V))
    (hmul : ∀ g ∈ G, ∀ h ∈ G, σ (g * h) = σ g * σ h) (hunit : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ V, (∀ g ∈ G, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hmeas : AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => σ (Matrix.of x)) μ) [Nontrivial V]
    (u u' v v' : V) :
    ∫ x, ⟪v', σ (Matrix.of x) u⟫_ℂ * ⟪σ (Matrix.of x) u', v⟫_ℂ ∂μ =
      ⟪v', v⟫_ℂ * ⟪u', u⟫_ℂ / (Module.finrank ℂ V : ℂ) := by
  classical
  set A : V →L[ℂ] V := (innerSL ℂ u').smulRight u with hA
  set F : Formalism.QuantumDeterminants.Mt k r → (V →L[ℂ] V) := fun x =>
    (σ (Matrix.of x)).comp (A.comp (ContinuousLinearMap.adjoint (σ (Matrix.of x)))) with hF
  have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ G := by
    rw [ae_iff]; simpa using hG0
  have hFm : AEStronglyMeasurable F μ := by
    have hc : Continuous (fun S : V →L[ℂ] V => S.comp (A.comp (ContinuousLinearMap.adjoint S))) :=
      continuous_id.clm_comp (continuous_const.clm_comp
        (ContinuousLinearMap.adjoint : (V →L[ℂ] V) ≃ₗᵢ⋆[ℂ] (V →L[ℂ] V)).continuous)
    exact hc.comp_aestronglyMeasurable hmeas
  have hFb : ∀ᵐ x ∂μ, ‖F x‖ ≤ ‖A‖ := hae.mono fun x hx => by
    have h1 := opNorm_le_one_of_isometry_alt _ (hunit _ hx)
    have h2 : ‖ContinuousLinearMap.adjoint (σ (Matrix.of x))‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]; exact h1
    calc ‖F x‖ ≤ ‖σ (Matrix.of x)‖ * (‖A‖ * ‖ContinuousLinearMap.adjoint (σ (Matrix.of x))‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖A‖ * 1) := by gcongr
      _ = ‖A‖ := by ring
  have hFi : Integrable F μ := Integrable.of_bound hFm ‖A‖ hFb
  have hFzi : ∀ z, Integrable (fun x => F x z) μ := fun z => hFi.apply_continuousLinearMap z
  set B : V →L[ℂ] V := ∫ x, F x ∂μ with hB
  have happ : ∀ z, B z = ∫ x, F x z ∂μ := fun z => ContinuousLinearMap.integral_apply hFi z
  have hadj : ∀ g ∈ G, (ContinuousLinearMap.adjoint (σ g)).comp (σ g) = 1 :=
    fun g hg => adjoint_comp_self_of_isometry _ (hunit g hg)
  have hcomm : ∀ g ∈ G, ∀ z, σ g (B z) = B (σ g z) := by
    intro g hg z
    rw [happ, happ, ← ContinuousLinearMap.integral_comp_comm _ (hFzi z)]
    have key : ∀ᵐ x ∂μ, σ g (F x z) = F (Formalism.QuantumDeterminants.lmulM g x) (σ g z) := hae.mono fun x hx => by
      have e : Matrix.of (Formalism.QuantumDeterminants.lmulM g x) = g * Matrix.of x := rfl
      simp only [hF, e, hmul g hg _ hx]
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp]
      simp only [ContinuousLinearMap.comp_apply]
      have := congrArg (fun T : V →L[ℂ] V => T z) (hadj g hg)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this
      rw [this]
    rw [integral_congr_ae key]
    conv_rhs => rw [← hinv g hg]
    rw [(measurableEmbedding_leftMul_of_isUnit (hGu g hg)).integral_map]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ z, B z = c • z := by
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (B : Module.End ℂ V)
    refine ⟨c, fun z => ?_⟩
    have hS : ∀ g ∈ G, ∀ v ∈ Module.End.eigenspace (B : Module.End ℂ V) c,
        σ g v ∈ Module.End.eigenspace (B : Module.End ℂ V) c := by
      intro g hg v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      change B (σ g v) = c • σ g v
      rw [← hcomm g hg]
      change σ g ((B : Module.End ℂ V) v) = c • σ g v
      rw [hv, map_smul]
    rcases hirr _ hS with h | h
    · exfalso
      obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      have hv1 := hv.apply_eq_smul
      have hv0 := hv.2
      have : v ∈ Module.End.eigenspace (B : Module.End ℂ V) c := Module.End.mem_eigenspace_iff.2 hv1
      rw [h, Submodule.mem_bot] at this
      exact hv0 this
    · have : z ∈ Module.End.eigenspace (B : Module.End ℂ V) c := h ▸ Submodule.mem_top
      exact Module.End.mem_eigenspace_iff.1 this
  have hd0 : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have htr : c * (Module.finrank ℂ V : ℂ) = ⟪u', u⟫_ℂ := by
    let tr : (V →L[ℂ] V) →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap ((LinearMap.trace ℂ V).comp (ContinuousLinearMap.coeLM ℂ))
    have htrv : ∀ T : V →L[ℂ] V, tr T = LinearMap.trace ℂ V (T : V →ₗ[ℂ] V) := fun T => rfl
    have h1 : tr B = ∫ x, tr (F x) ∂μ := (ContinuousLinearMap.integral_comp_comm tr hFi).symm
    have h2 : ∀ᵐ x ∂μ, tr (F x) = ⟪u', u⟫_ℂ := hae.mono fun x hx => by
      rw [htrv]
      have e1 : ((F x : V →L[ℂ] V) : V →ₗ[ℂ] V) =
          ((σ (Matrix.of x)).comp A : V →ₗ[ℂ] V) ∘ₗ
            (ContinuousLinearMap.adjoint (σ (Matrix.of x)) : V →ₗ[ℂ] V) := rfl
      rw [e1, LinearMap.trace_comp_comm']
      have e2 : (ContinuousLinearMap.adjoint (σ (Matrix.of x)) : V →ₗ[ℂ] V) ∘ₗ
          ((σ (Matrix.of x)).comp A : V →ₗ[ℂ] V) = (A : V →ₗ[ℂ] V) := by
        have := hadj _ hx
        ext y
        have h3 := congrArg (fun T : V →L[ℂ] V => T (A y)) this
        simpa using h3
      rw [e2]
      have e3 : (A : V →ₗ[ℂ] V) = ((innerSL ℂ u' : V →L[ℂ] ℂ) : V →ₗ[ℂ] ℂ).smulRight u := by
        ext y; rfl
      rw [e3, LinearMap.trace_smulRight]
      rfl
    have h3 : tr B = c * (Module.finrank ℂ V : ℂ) := by
      have eB : B = c • (1 : V →L[ℂ] V) := by ext z; simp [hc z]
      rw [htrv, eB]
      simp [LinearMap.trace_one]
    rw [← h3, h1, integral_congr_ae h2, integral_const]
    simp
  have hfin : ⟪v', B v⟫_ℂ = ∫ x, ⟪v', σ (Matrix.of x) u⟫_ℂ * ⟪σ (Matrix.of x) u', v⟫_ℂ ∂μ := by
    rw [happ, ← integral_inner (hFzi v)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hF, hA, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      map_smul, inner_smul_right, ContinuousLinearMap.adjoint_inner_right]
    ring
  rw [← hfin, hc, inner_smul_right]
  have hc' : c = ⟪u', u⟫_ℂ / (Module.finrank ℂ V : ℂ) := by
    rw [← htr]; field_simp
  rw [hc']
  ring

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
