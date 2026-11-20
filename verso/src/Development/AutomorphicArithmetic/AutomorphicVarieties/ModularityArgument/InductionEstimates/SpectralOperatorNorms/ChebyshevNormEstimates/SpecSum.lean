import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

/- English proof (translation)
Establish `hpos : a.IsPositive` using `(ContinuousLinearMap.nonneg_iff_isPositive a).1 ha`. Establish `hsym : (a : Eu d →ₗ[ℂ] Eu d).IsSymmetric` using `hpos.isSymmetric`. Establish `htop : (⨆ μ : ℂ, Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) μ) = ⊤` using `Submodule.orthogonal_eq_bot_iff.1 hsym.orthogonalComplement_iSup_eigenspaces_eq_bot`. Establish `hw : w ∈ (⨆ μ : ℂ, Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) μ)` using `htop ▸ Submodule.mem_top`. Proceed by induction on `hw using Submodule.iSup_induction' with`.

Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv => simp only [map_add, hu, hv, smul_add, Finset.sum_add_distrib]`. Consider the case `mem μ v hv`. Distinguish the cases in `h0 : v = 0`. Substitute `h0` using the available equality.

Simplify using the standard rewrite rules. Establish `hav : a v = μ • v` using `Module.End.mem_eigenspace_iff.1 hv`. Establish `hev : Module.End.HasEigenvalue (a : Eu d →ₗ[ℂ] Eu d) μ` using `Module.End.hasEigenvalue_of_hasEigenvector ⟨hv, h0⟩`. Establish `hre : (starRingEnd ℂ) μ = μ` using `hsym.conj_eigenvalue_eq_self hev`. Take `⟨r, rfl⟩ : ∃ r : ℝ, μ = r` from `⟨μ.re, (Complex.conj_eq_iff_re.1 hre).symm⟩`.

Establish `hr : 0 ≤ r`. Establish `h1` using `hpos.re_inner_nonneg_right v`. Rewrite `h1` using `[hav, inner_smul_right, inner_self_eq_norm_sq_to_K]`. Establish `h2 : 0 < ‖v‖ ^ 2` using `by positivity`. Establish `h3 : RCLike.re ((r : ℂ) * ((‖v‖ : ℂ)) ^ 2) = r * ‖v‖ ^ 2`.

Rewrite using `[← Complex.ofReal_pow, ← Complex.ofReal_mul]`. Simplify using `only [RCLike.re_to_complex, Complex.ofReal_re]`. Establish `h4 : 0 ≤ r * ‖v‖ ^ 2` using `by rw [← h3]; exact h1`. Conclude with `nonneg_of_mul_nonneg_left h4 h2`. Establish `hne : ∀ x : ℝ, x ≠ r → eigP a x v = 0`.

Introduce `x hx`. Unfold `eigP`. Rewrite using `[Submodule.starProjection_apply_eq_zero_iff]`. Introduce `u hu`. Establish `hx' : (x : ℂ) ≠ r` using `by exact_mod_cast hx`.

Conclude with `hsym.orthogonalFamily_eigenspaces hx' ⟨u, hu⟩ ⟨v, hv⟩`. Establish `heq : eigP a r v = v` using `Submodule.starProjection_eq_self_iff.2 hv`. Break down `hr.eq_or_lt with h | h` into its components or cases. Establish `h1 : a (Y v) = Y (a v)` using `congrArg (fun T : Eu d →L[ℂ] Eu d => T v) hc.eq`. Rewrite using `[h1, hav, ← h]`.

Simplify using `only [Complex.ofReal_zero, zero_smul, map_zero]`. Use `(Finset.sum_eq_zero fun x hx => ?_).symm` and prove the remaining obligations. Rewrite using `[hne x (h ▸ ((hsp x).1 hx).1.ne'), smul_zero]`. Establish `hm : r ∈ sp` using `(hsp r).2 ⟨h, hev⟩`. Rewrite using `[Finset.sum_eq_single_of_mem r hm fun x _ hx => by rw [hne x hx, smul_zero], heq, hY r h v hv, map_smul, hav, smul_smul, mul_comm]`.
-/
private theorem specSum_op {d : ℕ} (a Y : Eu d →L[ℂ] Eu d) (y : ℝ → ℂ) (sp : Finset ℝ) (ha : 0 ≤ a) (hc : Commute a Y)
    (hsp : ∀ x, x ∈ sp ↔ 0 < x ∧ Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) (x : ℂ) ≠ ⊥)
    (hY : ∀ x : ℝ, 0 < x → ∀ v ∈ Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) (x : ℂ), Y v = y x • v) (w : Eu d) :
    a (Y w) = ∑ x ∈ sp, ((x : ℂ) * y x) • eigP a x w := by
  have hpos : a.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive a).1 ha
  have hsym : (a : Eu d →ₗ[ℂ] Eu d).IsSymmetric := hpos.isSymmetric
  have htop : (⨆ μ : ℂ, Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) μ) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.1 hsym.orthogonalComplement_iSup_eigenspaces_eq_bot
  have hw : w ∈ (⨆ μ : ℂ, Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) μ) := htop ▸ Submodule.mem_top
  induction hw using Submodule.iSup_induction' with
  | zero => simp
  | add u v _ _ hu hv => simp only [map_add, hu, hv, smul_add, Finset.sum_add_distrib]
  | mem μ v hv =>
    by_cases h0 : v = 0
    · subst h0; simp
    have hav : a v = μ • v := Module.End.mem_eigenspace_iff.1 hv
    have hev : Module.End.HasEigenvalue (a : Eu d →ₗ[ℂ] Eu d) μ :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨hv, h0⟩
    have hre : (starRingEnd ℂ) μ = μ := hsym.conj_eigenvalue_eq_self hev
    obtain ⟨r, rfl⟩ : ∃ r : ℝ, μ = r := ⟨μ.re, (Complex.conj_eq_iff_re.1 hre).symm⟩
    have hr : 0 ≤ r := by
      have h1 := hpos.re_inner_nonneg_right v
      rw [hav, inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
      have h2 : 0 < ‖v‖ ^ 2 := by positivity
      have h3 : RCLike.re ((r : ℂ) * ((‖v‖ : ℂ)) ^ 2) = r * ‖v‖ ^ 2 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]; simp only [RCLike.re_to_complex, Complex.ofReal_re]
      have h4 : 0 ≤ r * ‖v‖ ^ 2 := by rw [← h3]; exact h1
      exact nonneg_of_mul_nonneg_left h4 h2
    have hne : ∀ x : ℝ, x ≠ r → eigP a x v = 0 := by
      intro x hx
      unfold eigP
      rw [Submodule.starProjection_apply_eq_zero_iff]
      intro u hu
      have hx' : (x : ℂ) ≠ r := by exact_mod_cast hx
      exact hsym.orthogonalFamily_eigenspaces hx' ⟨u, hu⟩ ⟨v, hv⟩
    have heq : eigP a r v = v := Submodule.starProjection_eq_self_iff.2 hv
    rcases hr.eq_or_lt with h | h
    · have h1 : a (Y v) = Y (a v) := congrArg (fun T : Eu d →L[ℂ] Eu d => T v) hc.eq
      rw [h1, hav, ← h]
      simp only [Complex.ofReal_zero, zero_smul, map_zero]
      refine (Finset.sum_eq_zero fun x hx => ?_).symm
      rw [hne x (h ▸ ((hsp x).1 hx).1.ne'), smul_zero]
    · have hm : r ∈ sp := (hsp r).2 ⟨h, hev⟩
      rw [Finset.sum_eq_single_of_mem r hm fun x _ hx => by rw [hne x hx, smul_zero], heq, hY r h v hv, map_smul, hav,
        smul_smul, mul_comm]

/- English proof (translation)
Introduce `d d' a Y Z N s y sp ha hc hsp hY`. Establish `key : (N ∘ₗ ((a ∘L Y ∘L Z : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ s) = ∑ x ∈ sp, ((x : ℂ) * y x) • (N ∘ₗ ((eigP a x ∘L Z : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ s)`. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.sum_apply]`. Express the relevant statement in the definitionally equal form `N (a (Y (Z (s w)))) = ∑ x ∈ sp, ((x : ℂ) * y x) • N (eigP a x (Z (s w)))`.

Rewrite using `[specSum_op a Y y sp ha hc hsp hY, map_sum]`. Simplify using `only [map_smul]`. Rewrite using `[key, map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.specSum :
    ∀ {d d' : ℕ} (a Y Z : Eu d' →L[ℂ] Eu d') (N : Eu d' →ₗ[ℂ] Eu d) (s : Eu d →ₗ[ℂ] Eu d') (y : ℝ → ℂ) (sp : Finset ℝ), 0 ≤ a → Commute a Y →
      (∀ x, x ∈ sp ↔ 0 < x ∧ Module.End.eigenspace (a : Eu d' →ₗ[ℂ] Eu d') (x : ℂ) ≠ ⊥) →
      (∀ x : ℝ, 0 < x → ∀ v ∈ Module.End.eigenspace (a : Eu d' →ₗ[ℂ] Eu d') (x : ℂ), Y v = y x • v) →
      LinearMap.trace ℂ (Eu d) (N ∘ₗ ((a ∘L Y ∘L Z : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ s) =
        ∑ x ∈ sp, x * y x * LinearMap.trace ℂ (Eu d) (N ∘ₗ ((eigP a x ∘L Z : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ s) := by
  intro d d' a Y Z N s y sp ha hc hsp hY
  have key : (N ∘ₗ ((a ∘L Y ∘L Z : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ s) =
      ∑ x ∈ sp, ((x : ℂ) * y x) • (N ∘ₗ ((eigP a x ∘L Z : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ s) := by
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.sum_apply]
    change N (a (Y (Z (s w)))) = ∑ x ∈ sp, ((x : ℂ) * y x) • N (eigP a x (Z (s w)))
    rw [specSum_op a Y y sp ha hc hsp hY, map_sum]
    simp only [map_smul]
  rw [key, map_sum]
  simp only [map_smul, smul_eq_mul]
