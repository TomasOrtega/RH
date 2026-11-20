import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelCext
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OneParam

noncomputable section

open Matrix Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section ExpL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma mder_exp_cont (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) :=
  NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)

end ExpL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Classical in

def kcurve (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : ℝ → KG ε :=
  if h : inK ε X then Classical.choose (exists_curve ε h) else fun _ => 1

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
lemma kcurve_eq (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    kcurve ε X = onepCurve ε hX := by
  unfold kcurve
  rw [dif_pos hX]
  funext t
  apply onep_KG_ext
  rw [Classical.choose_spec (exists_curve ε hX) t, toMK_onepCurve]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
lemma continuous_onepCurve (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    Continuous (onepCurve ε hX) := by
  apply continuous_induced_rng.2
  apply (isClosedEmbedding_toM ε).isInducing.continuous_iff.2
  have : ((fun g : UJ ε => toM g) ∘ Subtype.val ∘ onepCurve ε hX) =
      fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) := by
    funext t
    exact toMK_onepCurve ε hX t
  rw [this]
  exact mder_exp_cont X

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem kcurve_spec (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    Continuous (kcurve ε X) ∧ (∀ t, toMK (kcurve ε X t) = NormedSpace.exp ((t : ℂ) • X)) ∧
      ∀ s t, kcurve ε X (s + t) = kcurve ε X s * kcurve ε X t := by
  rw [kcurve_eq ε hX]
  refine ⟨continuous_onepCurve ε hX, toMK_onepCurve ε hX, ?_⟩
  intro s u
  apply onep_KG_ext
  show toMK (onepCurve ε hX (s + u)) = toMK (onepCurve ε hX s) * toMK (onepCurve ε hX u)
  rw [toMK_onepCurve, toMK_onepCurve, toMK_onepCurve,
    show (((s + u : ℝ) : ℂ) • X) = (s : ℂ) • X + (u : ℂ) • X by push_cast; exact add_smul _ _ _]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem curve_eq_kcurve (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) : γ = kcurve ε X := by
  funext t
  apply onep_KG_ext
  rw [hγ, (kcurve_spec ε hX).2.1]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify by unfolding definitions.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem differentiableAt_oneParam {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (φ : ℝ → (V →L[ℂ] V)) (hc : Continuous φ) (h0 : φ 0 = 1) (hadd : ∀ s t, φ (s + t) = φ s * φ t) :
    DifferentiableAt ℝ φ 0 := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  set Φ : ℝ → (V →L[ℂ] V) := fun x => ∫ s in (0:ℝ)..x, φ s with hΦ
  have hΦd : ∀ x, HasDerivAt Φ (φ x) x := fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hslope : Tendsto (slope Φ 0) (𝓝[≠] 0) (𝓝 (φ 0)) := hasDerivAt_iff_tendsto_slope.1 (hΦd 0)
  rw [h0] at hslope
  have hev : ∀ᶠ h in 𝓝[≠] (0:ℝ), IsUnit (slope Φ 0 h) := hslope (Units.isOpen.mem_nhds isUnit_one)
  obtain ⟨h, hh, hne⟩ := (hev.and self_mem_nhdsWithin).exists
  have hΦ0 : Φ 0 = 0 := by simp [hΦ]
  rw [slope_def_module, hΦ0, sub_zero, sub_zero] at hh
  obtain ⟨u, hu⟩ := hh
  have key : ∀ t, φ t * Φ h = Φ (t + h) - Φ t := by
    intro t
    have h1 := (ContinuousLinearMap.mul ℝ (V →L[ℂ] V) (φ t)).intervalIntegral_comp_comm
      (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 h)
    simp only [ContinuousLinearMap.mul_apply'] at h1
    rw [hΦ]
    dsimp only
    rw [← h1]
    simp_rw [← hadd]
    rw [intervalIntegral.integral_comp_add_left (fun x => φ x) t, add_zero,
      intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hrep : φ = fun t => h⁻¹ • (Φ (t + h) - Φ t) * ((u⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V) := by
    funext t
    rw [← key, ← mul_smul_comm, ← hu, Units.mul_inv_cancel_right]
  have hD : Differentiable ℝ Φ := fun x => (hΦd x).differentiableAt
  rw [hrep]
  exact ((((hD.comp (differentiable_id.add_const h)) 0).sub (hD 0)).const_smul h⁻¹).mul_const _

section Op

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

def derOp (ε : Fin n → Bool) (τ : KG ε →* unitary (V →L[ℂ] V)) (X : Matrix (Fin n) (Fin n) ℂ) : V →L[ℂ] V :=
  deriv (fun t : ℝ => ((τ (kcurve ε X t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) 0

/- English proof (translation)
Establish an intermediate fact. Substitute using the available equality. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem derOp_hasDeriv [FiniteDimensional ℂ V] (ε : Fin n → Bool) (τ : KG ε →* unitary (V →L[ℂ] V))
    (hcont : Continuous τ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) :
    HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (derOp ε τ X) 0 := by
  have hγk := curve_eq_kcurve ε hX γ hγ
  subst hγk
  obtain ⟨hc, -, hmul⟩ := kcurve_spec ε hX
  set φ : ℝ → V →L[ℂ] V := fun t => ((τ (kcurve ε X t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) with hφ
  have h0k : kcurve ε X 0 = 1 := by
    apply onep_KG_ext
    rw [(kcurve_spec ε hX).2.1]
    show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = (1 : Matrix (Fin n) (Fin n) ℂ)
    simp
  have hφc : Continuous φ := continuous_subtype_val.comp (hcont.comp hc)
  have hφ0 : φ 0 = 1 := by
    simp only [hφ, h0k, map_one]
    rfl
  have hφadd : ∀ s t, φ (s + t) = φ s * φ t := by
    intro s t
    simp only [hφ, hmul, map_mul]
    rfl
  exact (differentiableAt_oneParam φ hφc hφ0 hφadd).hasDerivAt

end Op

def rdc (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (f : KG ε → ℂ) (x : KG ε) : ℂ :=
  deriv (fun t : ℝ => f (x * kcurve ε (cpart1 ε (bdPart ε Z)) t)) 0 +
    Complex.I * deriv (fun t : ℝ => f (x * kcurve ε (cpart2 ε (bdPart ε Z)) t)) 0

end ReciprocityTheory.ChartRestriction.DS.HW
