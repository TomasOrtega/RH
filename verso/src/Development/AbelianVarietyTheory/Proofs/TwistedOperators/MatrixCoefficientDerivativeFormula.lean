import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit
open scoped InnerProductSpace

noncomputable section

open Matrix

namespace GlobalTheory.MatCoefDeriv

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Establish `hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0` using `hX`. Establish `hJJ` using `GlobalTheory.GKLie.Jm_mul_self ε`. Establish `hJinv : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε` using `Matrix.inv_eq_right_inv hJJ`. Establish `hu : IsUnit (Formalism.REAL.Jm ε)` using `⟨⟨_, _, hJJ, hJJ⟩, rfl⟩`. Establish `h1 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X)` using `eq_neg_of_add_eq_zero_left hX'`.

Establish `hXh : Xᴴ = Formalism.REAL.Jm ε * (-X) * (Formalism.REAL.Jm ε)⁻¹`. Rewrite using `[hJinv]`. Combine the equalities or inequalities in the displayed calculation. Establish `hc : ((t : ℂ) • X)ᴴ = Formalism.REAL.Jm ε * (-((t : ℂ) • X)) * (Formalism.REAL.Jm ε)⁻¹`. Rewrite using `[conjTranspose_smul, hXh, Complex.star_def, Complex.conj_ofReal]`.

Simplify using `[smul_neg, mul_smul_comm, smul_mul_assoc]`. Unfold `Formalism.REAL.inUJ`. Rewrite using `[← Matrix.exp_conjTranspose, hc, Matrix.exp_conj _ _ hu, hJinv]`. Establish `hcomm : Commute (-((t : ℂ) • X)) ((t : ℂ) • X)` using `(Commute.refl _).neg_left`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_assoc (Formalism.REAL.Jm ε * _) (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJJ, mul_one, mul_assoc]`. Use `_ = Formalism.REAL.Jm ε := by`. Rewrite using `[← Matrix.exp_add_of_commute _ _ hcomm, neg_add_cancel, NormedSpace.exp_zero, mul_one]`.
-/
theorem exp_inUJ {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ GlobalTheory.SmoothGlob.lieSet ε) (t : ℝ) :
    Formalism.REAL.inUJ ε (NormedSpace.exp ((t : ℂ) • X)) := by
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have hJJ := GlobalTheory.GKLie.Jm_mul_self ε
  have hJinv : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_right_inv hJJ
  have hu : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨_, _, hJJ, hJJ⟩, rfl⟩
  have h1 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX'
  have hXh : Xᴴ = Formalism.REAL.Jm ε * (-X) * (Formalism.REAL.Jm ε)⁻¹ := by
    rw [hJinv]
    calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [mul_assoc, hJJ, mul_one]
      _ = _ := by rw [h1, mul_neg, neg_mul]
  have hc : ((t : ℂ) • X)ᴴ = Formalism.REAL.Jm ε * (-((t : ℂ) • X)) * (Formalism.REAL.Jm ε)⁻¹ := by
    rw [conjTranspose_smul, hXh, Complex.star_def, Complex.conj_ofReal]
    simp [smul_neg, mul_smul_comm, smul_mul_assoc]
  unfold Formalism.REAL.inUJ
  rw [← Matrix.exp_conjTranspose, hc, Matrix.exp_conj _ _ hu, hJinv]
  have hcomm : Commute (-((t : ℂ) • X)) ((t : ℂ) • X) := (Commute.refl _).neg_left
  calc Formalism.REAL.Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε *
        NormedSpace.exp ((t : ℂ) • X)
      = Formalism.REAL.Jm ε * (NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X)) := by
        rw [mul_assoc (Formalism.REAL.Jm ε * _) (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJJ, mul_one, mul_assoc]
    _ = Formalism.REAL.Jm ε := by
        rw [← Matrix.exp_add_of_commute _ _ hcomm, neg_add_cancel, NormedSpace.exp_zero, mul_one]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Use `set γ : ℝ → H := fun t => ρ (NormedSpace.exp ((t : ℂ) • X)) u with hγ`. Set `L : H →L[ℝ] ℂ` to `((innerSL ℂ w).comp (ρ g)).restrictScalars ℝ`. Establish `hfun : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) = fun t => L (γ t)`. Use function extensionality and compare the values at `t`. Establish `he` using `exp_inUJ hX t`.

Rewrite using `[hf _ (by`. Unfold `Formalism.REAL.inUJ at hg he ⊢`. Rewrite using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hρ.2 g hg _ he]`.

Both sides reduce to the same expression. Establish `hdiff : DifferentiableAt ℝ γ 0`. Establish `h` using `GlobalTheory.GKLie.differentiableAt_orbit hu hX`. Establish `e : γ = fun t : ℝ => ρ (NormedSpace.exp (t • X)) u`. Use function extensionality and compare the values at `t`.

Simplify using `only [hγ, Complex.coe_smul]`. Rewrite using `[e]`. Conclude with `h`. Unfold `Formalism.REAL.Rd`. Rewrite using `[hfun]`.

Use `show deriv (⇑L ∘ γ) 0 = _`. Rewrite using `[(L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hdiff.hasDerivAt).deriv]`. Both sides reduce to the same expression.
-/
theorem Rd_coef {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hρ : Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ)
    {u : H} (hu : Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) ρ u) (w : H)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : ∀ g, Formalism.REAL.inUJ ε g → f g = ⟪w, ρ g u⟫_ℂ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ GlobalTheory.SmoothGlob.lieSet ε)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Rd X f g = ⟪w, ρ g (PI.PhMeasCore.dsig ρ X u)⟫_ℂ := by
  set γ : ℝ → H := fun t => ρ (NormedSpace.exp ((t : ℂ) • X)) u with hγ
  let L : H →L[ℝ] ℂ := ((innerSL ℂ w).comp (ρ g)).restrictScalars ℝ
  have hfun : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) = fun t => L (γ t) := by
    funext t
    have he := exp_inUJ hX t
    rw [hf _ (by
      unfold Formalism.REAL.inUJ at hg he ⊢
      rw [conjTranspose_mul]
      calc _ = (NormedSpace.exp ((t : ℂ) • X))ᴴ * (gᴴ * Formalism.REAL.Jm ε * g) *
            NormedSpace.exp ((t : ℂ) • X) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hg, he])]
    rw [hρ.2 g hg _ he]
    rfl
  have hdiff : DifferentiableAt ℝ γ 0 := by
    have h := GlobalTheory.GKLie.differentiableAt_orbit hu hX
    have e : γ = fun t : ℝ => ρ (NormedSpace.exp (t • X)) u := by
      funext t; simp only [hγ, Complex.coe_smul]
    rw [e]; exact h
  unfold Formalism.REAL.Rd
  rw [hfun]
  show deriv (⇑L ∘ γ) 0 = _
  rw [(L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hdiff.hasDerivAt).deriv]
  rfl

/- English proof (translation)
Simplify using `[Formalism.REAL.cpart1, PI.DSInfCharCap.thetaJ, sub_eq_add_neg]`.
-/
theorem cpart1_eq (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.cpart1 ε Z = (1 / 2 : ℂ) • (Z + PI.DSInfCharCap.thetaJ ε Z) := by
  simp [Formalism.REAL.cpart1, PI.DSInfCharCap.thetaJ, sub_eq_add_neg]

/- English proof (translation)
Simplify using `[Formalism.REAL.cpart2, PI.DSInfCharCap.thetaJ, sub_eq_add_neg]`.
-/
theorem cpart2_eq (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.cpart2 ε Z = (1 / (2 * Complex.I)) • (Z - PI.DSInfCharCap.thetaJ ε Z) := by
  simp [Formalism.REAL.cpart2, PI.DSInfCharCap.thetaJ, sub_eq_add_neg]

/- English proof (translation)
Introduce `n ε H _ _ ρ hρ u hu w f hf a b g hg`. Establish `h1` using `Rd_coef hρ hu w hf (GlobalTheory.GKLie.cre_mem (ε := ε) (Matrix.single a b 1)) hg`. Establish `h2` using `Rd_coef hρ hu w hf (GlobalTheory.GKLie.cim_mem (ε := ε) (Matrix.single a b 1)) hg`. Unfold `Formalism.REAL.Eab Formalism.REAL.Ec PI.DSInfCharCap.dsigC`. Rewrite using `[cpart1_eq, cpart2_eq]`.

Unfold `GlobalTheory.GKLie.cre at h1`. Unfold `GlobalTheory.GKLie.cim at h2`. Rewrite using `[h1, h2, map_add, map_smul, inner_add_right, inner_smul_right]`.
-/
theorem Eab_coef : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ →
    ∀ u : H, Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) ρ u → ∀ (w : H) (f : Matrix (Fin n) (Fin n) ℂ → ℂ),
    (∀ g, Formalism.REAL.inUJ ε g → f g = ⟪w, ρ g u⟫_ℂ) → ∀ (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ),
    Formalism.REAL.inUJ ε g → Formalism.REAL.Eab ε a b f g =
      ⟪w, ρ g (PI.DSInfCharCap.dsigC ε ρ (Matrix.single a b 1) u)⟫_ℂ := by
  intro n ε H _ _ ρ hρ u hu w f hf a b g hg
  have h1 := Rd_coef hρ hu w hf (GlobalTheory.GKLie.cre_mem (ε := ε) (Matrix.single a b 1)) hg
  have h2 := Rd_coef hρ hu w hf (GlobalTheory.GKLie.cim_mem (ε := ε) (Matrix.single a b 1)) hg
  unfold Formalism.REAL.Eab Formalism.REAL.Ec PI.DSInfCharCap.dsigC
  rw [cpart1_eq, cpart2_eq]
  unfold GlobalTheory.GKLie.cre at h1
  unfold GlobalTheory.GKLie.cim at h2
  rw [h1, h2, map_add, map_smul, inner_add_right, inner_smul_right]

end GlobalTheory.MatCoefDeriv
