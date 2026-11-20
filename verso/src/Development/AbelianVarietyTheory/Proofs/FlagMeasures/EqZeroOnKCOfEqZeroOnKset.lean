import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition

open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

namespace GlobalTheory.Dec.KCIdent

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder in

/- English proof (translation)
Establish `h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ yᴴ * y` using `star_mul_self_nonneg y`. Establish `hu : IsUnit (yᴴ * y)` using `hy.star.mul hy`. Establish `hsp : IsStrictlyPositive (yᴴ * y)` using `IsStrictlyPositive.iff_of_unital.mpr ⟨h0, hu⟩`. Use `⟨CFC.log (yᴴ * y), ?_, Commute.cfc_real hJ Real.log, CFC.exp_log (yᴴ * y) hsp⟩` and prove the remaining obligations. Conclude with `(IsSelfAdjoint.log : IsSelfAdjoint (CFC.log (yᴴ * y)))`.
-/
theorem exists_herm_log {n : ℕ} (y J : Matrix (Fin n) (Fin n) ℂ) (hy : IsUnit y)
    (hJ : Commute (yᴴ * y) J) :
    ∃ L : Matrix (Fin n) (Fin n) ℂ, Lᴴ = L ∧ Commute L J ∧ NormedSpace.exp L = yᴴ * y := by
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ yᴴ * y := star_mul_self_nonneg y
  have hu : IsUnit (yᴴ * y) := hy.star.mul hy
  have hsp : IsStrictlyPositive (yᴴ * y) := IsStrictlyPositive.iff_of_unital.mpr ⟨h0, hu⟩
  refine ⟨CFC.log (yᴴ * y), ?_, Commute.cfc_real hJ Real.log, CFC.exp_log (yᴴ * y) hsp⟩
  exact (IsSelfAdjoint.log : IsSelfAdjoint (CFC.log (yᴴ * y)))

/- English proof (translation)
Set `_ : NormedRing (Matrix (Fin n) (Fin n) ℂ)` to `Matrix.linftyOpNormedRing`. Set `_ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ)` to `Matrix.linftyOpNormedAlgebra`. Introduce `z`. Establish `hz : DifferentiableAt ℂ (fun w : ℂ => NormedSpace.exp (w • X)) z` using `(hasDerivAt_exp_smul_const (𝕂 := ℂ) X z).differentiableAt`. Conclude with `(LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).differentiableAt.comp z hz`.
-/
theorem differentiable_exp_entry {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    Differentiable ℂ (fun z : ℂ => NormedSpace.exp (z • X) i j) := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  intro z
  have hz : DifferentiableAt ℂ (fun w : ℂ => NormedSpace.exp (w • X)) z :=
    (hasDerivAt_exp_smul_const (𝕂 := ℂ) X z).differentiableAt
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).differentiableAt.comp z hz

/- English proof (translation)
Introduce `n ε E _ _ _ F hF hK y hy`. Unfold `GlobalTheory.Dec.KC at hy`. Take `⟨hyu, hyJ⟩` from `hy`. Establish `hJh : (Jm ε)ᴴ = Jm ε` using `Formalism.REAL.Jm_conjTranspose ε`. Establish `hyhJ : yᴴ * Jm ε = Jm ε * yᴴ`.

Establish `h` using `congrArg Matrix.conjTranspose hyJ`. Rewrite `h` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJh]`. Conclude with `h.symm`. Establish `hc : Commute (yᴴ * y) (Jm ε)` using `by show yᴴ * y * Jm ε = Jm ε * (yᴴ * y)`. Rewrite using `[mul_assoc, hyJ, ← mul_assoc, hyhJ, mul_assoc]`.

Take `⟨L, hLh, hLJ, hLe⟩` from `exists_herm_log y (Jm ε) hyu hc`. Take `⟨E', hE'⟩ : ∃ f : ℂ → Matrix (Fin n) (Fin n) ℂ, f = fun w => NormedSpace.exp (w • L)` from `⟨_, rfl⟩`. Establish `hmul : ∀ a b : ℂ, E' a * E' b = E' (a + b)`. Introduce `a b`. Simplify using `only [hE', add_smul]`.

Conclude with `(Matrix.exp_add_of_commute _ _ (((Commute.refl L).smul_left a).smul_right b)).symm`. Establish `hstar : ∀ w : ℂ, (E' w)ᴴ = E' (star w)`. Introduce `w`. Simplify using `only [hE']`. Rewrite using `[← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hLh]`.

Establish `hEJ : ∀ w : ℂ, E' w * Jm ε = Jm ε * E' w`. Introduce `w`. Simplify using `only [hE']`. Conclude with `(hLJ.smul_left w).exp_left.eq`. Establish `hE0 : E' 0 = 1` using `by simp [hE']`.

Establish `hEone : E' 1 = yᴴ * y`. Simplify using `only [hE', one_smul]`. Conclude with `hLe`. Establish `hEu : ∀ w : ℂ, IsUnit (E' w)`. Introduce `w`.

Simplify using `only [hE']`. Conclude with `Matrix.isUnit_exp _`. Take `⟨u, hu⟩ : ∃ u : Matrix (Fin n) (Fin n) ℂ, u = y * E' (-(1 / 2))` from `⟨_, rfl⟩`. Establish `hhalf : star (-(1 / 2 : ℂ)) = -(1 / 2)` using `by simp`. Establish `hu1 : uᴴ * u = 1`.

Rewrite using `[hu, Matrix.conjTranspose_mul, hstar, hhalf]`. Establish `e1 : E' (-(1 / 2)) * yᴴ * (y * E' (-(1 / 2))) = E' (-(1 / 2)) * (yᴴ * y) * E' (-(1 / 2))`. Simplify using `only [mul_assoc]`. Establish `e2 : (-(1 / 2 : ℂ) + 1 + -(1 / 2)) = 0` using `by ring`. Rewrite using `[e1, ← hEone, hmul, hmul, e2, hE0]`.

Establish `huJ : u * Jm ε = Jm ε * u`. Rewrite using `[hu, mul_assoc, hEJ, ← mul_assoc, hyJ, mul_assoc]`. Establish `huU : IsUnit u`. Rewrite using `[hu]`. Conclude with `hyu.mul (hEu _)`.

Establish `hKC : ∀ z : ℂ, u * E' z ∈ GlobalTheory.Dec.KC ε`. Introduce `z`. Unfold `GlobalTheory.Dec.KC`. Use `⟨huU.mul (hEu z), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, hEJ, ← mul_assoc, huJ, mul_assoc]`.

Establish `hzero : ∀ t : ℝ, F (u * E' ((t : ℂ) * Complex.I)) = 0`. Introduce `t`. Apply `hK` to reduce the goal to its premises. Unfold `Formalism.REAL.Kset`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, hstar]`. Establish `hsw : star ((t : ℂ) * Complex.I) + (t : ℂ) * Complex.I = 0`. Rewrite using `[Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_assoc, ← mul_assoc uᴴ, hu1, one_mul, hmul, hsw, hE0]`.

Rewrite using `[mul_assoc, hEJ, ← mul_assoc, huJ, mul_assoc]`. Establish `hγ : Differentiable ℂ (fun z : ℂ => (fun a b => (u * E' z) a b : Fin n → Fin n → ℂ))`. Use `differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_` and prove the remaining obligations. Establish `hd : ∀ c, Differentiable ℂ (fun z : ℂ => E' z c b)`. Introduce `c`.

Simplify using `only [hE']`. Apply the tactic sequence `exact differentiable_exp_entry L c b`. Simplify using `only [Matrix.mul_apply]`. Conclude with `Differentiable.fun_sum fun c _ => (differentiable_const (u a c)).mul (hd c)`. Establish `hg : Differentiable ℂ (fun z : ℂ => F (u * E' z))` using `fun z => ((hF _ (hKC z)).comp z ((hγ z).differentiableWithinAt (s := Set.univ)) (fun w _ => hKC w)).differentiableAt Filter.univ_mem`.

Establish `han : AnalyticOnNhd ℂ (fun z : ℂ => F (u * E' z)) Set.univ` using `fun z _ => hg.analyticAt z`. Establish `hfreq : ∃ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, F (u * E' z) = 0`. Establish `ht : Filter.Tendsto (fun t : ℝ => (t : ℂ) * Complex.I) (nhdsWithin (0 : ℝ) {0}ᶜ) (nhdsWithin (0 : ℂ) {0}ᶜ)`. Use `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_` and prove the remaining obligations. Establish `hcont : Continuous (fun t : ℝ => (t : ℂ) * Complex.I)` using `by fun_prop`.

Simplify using `using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds`. Use `filter_upwards [self_mem_nhdsWithin] with t ht`. Simplify `ht` using `[Complex.I_ne_zero]`. Conclude with `ht.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall hzero))`. Establish `hall` using `han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ 0) hfreq`.

Establish `h12` using `hall (Set.mem_univ (1 / 2 : ℂ))`. Establish `hy' : u * E' (1 / 2) = y`. Establish `e3 : (-(1 / 2 : ℂ) + 1 / 2) = 0` using `by ring`. Rewrite using `[hu, mul_assoc, hmul, e3, hE0, mul_one]`. Simplify using `only [Pi.zero_apply] at h12`.

Rewrite `h12` using `[hy']`. Conclude with `h12`.
-/
theorem eq_zero_on_KC_of_eq_zero_on_Kset : ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : Matrix (Fin n) (Fin n) ℂ → E), DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => F (Matrix.of y)) {y | Matrix.of y ∈ GlobalTheory.Dec.KC ε} → (∀ k ∈ Formalism.REAL.Kset ε, F k = 0) → ∀ y ∈ GlobalTheory.Dec.KC ε, F y = 0 := by
  intro n ε E _ _ _ F hF hK y hy
  unfold GlobalTheory.Dec.KC at hy
  obtain ⟨hyu, hyJ⟩ := hy
  have hJh : (Jm ε)ᴴ = Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hyhJ : yᴴ * Jm ε = Jm ε * yᴴ := by
    have h := congrArg Matrix.conjTranspose hyJ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJh] at h
    exact h.symm
  have hc : Commute (yᴴ * y) (Jm ε) := by
    show yᴴ * y * Jm ε = Jm ε * (yᴴ * y)
    rw [mul_assoc, hyJ, ← mul_assoc, hyhJ, mul_assoc]
  obtain ⟨L, hLh, hLJ, hLe⟩ := exists_herm_log y (Jm ε) hyu hc
  obtain ⟨E', hE'⟩ : ∃ f : ℂ → Matrix (Fin n) (Fin n) ℂ, f = fun w => NormedSpace.exp (w • L) :=
    ⟨_, rfl⟩
  have hmul : ∀ a b : ℂ, E' a * E' b = E' (a + b) := by
    intro a b
    simp only [hE', add_smul]
    exact (Matrix.exp_add_of_commute _ _ (((Commute.refl L).smul_left a).smul_right b)).symm
  have hstar : ∀ w : ℂ, (E' w)ᴴ = E' (star w) := by
    intro w
    simp only [hE']
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hLh]
  have hEJ : ∀ w : ℂ, E' w * Jm ε = Jm ε * E' w := by
    intro w
    simp only [hE']
    exact (hLJ.smul_left w).exp_left.eq
  have hE0 : E' 0 = 1 := by simp [hE']
  have hEone : E' 1 = yᴴ * y := by
    simp only [hE', one_smul]
    exact hLe
  have hEu : ∀ w : ℂ, IsUnit (E' w) := by
    intro w
    simp only [hE']
    exact Matrix.isUnit_exp _
  obtain ⟨u, hu⟩ : ∃ u : Matrix (Fin n) (Fin n) ℂ, u = y * E' (-(1 / 2)) := ⟨_, rfl⟩
  have hhalf : star (-(1 / 2 : ℂ)) = -(1 / 2) := by simp
  have hu1 : uᴴ * u = 1 := by
    rw [hu, Matrix.conjTranspose_mul, hstar, hhalf]
    have e1 : E' (-(1 / 2)) * yᴴ * (y * E' (-(1 / 2))) = E' (-(1 / 2)) * (yᴴ * y) * E' (-(1 / 2)) := by
      simp only [mul_assoc]
    have e2 : (-(1 / 2 : ℂ) + 1 + -(1 / 2)) = 0 := by ring
    rw [e1, ← hEone, hmul, hmul, e2, hE0]
  have huJ : u * Jm ε = Jm ε * u := by
    rw [hu, mul_assoc, hEJ, ← mul_assoc, hyJ, mul_assoc]
  have huU : IsUnit u := by
    rw [hu]
    exact hyu.mul (hEu _)
  have hKC : ∀ z : ℂ, u * E' z ∈ GlobalTheory.Dec.KC ε := by
    intro z
    unfold GlobalTheory.Dec.KC
    refine ⟨huU.mul (hEu z), ?_⟩
    rw [mul_assoc, hEJ, ← mul_assoc, huJ, mul_assoc]
  have hzero : ∀ t : ℝ, F (u * E' ((t : ℂ) * Complex.I)) = 0 := by
    intro t
    apply hK
    unfold Formalism.REAL.Kset
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, hstar]
      have hsw : star ((t : ℂ) * Complex.I) + (t : ℂ) * Complex.I = 0 := by
        rw [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I]
        ring
      rw [mul_assoc, ← mul_assoc uᴴ, hu1, one_mul, hmul, hsw, hE0]
    · rw [mul_assoc, hEJ, ← mul_assoc, huJ, mul_assoc]
  have hγ : Differentiable ℂ (fun z : ℂ => (fun a b => (u * E' z) a b : Fin n → Fin n → ℂ)) := by
    refine differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
    have hd : ∀ c, Differentiable ℂ (fun z : ℂ => E' z c b) := by
      intro c
      simp only [hE']
      exact differentiable_exp_entry L c b
    simp only [Matrix.mul_apply]
    exact Differentiable.fun_sum fun c _ => (differentiable_const (u a c)).mul (hd c)
  have hg : Differentiable ℂ (fun z : ℂ => F (u * E' z)) := fun z =>
    ((hF _ (hKC z)).comp z ((hγ z).differentiableWithinAt (s := Set.univ))
      (fun w _ => hKC w)).differentiableAt Filter.univ_mem
  have han : AnalyticOnNhd ℂ (fun z : ℂ => F (u * E' z)) Set.univ := fun z _ => hg.analyticAt z
  have hfreq : ∃ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, F (u * E' z) = 0 := by
    have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ) * Complex.I) (nhdsWithin (0 : ℝ) {0}ᶜ)
        (nhdsWithin (0 : ℂ) {0}ᶜ) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hcont : Continuous (fun t : ℝ => (t : ℂ) * Complex.I) := by fun_prop
        simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa [Complex.I_ne_zero] using ht
    exact ht.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall hzero))
  have hall := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ 0) hfreq
  have h12 := hall (Set.mem_univ (1 / 2 : ℂ))
  have hy' : u * E' (1 / 2) = y := by
    have e3 : (-(1 / 2 : ℂ) + 1 / 2) = 0 := by ring
    rw [hu, mul_assoc, hmul, e3, hE0, mul_one]
  simp only [Pi.zero_apply] at h12
  rw [hy'] at h12
  exact h12

end GlobalTheory.Dec.KCIdent
