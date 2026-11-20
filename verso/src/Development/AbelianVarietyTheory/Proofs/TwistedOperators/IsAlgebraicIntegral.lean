import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis

open MeasureTheory

namespace GlobalTheory.HaarAlg

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (κ : Measure K) [IsProbabilityMeasure κ] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Group K] [IsTopologicalGroup K] in
/- English proof (translation)
The claim follows from `hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)`.
-/
theorem integrable_of_continuous {f : K → ℂ} (hf : Continuous f) : Integrable f κ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

noncomputable def avg (F : K → Matrix ι ι ℂ) : Matrix ι ι ℂ := Matrix.of fun a b => ∫ g, F g a b ∂κ

omit [Group K] [IsTopologicalGroup K] [DecidableEq ι] in
/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [avg, Matrix.mul_apply, Matrix.of_apply]`. Rewrite using `[integral_finset_sum]`. Conclude with `Finset.sum_congr rfl fun c _ => (integral_const_mul _ _).symm`. Conclude with `fun c _ => integrable_of_continuous κ (by fun_prop)`.
-/
theorem mul_avg {F : K → Matrix ι ι ℂ} (hF : Continuous F) (M : Matrix ι ι ℂ) :
    M * avg κ F = avg κ fun g => M * F g := by
  ext a b
  simp only [avg, Matrix.mul_apply, Matrix.of_apply]
  rw [integral_finset_sum]
  · exact Finset.sum_congr rfl fun c _ => (integral_const_mul _ _).symm
  · exact fun c _ => integrable_of_continuous κ (by fun_prop)

omit [Group K] [IsTopologicalGroup K] [DecidableEq ι] in
/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [avg, Matrix.mul_apply, Matrix.of_apply]`. Rewrite using `[integral_finset_sum]`. Conclude with `Finset.sum_congr rfl fun c _ => (integral_mul_const _ _).symm`. Conclude with `fun c _ => integrable_of_continuous κ (by fun_prop)`.
-/
theorem avg_mul {F : K → Matrix ι ι ℂ} (hF : Continuous F) (M : Matrix ι ι ℂ) :
    avg κ F * M = avg κ fun g => F g * M := by
  ext a b
  simp only [avg, Matrix.mul_apply, Matrix.of_apply]
  rw [integral_finset_sum]
  · exact Finset.sum_congr rfl fun c _ => (integral_mul_const _ _).symm
  · exact fun c _ => integrable_of_continuous κ (by fun_prop)

omit [Group K] [IsTopologicalGroup K] [TopologicalSpace K] [CompactSpace K] [BorelSpace K] [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use extensionality with `a b`. Simplify using `[avg]`.
-/
theorem avg_const (M : Matrix ι ι ℂ) : avg κ (fun _ => M) = M := by
  ext a b
  simp [avg]

variable [κ.IsMulLeftInvariant]

omit [CompactSpace K] [IsProbabilityMeasure κ] [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use extensionality with `a b`. Conclude with `integral_mul_left_eq_self (fun g => F g a b) h`.
-/
theorem avg_left (F : K → Matrix ι ι ℂ) (h : K) : (avg κ fun g => F (h * g)) = avg κ F := by
  ext a b
  exact integral_mul_left_eq_self (fun g => F g a b) h

/- English proof (translation)
Rewrite using `[mul_avg κ hρ, ← avg_left κ ρ h]`. Simplify using `only [map_mul]`.
-/
theorem rho_mul_avg (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (h : K) : ρ h * avg κ ρ = avg κ ρ := by
  rw [mul_avg κ hρ, ← avg_left κ ρ h]
  simp only [map_mul]

/- English proof (translation)
Establish `hc : Continuous fun g : K => ρ g⁻¹` using `hρ.comp continuous_inv`. Establish `h1 : ∀ h, avg κ (fun g => ρ g⁻¹) * ρ h = avg κ fun g => ρ g⁻¹` using `fun h => by`. Rewrite using `[avg_mul κ hc, ← avg_left κ (fun g => ρ g⁻¹) h⁻¹]`. Simplify using `only [mul_inv_rev, inv_inv, map_mul]`. Establish `h2 : avg κ (fun g => ρ g⁻¹) * avg κ ρ = avg κ ρ`.

Rewrite using `[avg_mul κ hc]`. Simplify using `only [rho_mul_avg κ ρ hρ, avg_const]`. Establish `h3 : avg κ (fun g => ρ g⁻¹) * avg κ ρ = avg κ fun g => ρ g⁻¹`. Rewrite using `[mul_avg κ hρ]`. Simplify using `only [h1, avg_const]`.

Rewrite using `[h2.symm.trans h3, h1]`.
-/
theorem avg_mul_rho (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (h : K) : avg κ ρ * ρ h = avg κ ρ := by
  have hc : Continuous fun g : K => ρ g⁻¹ := hρ.comp continuous_inv
  have h1 : ∀ h, avg κ (fun g => ρ g⁻¹) * ρ h = avg κ fun g => ρ g⁻¹ := fun h => by
    rw [avg_mul κ hc, ← avg_left κ (fun g => ρ g⁻¹) h⁻¹]
    simp only [mul_inv_rev, inv_inv, map_mul]
  have h2 : avg κ (fun g => ρ g⁻¹) * avg κ ρ = avg κ ρ := by
    rw [avg_mul κ hc]
    simp only [rho_mul_avg κ ρ hρ, avg_const]
  have h3 : avg κ (fun g => ρ g⁻¹) * avg κ ρ = avg κ fun g => ρ g⁻¹ := by
    rw [mul_avg κ hρ]
    simp only [h1, avg_const]
  rw [h2.symm.trans h3, h1]

/- English proof (translation)
Use `set P := avg κ ρ with hP`. Set `Q` to `algebraicClosure ℚ ℂ`. Establish `key : ∀ s : ℂ ≃ₐ[Q] ℂ, P * P.map s = P.map s ∧ P.map s * P = P.map s` using `fun s => by`. Establish `hfix : ∀ γ ∈ Γ, (ρ γ).map s = ρ γ` using `fun γ hγ => by`. Use extensionality with `a b`.

Conclude with `s.commutes (⟨ρ γ a b, mem_algebraicClosure_iff.2 (halg γ hγ a b)⟩ : Q)`. Establish `hm : ∀ M N : Matrix ι ι ℂ, (M * N).map s = M.map s * N.map s` using `fun M N => Matrix.map_mul`. Establish `l : ∀ g, ρ g * P.map s = P.map s` using `fun g => congrFun (Continuous.ext_on hΓ (f := fun g => ρ g * P.map s) (g := fun _ => P.map s) (by fun_prop) continuous_const fun γ hγ => by show ρ γ * P.map s = P.map s`. Rewrite using `[← hfix γ hγ, ← hm, hP, rho_mul_avg κ ρ hρ]) g`. Establish `r : ∀ g, P.map s * ρ g = P.map s` using `fun g => congrFun (Continuous.ext_on hΓ (f := fun g => P.map s * ρ g) (g := fun _ => P.map s) (by fun_prop) continuous_const fun γ hγ => by show P.map s * ρ γ = P.map s`.

Rewrite using `[← hfix γ hγ, ← hm, hP, avg_mul_rho κ ρ hρ]) g`. Prove the components needed by the constructor for the conclusion. Use `conv_lhs => rw [hP]`. Rewrite using `[avg_mul κ hρ]`. Simplify using `only [← hP, l, avg_const]`.

Use `conv_lhs => rw [hP]`. Rewrite using `[mul_avg κ hρ]`. Simplify using `only [← hP, r, avg_const]`. Establish `fix : ∀ s : ℂ ≃ₐ[Q] ℂ, P.map s = P` using `fun s => by`. Establish `h1` using `congrArg (fun M : Matrix ι ι ℂ => M.map s) (key s.symm).1`.

Establish `e : (P.map s.symm).map s = P` using `by ext a b; simp`. Establish `hm : ∀ M N : Matrix ι ι ℂ, (M * N).map s = M.map s * N.map s` using `fun M N => Matrix.map_mul`. Simplify using `only [hm, e] at h1`. Rewrite using `[← (key s).2, h1]`. Take `⟨q, hq⟩` from `GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv (K := Q) (P a b) fun s => congrFun (congrFun (fix s) a) b`.

Establish `: P a b ∈ Q` using `hq ▸ q.2`. Conclude with `mem_algebraicClosure_iff.1 this`.
-/
theorem isAlgebraic_integral (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (Γ : Set K) (hΓ : Dense Γ)
    (halg : ∀ γ ∈ Γ, ∀ a b, IsAlgebraic ℚ (ρ γ a b)) (a b : ι) : IsAlgebraic ℚ (∫ g, ρ g a b ∂κ) := by
  set P := avg κ ρ with hP
  let Q := algebraicClosure ℚ ℂ
  have key : ∀ s : ℂ ≃ₐ[Q] ℂ, P * P.map s = P.map s ∧ P.map s * P = P.map s := fun s => by
    have hfix : ∀ γ ∈ Γ, (ρ γ).map s = ρ γ := fun γ hγ => by
      ext a b
      exact s.commutes (⟨ρ γ a b, mem_algebraicClosure_iff.2 (halg γ hγ a b)⟩ : Q)
    have hm : ∀ M N : Matrix ι ι ℂ, (M * N).map s = M.map s * N.map s := fun M N => Matrix.map_mul
    have l : ∀ g, ρ g * P.map s = P.map s := fun g =>
      congrFun (Continuous.ext_on hΓ (f := fun g => ρ g * P.map s) (g := fun _ => P.map s) (by fun_prop) continuous_const
        fun γ hγ => by
          show ρ γ * P.map s = P.map s
          rw [← hfix γ hγ, ← hm, hP, rho_mul_avg κ ρ hρ]) g
    have r : ∀ g, P.map s * ρ g = P.map s := fun g =>
      congrFun (Continuous.ext_on hΓ (f := fun g => P.map s * ρ g) (g := fun _ => P.map s) (by fun_prop) continuous_const
        fun γ hγ => by
          show P.map s * ρ γ = P.map s
          rw [← hfix γ hγ, ← hm, hP, avg_mul_rho κ ρ hρ]) g
    constructor
    · conv_lhs => rw [hP]
      rw [avg_mul κ hρ]
      simp only [← hP, l, avg_const]
    · conv_lhs => rw [hP]
      rw [mul_avg κ hρ]
      simp only [← hP, r, avg_const]
  have fix : ∀ s : ℂ ≃ₐ[Q] ℂ, P.map s = P := fun s => by
    have h1 := congrArg (fun M : Matrix ι ι ℂ => M.map s) (key s.symm).1
    have e : (P.map s.symm).map s = P := by ext a b; simp
    have hm : ∀ M N : Matrix ι ι ℂ, (M * N).map s = M.map s * N.map s := fun M N => Matrix.map_mul
    simp only [hm, e] at h1
    rw [← (key s).2, h1]
  obtain ⟨q, hq⟩ := GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv (K := Q) (P a b)
    fun s => congrFun (congrFun (fix s) a) b
  have : P a b ∈ Q := hq ▸ q.2
  exact mem_algebraicClosure_iff.1 this

end GlobalTheory.HaarAlg
