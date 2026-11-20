import Mathlib
import Formalism.PeriodIntegrals.LocDualGen

noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocDualGen.Part2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)

/- English proof (translation)
Rewrite using `[A.O_def]`. Establish `: algebraMap A.Fp A.Ep (r : A.Fp) = algebraMap 𝒪[A.Fp] A.Ep r` using `rfl`. Rewrite using `[this]`. Conclude with `isIntegral_algebraMap`.
-/
theorem alg_mem_O (r : 𝒪[A.Fp]) : algebraMap A.Fp A.Ep (r : A.Fp) ∈ A.O := by
  rw [A.O_def]
  have : algebraMap A.Fp A.Ep (r : A.Fp) = algebraMap 𝒪[A.Fp] A.Ep r := rfl
  rw [this]
  exact isIntegral_algebraMap

/- English proof (translation)
Introduce `x`. Rewrite using `[← h x]`. Take `⟨v, rfl⟩` from `hu`. Establish `hv : ((v : 𝒪[A.Fp]) : A.Fp) * ((v⁻¹ : (𝒪[A.Fp])ˣ) : A.Fp) = 1`. Rewrite using `[← Subring.coe_mul, Units.mul_inv]`.

Both sides reduce to the same expression. Use `set a := algebraMap A.Fp A.Ep ((v : 𝒪[A.Fp]) : A.Fp)`. Use `set b := algebraMap A.Fp A.Ep ((v⁻¹ : (𝒪[A.Fp])ˣ) : A.Fp)`. Establish `hab : a * b = 1` using `by rw [← map_mul, hv, map_one]`. Establish `hinv : (((v : 𝒪[A.Fp]) : A.Fp))⁻¹ = ((v⁻¹ : (𝒪[A.Fp])ˣ) : A.Fp)` using `inv_eq_of_mul_eq_one_right hv`.

Establish `key : algebraMap A.Fp A.Ep (δ * ((v : 𝒪[A.Fp]) : A.Fp))⁻¹ = algebraMap A.Fp A.Ep δ⁻¹ * b`. Rewrite using `[mul_inv, map_mul, hinv]`. Prove the components needed by the constructor for the conclusion. Introduce `H y hy`. Use `H (y * a) (A.O.mul_mem hy (alg_mem_O A _))` as an intermediate fact.

Rewrite `this` using `[key, show x * (y * a) * (algebraMap A.Fp A.Ep δ⁻¹ * b) = x * y * algebraMap A.Fp A.Ep δ⁻¹ * (a * b) by ring, hab, mul_one]`. Then use the resulting hypothesis. Introduce `H y hy`. Use `H (y * b) (A.O.mul_mem hy (alg_mem_O A _))` as an intermediate fact. Rewrite using `[key, show x * y * (algebraMap A.Fp A.Ep δ⁻¹ * b) = x * (y * b) * algebraMap A.Fp A.Ep δ⁻¹ by ring]` and apply the resulting hypothesis.
-/
theorem dualAtL_mul_unit (δ : A.Fp) (u : 𝒪[A.Fp]) (hu : IsUnit u) (h : DualAtL A δ) :
    DualAtL A (δ * (u : A.Fp)) := by
  intro x
  rw [← h x]
  obtain ⟨v, rfl⟩ := hu
  have hv : ((v : 𝒪[A.Fp]) : A.Fp) * ((v⁻¹ : (𝒪[A.Fp])ˣ) : A.Fp) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv]; rfl
  set a := algebraMap A.Fp A.Ep ((v : 𝒪[A.Fp]) : A.Fp)
  set b := algebraMap A.Fp A.Ep ((v⁻¹ : (𝒪[A.Fp])ˣ) : A.Fp)
  have hab : a * b = 1 := by rw [← map_mul, hv, map_one]
  have hinv : (((v : 𝒪[A.Fp]) : A.Fp))⁻¹ = ((v⁻¹ : (𝒪[A.Fp])ˣ) : A.Fp) :=
    inv_eq_of_mul_eq_one_right hv
  have key : algebraMap A.Fp A.Ep (δ * ((v : 𝒪[A.Fp]) : A.Fp))⁻¹ = algebraMap A.Fp A.Ep δ⁻¹ * b := by
    rw [mul_inv, map_mul, hinv]
  constructor
  · intro H y hy
    have := H (y * a) (A.O.mul_mem hy (alg_mem_O A _))
    rwa [key, show x * (y * a) * (algebraMap A.Fp A.Ep δ⁻¹ * b) = x * y * algebraMap A.Fp A.Ep δ⁻¹ * (a * b) by ring,
      hab, mul_one] at this
  · intro H y hy
    have := H (y * b) (A.O.mul_mem hy (alg_mem_O A _))
    rwa [key, show x * y * (algebraMap A.Fp A.Ep δ⁻¹ * b) = x * (y * b) * algebraMap A.Fp A.Ep δ⁻¹ by ring]

end PI.LocDualGen.Part2
