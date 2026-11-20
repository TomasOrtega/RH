import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussIntegralTransformWeilStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableQuadraticGaussIntegralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGroupSignMulAndNegOneStatement

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad

/- English proof (translation)
Establish `hu : IsUnit ((-1 : A.Kˣ) : A.K)` using `Units.isUnit _`. Establish `he : hu.unit = -1` using `Units.ext rfl`. Unfold `Et.absK`. Rewrite using `[dif_pos hu, he]`. Establish `h2 : (distribHaarChar A.K (-1 : A.Kˣ)) ^ 2 = 1`.

Rewrite using `[← map_pow]`. Simplify using the standard rewrite rules. Establish `h3 : distribHaarChar A.K (-1 : A.Kˣ) = 1` using `(pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h2`. Rewrite using `[h3]`. Simplify using the standard rewrite rules.
-/
theorem absK_units_neg_one {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] (A : Et F E) : A.absK ((-1 : A.Kˣ) : A.K) = 1 := by
  have hu : IsUnit ((-1 : A.Kˣ) : A.K) := Units.isUnit _
  have he : hu.unit = -1 := Units.ext rfl
  unfold Et.absK
  rw [dif_pos hu, he]
  have h2 : (distribHaarChar A.K (-1 : A.Kˣ)) ^ 2 = 1 := by
    rw [← map_pow]; simp
  have h3 : distribHaarChar A.K (-1 : A.Kˣ) = 1 :=
    (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h2
  rw [h3]; simp

/- English proof (translation)
Introduce `F E _ _ _ _ _ A ψ x μ ω h G₁ h1`. Take `⟨G, hG⟩` from `GlobalTheory.T.exists_stable_quadraticGaussIntegral F E A ψ x μ ω h (-1)`. Establish `hω` using `(GlobalTheory.T.normGroupSign_mul_and_neg_one F E A ψ x μ ω h).2`. Establish `h1' : IsStableGauss A ψ x μ ((1 : A.Kˣ) : A.K) G₁` using `by simpa using h1`. Establish `key` using `GlobalTheory.T.stableQuadraticGaussIntegral_transform_weil F E A ψ x μ ω h (-1) G G₁ hG h1'`.

Rewrite `key` using `[hω, absK_units_neg_one]`. Simplify using `at key`. Substitute `key` using the available equality. Simplify using `using hG`.
-/
theorem stableGauss_neg_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ)
    (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ G₁ : ℂ, IsStableGauss A ψ x μ 1 G₁ →
    IsStableGauss A ψ x μ (-1) G₁ := by
  intro F E _ _ _ _ _ A ψ x μ ω h G₁ h1
  obtain ⟨G, hG⟩ := GlobalTheory.T.exists_stable_quadraticGaussIntegral F E A ψ x μ ω h (-1)
  have hω := (GlobalTheory.T.normGroupSign_mul_and_neg_one F E A ψ x μ ω h).2
  have h1' : IsStableGauss A ψ x μ ((1 : A.Kˣ) : A.K) G₁ := by simpa using h1
  have key := GlobalTheory.T.stableQuadraticGaussIntegral_transform_weil F E A ψ x μ ω h (-1) G G₁ hG h1'
  rw [hω, absK_units_neg_one] at key
  simp at key
  subst key
  simpa using hG

end GlobalTheory.JR.WeilQuad
