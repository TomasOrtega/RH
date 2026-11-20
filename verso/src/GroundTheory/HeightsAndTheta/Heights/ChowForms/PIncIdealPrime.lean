import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Introduce `F _ n k P hP hrel`. Use `hP` as an intermediate fact. Take `⟨j, hj⟩` from `hrel`. Establish `hξ : genPt P j ≠ 0`. Unfold `genPt`.

Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hj`. Use `set c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P) := Pi.single j (genPt P j)⁻¹ with hc`. Establish `hsum : ∑ l, c l * genPt P l = 1`. Rewrite using `[Finset.sum_eq_single j]`.

Simplify using `[hc, inv_mul_cancel₀ hξ]`. Introduce `b _ hb`. Simplify using `[hc, Pi.single_eq_of_ne hb]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`.

Establish `hker : incIdeal P k = RingHom.ker (aeval (genSubst (k` using `k) (genPt P) c) : MvPolynomial (Fin k × Fin n) F →ₐ[F] MvPolynomial (Fin k × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ P))) := by`. Use extensionality with `g`. Rewrite using `[RingHom.mem_ker]`. Conclude with `h₁ F n k P c hsum g`. Rewrite using `[hker]`.

Conclude with `RingHom.ker_isPrime _`.
-/
theorem IncIdealPrime.proof (h₁ : IncidenceGeneric.Statement) : IncIdealPrime.Statement := by
  intro F _ n k P hP hrel
  have := hP
  obtain ⟨j, hj⟩ := hrel
  have hξ : genPt P j ≠ 0 := by
    unfold genPt
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hj
  set c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P) := Pi.single j (genPt P j)⁻¹ with hc
  have hsum : ∑ l, c l * genPt P l = 1 := by
    rw [Finset.sum_eq_single j]
    · simp [hc, inv_mul_cancel₀ hξ]
    · intro b _ hb
      simp [hc, Pi.single_eq_of_ne hb]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hker : incIdeal P k =
      RingHom.ker (aeval (genSubst (k := k) (genPt P) c) :
        MvPolynomial (Fin k × Fin n) F →ₐ[F]
          MvPolynomial (Fin k × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ P))) := by
    ext g
    rw [RingHom.mem_ker]
    exact h₁ F n k P c hsum g
  rw [hker]
  exact RingHom.ker_isPrime _

end GroundTheory.Heights₂.Heights
