import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import ReciprocityTheory.Chebotarev.EulerSum

set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Establish `h0 : -s ≠ 0` using `fun h => by`. Establish `: s = 0` using `neg_eq_zero.mp h`. Simplify using `[this] at hs`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1 : -s.re ≠ 0` using `by linarith`. Simplify using `[Complex.zero_cpow h0, Real.zero_rpow h1]`. Simplify using `using Complex.norm_natCast_cpow_of_pos hn (-s)`.
-/
theorem norm_natCast_cpow_neg (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : -s ≠ 0 := fun h => by
      have : s = 0 := neg_eq_zero.mp h
      simp [this] at hs
      linarith
    have h1 : -s.re ≠ 0 := by linarith
    simp [Complex.zero_cpow h0, Real.zero_rpow h1]
  · simpa using Complex.norm_natCast_cpow_of_pos hn (-s)

/- English proof (translation)
Introduce `F _ _ _ 𝔣 𝔞 𝔟 J _ r y v _ s hs`. Establish `h` using `(ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).subtype {I : Ideal (𝓞 F) | CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞}`. Use `Summable.of_norm (h.congr fun I => ?_)` and prove the remaining obligations. Conclude with `(norm_natCast_cpow_neg _ hs).symm`.
-/
theorem classSummable : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 : Ideal (𝓞 F)) (J : Type) [Fintype J]
    (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → ∀ s : ℂ, 1 < s.re →
      Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
  intro F _ _ _ 𝔣 𝔞 𝔟 J _ r y v _ s hs
  have h := (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).subtype
    {I : Ideal (𝓞 F) | CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞}
  refine Summable.of_norm (h.congr fun I => ?_)
  exact (norm_natCast_cpow_neg _ hs).symm

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
