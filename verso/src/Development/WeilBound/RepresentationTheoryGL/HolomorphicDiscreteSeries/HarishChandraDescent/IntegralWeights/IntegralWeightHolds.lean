import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Commutant
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeWt

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Unfold `IntWt ForRep`. Introduce `n ε H _ _ _ ρ hρ ν x hx hwt a`. Establish `hD` using `isDerivedOn_smE hρ`. Establish `hG` using `(isWtOn_iff hρ hD x ν).2 hwt`. Set `θ : Fin n → ℝ` to `Pi.single a (2 * Real.pi)`.

Establish `hdiag : (diagonal fun b => Complex.exp (↑(θ b) * Complex.I)) = 1`. Rewrite using `[← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Distinguish the cases in `hb : b = a`.

Substitute `hb` using the available equality. Establish `: θ b = 2 * Real.pi` using `by simp [θ]`. Rewrite using `[this]`. Use `push_cast`. Conclude with `Complex.exp_two_pi_mul_I`.

Establish `: θ b = 0` using `by simp [θ, hb]`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `hK : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε` using `⟨one_mem _, by simp⟩`. Establish `h1` using `hG θ (by rw [hdiag]; exact hK)`.

Rewrite `h1` using `[hdiag, hρ.1.1]`. Establish `hsum : ∑ b, ν b * θ b = ν a * (2 * Real.pi)`. Rewrite using `[Finset.sum_eq_single a]`. Simplify using `[θ]`. Introduce `b _ hb`.

Simplify using `[θ, hb]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ a) h`. Rewrite `h1` using `[hsum]`. Establish `hx' : (x : H) ≠ 0` using `fun h => hx (Subtype.ext h)`.

Establish `hexp : Complex.exp (↑(ν a * (2 * Real.pi)) * Complex.I) = 1`. Assume the negation of the conclusion as `hne`. Apply `hx'` to reduce the goal to its premises. Establish `h3 : (Complex.exp (↑(ν a * (2 * Real.pi)) * Complex.I) - 1) • (x : H) = 0`. Rewrite using `[sub_smul, ← h1]`.

Simplify using the standard rewrite rules. Conclude with `(smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)`. Take `⟨m, hm⟩` from `Complex.exp_eq_one_iff.1 hexp`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `by simp [Real.pi_ne_zero]`.

Establish `h4 : ((ν a : ℝ) : ℂ) = (m : ℂ)`. Apply `mul_right_cancel₀ hpi` to reduce the goal to its premises. Move the coercions through the operations in `at hm`. Take the linear combination `hm`. Conclude with `h4` after adjusting the coercions.
-/
theorem integral_weight_holds : IntWt := by
  unfold IntWt ForRep
  intro n ε H _ _ _ ρ hρ ν x hx hwt a
  have hD := isDerivedOn_smE hρ
  have hG := (isWtOn_iff hρ hD x ν).2 hwt
  let θ : Fin n → ℝ := Pi.single a (2 * Real.pi)
  have hdiag : (diagonal fun b => Complex.exp (↑(θ b) * Complex.I)) = 1 := by
    rw [← diagonal_one]
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb
      have : θ b = 2 * Real.pi := by simp [θ]
      rw [this]
      push_cast
      exact Complex.exp_two_pi_mul_I
    · have : θ b = 0 := by simp [θ, hb]
      rw [this]
      simp
  have hK : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε := ⟨one_mem _, by simp⟩
  have h1 := hG θ (by rw [hdiag]; exact hK)
  rw [hdiag, hρ.1.1] at h1
  have hsum : ∑ b, ν b * θ b = ν a * (2 * Real.pi) := by
    rw [Finset.sum_eq_single a]
    · simp [θ]
    · intro b _ hb
      simp [θ, hb]
    · intro h
      exact absurd (Finset.mem_univ a) h
  rw [hsum] at h1
  have hx' : (x : H) ≠ 0 := fun h => hx (Subtype.ext h)
  have hexp : Complex.exp (↑(ν a * (2 * Real.pi)) * Complex.I) = 1 := by
    by_contra hne
    apply hx'
    have h3 : (Complex.exp (↑(ν a * (2 * Real.pi)) * Complex.I) - 1) • (x : H) = 0 := by
      rw [sub_smul, ← h1]
      simp
    exact (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hexp
  refine ⟨m, ?_⟩
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h4 : ((ν a : ℝ) : ℂ) = (m : ℂ) := by
    apply mul_right_cancel₀ hpi
    push_cast at hm
    linear_combination hm
  exact_mod_cast h4

end PositivityTheory.RgHe3
