import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightPolynomialEvalStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightPowerSumOneZeroStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyBoundaryDimensionDropStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

/- English proof (translation)
Simplify using `[PB.gap, PB.gapX, h]`.
-/
theorem flag_gap_eq_sub {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (lam : Wt Ψ N) (τ : Ψ) (a : Fin N)
    (h : (a : ℕ) + 1 < N) :
    PB.gap (fun x : Ψ × Fin N => lam x.1 x.2) (τ, a) = lam τ a - lam τ ⟨(a : ℕ) + 1, h⟩ := by
  simp [PB.gap, PB.gapX, h]

/- English proof (translation)
Simplify using `[dimFl, GroundTheory.Heights₂.Heights.antisymDegree, Nat.choose_two_right]`.
-/
theorem flag_dim_eq_antisymmetric_degree (Ψ : Type) [Fintype Ψ] (N : ℕ) :
    dimFl Ψ N = GroundTheory.Heights₂.Heights.antisymDegree Ψ N := by
  simp [dimFl, GroundTheory.Heights₂.Heights.antisymDegree, Nat.choose_two_right]

/- English proof (translation)
Introduce `hFH hIn II hII Ψ _ _ N _ hN`. Establish `hA : IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1)`. Rewrite using `[flag_dim_eq_antisymmetric_degree]`. Conclude with `(GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1`. Establish `hev : ∀ lam : Wt Ψ N, hhFl Ψ N II (linRoot lam ^ (dimFl Ψ N + 1)) = eval (fun x => lam x.1 x.2) (PB.hFlPoly Ψ N II)` using `fun lam => GlobalTheory.T.flag_height_polynomial_eval II hII Ψ N lam hN hA`.

Take `⟨-, hgap, hdom⟩` from `hFH hIn II hII Ψ N hN`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `lam - ⟨τ, a, b, hab, heq⟩`. Establish `h : (a : ℕ) + 1 < N` using `hab ▸ b.2`. Establish `hb : b = ⟨(a : ℕ) + 1, h⟩` using `Fin.ext hab`.

Rewrite using `[hev]`. Use `hgap _ (τ, a) h ?_` and prove the remaining obligations. Rewrite using `[flag_gap_eq_sub lam τ a h, ← hb, heq, sub_self]`. Introduce `lam hlam`. Rewrite using `[hev]`.

Use `hdom _ fun p hp => ?_` and prove the remaining obligations. Take `⟨τ, a⟩` from `p`. Rewrite using `[flag_gap_eq_sub lam τ a hp, sub_nonneg]`. Conclude with `hlam τ a ⟨(a : ℕ) + 1, hp⟩ (Fin.le_def.2 (Nat.le_succ _))`. Introduce `τ Q hQ`.

Conclude with `GlobalTheory.T.flag_height_power_sum_one_zero II hII Ψ N τ Q hN hA hQ`.
-/
theorem flag_height_I9 : PB.FlagHeight → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ], 2 ≤ N →
      I9 (Ψ := Ψ) (N := N) (hhFl Ψ N II) := by
  intro hFH hIn II hII Ψ _ _ N _ hN
  have hA : IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) := by
    rw [flag_dim_eq_antisymmetric_degree]
    exact (GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1
  have hev : ∀ lam : Wt Ψ N, hhFl Ψ N II (linRoot lam ^ (dimFl Ψ N + 1)) =
      eval (fun x => lam x.1 x.2) (PB.hFlPoly Ψ N II) := fun lam =>
    GlobalTheory.T.flag_height_polynomial_eval II hII Ψ N lam hN hA
  obtain ⟨-, hgap, hdom⟩ := hFH hIn II hII Ψ N hN
  refine ⟨?_, ?_, ?_⟩
  · rintro lam - ⟨τ, a, b, hab, heq⟩
    have h : (a : ℕ) + 1 < N := hab ▸ b.2
    have hb : b = ⟨(a : ℕ) + 1, h⟩ := Fin.ext hab
    rw [hev]
    refine hgap _ (τ, a) h ?_
    rw [flag_gap_eq_sub lam τ a h, ← hb, heq, sub_self]
  · intro lam hlam
    rw [hev]
    refine hdom _ fun p hp => ?_
    obtain ⟨τ, a⟩ := p
    rw [flag_gap_eq_sub lam τ a hp, sub_nonneg]
    exact hlam τ a ⟨(a : ℕ) + 1, hp⟩ (Fin.le_def.2 (Nat.le_succ _))
  · intro τ Q hQ
    exact GlobalTheory.T.flag_height_power_sum_one_zero II hII Ψ N τ Q hN hA hQ

end GlobalTheory.CompanionTheory.Ar.Top
