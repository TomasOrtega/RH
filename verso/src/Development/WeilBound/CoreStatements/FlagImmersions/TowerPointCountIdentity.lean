import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.WeilBound.CoreStatements.FlagImmersions.DegLApply

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
private theorem degFl_sum' {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {ι : Type} (s : Finset ι)
    (f : ι → RP Ψ N) : degFl (∑ i ∈ s, f i) = ∑ i ∈ s, degFl (f i) := by
  unfold degFl
  simp only [MvPolynomial.coeff_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
private theorem Sh_sum {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {ι : Type} (j : ℕ) (τ : Ψ)
    (s : Finset ι) (f : ι → RP Ψ N) : Sh j τ (∑ i ∈ s, f i) = ∑ i ∈ s, Sh j τ (f i) := by
  simp only [Sh, map_sum]
  rw [Finset.sum_comm, degFl_sum']
/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
private theorem Tot_sum {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {ι : Type} (τ : Ψ)
    (s : Finset ι) (f : ι → RP Ψ N) : Tot τ (∑ i ∈ s, f i) = ∑ i ∈ s, Tot τ (f i) := by
  simp only [Tot, map_sum]
  rw [Finset.sum_comm, degFl_sum']
/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
private theorem PPt_sum {Ψ : Type} [Fintype Ψ] {N : ℕ} {ι : Type} (T : RootTower Ψ N)
    (II : IntersectionSystem) (B : ℕ) (s : Finset ι) (f : ι → RP Ψ N) :
    T.PPt II B (∑ i ∈ s, f i) = ∑ i ∈ s, T.PPt II B (f i) := by
  simp only [RootTower.PPt, RootTower.PPc, toA, map_sum]
  rw [Finset.sum_comm]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem tower_point_count_identity : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (B₀ : ℕ) (A₀ b₀ : ℝ) (F : RP Ψ N) (Q : Ψ → ℕ → RP Ψ N), T.IdentAt II hh frob B₀ A₀ b₀ → IsDecomp F Q → T.PPt II B₀ F = T.volT * (hh F - A₀ * ∑ σ, Sh T.j σ F - b₀ * ∑ σ, Tot σ F + ∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum T.j T.bad frob B₀ τ k (Q τ k)) := by
  intro II Ψ _ _ N T hh frob B₀ A₀ b₀ F Q hI hD
  obtain ⟨hQ, rfl⟩ := hD
  have key : ∀ τ, ∀ k ∈ Finset.Icc 1 N, T.PPt II B₀ (pk τ k * Q τ k) = T.volT * (hh (pk τ k * Q τ k)
      - A₀ * ∑ σ, Sh T.j σ (pk τ k * Q τ k) - b₀ * ∑ σ, Tot σ (pk τ k * Q τ k)
      + restSum T.j T.bad frob B₀ τ k (Q τ k)) := by
    intro τ k hk
    have hk' := Finset.mem_Icc.1 hk
    exact hI τ k hk'.1 hk'.2 _ (hQ τ k hk'.1 hk'.2)
  simp_rw [PPt_sum, map_sum, Sh_sum, Tot_sum]
  rw [Finset.sum_congr rfl (fun τ _ => Finset.sum_congr rfl (key τ))]
  have e1 : ∑ σ, ∑ τ, ∑ k ∈ Finset.Icc 1 N, Sh T.j σ (pk τ k * Q τ k)
      = ∑ τ, ∑ k ∈ Finset.Icc 1 N, ∑ σ, Sh T.j σ (pk τ k * Q τ k) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have e2 : ∑ σ, ∑ τ, ∑ k ∈ Finset.Icc 1 N, Tot σ (pk τ k * Q τ k)
      = ∑ τ, ∑ k ∈ Finset.Icc 1 N, ∑ σ, Tot σ (pk τ k * Q τ k) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [e1, e2]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub]

end RootFieldNumerics
