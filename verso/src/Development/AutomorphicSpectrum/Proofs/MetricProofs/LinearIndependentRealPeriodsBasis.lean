import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.QuotientLatticeByIsotropicSubmoduleStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp

/- English proof (translation)
Introduce `E _ _ _ g Λ _ _ R n b`. Establish `hspan : Submodule.span ℝ (Set.range R.P) = ⊤` using `(GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R).2.1`. Establish `hmem : ∀ x : Λ, R.P x ∈ Submodule.span ℝ (Set.range fun j => R.P (b j))`. Introduce `x`. Establish `hx : x ∈ Submodule.span ℤ (Set.range b)`.

Rewrite using `[b.span_eq]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`.

Conclude with `Submodule.subset_span ⟨j, rfl⟩`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hy hz`.

Consider the case `smul c y _ hy`. Rewrite using `[map_zsmul]`. Conclude with `Submodule.smul_of_tower_mem _ c hy`. Establish `htop : ⊤ ≤ Submodule.span ℝ (Set.range fun j => R.P (b j))`. Rewrite using `[← hspan]`.

Apply `Submodule.span_le.mpr` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hmem x`. Establish `hcard : Fintype.card (Fin n) = Module.finrank ℝ (Fin g → ℂ)`. Establish `h1 : Module.finrank ℤ Λ = Fintype.card (Fin n)` using `by haveI := R.free haveI := R.fin`.

Conclude with `Module.finrank_eq_card_basis b`. Establish `h2 : Module.finrank ℝ (Fin g → ℂ) = 2 * g`. Simplify using `[Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]`. Rewrite using `[← h1, R.rank, h2]`. Conclude with `linearIndependent_of_top_le_span_of_card_eq_finrank htop hcard`.
-/
theorem riemLat_basis_periods_linearIndependent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ), LinearIndependent ℝ (fun j => R.P (b j)) := by
  intro E _ _ _ g Λ _ _ R n b
  have hspan : Submodule.span ℝ (Set.range R.P) = ⊤ := (GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R).2.1
  have hmem : ∀ x : Λ, R.P x ∈ Submodule.span ℝ (Set.range fun j => R.P (b j)) := by
    intro x
    have hx : x ∈ Submodule.span ℤ (Set.range b) := by
      rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Submodule.subset_span ⟨j, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [map_zsmul]
      exact Submodule.smul_of_tower_mem _ c hy
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range fun j => R.P (b j)) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact hmem x
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (Fin g → ℂ) := by
    have h1 : Module.finrank ℤ Λ = Fintype.card (Fin n) := by
      haveI := R.free
      haveI := R.fin
      exact Module.finrank_eq_card_basis b
    have h2 : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
      simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
    rw [← h1, R.rank, h2]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank htop hcard

end GlobalTheory.CompanionTheory.Ar.Cusp
