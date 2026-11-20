import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

/- English proof (translation)
Introduce `n`. Establish `h : {z : Fin n → ℂ | ∀ i, z i ≠ 0} = Set.pi Set.univ (fun _ => ({0}ᶜ : Set ℂ))`. Use extensionality with `z`. Simplify using the standard rewrite rules. Rewrite using `[h]`.

Conclude with `dense_pi Set.univ (fun _ _ => dense_compl_singleton 0)`.
-/
theorem dense_forall_coord_ne_zero : ∀ n : ℕ, Dense {z : Fin n → ℂ | ∀ i, z i ≠ 0} := by
  intro n
  have h : {z : Fin n → ℂ | ∀ i, z i ≠ 0} = Set.pi Set.univ (fun _ => ({0}ᶜ : Set ℂ)) := by
    ext z
    simp
  rw [h]
  exact dense_pi Set.univ (fun _ _ => dense_compl_singleton 0)

end GlobalTheory.CompanionTheory.Ar.PB.Flat
