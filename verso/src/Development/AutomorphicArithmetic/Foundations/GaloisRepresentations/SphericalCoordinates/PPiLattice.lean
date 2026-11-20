import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

/- English proof (translation)
Introduce `g k Λ hd hs`. Prove the components needed by the constructor for the conclusion. Set `φ : ↥(AddSubgroup.pi Set.univ fun _ : Fin k => Λ) → (Fin k → ↥Λ)` to `fun x i => ⟨x.1 i, (AddSubgroup.mem_pi _).mp x.2 i trivial⟩`. Use `DiscreteTopology.of_continuous_injective (f := φ) ?_ ?_` and prove the remaining obligations. Use `continuous_pi fun i => ?_` and prove the remaining obligations.

Conclude with `((continuous_apply i).comp continuous_subtype_val).subtype_mk _`. Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `congrArg (fun z => (z i : Fin g → ℂ)) hxy` as an intermediate fact.

Simplify `this` using `[φ]`. Rewrite using `[eq_top_iff]`. Introduce `w _`. Rewrite using `[← Finset.univ_sum_single w]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Establish `hw : w i ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ))` using `by rw [hs]; trivial`. Establish `hmap : (Submodule.span ℝ (Λ : Set (Fin g → ℂ))).map (LinearMap.single ℝ (fun _ : Fin k => Fin g → ℂ) i) ≤ Submodule.span ℝ ↑(AddSubgroup.pi Set.univ fun _ : Fin k => Λ)`. Rewrite using `[Submodule.map_span]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨v, hv, rfl⟩`.

Simplify using `only [SetLike.mem_coe, AddSubgroup.mem_pi]`. Introduce `j _`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `using hv`.

Simplify using `[hj]`. Conclude with `hmap ⟨w i, hw, rfl⟩`.
-/
theorem UpperTheory.Gal.W2.piLattice_of :
    UpperTheory.Gal.W2.PiLattice := by
  intro g k Λ hd hs
  constructor
  · let φ : ↥(AddSubgroup.pi Set.univ fun _ : Fin k => Λ) → (Fin k → ↥Λ) :=
      fun x i => ⟨x.1 i, (AddSubgroup.mem_pi _).mp x.2 i trivial⟩
    refine DiscreteTopology.of_continuous_injective (f := φ) ?_ ?_
    · refine continuous_pi fun i => ?_
      exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
    · intro x y hxy
      apply Subtype.ext
      funext i
      have := congrArg (fun z => (z i : Fin g → ℂ)) hxy
      simpa [φ] using this
  · rw [eq_top_iff]
    intro w _
    rw [← Finset.univ_sum_single w]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hw : w i ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := by rw [hs]; trivial
    have hmap : (Submodule.span ℝ (Λ : Set (Fin g → ℂ))).map
        (LinearMap.single ℝ (fun _ : Fin k => Fin g → ℂ) i) ≤
        Submodule.span ℝ ↑(AddSubgroup.pi Set.univ fun _ : Fin k => Λ) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨v, hv, rfl⟩
      simp only [SetLike.mem_coe, AddSubgroup.mem_pi]
      intro j _
      by_cases hj : j = i
      · subst hj; simpa using hv
      · simp [hj]
    exact hmap ⟨w i, hw, rfl⟩
