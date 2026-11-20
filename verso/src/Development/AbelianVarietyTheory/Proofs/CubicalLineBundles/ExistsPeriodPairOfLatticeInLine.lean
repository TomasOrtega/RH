import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Introduce `g Λ w hg hw hdisc hspan`. Substitute `hg` using the available equality. Establish `hw0 : w 0 ≠ 0`. Introduce `h`. Apply `hw` to reduce the goal to its premises.

Use function extensionality and compare the values at `j`. Use `fin_cases j`. Simplify using `using h`. Choose the witnesses or unpack the hypotheses as in `⟨e, he⟩ : ∃ e : ℂ ≃L[ℝ] (Fin 1 → ℂ), ∀ z, e z = z • w := by`. Set `φ : ℂ →ₗ[ℝ] (Fin 1 → ℂ)` to `{ toFun := fun z => z • w map_add' := fun a b => add_smul a b w map_smul' := fun r z => by`.

Simplify using `only [RingHom.id_apply]`. Conclude with `smul_assoc r z w }`. Establish `hinj : Function.Injective φ` using `fun a b h => smul_left_injective ℂ hw h`. Establish `hsurj : Function.Surjective φ`. Introduce `y`.

Use `⟨y 0 / w 0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Use `fin_cases j`. Simplify using `[φ, hw0]`. Conclude with `⟨(LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun z => rfl⟩`.

Establish `: DiscreteTopology Λ` using `hdisc`. Establish `: IsZLattice ℝ Λ` using `⟨hspan⟩`. Use `set Λ' := ZLattice.comap ℝ Λ e.toLinearMap with hΛ'`. Establish `hrank : Module.finrank ℤ Λ' = 2`. Rewrite using `[ZLattice.rank ℝ Λ', Complex.finrank_real_complex]`.

Use `set b := Module.finBasisOfFinrankEq ℤ Λ' hrank with hb`. Use `set bR := b.ofZLatticeBasis ℝ Λ' with hbR`. Use `⟨⟨bR 0, bR 1, ?_⟩, fun z => ?_⟩` and prove the remaining obligations. Establish `hv : ![bR 0, bR 1] = ⇑bR`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `fin_cases i <;> rfl`. Rewrite using `[hv]`. Conclude with `bR.linearIndependent`. Establish `hr : ({bR 0, bR 1} : Set ℂ) = Set.range bR`. Use extensionality with `x`.

Simplify using `[Fin.exists_fin_two, eq_comm]`. Rewrite using `[PeriodPair.lattice]`. Simplify using `only`. Rewrite using `[hr, hbR, Module.Basis.ofZLatticeBasis_span, ← SetLike.mem_coe, hΛ', ZLattice.coe_comap]`. Simplify using `[he]`.
-/
theorem exists_periodPair_of_lattice_in_line :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (w : Fin g → ℂ), g = 1 → w ≠ 0 → DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∃ L : PeriodPair, ∀ z : ℂ, z ∈ L.lattice ↔ z • w ∈ Λ := by
  intro g Λ w hg hw hdisc hspan
  subst hg
  have hw0 : w 0 ≠ 0 := by
    intro h
    apply hw
    funext j
    fin_cases j
    simpa using h

  obtain ⟨e, he⟩ : ∃ e : ℂ ≃L[ℝ] (Fin 1 → ℂ), ∀ z, e z = z • w := by
    let φ : ℂ →ₗ[ℝ] (Fin 1 → ℂ) :=
      { toFun := fun z => z • w
        map_add' := fun a b => add_smul a b w
        map_smul' := fun r z => by
          simp only [RingHom.id_apply]
          exact smul_assoc r z w }
    have hinj : Function.Injective φ := fun a b h => smul_left_injective ℂ hw h
    have hsurj : Function.Surjective φ := by
      intro y
      refine ⟨y 0 / w 0, ?_⟩
      funext j
      fin_cases j
      simp [φ, hw0]
    exact ⟨(LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun z => rfl⟩

  have : DiscreteTopology Λ := hdisc
  have : IsZLattice ℝ Λ := ⟨hspan⟩
  set Λ' := ZLattice.comap ℝ Λ e.toLinearMap with hΛ'
  have hrank : Module.finrank ℤ Λ' = 2 := by
    rw [ZLattice.rank ℝ Λ', Complex.finrank_real_complex]
  set b := Module.finBasisOfFinrankEq ℤ Λ' hrank with hb
  set bR := b.ofZLatticeBasis ℝ Λ' with hbR
  refine ⟨⟨bR 0, bR 1, ?_⟩, fun z => ?_⟩
  · have hv : ![bR 0, bR 1] = ⇑bR := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact bR.linearIndependent
  · have hr : ({bR 0, bR 1} : Set ℂ) = Set.range bR := by
      ext x
      simp [Fin.exists_fin_two, eq_comm]
    rw [PeriodPair.lattice]
    dsimp only
    rw [hr, hbR, Module.Basis.ofZLatticeBasis_span, ← SetLike.mem_coe, hΛ', ZLattice.coe_comap]
    simp [he]

end GlobalTheory
