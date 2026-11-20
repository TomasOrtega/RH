import ReciprocityTheory.L2DbarEstimates.NormFibrations.NormFib
import ReciprocityTheory.L2DbarEstimates.NormFibrations.NormOrd
import ReciprocityTheory.L2DbarEstimates.SymmetricSections.NormVanishOfHoloSection

universe u

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem norm (n : ℕ) (M : Type u) [TopologicalSpace M] : NORMStatement n M := by
  intro z Δ u C m hΔ hcov himg hfin hconn hu hgr hvan
  have hpre : z ⁻¹' {y : V n | MvPolynomial.eval (fun i => y i) Δ ≠ 0} = Set.univ :=
    Set.eq_univ_of_forall himg
  have hz : IsLocalHomeomorph z := by
    have h := hcov.isLocalHomeomorphOn
    rw [hpre] at h
    exact isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.2 h
  obtain ⟨δ, hδ⟩ := normFib.{u} n M z _ hcov himg hfin hconn
  have hΔ0 : Norm.polyAt n Δ 0 ≠ 0 := by
    have h0 : Norm.polyAt n Δ 0 = MvPolynomial.constantCoeff Δ := by
      rw [← MvPolynomial.eval_zero]
      rfl
    rw [h0]
    exact hΔ
  funext x
  exact Norm.normVanish.{u} n M z Δ δ m C u hΔ0 hcov himg hδ hu hgr
    (fun x hx => normOrd.{u} n M z u x m hz hu (hvan x hx)) x

end ReciprocityTheory.L2DbarEstimates
