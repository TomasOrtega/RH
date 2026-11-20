import ReciprocityTheory.L2DbarEstimates.NormFibrations.NormFib
import ReciprocityTheory.L2DbarEstimates.NormFibrations.NormOrd
import ReciprocityTheory.L2DbarEstimates.SymmetricSections.NormVanishOfHoloSection

universe u

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

/- English proof (translation)
Introduce `z Δ u C m hΔ hcov himg hfin hconn hu hgr hvan`. Establish `hpre : z ⁻¹' {y : V n | MvPolynomial.eval (fun i => y i) Δ ≠ 0} = Set.univ` using `Set.eq_univ_of_forall himg`. Establish `hz : IsLocalHomeomorph z`. Establish `h` using `hcov.isLocalHomeomorphOn`. Rewrite `h` using `[hpre]`.

Conclude with `isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.2 h`. Take `⟨δ, hδ⟩` from `normFib.{u} n M z _ hcov himg hfin hconn`. Establish `hΔ0 : Norm.polyAt n Δ 0 ≠ 0`. Establish `h0 : Norm.polyAt n Δ 0 = MvPolynomial.constantCoeff Δ`. Rewrite using `[← MvPolynomial.eval_zero]`.

Both sides reduce to the same expression. Rewrite using `[h0]`. Conclude with `hΔ`. Use function extensionality and compare the values at `x`. Conclude with `Norm.normVanish.{u} n M z Δ δ m C u hΔ0 hcov himg hδ hu hgr (fun x hx => normOrd.{u} n M z u x m hz hu (hvan x hx)) x`.
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
