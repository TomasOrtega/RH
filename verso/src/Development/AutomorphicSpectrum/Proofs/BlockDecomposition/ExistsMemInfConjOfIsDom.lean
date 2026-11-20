import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Casselman

/- English proof (translation)
Introduce `G _ _ _ D t ht y hy`. Take `⟨c, hc, b, hb, a, ha, rfl⟩` from `D.fact_up y hy`. Establish `hb' : b ∈ D.J` using `(Subgroup.mem_inf.1 hb).1`. Establish `ha' : a ∈ D.J` using `(Subgroup.mem_inf.1 ha).1`. Establish `hbt : (t : G)⁻¹ * b * t ∈ D.J` using `(Subgroup.mem_inf.1 (ht.2.2 b hb).2).1`.

Establish `hat : (t : G)⁻¹ * a * t ∈ D.J` using `(Subgroup.mem_inf.1 (ht.2.1 a ha)).1`. Establish `he : c⁻¹ * (c * b * a) = b * a` using `by group`. Use `⟨c, hc, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[he]`. Conclude with `D.J.mul_mem hb' ha'`.

Rewrite using `[he, Subgroup.mem_map]`. Use `⟨((t : G)⁻¹ * b * t) * ((t : G)⁻¹ * a * t), D.J.mul_mem hbt hat, ?_⟩` and prove the remaining obligations. Simplify using `only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Use `group`.
-/
theorem exists_mem_inf_conj_of_isDom : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∀ y ∈ D.J,
      ∃ a ∈ D.J ⊓ D.N, a⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by
  intro G _ _ _ D t ht y hy
  obtain ⟨c, hc, b, hb, a, ha, rfl⟩ := D.fact_up y hy
  have hb' : b ∈ D.J := (Subgroup.mem_inf.1 hb).1
  have ha' : a ∈ D.J := (Subgroup.mem_inf.1 ha).1
  have hbt : (t : G)⁻¹ * b * t ∈ D.J := (Subgroup.mem_inf.1 (ht.2.2 b hb).2).1
  have hat : (t : G)⁻¹ * a * t ∈ D.J := (Subgroup.mem_inf.1 (ht.2.1 a ha)).1
  have he : c⁻¹ * (c * b * a) = b * a := by group
  refine ⟨c, hc, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
  · rw [he]
    exact D.J.mul_mem hb' ha'
  · rw [he, Subgroup.mem_map]
    refine ⟨((t : G)⁻¹ * b * t) * ((t : G)⁻¹ * a * t), D.J.mul_mem hbt hat, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end GlobalTheory.CompanionTheory.Casselman
