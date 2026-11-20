import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ThetaUnifAVOfLaws

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LatticeHom

/- English proof (translation)
Establish `hc : Continuous fun t : ℂ => (⟨t • z, hz t⟩ : Λ)` using `by fun_prop`. Establish `h` using `(IsLocallyConstant.iff_continuous _).2 hc |>.apply_eq_of_preconnectedSpace 1 0`. Simplify using `using congrArg Subtype.val h`.
-/
theorem eq_zero_of_forall_smul_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Λ : Submodule ℤ E) (hd : DiscreteTopology Λ) {z : E} (hz : ∀ t : ℂ, t • z ∈ Λ) : z = 0 := by
  have hc : Continuous fun t : ℂ => (⟨t • z, hz t⟩ : Λ) := by fun_prop
  have h := (IsLocallyConstant.iff_continuous _).2 hc |>.apply_eq_of_preconnectedSpace 1 0
  simpa using congrArg Subtype.val h

/- English proof (translation)
Take `⟨G, hG0, hGa, hGe⟩` from `hv g u.ex (fun U f => by simpa using u.hol U f) ((u.ker 0).2 u.Λ.zero_mem)`. Establish `hT` using `EndoLinear.fderiv_lifts v.ex v.ex_add v.Λ v.ker v.discrete u.ex u.ex_add G hG0 hGa.differentiableAt hGe`. Establish `hi : Function.Injective (fderiv ℂ G 0).toLinearMap`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`.

Use `eq_zero_of_forall_smul_mem u.Λ u.discrete fun t => ?_` and prove the remaining obligations. Establish `hz' : fderiv ℂ G 0 z = 0` using `hz`. Rewrite using `[← u.ker, ← hT, map_smul, hz', smul_zero]`. Conclude with `(v.ker 0).2 v.Λ.zero_mem`. Conclude with `⟨LinearEquiv.ofInjectiveEndo _ hi, hT⟩`.
-/
theorem exists_linearEquiv_of_lifting {A : Over (Sp ℂ)} [GrpObj A] {L L₁ : LB A.left} {g : ℕ}
    (u : HolUnif A L g) (v : HolUnif A L₁ g)
    (hv : ∀ (n : ℕ) (a : (Fin n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)), (∀ (U : A.left.Opens) (f : Γ(A.left, U)),
      IsOpen {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧
        DifferentiableOn ℂ (fun w => valAt' (a w).left U f)
          {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → a 0 = 1 →
      ∃ G : (Fin n → ℂ) → (Fin g → ℂ), G 0 = 0 ∧ AnalyticAt ℂ G 0 ∧ ∀ᶠ w in 𝓝 0, v.ex (G w) = a w) :
    ∃ T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, v.ex (T z) = u.ex z := by
  obtain ⟨G, hG0, hGa, hGe⟩ := hv g u.ex (fun U f => by simpa using u.hol U f)
    ((u.ker 0).2 u.Λ.zero_mem)
  have hT := EndoLinear.fderiv_lifts v.ex v.ex_add v.Λ v.ker v.discrete u.ex u.ex_add G hG0
    hGa.differentiableAt hGe
  have hi : Function.Injective (fderiv ℂ G 0).toLinearMap := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    refine eq_zero_of_forall_smul_mem u.Λ u.discrete fun t => ?_
    have hz' : fderiv ℂ G 0 z = 0 := hz
    rw [← u.ker, ← hT, map_smul, hz', smul_zero]
    exact (v.ker 0).2 v.Λ.zero_mem
  exact ⟨LinearEquiv.ofInjectiveEndo _ hi, hT⟩

/- English proof (translation)
Establish `hval` using `@valAt'_rules`. Establish `hvalaff` using `@existsUnique_point_of_ringHom`. Take `⟨v, -, hv⟩` from `@AbelianExp.exists_holUnif hmul hval (@holFamily_lift hval) (@isTopologicalGroup_complexPoints hval) (@PointsCompact.compactSpace_points_polAV hval hvalaff) (@HolChart.exists_holomorphic_chart hval hvalaff @exists_holomorphic_section_of_etale) P`. Take `⟨T, hT⟩` from `exists_linearEquiv_of_lifting u v hv`. Take `⟨T', hT'⟩` from `exists_linearEquiv_of_lifting u' v hv`.

Use `⟨T.trans T'.symm, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[← hT', ← hT]`. Simplify using the standard rewrite rules.
-/
theorem exists_linearEquiv_of_holUnif (hmul : Out.MulNSt) (P : Out.PolAV (Sp ℂ)) {L L' : LB P.A.left}
    (u : HolUnif P.A L P.g) (u' : HolUnif P.A L' P.g) :
    ∃ T : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u'.ex (T z) = u.ex z := by
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  obtain ⟨v, -, hv⟩ := @AbelianExp.exists_holUnif hmul hval (@holFamily_lift hval)
    (@isTopologicalGroup_complexPoints hval) (@PointsCompact.compactSpace_points_polAV hval hvalaff)
    (@HolChart.exists_holomorphic_chart hval hvalaff @exists_holomorphic_section_of_etale) P
  obtain ⟨T, hT⟩ := exists_linearEquiv_of_lifting u v hv
  obtain ⟨T', hT'⟩ := exists_linearEquiv_of_lifting u' v hv
  refine ⟨T.trans T'.symm, fun z => ?_⟩
  rw [← hT', ← hT]
  simp

end GlobalTheory.LatticeHom
