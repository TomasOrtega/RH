import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.VB

set_option autoImplicit false

open GlobalTheory.Twist (resM resM_resM) in

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem eq_zero_of_forall_hom_app_eq_zero (X : Scheme.{0}) [IsAffine X] (F : X.Modules) (r : ℕ)
    (hF : GlobalTheory.VB.IsVB F r) (z : Γ(F, ⊤))
    (H : ∀ L : F ⟶ GlobalTheory.structureModule X, L.app ⊤ z = 0) : z = 0 := by
  haveI := hF.dual.isQuasicoherent
  have key : ∀ x : X, ∃ f : Γ(X, ⊤), x ∈ X.basicOpen f ∧ resM F (X.basicOpen_le f) z = 0 := by
    intro x
    obtain ⟨U, e, hxU, he⟩ := hF x
    obtain ⟨f, hfU, hxf⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨x, hxU⟩ (by trivial)
    refine ⟨f, hxf, ?_⟩
    classical
    have hqs : IsQuasiSeparated ((⊤ : X.Opens) : Set X) := by
      simpa using (isQuasiSeparated_univ (α := X))
    have hext : ∀ i, ∃ (n : ℕ) (t : Γ(dual F, ⊤)),
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n • resM (dual F) hfU (he.coord i) =
          (dual F).presheaf.map (homOfLE (X.basicOpen_le f)).op t := fun i =>
      QCoh.exists_pow_res_smul_eq_res_of_qcqs (dual F) (U := ⊤) (by simpa using isCompact_univ)
        hqs f _
    choose n t ht using hext
    have hc : ∀ i, (he.basis hfU).repr (resM F (X.basicOpen_le f) z) i = 0 := by
      intro i
      have h1 : dualApp (t i) le_top z = 0 := H (homGlobalEquiv F _ (t i))
      have h2 : dualApp (resM (dual F) (X.basicOpen_le f) (t i)) le_rfl
          (resM F (X.basicOpen_le f) z) = 0 := by
        have h4 := dualApp_resM (t i) (le_top : (⊤ : X.Opens) ≤ ⊤) (X.basicOpen_le f) z
        rw [h1, map_zero] at h4
        rw [dualApp_res]
        exact h4
      have h3 := ht i
      change _ = resM (dual F) (X.basicOpen_le f) (t i) at h3
      rw [← h3, dualApp_smul, LinearMap.smul_apply, dualApp_res, IsFrame.dualApp_coord,
        GlobalTheory.LB.resG_self] at h2
      have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n i) :=
        (QCoh.isUnit_res_of_le_basicOpen f (X.basicOpen_le f) le_rfl).pow _
      exact (hu.smul_eq_zero).1 h2
    exact (he.basis hfU).repr.map_eq_zero_iff.1 (Finsupp.ext hc)
  choose f hxf hf using key
  refine QCoh.section_eq_of_cover F (fun x => X.basicOpen (f x)) (fun x => X.basicOpen_le (f x))
    (fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxf x⟩) z 0 fun x => ?_
  exact (hf x).trans (map_zero _).symm

end GlobalTheory.VB
