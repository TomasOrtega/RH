import Mathlib
import Formalism.HermitianLattices.StatementMass
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ClassRepsDefinite
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.LatLiftIndep
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic

open NumberField

noncomputable section

namespace Formalism.HermitianLatticesTheory

section MassBasicAux

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem massBasic_sum_cast (h : V →ₗ⋆[K] V →ₗ[K] K)
    (s : Finset (Submodule (RingOfIntegers K) V)) :
    (((∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ : ℝ)) : ℂ) =
      Formalism.ThetaLiftIndependence.latLift h s (fun _ => 1) (fun _ => 1) := by
  simp [Formalism.ThetaLiftIndependence.latLift, Formalism.ThetaLiftIndependence.latWt]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem massBasic_mass_eq (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (RingOfIntegers K) V)
    (hs : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s) :
    mass h L = ∑ M ∈ hs.choose, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ := by
  unfold mass
  rw [dif_pos hs]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules.
-/
theorem massBasic_self_mem_genus (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (RingOfIntegers K) V)
    (hL : Submodule.IsLattice K L) : L ∈ genus h L := by
  rw [genus, Set.mem_setOf_eq]
  refine ⟨hL, ?_⟩
  intro p _
  refine ⟨1, (isom h).one_mem, ?_⟩
  ext x
  simp [gmap]

end MassBasicAux

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem massBasic : MassBasic := by
  intro K V _ _ _ _ _ _ _ _ h hh hpos L hL
  obtain ⟨hex, hwt, -⟩ := Formalism.ThetaLiftIndependence.classRepsDefinite K V h hh hpos L hL
  refine ⟨hex, fun s hs => ?_, ?_⟩
  · rw [massBasic_mass_eq h L hex]
    have e := Formalism.ThetaLiftIndependence.latLiftIndep K V h L (fun _ => 1) (fun _ => 1)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _ hex.choose_spec hs
    rw [← massBasic_sum_cast, ← massBasic_sum_cast] at e
    exact_mod_cast e
  · rw [massBasic_mass_eq h L hex]
    obtain ⟨hmem, huniq⟩ := hex.choose_spec
    obtain ⟨N, ⟨hN, -⟩, -⟩ := huniq L (massBasic_self_mem_genus h L hL)
    apply Finset.sum_pos
    · intro M hM
      obtain ⟨n, hn, hnw⟩ := hwt M (hmem M hM)
      have hc : Nat.card (Formalism.ThetaLiftIndependence.autL h M) = n := by
        simp only [Formalism.ThetaLiftIndependence.latWt] at hnw
        exact_mod_cast inv_inj.mp hnw
      rw [hc]
      exact inv_pos.mpr (by exact_mod_cast hn)
    · exact ⟨N, hN⟩

end Formalism.HermitianLatticesTheory
