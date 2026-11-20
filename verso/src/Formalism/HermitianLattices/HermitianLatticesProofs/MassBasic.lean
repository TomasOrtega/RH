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
Simplify using `[Formalism.ThetaLiftIndependence.latLift, Formalism.ThetaLiftIndependence.latWt]`.
-/
theorem massBasic_sum_cast (h : V →ₗ⋆[K] V →ₗ[K] K)
    (s : Finset (Submodule (RingOfIntegers K) V)) :
    (((∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ : ℝ)) : ℂ) =
      Formalism.ThetaLiftIndependence.latLift h s (fun _ => 1) (fun _ => 1) := by
  simp [Formalism.ThetaLiftIndependence.latLift, Formalism.ThetaLiftIndependence.latWt]

/- English proof (translation)
Unfold `mass`. Rewrite using `[dif_pos hs]`.
-/
theorem massBasic_mass_eq (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (RingOfIntegers K) V)
    (hs : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s) :
    mass h L = ∑ M ∈ hs.choose, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ := by
  unfold mass
  rw [dif_pos hs]

/- English proof (translation)
Rewrite using `[genus, Set.mem_setOf_eq]`. Use `⟨hL, ?_⟩` and prove the remaining obligations. Introduce `p _`. Use `⟨1, (isom h).one_mem, ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Simplify using `[gmap]`.
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
Introduce `K V _ _ _ _ _ _ _ _ h hh hpos L hL`. Take `⟨hex, hwt, -⟩` from `Formalism.ThetaLiftIndependence.classRepsDefinite K V h hh hpos L hL`. Use `⟨hex, fun s hs => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[massBasic_mass_eq h L hex]`. Establish `e` using `Formalism.ThetaLiftIndependence.latLiftIndep K V h L (fun _ => 1) (fun _ => 1) (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _ hex.choose_spec hs`.

Rewrite `e` using `[← massBasic_sum_cast, ← massBasic_sum_cast]`. Conclude with `e` after adjusting the coercions. Rewrite using `[massBasic_mass_eq h L hex]`. Take `⟨hmem, huniq⟩` from `hex.choose_spec`. Take `⟨N, ⟨hN, -⟩, -⟩` from `huniq L (massBasic_self_mem_genus h L hL)`.

Apply `Finset.sum_pos` to reduce the goal to its premises. Introduce `M hM`. Take `⟨n, hn, hnw⟩` from `hwt M (hmem M hM)`. Establish `hc : Nat.card (Formalism.ThetaLiftIndependence.autL h M) = n`. Simplify using `only [Formalism.ThetaLiftIndependence.latWt] at hnw`.

Conclude with `inv_inj.mp hnw` after adjusting the coercions. Rewrite using `[hc]`. Conclude with `inv_pos.mpr (by exact_mod_cast hn)`. Conclude with `⟨N, hN⟩`.
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
