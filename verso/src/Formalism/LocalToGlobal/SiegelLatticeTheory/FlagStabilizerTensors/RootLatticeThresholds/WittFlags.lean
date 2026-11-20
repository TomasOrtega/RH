import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.WittFlags

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.gmap`. Rewrite using `[← Submodule.map_comp]`. Both sides reduce to the same expression.
-/
theorem gmap_mul (a b : V ≃ₗ[K] V) (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  rfl

/- English proof (translation)
Use extensionality with `x`. Simplify using `[Formalism.HermitianLatticesTheory.gmap]`.
-/
theorem gmap_one (L : Submodule R V) : Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) L = L := by
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

/- English proof (translation)
Rewrite using `[← gmap_mul, inv_mul_cancel, gmap_one]`.
-/
theorem gmap_inv_gmap (a : V ≃ₗ[K] V) (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap a⁻¹ (Formalism.HermitianLatticesTheory.gmap a L) = L := by
  rw [← gmap_mul, inv_mul_cancel, gmap_one]

/- English proof (translation)
Rewrite using `[← gmap_mul, mul_inv_cancel, gmap_one]`.
-/
theorem gmap_gmap_inv (a : V ≃ₗ[K] V) (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap a⁻¹ L) = L := by
  rw [← gmap_mul, mul_inv_cancel, gmap_one]

end Gen

/- English proof (translation)
Introduce `β hβ Λ`. Take `⟨-, hloc, -, hU, hLat⟩` from `Formalism.HermitianLatticesTheory.isomAct _ _ _ (VS D).hT β hβ Λ`. Use `⟨fun hΛ => ?_, hLat.2, hU.2⟩` and prove the remaining obligations. Simplify using `only [Formalism.HermitianLatticesTheory.genus, Set.mem_setOf_eq] at hΛ ⊢`. Take `⟨hΛL, hΛG⟩` from `hΛ`.

Use `⟨hLat.2 hΛL, fun p hp => ?_⟩` and prove the remaining obligations. Take `⟨g, hg, hgΛ⟩` from `hΛG p hp`. Use `⟨β * g, (Formalism.HermitianLatticesTheory.isom _).mul_mem hβ hg, ?_⟩` and prove the remaining obligations. Rewrite using `[gmap_mul, hgΛ, hloc p]`.
-/
theorem LatIso_holds (D : D7) : Formalism.L2.SG.TermTieOf.LatIso D := by
  intro β hβ Λ
  obtain ⟨-, hloc, -, hU, hLat⟩ := Formalism.HermitianLatticesTheory.isomAct _ _ _ (VS D).hT β hβ Λ
  refine ⟨fun hΛ => ?_, hLat.2, hU.2⟩
  simp only [Formalism.HermitianLatticesTheory.genus, Set.mem_setOf_eq] at hΛ ⊢
  obtain ⟨hΛL, hΛG⟩ := hΛ
  refine ⟨hLat.2 hΛL, fun p hp => ?_⟩
  obtain ⟨g, hg, hgΛ⟩ := hΛG p hp
  refine ⟨β * g, (Formalism.HermitianLatticesTheory.isom _).mul_mem hβ hg, ?_⟩
  rw [gmap_mul, hgΛ, hloc p]

end Formalism.L2.SG.Pf.WittFlags
