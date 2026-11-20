import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.StandardHermitianSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation

noncomputable section

namespace GlobalTheory.Equiv.StdSpace

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[SetLike.mem_coe, Submodule.mem_pi]`. Conclude with `⟨fun k a => Submodule.mem_one.1 (k a trivial), fun k a _ => Submodule.mem_one.2 (k a)⟩`.
-/
theorem coe_pi_one_eq_intVecs (n : ℕ) :
    ((Submodule.pi Set.univ (fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)) :
      Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.intVecs D n := by
  ext x
  rw [SetLike.mem_coe, Submodule.mem_pi]
  exact ⟨fun k a => Submodule.mem_one.1 (k a trivial), fun k a _ => Submodule.mem_one.2 (k a)⟩

/- English proof (translation)
Take `⟨-, -, hfg, hsp, -⟩` from `GlobalTheory.Member.latHat_eq_hat_and_gram D V`. Establish `key` using `(GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ hfg hsp).1`. Rewrite using `[← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, SetLike.coe_set_eq]`. Unfold `Bridge.hLat`. Rewrite using `[← Submodule.span_eq (GlobalTheory.Member.latC V)]`.

Use `congr 1`. Use extensionality with `x`. Rewrite using `[SetLike.mem_coe, ← key x, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, show ((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) = 1 from Subtype.ext inv_one]`. Use `show (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ _ ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ _`. Rewrite using `[Matrix.one_mulVec]`.

Conclude with `Iff.rfl`.
-/
theorem identityClassLattice_eq_selfDualFrameLattice (V : HSp D) : (Bridge.hLat V 1 : Set (Fin V.rank → D.host.E)) = L0c D V := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ hfg hsp).1
  rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, SetLike.coe_set_eq]
  unfold Bridge.hLat
  rw [← Submodule.span_eq (GlobalTheory.Member.latC V)]
  congr 1
  ext x
  rw [SetLike.mem_coe, ← key x, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq,
    show ((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) = 1 from Subtype.ext inv_one]
  show (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ _ ∈
    Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ _
  rw [Matrix.one_mulVec]
  exact Iff.rfl

/- English proof (translation)
Rewrite using `[← identityClassLattice_eq_selfDualFrameLattice, ← coe_pi_one_eq_intVecs, SetLike.coe_set_eq]`.
-/
theorem lattice_clause_iff (V : HSp D) :
    (Bridge.hLat V 1 = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)) ↔
      L0c D V = GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.intVecs D V.rank := by
  rw [← identityClassLattice_eq_selfDualFrameLattice, ← coe_pi_one_eq_intVecs, SetLike.coe_set_eq]

/- English proof (translation)
The claim follows from `and_congr Iff.rfl (lattice_clause_iff (Vc D i))`.
-/
theorem vStd_iff_isStdSpace (D : D7) (i : Fin D.R.m) :
    Formalism.IndefR.FWT.VStd D i ↔ GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.IsStdSpace (Vc D i) :=
  and_congr Iff.rfl (lattice_clause_iff (Vc D i))

/- English proof (translation)
Assemble the required witnesses or components as `⟨vStd_iff_isStdSpace D, forall_congr' (vStd_iff_isStdSpace D)⟩`.
-/
theorem vStd_equiv (D : D7) :
    (∀ i : Fin D.R.m, Formalism.IndefR.FWT.VStd D i ↔ GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.IsStdSpace (Vc D i)) ∧
      ((∀ i : Fin D.R.m, Formalism.IndefR.FWT.VStd D i) ↔ GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.VStd D) :=
  ⟨vStd_iff_isStdSpace D, forall_congr' (vStd_iff_isStdSpace D)⟩

end GlobalTheory.Equiv.StdSpace

end
