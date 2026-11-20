import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBoundLatLoc
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

/- English proof (translation)
Use `first`. Consider the case `(run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll]))`. Conclude with `@_root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc`. Consider the case `(run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll]))`. Conclude with `_root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc`.

Consider the case `exact @_root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc`. Consider the case `exact _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc`. Consider the case `(apply _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc <;> assumption)`. Consider the case `(intros; apply @_root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc <;> first | assumption | infer_instance)`.

Consider the case `(intros; exact _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc ..)`.
-/
theorem absFin_latLoc_le : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)),
    ∃ C : ℝ≥0, ∀ y ∈ latLoc F L v, ∀ i, absFin F v (y i) ≤ C := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc
  | exact @_root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc
  | exact _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc
  | (apply _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc ..)

/- English proof (translation)
The claim follows from `@absFin_latLoc_le`.
-/
example : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)), ∃ C : ℝ≥0, ∀ y ∈ latLoc F L v, ∀ i, absFin F v (y i) ≤ C := @absFin_latLoc_le

end GlobalTheory
