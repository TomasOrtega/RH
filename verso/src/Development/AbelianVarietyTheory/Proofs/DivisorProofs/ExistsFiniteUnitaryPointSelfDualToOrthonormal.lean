import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryMovesSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCompletionComapRationalMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnLatticeComapEqStandardLattice

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefTransfer.LatMove

open scoped Matrix

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i`. Proceed by induction on `h using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, x, hx, rfl⟩` from `hy`.

Take `⟨r, hr⟩` from `Submodule.mem_one.1 (hx i trivial)`. Conclude with `AddSubgroup.subset_closure ⟨a, ha, r, congrArg (fun t => a ⊗ₜ[D.host.F] t) hr.symm⟩`. Consider the case `zero => exact zero_mem _`. Consider the case `add y z _ _ hy hz => exact add_mem hy hz`. Consider the case `neg y _ hy => exact neg_mem hy`.

Introduce `h`. Rewrite using `[← Finset.univ_sum_single z]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Establish `hi` using `h i`. Generalize the expression as in `z i = c at hi`.

Proceed by induction on `hi using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, x, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), fun j _ => ?_, funext fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.single_apply] split_ifs exacts [Submodule.mem_one.2 ⟨x, rfl⟩, zero_mem _]`.

Rewrite using `[Pi.single_apply, Pi.single_apply] split_ifs exacts [rfl, (TensorProduct.tmul_zero _ _).symm]`. Consider the case `zero => rw [Pi.single_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [Pi.single_add]`. Conclude with `add_mem hy hz`.

Consider the case `neg y _ hy => rw [Pi.single_neg]`. Conclude with `neg_mem hy`.
-/
theorem mem_hat_stdLat_iff {D : D7} {n : ℕ} (z : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.stdLat D.host.E n : Set (Fin n → D.host.E)) ↔ IntVec z := by
  constructor
  · intro h i
    induction h using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hx i trivial)
      exact AddSubgroup.subset_closure ⟨a, ha, r, congrArg (fun t => a ⊗ₜ[D.host.F] t) hr.symm⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro h
    rw [← Finset.univ_sum_single z]
    refine sum_mem fun i _ => ?_
    have hi := h i
    generalize z i = c at hi
    induction hi using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), fun j _ => ?_, funext fun j => ?_⟩
      · rw [Pi.single_apply]
        split_ifs
        exacts [Submodule.mem_one.2 ⟨x, rfl⟩, zero_mem _]
      · rw [Pi.single_apply, Pi.single_apply]
        split_ifs
        exacts [rfl, (TensorProduct.tmul_zero _ _).symm]
    | zero => rw [Pi.single_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
    | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy

/- English proof (translation)
Establish `ew : GlobalTheory.UnRep.fm D.host.F B.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w) = w`. Rewrite using `[Matrix.mulVec_mulVec, ← GlobalTheory.HatPullback.fm_mul', Units.mul_inv, GlobalTheory.HatPullback.fm_one', Matrix.one_mulVec]`. Establish `h1` using `GlobalTheory.HatPullback.main D.host.F D.host.E n B (Formalism.L2.DIV.colLat B) (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w)`. Rewrite `h1` using `[ew, GlobalTheory.ColStd.colLat_comap_eq_stdLat]`. Conclude with `h1.trans (mem_hat_stdLat_iff _)`.
-/
theorem mem_hat_colLat_iff {D : D7} {n : ℕ} (B : GL (Fin n) D.host.E)
    (w : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    w ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.DIV.colLat B : Set (Fin n → D.host.E)) ↔
      IntVec (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w) := by
  have ew : GlobalTheory.UnRep.fm D.host.F B.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, ← GlobalTheory.HatPullback.fm_mul', Units.mul_inv, GlobalTheory.HatPullback.fm_one', Matrix.one_mulVec]
  have h1 := GlobalTheory.HatPullback.main D.host.F D.host.E n B (Formalism.L2.DIV.colLat B) (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w)
  rw [ew, GlobalTheory.ColStd.colLat_comap_eq_stdLat] at h1
  exact h1.trans (mem_hat_stdLat_iff _)

/- English proof (translation)
Rewrite using `[GlobalTheory.GenusTranslate.hatL_iff]`. Simplify using `only [AlgEquiv.symm_apply_apply]`.
-/
theorem swap_mem_hatL_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (u : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E) :
    (fun i => Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (u i)) ∈ Formalism.L2.Herm.hatL (F := F) L ↔
      u ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
  rw [GlobalTheory.GenusTranslate.hatL_iff]
  simp only [AlgEquiv.symm_apply_apply]

/- English proof (translation)
Take `⟨x, hx, h⟩` from `GlobalTheory.GenusTranslate.exists_move_colLat D V B _ hB (GlobalTheory.PlaceModel.isSelfDualC_latFrame V)`. Use `⟨x, hx, fun w => ?_⟩` and prove the remaining obligations. Establish `h1` using `h fun i => Formalism.IndefR.Lev.swapAE D (w i)`. Establish `h2 : (Formalism.IndefR.Lev.finE V x).1 *ᵥ (fun i => Formalism.IndefR.Lev.swapAE D (w i)) = fun i => Formalism.IndefR.Lev.swapAE D (((finHom V x).1 *ᵥ w) i)`. Use function extensionality and compare the values at `fun i => (RingHom.map_mulVec (Formalism.IndefR.Lev.swapAE D) (finHom V x).1 w i).symm`.

Rewrite `h1` using `[h2]`. Conclude with `(swap_mem_hatL_iff _ w).symm.trans (h1.trans (swap_mem_hatL_iff _ ((finHom V x).1 *ᵥ w)))`.
-/
theorem exists_move {D : D7} (V : HSp D) (B : GL (Fin V.rank) D.host.E)
    (hB : cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * V.gram * B.1 = 1) :
    ∃ x ∈ GfC V, ∀ w, w ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.DIV.colLat B : Set (Fin V.rank → D.host.E)) ↔
      (finHom V x).1 *ᵥ w ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.PlaceModel.latFrame V : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨x, hx, h⟩ := GlobalTheory.GenusTranslate.exists_move_colLat D V B _ hB (GlobalTheory.PlaceModel.isSelfDualC_latFrame V)
  refine ⟨x, hx, fun w => ?_⟩
  have h1 := h fun i => Formalism.IndefR.Lev.swapAE D (w i)
  have h2 : (Formalism.IndefR.Lev.finE V x).1 *ᵥ (fun i => Formalism.IndefR.Lev.swapAE D (w i)) =
      fun i => Formalism.IndefR.Lev.swapAE D (((finHom V x).1 *ᵥ w) i) :=
    funext fun i => (RingHom.map_mulVec (Formalism.IndefR.Lev.swapAE D) (finHom V x).1 w i).symm
  rw [h2] at h1
  exact (swap_mem_hatL_iff _ w).symm.trans (h1.trans (swap_mem_hatL_iff _ ((finHom V x).1 *ᵥ w)))

/- English proof (translation)
Introduce `D _ V M hM`. Establish `hu : IsUnit M` using `(Matrix.isUnit_iff_isUnit_det M).2 (Matrix.isUnit_det_of_left_inverse hM)`. Take `⟨B, rfl⟩` from `hu`. Take `⟨x, hx, h⟩` from `exists_move V B hM`. Use `⟨x⁻¹, inv_mem hx, fun y => ?_⟩` and prove the remaining obligations.

Establish `hL : L0c D V = (GlobalTheory.PlaceModel.latFrame V : Set (Fin V.rank → D.host.E))` using `Set.ext fun z => (GlobalTheory.PlaceModel.mem_latFrame V z).symm`. Establish `h1` using `h ((finHom V x⁻¹).1 *ᵥ y)`. Rewrite `h1` using `[Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec, mem_hat_colLat_iff, Matrix.coe_units_inv]`. Rewrite using `[hL]`. Conclude with `h1.symm`.
-/
theorem exists_finite_point : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 →
    ∃ h₀ ∈ GfC V, ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y)) := by
  intro D _ V M hM
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (Matrix.isUnit_det_of_left_inverse hM)
  obtain ⟨B, rfl⟩ := hu
  obtain ⟨x, hx, h⟩ := exists_move V B hM
  refine ⟨x⁻¹, inv_mem hx, fun y => ?_⟩
  have hL : L0c D V = (GlobalTheory.PlaceModel.latFrame V : Set (Fin V.rank → D.host.E)) :=
    Set.ext fun z => (GlobalTheory.PlaceModel.mem_latFrame V z).symm
  have h1 := h ((finHom V x⁻¹).1 *ᵥ y)
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec,
    mem_hat_colLat_iff, Matrix.coe_units_inv] at h1
  rw [hL]
  exact h1.symm

end GlobalTheory.DefTransfer.LatMove
