import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverseStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfIntUp

/- English proof (translation)
Establish `he : ∀ c : k, q.sec c = q.e * q.sec c` using `fun c => by rw [← q.sec_pr, q.pr_sec]`. Establish `h1 : q.sec (a * b) = q.e * (q.sec a * q.sec b)`. Rewrite using `[← q.sec_pr, map_mul q.pr, q.pr_sec, q.pr_sec]`. Rewrite using `[h1, ← mul_assoc, ← he]`.
-/
theorem sec_mul' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (a b : k) : q.sec (a * b) = q.sec a * q.sec b := by

  have he : ∀ c : k, q.sec c = q.e * q.sec c := fun c => by rw [← q.sec_pr, q.pr_sec]
  have h1 : q.sec (a * b) = q.e * (q.sec a * q.sec b) := by
    rw [← q.sec_pr, map_mul q.pr, q.pr_sec, q.pr_sec]
  rw [h1, ← mul_assoc, ← he]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `he : q.sec (z j) = q.e * q.sec (z j)` using `by rw [← q.sec_pr, q.pr_sec]`. Rewrite using `[sec_mul', q.sec_pr]`.

Use `conv_lhs => rw [he]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma mulVec_sec_eq_sec_mulVec {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {m n : Type} [Fintype n]
    (u : Matrix m n (AE D)) (z : n → k) :
    u *ᵥ (fun j => q.sec (z j)) = fun i => q.sec ((u.map q.pr *ᵥ z) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have he : q.sec (z j) = q.e * q.sec (z j) := by rw [← q.sec_pr, q.pr_sec]
  rw [sec_mul', q.sec_pr]
  conv_lhs => rw [he]
  ring

/- English proof (translation)
Introduce `D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT LS LT hSd _ hS hT u hu hh`. Use `⟨(ofSplit q).down FS FT u, ?_, (GlobalTheory.LocMod.Witness.up_down (ofSplit q) FS FT hh).symm⟩` and prove the remaining obligations. Introduce `r s`. Establish `hz : (fun i => q.sec ((FS.β *ᵥ Pi.single s 1) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)`. Use `(hS (Pi.single s 1)).1 fun i => ?_` and prove the remaining obligations.

Break down `eq_or_ne i s with rfl | h` into its components or cases. Rewrite using `[Pi.single_eq_same]`. Conclude with `one_mem _`. Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `zero_mem _`.

Establish `hmem` using `GlobalTheory.FinPl.LatMem.latO_maps hSd hu hz`. Rewrite `hmem` using `[hU.2 T LT, mulVec_sec_eq_sec_mulVec q u (FS.β *ᵥ Pi.single s 1)]`. Establish `hcol : FT.β *ᵥ (fun r => (ofSplit q).down FS FT u r s) = (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr *ᵥ (FS.β *ᵥ Pi.single s 1)`. Establish `e1 : (fun r => (ofSplit q).down FS FT u r s) = (ofSplit q).down FS FT u *ᵥ Pi.single s 1`. Use function extensionality and compare the values at `r`.

Simplify using `[Matrix.mulVec_single]`. Rewrite using `[e1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Use `congr 1`. Simplify using `only [GlobalTheory.LocMod.Place.down, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul]`. Both sides reduce to the same expression.

Establish `hin : (fun i => q.sec ((FT.β *ᵥ (fun r => (ofSplit q).down FS FT u r s)) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)`. Rewrite using `[hcol]`. Conclude with `hmem`. Conclude with `(hT _).2 hin r`.
-/
theorem exists_int_up : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ u : WO S T, u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) → IsHalf q.e u → ∃ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) ∧ u = (ofSplit q).up FS FT x := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT LS LT hSd _ hS hT u hu hh
  refine ⟨(ofSplit q).down FS FT u, ?_, (GlobalTheory.LocMod.Witness.up_down (ofSplit q) FS FT hh).symm⟩
  intro r s

  have hz : (fun i => q.sec ((FS.β *ᵥ Pi.single s 1) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v) := by
    refine (hS (Pi.single s 1)).1 fun i => ?_
    rcases eq_or_ne i s with rfl | h
    · rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _

  have hmem := GlobalTheory.FinPl.LatMem.latO_maps hSd hu hz
  rw [hU.2 T LT, mulVec_sec_eq_sec_mulVec q u (FS.β *ᵥ Pi.single s 1)] at hmem

  have hcol : FT.β *ᵥ (fun r => (ofSplit q).down FS FT u r s) =
      (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr *ᵥ (FS.β *ᵥ Pi.single s 1) := by
    have e1 : (fun r => (ofSplit q).down FS FT u r s) = (ofSplit q).down FS FT u *ᵥ Pi.single s 1 := by
      funext r; simp [Matrix.mulVec_single]
    rw [e1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    simp only [GlobalTheory.LocMod.Place.down, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul]
    rfl
  have hin : (fun i => q.sec ((FT.β *ᵥ (fun r => (ofSplit q).down FS FT u r s)) i)) ∈
      GlobalTheory.FinPl.latV T LT (· = q.v) := by
    rw [hcol]; exact hmem
  exact (hT _).2 hin r

end GlobalTheory.HalfIntUp
