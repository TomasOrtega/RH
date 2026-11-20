import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeEigenfunctionOfLiftableElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEquivarianceWeilModel

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F hC _ i x`. Establish `hW` using `hC.models.HW`. Establish `hg` using `hC.models.gW`. Establish `hl` using `GlobalTheory.GalLift.Transl.lifts R i hC.lev`. Establish `hx : (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A)` using `(hW i _).2.1.le (LinearMap.mem_range_self _ x)`.

Establish `hm` using `(GlobalTheory.MultMem.mem_mult_iff ..).1 hx`. Establish `hT` using `GlobalTheory.GalLift.Transl.hasType R i hW (sg0 D A) x`. Establish `hsum : (∑ g, RealDat.eC (A` using `A) (sg0 D A) g • R.gW i (sg0 D A) g x) = eH R i x := by`. Simplify using `[eH, LinearMap.sum_apply]`. Establish `hproj : eH R i x = x ↔ ∀ v, R.eWf i (sg0 D A) ((R.HW i (sg0 D A)).e x v) = (R.HW i (sg0 D A)).e x v`.

Prove the components needed by the constructor for the conclusion. Introduce `h v`. Rewrite using `[GlobalTheory.GalLift.Transl.proj R i hg, hsum, h]`. Introduce `h`. Apply `(hW i _).1` to reduce the goal to its premises.

Use extensionality with `v : 1`. Rewrite using `[← h v, GlobalTheory.GalLift.Transl.proj R i hg, hsum]`. Unfold `RealDat.Wat`. Rewrite using `[mem_goodPart, GlobalTheory.MultMem.mem_mult_iff, hproj]`. Establish `hmem : ∀ p : F.P0, R.eG p ∈ (R.levL F false (sg0 D A)).H` using `fun p => by show R.eG.symm (R.eG p) ∈ F.P0`.

Rewrite using `[MulEquiv.symm_apply_apply]`. Conclude with `p.2`. Establish `hchi : ∀ p : F.P0, (((R.levL F false (sg0 D A)).chi ⟨R.eG p, hmem p⟩ : ℂˣ) : ℂ) = sg0 D A ((F.ψ0⁻¹ p : D.what₂.LLˣ) : D.what₂.LL)` using `fun p => by show sg0 D A ((F.ψ0⁻¹ ⟨R.eG.symm (R.eG p), _⟩ : D.what₂.LLˣ) : D.what₂.LL) = _`. Use `congr 4`. Conclude with `R.eG.symm_apply_apply _`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨h2, fun p => ?_⟩` and prove the remaining obligations. Apply `(hW i _).1` to reduce the goal to its premises. Rewrite using `[hg, map_smul]`.

Use extensionality with `v h`. Establish `h3` using `GlobalTheory.LevelRows.levelType_eigenfunction_of_liftable_element (V := Wc D i) (β := R.βW i) (L := R.datWp i R.triv) (P := R.levL F false (sg0 D A)) (F := (R.HW i (sg0 D A)).e x v) (fun κ hκ h => h1.lev v κ hκ h) ⟨R.eG p, hmem p⟩ (hl _)`. Conclude with `(congrFun h3 h).trans (congrArg (· * (R.HW i (sg0 D A)).e x v h) (hchi p))`. Introduce and unpack `⟨h2, h⟩`. Use `⟨⟨hm.aut, hm.cusp, fun v => ?_, hm.equiv, hm.cont⟩, h2⟩` and prove the remaining obligations.

Establish `hP : IsPLevel (Wc D i) (R.βW i) (R.datWp i R.triv) (R.levL F false (sg0 D A)) ((R.HW i (sg0 D A)).e x v)`. Use `⟨hT v, fun p => ?_⟩` and prove the remaining obligations. Establish `hp : R.eG.symm p.1 ∈ F.P0` using `p.2`. Establish `h4` using `congrArg (fun z => (R.HW i (sg0 D A)).e z v) (h ⟨R.eG.symm p.1, hp⟩)`. Simplify using `only [hg _ _ _ x, map_smul] at h4`.

Establish `h5 : R.eG (R.eG.symm p.1) = p.1` using `R.eG.apply_symm_apply p.1`. Rewrite `h4` using `[h5]`. Conclude with `h4`. Conclude with `fun κ hκ y => hP.hasType κ hκ y`.
-/
theorem goodForms_baseLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ i (x : (R.HW i (sg0 D A)).H), (R.HW i _).e x ∈ R.Wat i (sg0 D A) (R.levL F false (sg0 D A)) ↔ eH R i x = x ∧ ∀ p : F.P0, R.gW i (sg0 D A) p x = sg0 D A ((F.ψ0⁻¹ p : D.what₂.LLˣ) : D.what₂.LL) • x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC _ i x
  have hW := hC.models.HW
  have hg := hC.models.gW
  have hl := GlobalTheory.GalLift.Transl.lifts R i hC.lev
  have hx : (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := (hW i _).2.1.le (LinearMap.mem_range_self _ x)
  have hm := (GlobalTheory.MultMem.mem_mult_iff ..).1 hx
  have hT := GlobalTheory.GalLift.Transl.hasType R i hW (sg0 D A) x
  have hsum : (∑ g, RealDat.eC (A := A) (sg0 D A) g • R.gW i (sg0 D A) g x) = eH R i x := by
    simp [eH, LinearMap.sum_apply]
  have hproj : eH R i x = x ↔ ∀ v, R.eWf i (sg0 D A) ((R.HW i (sg0 D A)).e x v) = (R.HW i (sg0 D A)).e x v := by
    constructor
    · intro h v
      rw [GlobalTheory.GalLift.Transl.proj R i hg, hsum, h]
    · intro h
      apply (hW i _).1
      ext v : 1
      rw [← h v, GlobalTheory.GalLift.Transl.proj R i hg, hsum]
  unfold RealDat.Wat
  rw [mem_goodPart, GlobalTheory.MultMem.mem_mult_iff, hproj]
  have hmem : ∀ p : F.P0, R.eG p ∈ (R.levL F false (sg0 D A)).H := fun p => by
    show R.eG.symm (R.eG p) ∈ F.P0
    rw [MulEquiv.symm_apply_apply]; exact p.2
  have hchi : ∀ p : F.P0, (((R.levL F false (sg0 D A)).chi ⟨R.eG p, hmem p⟩ : ℂˣ) : ℂ) =
      sg0 D A ((F.ψ0⁻¹ p : D.what₂.LLˣ) : D.what₂.LL) := fun p => by
    show sg0 D A ((F.ψ0⁻¹ ⟨R.eG.symm (R.eG p), _⟩ : D.what₂.LLˣ) : D.what₂.LL) = _
    congr 4
    exact R.eG.symm_apply_apply _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun p => ?_⟩
    apply (hW i _).1
    rw [hg, map_smul]
    ext v h
    have h3 := GlobalTheory.LevelRows.levelType_eigenfunction_of_liftable_element (V := Wc D i) (β := R.βW i) (L := R.datWp i R.triv)
      (P := R.levL F false (sg0 D A)) (F := (R.HW i (sg0 D A)).e x v) (fun κ hκ h => h1.lev v κ hκ h) ⟨R.eG p, hmem p⟩ (hl _)
    exact (congrFun h3 h).trans (congrArg (· * (R.HW i (sg0 D A)).e x v h) (hchi p))
  · rintro ⟨h2, h⟩
    refine ⟨⟨hm.aut, hm.cusp, fun v => ?_, hm.equiv, hm.cont⟩, h2⟩
    have hP : IsPLevel (Wc D i) (R.βW i) (R.datWp i R.triv) (R.levL F false (sg0 D A)) ((R.HW i (sg0 D A)).e x v) := by
      refine ⟨hT v, fun p => ?_⟩
      have hp : R.eG.symm p.1 ∈ F.P0 := p.2
      have h4 := congrArg (fun z => (R.HW i (sg0 D A)).e z v) (h ⟨R.eG.symm p.1, hp⟩)
      simp only [hg _ _ _ x, map_smul] at h4
      have h5 : R.eG (R.eG.symm p.1) = p.1 := R.eG.apply_symm_apply p.1
      rw [h5] at h4
      exact h4
    exact fun κ hκ y => hP.hasType κ hκ y

end GlobalTheory.Hk3

end
