import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MatchUpProof

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F hC SF hTR c hE i`. Establish `hHE` using `hC.models.HE`. Unfold `RealDat.models_HE at hHE`. Take `⟨hinjE, hrngE, -⟩` from `hHE`. Establish `hHW` using `hC.models.HW`.

Unfold `RealDat.models_HW at hHW`. Take `⟨-, hrngW, -⟩` from `hHW i (sg0 D A)`. Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 hE`. Establish `hE' : TrCopy.partE R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) R.e0 SF c ≠ ⊥`. Use `(Submodule.ne_bot_iff _).2 ⟨R.HE.e x, Submodule.mem_inf.2 ⟨hx, ?_⟩, ?_⟩` and prove the remaining obligations.

Establish `hmem : R.HE.e x ∈ LinearMap.range R.HE.e` using `LinearMap.mem_range_self _ x`. Rewrite `hmem` using `[hrngE]`. Conclude with `hmem`. Introduce `h0`. Conclude with `hx0 (hinjE (h0.trans (map_zero R.HE.e).symm))`.

Establish `hW' : TrCopy.partW R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) (R.eWf i (sg0 D A)) SF c ≠ ⊥`. Introduce `hbot`. Apply `hE'` to reduce the goal to its premises. Apply `Submodule.rank_eq_zero.1` to reduce the goal to its premises. Rewrite using `[(hTR i).1 c]`.

Conclude with `Submodule.rank_eq_zero.2 hbot`. Take `⟨y, hy, hy0⟩` from `(Submodule.ne_bot_iff _).1 hW'`. Take `⟨hyF, hyG⟩` from `Submodule.mem_inf.1 hy`. Establish `hyR : y ∈ LinearMap.range (R.HW i (sg0 D A)).e`. Rewrite using `[hrngW]`.

Conclude with `(Submodule.mem_inf.1 hyG).1`. Take `⟨z, rfl⟩` from `hyR`. Use `(Submodule.ne_bot_iff _).2 ⟨z, ?_, ?_⟩` and prove the remaining obligations. Use `show (R.HW i (sg0 D A)).e z ∈ R.Wat i (sg0 D A) R.triv ⊓ _`. Conclude with `Submodule.mem_inf.2 ⟨hyG, hyF⟩`.

Introduce and unpack `rfl`. Conclude with `hy0 (map_zero _)`.
-/
theorem matchUp_of_tr : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ SF, GlobalTheory.TrCopy.TRLev R F SF → MatchUp R SF := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hTR c hE i

  have hHE := hC.models.HE
  unfold RealDat.models_HE at hHE
  obtain ⟨hinjE, hrngE, -⟩ := hHE

  have hHW := hC.models.HW
  unfold RealDat.models_HW at hHW
  obtain ⟨-, hrngW, -⟩ := hHW i (sg0 D A)

  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hE
  have hE' : TrCopy.partE R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv))
      (levChi _ (R.βY 0) (R.dat0 R.triv)) R.e0 SF c ≠ ⊥ := by
    refine (Submodule.ne_bot_iff _).2 ⟨R.HE.e x, Submodule.mem_inf.2 ⟨hx, ?_⟩, ?_⟩
    · have hmem : R.HE.e x ∈ LinearMap.range R.HE.e := LinearMap.mem_range_self _ x
      rw [hrngE] at hmem
      exact hmem
    · intro h0
      exact hx0 (hinjE (h0.trans (map_zero R.HE.e).symm))

  have hW' : TrCopy.partW R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) (R.eWf i (sg0 D A)) SF c ≠ ⊥ := by
    intro hbot
    apply hE'
    apply Submodule.rank_eq_zero.1
    rw [(hTR i).1 c]
    exact Submodule.rank_eq_zero.2 hbot

  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hW'
  obtain ⟨hyF, hyG⟩ := Submodule.mem_inf.1 hy
  have hyR : y ∈ LinearMap.range (R.HW i (sg0 D A)).e := by
    rw [hrngW]
    exact (Submodule.mem_inf.1 hyG).1
  obtain ⟨z, rfl⟩ := hyR
  refine (Submodule.ne_bot_iff _).2 ⟨z, ?_, ?_⟩
  · show (R.HW i (sg0 D A)).e z ∈ R.Wat i (sg0 D A) R.triv ⊓ _
    exact Submodule.mem_inf.2 ⟨hyG, hyF⟩
  · rintro rfl
    exact hy0 (map_zero _)

end GlobalTheory.MatchUpProof
