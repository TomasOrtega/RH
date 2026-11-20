import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWEigenpartEqRowsFullHeckeStatement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.OccW

/- English proof (translation)
Take `⟨H, chi⟩` from `L`. Simplify using `only at h`. Substitute `h` using the available equality. Unfold `LevelP.triv`. Use `congr 1`.

Use extensionality with `x`. Establish `hx : x = 1` using `Subtype.ext (Subgroup.mem_bot.mp x.2)`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules.
-/
theorem level_eq_trivial_of_subgroup_eq_bot {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {LL : Type} [CommRing LL]
    (L : LevelP Pg r LL) (h : L.H = ⊥) : L = LevelP.triv Pg r LL := by
  obtain ⟨H, chi⟩ := L
  simp only at h
  subst h
  unfold LevelP.triv
  congr 1
  ext x
  have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.mp x.2)
  subst hx
  simp

/- English proof (translation)
Apply `level_eq_trivial_of_subgroup_eq_bot` to reduce the goal to its premises. Use `show Subgroup.comap eG.symm.toMonoidHom ⊥ = ⊥`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem levPOf_bot {D : D7} {G K : Type} [Group G] [Field K] {Pg : Finset (Pl D.host.E)} {r : ℕ} (eG : G ≃* G0 Pg r)
    (σ : K →+* ℂ) (ψ : (⊥ : Subgroup G) →* Kˣ) : levPOf eG σ ⊥ ψ = LevelP.triv Pg r ℂ := by
  apply level_eq_trivial_of_subgroup_eq_bot
  show Subgroup.comap eG.symm.toMonoidHom ⊥ = ⊥
  ext x
  simp

end GlobalTheory.OccW

open GlobalTheory.OccW in

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F s hOk hCore hSchur hGood hCusp hMult SF hSF i c hW`. Establish `hdim` using `GlobalTheory.T.finrank_W_eigenpart_eq_rows_full_hecke R F hOk hCore hSchur hGood hCusp hMult SF hSF ⊥ 1 i c`. Rewrite `hdim` using `[inv_one, levPOf_bot]`. Establish `hWle : Wcc R SF i c ≤ (R.Wat i (sg0 D A) R.triv).comap (R.HW i _).e` using `Submodule.comap_mono inf_le_left`. Rewrite `hdim` using `[inf_eq_left.mpr hWle]`.

Introduce `hE`. Rewrite `hdim` using `[hE, bot_inf_eq, finrank_bot]`. Conclude with `hW (Submodule.finrank_eq_zero.mp hdim)`.
-/
theorem GlobalTheory.Hk3.eec_ne_bot_of_wcc_ne_bot : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → SchurAll R → GoodStable A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R → ∀ SF, IsSF R SF → ∀ i c, Wcc R SF i c ≠ ⊥ → EEc R SF c ≠ ⊥ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hCore hSchur hGood hCusp hMult SF hSF i c hW
  have hdim := GlobalTheory.T.finrank_W_eigenpart_eq_rows_full_hecke R F hOk hCore hSchur hGood hCusp hMult SF hSF ⊥ 1 i c
  rw [inv_one, levPOf_bot] at hdim
  have hWle : Wcc R SF i c ≤ (R.Wat i (sg0 D A) R.triv).comap (R.HW i _).e :=
    Submodule.comap_mono inf_le_left
  rw [inf_eq_left.mpr hWle] at hdim
  intro hE
  rw [hE, bot_inf_eq, finrank_bot] at hdim
  exact hW (Submodule.finrank_eq_zero.mp hdim)
