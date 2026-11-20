import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CrysWD

/- English proof (translation)
Set `M : G →* Matrix (Fin a) (Fin a) ↥L.1` to `{ toFun := fun g => Matrix.of fun i j => ⟨_, hL g i j⟩ map_one' := by`. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, map_one, Units.val_one, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> rfl`. Use the proof step `map_mul' := fun g h => by`.

Use extensionality with `i j`. Simplify using `[Matrix.mul_apply] }`. Use `⟨M.toHomUnits, ?_, ?_⟩` and prove the remaining obligations. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Conclude with `Continuous.subtype_mk ((continuous_apply j).comp ((continuous_apply i).comp hr)) _`.

Use extensionality with `g i j`. Both sides reduce to the same expression.
-/
theorem exists_descent {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] {a : ℕ}
    (r : G →* Matrix.GeneralLinearGroup (Fin a) (Om l))
    (hr : Continuous (fun g => ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) :
      Matrix (Fin a) (Fin a) (Om l))))
    (L : FinExt l)
    (hL : ∀ g i j, ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) :
      Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1) :
    ∃ ρ : G →* Matrix.GeneralLinearGroup (Fin a) ↥L.1,
      Continuous (fun g => ((ρ g : Matrix.GeneralLinearGroup (Fin a) ↥L.1) :
        Matrix (Fin a) (Fin a) ↥L.1)) ∧
      mapRep (algebraMap ↥L.1 (Om l)) ρ = r := by
  let M : G →* Matrix (Fin a) (Fin a) ↥L.1 :=
    { toFun := fun g => Matrix.of fun i j => ⟨_, hL g i j⟩
      map_one' := by
        ext i j
        simp only [Matrix.of_apply, map_one, Units.val_one, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := fun g h => by
        ext i j
        simp [Matrix.mul_apply] }
  refine ⟨M.toHomUnits, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact Continuous.subtype_mk ((continuous_apply j).comp ((continuous_apply i).comp hr)) _
  · ext g i j
    rfl

/- English proof (translation)
Introduce `i a r w hw hr`. Use `⟨fun hc => ?_, fun h => (D.naut.wdOf_unrL i r w hw hr h.1).1 h.2⟩` and prove the remaining obligations. It suffices to establish `hd : D.naut.IsdRW i r w from ⟨hd, (D.naut.wdOf_unrL i r w hw hr hd).2 hc⟩`. Use `D.nd.lPrime i` as an intermediate fact. Take `⟨L, hle, hL⟩` from `GlobalTheory.T.compactGroup_rep_defined_over_finite_extension (D.nd.l i) _ a r hr (D.nbr i w hw).LL`.

Take `⟨ρ, hρ, rfl⟩` from `exists_descent r hr L hL`. Take `⟨h1, h2, -⟩` from `(D.loc_tie i w hw).2.2 L hle a ρ hρ`. Use `L.2` as an intermediate fact. Establish `h3` using `(GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT (D.nd.l i)) _ L _ _ (h1.1 hc)).1`. Use `h2.2 ?_` and prove the remaining obligations.

Unfold `IsDR at h3`. Unfold `LocBridge.IsdRE`. Simplify using `using h3`.
-/
theorem crysIffWD (D : D7) : CrysIffWD D.nd D.naut := by
  intro i a r w hw hr
  refine ⟨fun hc => ?_, fun h => (D.naut.wdOf_unrL i r w hw hr h.1).1 h.2⟩
  suffices hd : D.naut.IsdRW i r w from ⟨hd, (D.naut.wdOf_unrL i r w hw hr hd).2 hc⟩
  have := D.nd.lPrime i
  obtain ⟨L, hle, hL⟩ := GlobalTheory.T.compactGroup_rep_defined_over_finite_extension (D.nd.l i) _ a r hr (D.nbr i w hw).LL
  obtain ⟨ρ, hρ, rfl⟩ := exists_descent r hr L hL
  obtain ⟨h1, h2, -⟩ := (D.loc_tie i w hw).2.2 L hle a ρ hρ
  have := L.2
  have h3 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT (D.nd.l i)) _ L _ _ (h1.1 hc)).1
  refine h2.2 ?_
  unfold IsDR at h3
  unfold LocBridge.IsdRE
  simpa using h3

end GlobalTheory.CrysWD
