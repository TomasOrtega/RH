import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

/- English proof (translation)
Substitute `hV` using the available equality. Use `show T.phiJ j σ a 0 = 0`. Unfold `CoreJ.phiJ`. Rewrite using `[map_zero, map_zero, smul_zero]`.
-/
theorem phiC_zero_rule {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) : phiC T hV a (0 : T.R j) = 0 := by
  subst hV
  show T.phiJ j σ a 0 = 0
  unfold CoreJ.phiJ
  rw [map_zero, map_zero, smul_zero]

set_option linter.unusedVariables false in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ fw hU i σ hσ hV f`. Distinguish the cases in `hj : ∃ j' : (Fin (R.nW i) → D.what₂.LL) →ₛₗ[σ] (R.HW i σ).H, ∀ f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ((R.HW i σ).e (j' ((fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) (v₀ i σ) = hV ▸ T.phiJ ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) (wtA (κ i)) (f : …`. Conclude with `fw.ev i σ hσ hV hj f`. It suffices to derive a contradiction. Establish `hz : (R.FW i).j σ = 0` using `fw.ev0 i σ hσ hV hj`.

Establish `hx : ∀ x : Fin (R.nW i) → D.what₂.LL, x = 0`. Introduce `x`. Assume the negation of the conclusion as `hne`. Establish `hli` using `(hU i σ).1 1 (fun _ => x) (linearIndependent_unique_iff.mpr hne)`. Simplify using `only [hz, LinearMap.zero_apply] at hli`.

Conclude with `hli.ne_zero 0 rfl`. Apply `hj` to reduce the goal to its premises. Use `⟨0, fun f' => ?_⟩` and prove the remaining obligations. Establish `hf' : f' = 0`. Simplify using `using hx ((fw.e i f' : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)`.

Substitute `hf'` using the available equality. Simplify using the standard rewrite rules. Conclude with `(phiC_zero_rule T hV (wtA (κ i))).symm`.
-/
theorem evaluates_of_unif : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T R κ v₀), R.LUnif → fw.Evaluates := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw hU i σ hσ hV f
  by_cases hj : ∃ j' : (Fin (R.nW i) → D.what₂.LL) →ₛₗ[σ] (R.HW i σ).H,
      ∀ f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
        ((R.HW i σ).e (j' ((fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) (v₀ i σ) =
          hV ▸ T.phiJ ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) (wtA (κ i)) (f : T.R ((i : ℕ) + 1))
  · exact fw.ev i σ hσ hV hj f
  · exfalso
    have hz : (R.FW i).j σ = 0 := fw.ev0 i σ hσ hV hj

    have hx : ∀ x : Fin (R.nW i) → D.what₂.LL, x = 0 := by
      intro x
      by_contra hne
      have hli := (hU i σ).1 1 (fun _ => x) (linearIndependent_unique_iff.mpr hne)
      simp only [hz, LinearMap.zero_apply] at hli
      exact hli.ne_zero 0 rfl

    apply hj
    refine ⟨0, fun f' => ?_⟩
    have hf' : f' = 0 := by
      simpa using hx ((fw.e i f' : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)
    subst hf'
    simp
    exact (phiC_zero_rule T hV (wtA (κ i))).symm

end GlobalTheory
