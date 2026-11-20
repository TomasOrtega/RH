import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceHeis
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeisJointEigen

/- English proof (translation)
Introduce `R`. Proceed by induction on `R using Finset.induction_on with`. Consider the case `empty => intro _ _ c _ z hz`. Simplify using `at hz`. Consider the case `insert a s ha ih`.

Introduce `hv hsep c hsum`. Establish `hv' : ∀ z ∈ s, v z ≠ 0` using `fun z hz => hv z (Finset.mem_insert_of_mem hz)`. Establish `hsep' : ∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → ∃ (A : V →ₗ[ℂ] V) (χ : ι → ℂ), (∀ z ∈ s, A (v z) = χ z • v z) ∧ χ y ≠ χ y'`. Introduce `y hy y' hy' hne`. Take `⟨A, χ, hA, hχ⟩` from `hsep y (Finset.mem_insert_of_mem hy) y' (Finset.mem_insert_of_mem hy') hne`.

Conclude with `⟨A, χ, fun z hz => hA z (Finset.mem_insert_of_mem hz), hχ⟩`. Rewrite `hsum` using `[Finset.sum_insert ha]`. Establish `hs0 : ∀ b ∈ s, c b = 0`. Introduce `b hb`. Establish `hab : b ≠ a` using `fun h => ha (h ▸ hb)`.

Take `⟨A, χ, hA, hχ⟩` from `hsep b (Finset.mem_insert_of_mem hb) a (Finset.mem_insert_self a s) hab`. Establish `key : ∑ z ∈ s, (c z * (χ z - χ a)) • v z = A (c a • v a + ∑ z ∈ s, c z • v z) - χ a • (c a • v a + ∑ z ∈ s, c z • v z)`. Rewrite using `[map_add, map_sum, map_smul, hA a (Finset.mem_insert_self a s), smul_add, Finset.smul_sum, add_sub_add_comm, smul_comm (χ a) (c a), sub_self, zero_add, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun z hz => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hA z (Finset.mem_insert_of_mem hz), smul_smul, smul_smul, ← sub_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[hsum, map_zero, smul_zero, sub_zero]`. Establish `h` using `ih hv' hsep' (fun z => c z * (χ z - χ a)) key b hb`. Break down `mul_eq_zero.1 h with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd (sub_eq_zero.1 h) hχ`. Establish `hsum0 : ∑ z ∈ s, c z • v z = 0` using `Finset.sum_eq_zero fun z hz => by rw [hs0 z hz, zero_smul]`. Rewrite `hsum` using `[hsum0, add_zero]`. Establish `hca : c a = 0` using `(smul_eq_zero.1 hsum).resolve_right (hv a (Finset.mem_insert_self a s))`.

Introduce `z hz`. Break down `Finset.mem_insert.1 hz with rfl | hz` into its components or cases. Conclude with `hca`. Conclude with `hs0 z hz`.
-/
theorem coeff_zero_of_separated {ι V : Type*} [AddCommGroup V] [Module ℂ V] [DecidableEq ι] (v : ι → V) :
    ∀ R : Finset ι, (∀ z ∈ R, v z ≠ 0) →
      (∀ y ∈ R, ∀ y' ∈ R, y ≠ y' → ∃ (A : V →ₗ[ℂ] V) (χ : ι → ℂ), (∀ z ∈ R, A (v z) = χ z • v z) ∧ χ y ≠ χ y') →
      ∀ c : ι → ℂ, ∑ z ∈ R, c z • v z = 0 → ∀ z ∈ R, c z = 0 := by
  intro R
  induction R using Finset.induction_on with
  | empty => intro _ _ c _ z hz; simp at hz
  | insert a s ha ih =>
    intro hv hsep c hsum
    have hv' : ∀ z ∈ s, v z ≠ 0 := fun z hz => hv z (Finset.mem_insert_of_mem hz)
    have hsep' : ∀ y ∈ s, ∀ y' ∈ s, y ≠ y' →
        ∃ (A : V →ₗ[ℂ] V) (χ : ι → ℂ), (∀ z ∈ s, A (v z) = χ z • v z) ∧ χ y ≠ χ y' := by
      intro y hy y' hy' hne
      obtain ⟨A, χ, hA, hχ⟩ := hsep y (Finset.mem_insert_of_mem hy) y' (Finset.mem_insert_of_mem hy') hne
      exact ⟨A, χ, fun z hz => hA z (Finset.mem_insert_of_mem hz), hχ⟩
    rw [Finset.sum_insert ha] at hsum
    have hs0 : ∀ b ∈ s, c b = 0 := by
      intro b hb
      have hab : b ≠ a := fun h => ha (h ▸ hb)
      obtain ⟨A, χ, hA, hχ⟩ := hsep b (Finset.mem_insert_of_mem hb) a (Finset.mem_insert_self a s) hab
      have key : ∑ z ∈ s, (c z * (χ z - χ a)) • v z =
          A (c a • v a + ∑ z ∈ s, c z • v z) - χ a • (c a • v a + ∑ z ∈ s, c z • v z) := by
        rw [map_add, map_sum, map_smul, hA a (Finset.mem_insert_self a s), smul_add, Finset.smul_sum,
          add_sub_add_comm, smul_comm (χ a) (c a), sub_self, zero_add, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun z hz => ?_
        rw [map_smul, hA z (Finset.mem_insert_of_mem hz), smul_smul, smul_smul, ← sub_smul]
        congr 1
        ring
      rw [hsum, map_zero, smul_zero, sub_zero] at key
      have h := ih hv' hsep' (fun z => c z * (χ z - χ a)) key b hb
      rcases mul_eq_zero.1 h with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) hχ
    have hsum0 : ∑ z ∈ s, c z • v z = 0 := Finset.sum_eq_zero fun z hz => by rw [hs0 z hz, zero_smul]
    rw [hsum0, add_zero] at hsum
    have hca : c a = 0 := (smul_eq_zero.1 hsum).resolve_right (hv a (Finset.mem_insert_self a s))
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hca
    · exact hs0 z hz

/- English proof (translation)
Introduce `D ψ S T ΛS ΛT P e he R hsep g hg hg0 c hc hsum`. Take `⟨z0, hz0, hcz⟩` from `hc`. Apply `hcz` to reduce the goal to its premises. Use `coeff_zero_of_separated (fun z => heisO ψ S T z g) R ?_ ?_ c hsum z0 hz0` and prove the remaining obligations. Introduce `z _ h`.

Apply `hg0` to reduce the goal to its premises. Use function extensionality and compare the values at `w`. Establish `h1` using `congrFun h (w - z)`. Simplify using `only [heisO, Pi.zero_apply, sub_add_cancel] at h1`. Break down `mul_eq_zero.1 h1 with h2 | h2` into its components or cases.

Conclude with `absurd h2 (Formalism.IndefR.Fin.psi_ne_zero ψ _)`. Conclude with `h2`. Introduce `y hy y' hy' hne`. Take `⟨u, hu, hhalf, hψ⟩` from `hsep y hy y' hy' hne`. Establish `hfix : heisO ψ S T u g = g` using `Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_fix_of_latVac ψ hg he u hu (Or.inl hhalf)`.

Use `⟨Formalism.IndefR.Fin.heisL ψ S T u, fun z => ψ (symplO S T u z), fun z _ => ?_, hψ⟩` and prove the remaining obligations. Establish `h1` using `congrArg (fun L => L g) (Formalism.IndefR.Fin.heisL_comm ψ S T u z)`. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply, Formalism.IndefR.Fin.heisL_apply] at h1`. Rewrite `h1` using `[hfix]`. Rewrite using `[Formalism.IndefR.Fin.heisL_apply]`.

Conclude with `h1`.
-/
theorem sum_heisO_ne_zero : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ (R : Finset (WO S T)), (∀ y ∈ R, ∀ y' ∈ R, y ≠ y' → ∃ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf e u ∧ ψ (symplO S T u y) ≠ ψ (symplO S T u y')) → ∀ g : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) g → g ≠ 0 → ∀ c : WO S T → ℂ, (∃ z ∈ R, c z ≠ 0) → ∑ z ∈ R, c z • heisO ψ S T z g ≠ 0 := by
  intro D ψ S T ΛS ΛT P e he R hsep g hg hg0 c hc hsum
  obtain ⟨z0, hz0, hcz⟩ := hc
  apply hcz
  classical
  refine coeff_zero_of_separated (fun z => heisO ψ S T z g) R ?_ ?_ c hsum z0 hz0
  · intro z _ h
    apply hg0
    funext w
    have h1 := congrFun h (w - z)
    simp only [heisO, Pi.zero_apply, sub_add_cancel] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (Formalism.IndefR.Fin.psi_ne_zero ψ _)
    · exact h2
  · intro y hy y' hy' hne
    obtain ⟨u, hu, hhalf, hψ⟩ := hsep y hy y' hy' hne
    have hfix : heisO ψ S T u g = g :=
      Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_fix_of_latVac ψ hg he u hu (Or.inl hhalf)
    refine ⟨Formalism.IndefR.Fin.heisL ψ S T u, fun z => ψ (symplO S T u z), fun z _ => ?_, hψ⟩
    have h1 := congrArg (fun L => L g) (Formalism.IndefR.Fin.heisL_comm ψ S T u z)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Formalism.IndefR.Fin.heisL_apply] at h1
    rw [hfix] at h1
    rw [Formalism.IndefR.Fin.heisL_apply]
    exact h1

end GlobalTheory.HeisJointEigen
