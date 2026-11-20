import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoLMk
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BDLocConst

/- English proof (translation)
Introduce `l _ P K LL _ _ _ O _ _ hO A LA c hc`. Take `⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩` from `hO`. Use `haveI := hDom`. Use `haveI := hDVR`. Use `haveI := hFr`.

Use `haveI := htr`. Use `haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V`. Take `⟨y, rfl⟩` from `hc`. Proceed by induction on `y using Submodule.Quotient.induction_on with`. Consider the case `H x`.

Establish `hval : ∀ g, (LinearMap.pi (fun g => actD LA g - LinearMap.id) (Submodule.Quotient.mk x : A.V ⧸ LA.T)) g = Submodule.Quotient.mk (A.ρ g x - x)`. Introduce `g`. Both sides reduce to the same expression. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hT : IsOpen (LA.T : Set A.V)` using `Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA.T LA.fg LA.span`.

Use `Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk LA.T hT (fun g => A.ρ g x - x) ((A.cont x).sub continuous_const)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Conclude with `hval g`. Introduce `g h`.

Rewrite using `[hval, hval, hval]`. Use `show _ = Submodule.Quotient.mk (A.ρ g x - x) + Submodule.Quotient.mk (A.ρ g (A.ρ h x - x))`. Rewrite using `[← Submodule.Quotient.mk_add, map_mul]`. Use `congr 1`. Simplify using `only [Module.End.mul_apply, map_sub]`.

Normalize the expressions using the abelian group laws.
-/
theorem lattice_divisible_coboundaries_le_locConst_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), BD LA ≤ divisibleCocycles LA := by
  intro l _ P K LL _ _ _ O _ _ hO A LA c hc
  obtain ⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFr; haveI := htr
  haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
  obtain ⟨y, rfl⟩ := hc
  induction y using Submodule.Quotient.induction_on with
  | H x =>
  have hval : ∀ g, (LinearMap.pi (fun g => actD LA g - LinearMap.id) (Submodule.Quotient.mk x : A.V ⧸ LA.T)) g
      = Submodule.Quotient.mk (A.ρ g x - x) := by
    intro g
    rfl
  refine ⟨?_, ?_⟩
  · have hT : IsOpen (LA.T : Set A.V) := Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA.T LA.fg LA.span
    have := Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk LA.T hT (fun g => A.ρ g x - x) ((A.cont x).sub continuous_const)
    convert this using 1
    funext g
    exact hval g
  · intro g h
    rw [hval, hval, hval]
    show _ = Submodule.Quotient.mk (A.ρ g x - x) + Submodule.Quotient.mk (A.ρ g (A.ρ h x - x))
    rw [← Submodule.Quotient.mk_add, map_mul]
    congr 1
    simp only [Module.End.mul_apply, map_sub]
    abel

end GlobalTheory.BDLocConst
