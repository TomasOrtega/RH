import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientOfCompleteNakayamaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FreeModuleAdicCompleteSeparatedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientsExplicitSumsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCocyclesFinitelyGeneratedModPrimeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateFiniteH1

/- English proof (translation)
Introduce `l _ P K LL _ _ _ O _ _ hO A LA`. Take `⟨hR, hRs⟩` from `GlobalTheory.T.goodCoefficients_explicit_sums l LL O hO`. Use `haveI : Module.Free O ↥LA.T := LA.free`. Use `haveI : Module.Finite O ↥LA.T := Module.Finite.iff_fg.2 LA.fg`. Take `⟨hTc, hTs⟩` from `GlobalTheory.T.free_finite_module_adicComplete_and_separated ((l : ℕ) : O) hR hRs ↥LA.T`.

Establish `hmemT : ∀ c : ↥(latticeCocycles LA), ∀ g, (c : ↥(GK K) → A.V) g ∈ LA.T` using `fun c g => (Submodule.mem_pi.1 (Submodule.mem_inf.1 c.2).2) g (Set.mem_univ g)`. Establish `hd : ∀ t : ↥LA.T, ((cob A.ρ).restrictScalars O) (t : A.V) ∈ latticeCocycles LA` using `fun t => by`. Use `Submodule.mem_inf.2 ⟨⟨?_, fun g h => ?_⟩, Submodule.mem_pi.2 fun g _ => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Continuous fun g => A.ρ g (t : A.V) - (t : A.V)`. Simplify using `only [sub_eq_add_neg]`.

Conclude with `(A.cont _).add continuous_const`. Express the relevant statement in the definitionally equal form `A.ρ (g * h) (t : A.V) - (t : A.V) = (A.ρ g (t : A.V) - (t : A.V)) + A.ρ g (A.ρ h (t : A.V) - (t : A.V))`. Rewrite using `[map_mul, Module.End.mul_apply, map_sub]`. Normalize the expressions using the abelian group laws. Express the relevant statement in the definitionally equal form `A.ρ g (t : A.V) - (t : A.V) ∈ LA.T`.

Conclude with `LA.T.sub_mem (LA.stable g _ t.2) t.2`. Set `d : ↥LA.T →ₗ[O] ↥(latticeCocycles LA)` to `LinearMap.codRestrict (latticeCocycles LA) (((cob A.ρ).restrictScalars O).comp LA.T.subtype) hd`. Establish `hdN : LinearMap.range d ≤ (latticeCoboundaries LA).comap (latticeCocycles LA).subtype`. Introduce and unpack `_ ⟨t, rfl⟩`. Conclude with `⟨t, t.2, rfl⟩`.

Establish `hZ : ∀ c : ↥(latticeCocycles LA), (∀ n : ℕ, ∃ z : ↥(latticeCocycles LA), c = ((l : ℕ) : O) ^ n • z) → c = 0`. Introduce `c hc`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Establish `h0` using `hTs ⟨_, hmemT c g⟩ fun n => by`.

Take `⟨z, hz⟩` from `hc n`. Use `⟨⟨_, hmemT z g⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(c : ↥(GK K) → A.V) g = ((l : ℕ) : O) ^ n • (z : ↥(GK K) → A.V) g`. Rewrite using `[hz]`. Both sides reduce to the same expression.

Conclude with `congrArg Subtype.val h0`. Take `⟨s, hs⟩` from `GlobalTheory.T.latticeCocycles_finitelyGenerated_mod_prime hT l K LL O hO A LA`. Use `GlobalTheory.T.module_finite_quotient_of_complete_of_span_mod_range ((l : ℕ) : O) hR hTc hZ d _ hdN s fun c => ?_` and prove the remaining obligations. Take `⟨a, c', hm⟩` from `hs c`. Take `⟨x, hx, hxe⟩` from `hm`.

Use `⟨a, c', ⟨x, hx⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Establish `e : ((d ⟨x, hx⟩ : ↥(latticeCocycles LA)) : ↥(GK K) → A.V) = ((cob A.ρ).restrictScalars O) x` using `rfl`. Simplify using `only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, e, hxe]`. Normalize the expressions using the abelian group laws.
-/
theorem tate_finH1 (hT : Formalism.GaloisCohomology.LocalTateDualityK) :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), TateFiniteness (P.PD K) := by
  intro l _ P K LL _ _ _ O _ _ hO A LA
  obtain ⟨hR, hRs⟩ := GlobalTheory.T.goodCoefficients_explicit_sums l LL O hO
  haveI : Module.Free O ↥LA.T := LA.free
  haveI : Module.Finite O ↥LA.T := Module.Finite.iff_fg.2 LA.fg
  obtain ⟨hTc, hTs⟩ := GlobalTheory.T.free_finite_module_adicComplete_and_separated ((l : ℕ) : O) hR hRs ↥LA.T
  have hmemT : ∀ c : ↥(latticeCocycles LA), ∀ g, (c : ↥(GK K) → A.V) g ∈ LA.T := fun c g =>
    (Submodule.mem_pi.1 (Submodule.mem_inf.1 c.2).2) g (Set.mem_univ g)
  have hd : ∀ t : ↥LA.T, ((cob A.ρ).restrictScalars O) (t : A.V) ∈ latticeCocycles LA := fun t => by
    refine Submodule.mem_inf.2 ⟨⟨?_, fun g h => ?_⟩, Submodule.mem_pi.2 fun g _ => ?_⟩
    · change Continuous fun g => A.ρ g (t : A.V) - (t : A.V)
      simp only [sub_eq_add_neg]
      exact (A.cont _).add continuous_const
    · change A.ρ (g * h) (t : A.V) - (t : A.V) = (A.ρ g (t : A.V) - (t : A.V)) + A.ρ g (A.ρ h (t : A.V) - (t : A.V))
      rw [map_mul, Module.End.mul_apply, map_sub]
      abel
    · change A.ρ g (t : A.V) - (t : A.V) ∈ LA.T
      exact LA.T.sub_mem (LA.stable g _ t.2) t.2
  let d : ↥LA.T →ₗ[O] ↥(latticeCocycles LA) :=
    LinearMap.codRestrict (latticeCocycles LA) (((cob A.ρ).restrictScalars O).comp LA.T.subtype) hd
  have hdN : LinearMap.range d ≤ (latticeCoboundaries LA).comap (latticeCocycles LA).subtype := by
    rintro _ ⟨t, rfl⟩
    exact ⟨t, t.2, rfl⟩
  have hZ : ∀ c : ↥(latticeCocycles LA), (∀ n : ℕ, ∃ z : ↥(latticeCocycles LA), c = ((l : ℕ) : O) ^ n • z) → c = 0 := by
    intro c hc
    apply Subtype.ext
    funext g
    have h0 := hTs ⟨_, hmemT c g⟩ fun n => by
      obtain ⟨z, hz⟩ := hc n
      refine ⟨⟨_, hmemT z g⟩, Subtype.ext ?_⟩
      change (c : ↥(GK K) → A.V) g = ((l : ℕ) : O) ^ n • (z : ↥(GK K) → A.V) g
      rw [hz]
      rfl
    exact congrArg Subtype.val h0
  obtain ⟨s, hs⟩ := GlobalTheory.T.latticeCocycles_finitelyGenerated_mod_prime hT l K LL O hO A LA
  refine GlobalTheory.T.module_finite_quotient_of_complete_of_span_mod_range ((l : ℕ) : O) hR hTc hZ d _ hdN s fun c => ?_
  obtain ⟨a, c', hm⟩ := hs c
  obtain ⟨x, hx, hxe⟩ := hm
  refine ⟨a, c', ⟨x, hx⟩, Subtype.ext ?_⟩
  have e : ((d ⟨x, hx⟩ : ↥(latticeCocycles LA)) : ↥(GK K) → A.V) = ((cob A.ρ).restrictScalars O) x := rfl
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, e, hxe]
  abel

end GlobalTheory.TateFiniteH1
