import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK

namespace GlobalTheory.FixedFinsetInvariants

/- English proof (translation)
Set `F : Finset G → Submodule LL V` to `fun s => ⨅ g ∈ s, LinearMap.ker (ρ g - LinearMap.id)`. Establish `hF : ∀ (s : Finset G) (v : V), v ∈ F s ↔ ∀ g ∈ s, ρ g v = v`. Introduce `s v`. Simplify using `only [F, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`. Take `⟨_, ⟨s, rfl⟩, hmin⟩` from `(wellFounded_lt (α := Submodule LL V)).has_min (Set.range F) ⟨F ∅, ∅, rfl⟩`.

Use `⟨s, fun v hv => ?_⟩` and prove the remaining obligations. Unfold `Formalism.WeaklyAdmissibleFiltrations.H0V`. Rewrite using `[Submodule.mem_iInf]`. Introduce `g`. Establish `hle : F (insert g s) ≤ F s`.

Introduce `w hw`. Rewrite `hw`, the goal using `[hF]`. Conclude with `fun h hh => hw h (Finset.mem_insert_of_mem hh)`. Establish `heq : F (insert g s) = F s`. Assume the negation of the conclusion as `hne`.

Conclude with `hmin _ ⟨insert g s, rfl⟩ (lt_of_le_of_ne hle hne)`. Establish `hv' : v ∈ F (insert g s)` using `heq ▸ (hF s v).2 hv`. Establish `hg` using `(hF _ v).1 hv' g (Finset.mem_insert_self g s)`. Simplify using `only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`. Conclude with `hg`.
-/
theorem exists_finset_fixed_mem_invariants {G LL V : Type} [Group G] [Field LL] [AddCommGroup V]
    [Module LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) :
    ∃ s : Finset G, ∀ v : V, (∀ g ∈ s, ρ g v = v) → v ∈ Formalism.WeaklyAdmissibleFiltrations.H0V ρ := by
  classical
  let F : Finset G → Submodule LL V := fun s => ⨅ g ∈ s, LinearMap.ker (ρ g - LinearMap.id)
  have hF : ∀ (s : Finset G) (v : V), v ∈ F s ↔ ∀ g ∈ s, ρ g v = v := by
    intro s v
    simp only [F, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
  obtain ⟨_, ⟨s, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule LL V)).has_min (Set.range F) ⟨F ∅, ∅, rfl⟩
  refine ⟨s, fun v hv => ?_⟩
  unfold Formalism.WeaklyAdmissibleFiltrations.H0V
  rw [Submodule.mem_iInf]
  intro g
  have hle : F (insert g s) ≤ F s := by
    intro w hw
    rw [hF] at hw ⊢
    exact fun h hh => hw h (Finset.mem_insert_of_mem hh)
  have heq : F (insert g s) = F s := by
    by_contra hne
    exact hmin _ ⟨insert g s, rfl⟩ (lt_of_le_of_ne hle hne)
  have hv' : v ∈ F (insert g s) := heq ▸ (hF s v).2 hv
  have hg := (hF _ v).1 hv' g (Finset.mem_insert_self g s)
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  exact hg

end GlobalTheory.FixedFinsetInvariants
