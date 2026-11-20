import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

namespace GlobalTheory

/- English proof (translation)
Introduce `O _ _ G _ _ _ ε Θ M _ _ _ _ _ N hmono hopen hcov hfg n`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `z hz`. Proceed by induction on `z using Submodule.Quotient.induction_on with`. Consider the case `H f`.

Unfold `mapH2 at hz`. Rewrite `hz` using `[Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`. Take `⟨c, hc, hcf⟩` from `(separated_dvr_second_cohomology_mem _ _).1 hz`. Establish `hK : IsCompact (Set.range c)` using `isCompact_range hc`. Take `⟨i, hi⟩` from `hK.elim_directed_cover (fun k => (N k : Set M)) hopen (fun x _ => Set.mem_iUnion.2 (hcov x)) (hmono.directed_le)`.

Use `set m := max n i with hm`. Establish `hnm : N n ≤ N m` using `hmono (le_max_left n i)`. Establish `him : ∀ g, c g ∈ N m` using `fun g => hmono (le_max_right n i) (hi ⟨g, rfl⟩)`. Establish `hincl : Continuous (Submodule.inclusion hnm)` using `continuous_inclusion hnm`. Establish `hzero : mapH2 (twist ε (N n)) (twist ε (N m)) (Submodule.inclusion hnm) hincl (twist_map ε (Submodule.inclusion hnm)) (Submodule.Quotient.mk f) = 0`.

Unfold `mapH2`. Rewrite using `[Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`. Use `(separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => ⟨c g, him g⟩, hc.subtype_mk him, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `e` using `congrFun hcf p`. Simplify using `[d1, twist] at e ⊢`. Rewrite using `[e]`. Both sides reduce to the same expression. Establish `hnat` using `Θ.nat (N n) (N m) (hfg n) (hfg m) (Submodule.inclusion hnm) hincl (Submodule.Quotient.mk f)`.

Rewrite `hnat` using `[hzero, map_zero]`. Establish `h0 : Θ.θ (N n) (hfg n) (Submodule.Quotient.mk f) = 0`. Use `hnat.symm` as an intermediate fact. Rewrite `this` using `[← (Submodule.inclusion hnm).map_zero]`. Conclude with `Submodule.inclusion_injective hnm this`.

Conclude with `(LinearEquiv.map_eq_zero_iff _).1 h0`.
-/
theorem map_H2_subtype_injective_of_union : ∀ {O : Type} [CommRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {ε : G →* Oˣ} (Θ : NatInv ε (fun M _ _ _ => IsFGTop O M))
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] (N : ℕ → Submodule O M), Monotone N → (∀ n, IsOpen (N n : Set M)) → (∀ x, ∃ n, x ∈ N n) →
    ∀ (hfg : ∀ n, IsFGTop O (N n)) (n : ℕ),
      Function.Injective (mapH2 (twist ε (N n)) (twist ε M) (N n).subtype continuous_subtype_val (twist_map ε (N n).subtype)) := by
  intro O _ _ G _ _ _ ε Θ M _ _ _ _ _ N hmono hopen hcov hfg n
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  induction z using Submodule.Quotient.induction_on with
  | H f =>
  unfold mapH2 at hz
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 hz

  have hK : IsCompact (Set.range c) := isCompact_range hc
  obtain ⟨i, hi⟩ := hK.elim_directed_cover (fun k => (N k : Set M)) hopen
    (fun x _ => Set.mem_iUnion.2 (hcov x)) (hmono.directed_le)
  set m := max n i with hm
  have hnm : N n ≤ N m := hmono (le_max_left n i)
  have him : ∀ g, c g ∈ N m := fun g => hmono (le_max_right n i) (hi ⟨g, rfl⟩)
  have hincl : Continuous (Submodule.inclusion hnm) := continuous_inclusion hnm
  have hzero : mapH2 (twist ε (N n)) (twist ε (N m)) (Submodule.inclusion hnm) hincl
      (twist_map ε (Submodule.inclusion hnm)) (Submodule.Quotient.mk f) = 0 := by
    unfold mapH2
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => ⟨c g, him g⟩, hc.subtype_mk him, ?_⟩
    funext p
    apply Subtype.ext
    have e := congrFun hcf p
    simp [d1, twist] at e ⊢
    rw [e]
    rfl
  have hnat := Θ.nat (N n) (N m) (hfg n) (hfg m) (Submodule.inclusion hnm) hincl (Submodule.Quotient.mk f)
  rw [hzero, map_zero] at hnat
  have h0 : Θ.θ (N n) (hfg n) (Submodule.Quotient.mk f) = 0 := by
    have := hnat.symm
    rw [← (Submodule.inclusion hnm).map_zero] at this
    exact Submodule.inclusion_injective hnm this
  exact (LinearEquiv.map_eq_zero_iff _).1 h0

end GlobalTheory
