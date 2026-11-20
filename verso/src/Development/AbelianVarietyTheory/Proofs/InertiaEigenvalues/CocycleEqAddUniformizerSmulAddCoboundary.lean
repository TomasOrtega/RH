import Mathlib
import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
open ReciprocityTheory.Gal

namespace GlobalTheory

/- English proof (translation)
Take `⟨i, his, x, hx⟩` from `hs c`. Set `d : Z1 ρ` to `⟨d0 ρ x, coboundaries_le_cocycles ρ hρ ⟨x, rfl⟩⟩`. Set `E : Z1 ρ` to `c - i - d`. Establish `hE : ∀ g, (E : G → M) g = (c : G → M) g - (i : G → M) g - (ρ g x - x)` using `fun g => rfl`. Establish `hx' : ∀ g, ∃ y : M, ϖ • y = (E : G → M) g`.

Introduce `g`. Take `⟨y, hy⟩` from `hx g`. Conclude with `⟨y, by rw [hE]; simpa using hy⟩`. Use `choose f hf using hx'`. Establish `hfE : (fun g => ϖ • f g) = (E : G → M)` using `funext hf`.

Establish `hfc : Continuous f`. Rewrite using `[hemb.continuous_iff]`. Express the relevant statement in the definitionally equal form `Continuous (fun g => ϖ • f g)`. Rewrite using `[hfE]`. Conclude with `E.2.1`.

Establish `hfco : ∀ g h, f (g * h) = f g + ρ g (f h)`. Introduce `g h`. Apply `hemb.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `ϖ • f (g * h) = ϖ • (f g + ρ g (f h))`. Rewrite using `[smul_add, ← map_smul, hf, hf, hf]`.

Conclude with `E.2.2 g h`. Use `⟨fun j => if j = i then 1 else 0, ⟨f, hfc, hfco⟩, x, ?_⟩` and prove the remaining obligations. Establish `hsum : ∑ j ∈ s, (if j = i then (1 : O) else 0) • (j : G → M) = (i : G → M)`. Simplify using `only [ite_smul, one_smul, zero_smul]`. Rewrite using `[Finset.sum_ite_eq' s i (fun j => (j : G → M))]`.

Simplify using `[his]`. Rewrite using `[hsum]`. Use function extensionality and compare the values at `g`. Use `hf g` as an intermediate fact. Rewrite `this` using `[hE]`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, amitsur_d0_apply]`. Rewrite using `[this]`. Normalize the expressions using the abelian group laws.
-/
theorem cocycle_lift_mod_uniformizer
    {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul O M] {G : Type} [Group G] [TopologicalSpace G]
    (ρ : Representation O G M) (hρ : ContAction ρ) (ϖ : O)
    (hemb : Topology.IsEmbedding (fun m : M => ϖ • m)) (s : Finset (Z1 ρ))
    (hs : ∀ c : Z1 ρ, ∃ i ∈ s, ∃ x : M, ∀ g, (c : G → M) g - (i : G → M) g - (ρ g x - x) ∈
      LinearMap.range (LinearMap.lsmul O M ϖ))
    (c : Z1 ρ) : ∃ (a : Z1 ρ → O) (c' : Z1 ρ) (x : M),
      (c : G → M) = ∑ i ∈ s, a i • (i : G → M) + ϖ • (c' : G → M) + d0 ρ x := by
  classical
  obtain ⟨i, his, x, hx⟩ := hs c
  let d : Z1 ρ := ⟨d0 ρ x, coboundaries_le_cocycles ρ hρ ⟨x, rfl⟩⟩
  let E : Z1 ρ := c - i - d
  have hE : ∀ g, (E : G → M) g = (c : G → M) g - (i : G → M) g - (ρ g x - x) := fun g => rfl
  have hx' : ∀ g, ∃ y : M, ϖ • y = (E : G → M) g := by
    intro g
    obtain ⟨y, hy⟩ := hx g
    exact ⟨y, by rw [hE]; simpa using hy⟩
  choose f hf using hx'
  have hfE : (fun g => ϖ • f g) = (E : G → M) := funext hf
  have hfc : Continuous f := by
    rw [hemb.continuous_iff]
    change Continuous (fun g => ϖ • f g)
    rw [hfE]
    exact E.2.1
  have hfco : ∀ g h, f (g * h) = f g + ρ g (f h) := by
    intro g h
    apply hemb.injective
    change ϖ • f (g * h) = ϖ • (f g + ρ g (f h))
    rw [smul_add, ← map_smul, hf, hf, hf]
    exact E.2.2 g h
  refine ⟨fun j => if j = i then 1 else 0, ⟨f, hfc, hfco⟩, x, ?_⟩
  have hsum : ∑ j ∈ s, (if j = i then (1 : O) else 0) • (j : G → M) = (i : G → M) := by
    simp only [ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq' s i (fun j => (j : G → M))]
    simp [his]
  rw [hsum]
  funext g
  have := hf g
  rw [hE] at this
  simp only [Pi.add_apply, Pi.smul_apply, amitsur_d0_apply]
  rw [this]
  abel

end GlobalTheory
