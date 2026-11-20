import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisibilityLatticeDescendsIntegralExtStatement

set_option autoImplicit false

open GlobalTheory.RingChain GlobalTheory.PerfdLat
open scoped TensorProduct Pointwise

namespace GlobalTheory.RingChain

/- English proof (translation)
Introduce `B _ _ h ϖ P _ _ h0 hb`. Take `⟨m, f, s, -, -, hfs⟩` from `Module.Finite.exists_comp_eq_id_of_projective B P`. Establish `he : ∀ k : Fin h, ϖ • (Pi.single k 1 : Fin h → B) ∈ P` using `fun k => hb (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)`. Set `u : Fin m → P` to `fun i => f (Pi.single i 1)`. Establish `hu : ∀ x : P, x = ∑ i, s x i • u i` using `fun x => by`.

Establish `h1 : f (s x) = x` using `LinearMap.congr_fun hfs x`. Use `conv_lhs => rw [← h1, pi_eq_sum_univ' (s x)]`. Simplify using `only [map_sum, map_smul, u]`. Use `⟨insert ϖ (Set.range (fun q : Fin m × Fin h => (u q.1).1 q.2) ∪ Set.range (fun q : Fin h × Fin m => s ⟨_, he q.1⟩ q.2)), ((Set.finite_range _).union (Set.finite_range _)).insert _, ?_⟩` and prove the remaining obligations. Introduce `A' _ _ _ g hg hi hT`.

Take `⟨a, ha⟩` from `hT (Set.mem_insert _ _)`. Establish `hU : ∀ i k, ∃ z, g z = (u i).1 k` using `fun i k => hT (Set.mem_insert_of_mem _ (Or.inl ⟨(i, k), rfl⟩))`. Establish `hc : ∀ k i, ∃ z, g z = s ⟨_, he k⟩ i` using `fun k i => hT (Set.mem_insert_of_mem _ (Or.inr ⟨(k, i), rfl⟩))`. Use `choose U hU using hU`. Use `choose c hc using hc`.

Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `h0 (by rw [← ha, map_zero])`. Establish `hpi : ∀ (x : Fin h → A') k, piMap g (Fin h) x k = g (x k)` using `fun _ _ => rfl`. Establish `hUu : ∀ i, piMap g (Fin h) (U i) = (u i).1` using `fun i => funext fun k => hU i k`.

Set `G : P.comap (piMap g (Fin h)) → P` to `fun x => ⟨piMap g (Fin h) x.1, x.2⟩`. Establish `hσ : ∀ x i, ∃ z, g z = s (G x) i` using `fun x i => by`. Establish `h1 : ϖ • G x = ∑ k, g (x.1 k) • (⟨_, he k⟩ : P)`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `k`.

Simplify using `[G, hpi, Finset.sum_apply, Pi.single_apply, mul_comm]`. Establish `h2 : g a * s (G x) i = g (∑ k, x.1 k * c k i)`. Use `congrFun (congrArg s h1) i` as an intermediate fact. Simplify using `only [map_smul, map_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this`. Rewrite using `[ha, this, map_sum]`.

Simplify using `only [map_mul, hc]`. Take `⟨z, hz⟩` from `(GlobalTheory.T.divisibility_lattice_descends_integral_ext A' B g hg hi).1 a _ ha0 ⟨_, h2.symm⟩`. Rewrite `h2` using `[hz, map_mul, ha]`. Conclude with `⟨z, (mul_left_cancel₀ h0 h2).symm⟩`. Use `choose σ hσ using hσ`.

Set `s' : P.comap (piMap g (Fin h)) →ₗ[A'] (Fin m → A')` to `{ toFun := σ map_add' := fun x y => funext fun i => hg (by`. Establish `: G (x + y) = G x + G y` using `Subtype.ext (map_add (piMap g (Fin h)) x.1 y.1)`. Rewrite using `[Pi.add_apply, map_add, hσ, hσ, hσ, this, map_add, Pi.add_apply])`. Use the proof step `map_smul' := fun r x => funext fun i => hg (by`. Establish `: G (r • x) = g r • G x` using `Subtype.ext (map_smulₛₗ (piMap g (Fin h)) r x.1)`.

Rewrite using `[RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_mul, hσ, hσ, this, map_smul, Pi.smul_apply, smul_eq_mul]) }`. Set `V : Fin m → P.comap (piMap g (Fin h))` to `fun i => ⟨U i, by`. Rewrite using `[Submodule.mem_comap, hUu]`. Conclude with `(u i).2⟩`. Set `f' : (Fin m → A') →ₗ[A'] P.comap (piMap g (Fin h))` to `Fintype.linearCombination A' V`.

Establish `hfs' : f'.comp s' = LinearMap.id`. Use extensionality with `x k`. Apply `hg` to reduce the goal to its premises. Use `congrFun (congrArg Subtype.val (hu (G x))) k` as an intermediate fact. Express the relevant statement in the definitionally equal form `g (x.1 k) = _ at this`.

Express the relevant statement in the definitionally equal form `g ((f' (σ x)).1 k) = g (x.1 k)`. Rewrite using `[this]`. Simplify using `[f', V, Fintype.linearCombination_apply, Finset.sum_apply, hσ, hU]`. Use `⟨Module.Finite.of_surjective f' fun x => ⟨s' x, LinearMap.congr_fun hfs' x⟩, Module.Projective.of_split s' f' hfs', le_antisymm (fun x hx => ?_) (Submodule.span_le.2 ?_)⟩` and prove the remaining obligations. Use `congrArg Subtype.val (hu ⟨x, hx⟩)` as an intermediate fact.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at this`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨U i, (V i).2, hUu i⟩)`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hx`.
-/
theorem lattice_comap_finite_projective_span : ∀ (B : Type) [CommRing B] [IsDomain B] (h : ℕ) (ϖ : B) (P : Submodule B (Fin h → B)) [Module.Finite B P] [Module.Projective B P], ϖ ≠ 0 → baseOf ϖ h ≤ P → ∃ T : Set B, T.Finite ∧ ∀ (A' : Type) [CommRing A'] [IsDomain A'] [IsIntegrallyClosed A'] (g : A' →+* B), Function.Injective g → g.IsIntegral → T ⊆ Set.range g → Module.Finite A' (P.comap (piMap g (Fin h))) ∧ Module.Projective A' (P.comap (piMap g (Fin h))) ∧ P = Submodule.span B (piMap g (Fin h) '' (P.comap (piMap g (Fin h)) : Set (Fin h → A'))) := by
  intro B _ _ h ϖ P _ _ h0 hb
  classical
  obtain ⟨m, f, s, -, -, hfs⟩ := Module.Finite.exists_comp_eq_id_of_projective B P
  have he : ∀ k : Fin h, ϖ • (Pi.single k 1 : Fin h → B) ∈ P := fun k =>
    hb (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
  let u : Fin m → P := fun i => f (Pi.single i 1)
  have hu : ∀ x : P, x = ∑ i, s x i • u i := fun x => by
    have h1 : f (s x) = x := LinearMap.congr_fun hfs x
    conv_lhs => rw [← h1, pi_eq_sum_univ' (s x)]
    simp only [map_sum, map_smul, u]
  refine ⟨insert ϖ (Set.range (fun q : Fin m × Fin h => (u q.1).1 q.2) ∪
    Set.range (fun q : Fin h × Fin m => s ⟨_, he q.1⟩ q.2)),
    ((Set.finite_range _).union (Set.finite_range _)).insert _, ?_⟩
  intro A' _ _ _ g hg hi hT
  obtain ⟨a, ha⟩ := hT (Set.mem_insert _ _)
  have hU : ∀ i k, ∃ z, g z = (u i).1 k := fun i k => hT (Set.mem_insert_of_mem _ (Or.inl ⟨(i, k), rfl⟩))
  have hc : ∀ k i, ∃ z, g z = s ⟨_, he k⟩ i := fun k i => hT (Set.mem_insert_of_mem _ (Or.inr ⟨(k, i), rfl⟩))
  choose U hU using hU
  choose c hc using hc
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact h0 (by rw [← ha, map_zero])
  have hpi : ∀ (x : Fin h → A') k, piMap g (Fin h) x k = g (x k) := fun _ _ => rfl
  have hUu : ∀ i, piMap g (Fin h) (U i) = (u i).1 := fun i => funext fun k => hU i k
  let G : P.comap (piMap g (Fin h)) → P := fun x => ⟨piMap g (Fin h) x.1, x.2⟩
  have hσ : ∀ x i, ∃ z, g z = s (G x) i := fun x i => by
    have h1 : ϖ • G x = ∑ k, g (x.1 k) • (⟨_, he k⟩ : P) := by
      apply Subtype.ext
      funext k
      simp [G, hpi, Finset.sum_apply, Pi.single_apply, mul_comm]
    have h2 : g a * s (G x) i = g (∑ k, x.1 k * c k i) := by
      have := congrFun (congrArg s h1) i
      simp only [map_smul, map_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [ha, this, map_sum]
      simp only [map_mul, hc]
    obtain ⟨z, hz⟩ := (GlobalTheory.T.divisibility_lattice_descends_integral_ext A' B g hg hi).1 a _ ha0 ⟨_, h2.symm⟩
    rw [hz, map_mul, ha] at h2
    exact ⟨z, (mul_left_cancel₀ h0 h2).symm⟩
  choose σ hσ using hσ
  let s' : P.comap (piMap g (Fin h)) →ₗ[A'] (Fin m → A') :=
    { toFun := σ
      map_add' := fun x y => funext fun i => hg (by
        have : G (x + y) = G x + G y := Subtype.ext (map_add (piMap g (Fin h)) x.1 y.1)
        rw [Pi.add_apply, map_add, hσ, hσ, hσ, this, map_add, Pi.add_apply])
      map_smul' := fun r x => funext fun i => hg (by
        have : G (r • x) = g r • G x := Subtype.ext (map_smulₛₗ (piMap g (Fin h)) r x.1)
        rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_mul, hσ, hσ, this, map_smul, Pi.smul_apply, smul_eq_mul]) }
  let V : Fin m → P.comap (piMap g (Fin h)) := fun i => ⟨U i, by
    rw [Submodule.mem_comap, hUu]; exact (u i).2⟩
  let f' : (Fin m → A') →ₗ[A'] P.comap (piMap g (Fin h)) := Fintype.linearCombination A' V
  have hfs' : f'.comp s' = LinearMap.id := by
    ext x k
    apply hg
    have := congrFun (congrArg Subtype.val (hu (G x))) k
    change g (x.1 k) = _ at this
    change g ((f' (σ x)).1 k) = g (x.1 k)
    rw [this]
    simp [f', V, Fintype.linearCombination_apply, Finset.sum_apply, hσ, hU]
  refine ⟨Module.Finite.of_surjective f' fun x => ⟨s' x, LinearMap.congr_fun hfs' x⟩,
    Module.Projective.of_split s' f' hfs', le_antisymm (fun x hx => ?_) (Submodule.span_le.2 ?_)⟩
  · have := congrArg Subtype.val (hu ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨U i, (V i).2, hUu i⟩)
  · rintro _ ⟨x, hx, rfl⟩
    exact hx

end GlobalTheory.RingChain
