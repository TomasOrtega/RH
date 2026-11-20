import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.ZeroRight

noncomputable section

namespace PositivityTheory.Rg.Sw.LC

namespace CoreA

variable {V : Type} [AddCommGroup V] [Module ℂ V] {φ : V → V → ℂ}

namespace PosH

variable (h : PosH φ)
include h

/- English proof (translation)
Set `b` to `Module.finBasis ℂ W`. Set `L : V →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ)` to `{ toFun := fun v k => φ (b k : V) v map_add' := fun v w => by funext k; exact h.add _ v w map_smul' := fun r v => by funext k; simp [h.smul] }`. Establish `hker : LinearMap.ker L ≤ h.perp W`. Introduce `v hv w hw`. Establish `hv' : ∀ k, φ (b k : V) v = 0` using `fun k => congrFun (LinearMap.mem_ker.1 hv) k`.

Establish `hw' : w = ∑ k, (b.repr ⟨w, hw⟩ k) • (b k : V)`. Establish `h2 : ((∑ k, b.repr ⟨w, hw⟩ k • b k : W) : V) = w` using `by rw [b.sum_repr]`. Rewrite `h2` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at h2`. Conclude with `h2.symm`.

Rewrite using `[hw', h.sum_left]`. Simplify using `[hv']`. Establish `hrank` using `LinearMap.finrank_range_add_finrank_ker L`. Establish `hr : Module.finrank ℂ (LinearMap.range L) ≤ Module.finrank ℂ W`. Combine the equalities or inequalities in the displayed calculation.

Establish `hk : Module.finrank ℂ (LinearMap.ker L) ≤ Module.finrank ℂ (h.perp W)` using `Submodule.finrank_mono hker`. Establish `hsum` using `Submodule.finrank_sup_add_finrank_inf_eq W (h.perp W)`. Rewrite `hsum` using `[h.inf_perp, finrank_bot]`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Apply `le_antisymm (Submodule.finrank_le _)` to reduce the goal to its premises.

Use linear arithmetic over natural numbers and integers.
-/
theorem sup_perp [FiniteDimensional ℂ V] (W : Submodule ℂ V) : W ⊔ h.perp W = ⊤ := by
  classical
  let b := Module.finBasis ℂ W
  let L : V →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    { toFun := fun v k => φ (b k : V) v
      map_add' := fun v w => by funext k; exact h.add _ v w
      map_smul' := fun r v => by funext k; simp [h.smul] }
  have hker : LinearMap.ker L ≤ h.perp W := by
    intro v hv w hw
    have hv' : ∀ k, φ (b k : V) v = 0 := fun k => congrFun (LinearMap.mem_ker.1 hv) k
    have hw' : w = ∑ k, (b.repr ⟨w, hw⟩ k) • (b k : V) := by
      have h2 : ((∑ k, b.repr ⟨w, hw⟩ k • b k : W) : V) = w := by rw [b.sum_repr]
      rw [Submodule.coe_sum] at h2
      simp only [Submodule.coe_smul] at h2
      exact h2.symm
    rw [hw', h.sum_left]
    simp [hv']
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hr : Module.finrank ℂ (LinearMap.range L) ≤ Module.finrank ℂ W := by
    calc Module.finrank ℂ (LinearMap.range L) ≤ Module.finrank ℂ (Fin (Module.finrank ℂ W) → ℂ) :=
          Submodule.finrank_le _
      _ = Module.finrank ℂ W := by simp
  have hk : Module.finrank ℂ (LinearMap.ker L) ≤ Module.finrank ℂ (h.perp W) := Submodule.finrank_mono hker
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W (h.perp W)
  rw [h.inf_perp, finrank_bot] at hsum
  apply Submodule.eq_top_of_finrank_eq
  apply le_antisymm (Submodule.finrank_le _)
  omega

end PosH

end CoreA

open CoreA in
/- English proof (translation)
Introduce `V _ _ _ φ hadd hsmul hherm hpos ι T hT`. Establish `h : PosH φ` using `⟨hadd, hsmul, hherm, hpos⟩`. Use `⟨fun v => ?_, fun v hv hvW => ?_⟩` and prove the remaining obligations. Establish `hv : v ∈ (⨆ i, LinearMap.range (T i)) ⊔ h.perp (⨆ i, LinearMap.range (T i))`. Rewrite using `[h.sup_perp]`.

Discharge the goal by the elementary cases of `trivial`. Take `⟨w, hw, v₀, hv₀, hvw⟩` from `Submodule.mem_sup.1 hv`. Use `⟨v₀, w, by rw [← hvw, add_comm], fun i => ?_, hw⟩` and prove the remaining obligations. Take `⟨j, hj⟩` from `hT i`. Apply `h.definite` to reduce the goal to its premises.

Establish `hmem : T j (T i v₀) ∈ ⨆ i, LinearMap.range (T i)` using `Submodule.mem_iSup_of_mem j (LinearMap.mem_range_self _ _)`. Rewrite using `[hj, hherm (T j (T i v₀)) v₀, hv₀ _ hmem, star_zero]`. Apply `h.definite` to reduce the goal to its premises. Use `Submodule.iSup_induction (motive := fun w => φ w v = 0) _ hvW ?_ (h.zero_left v) ?_` and prove the remaining obligations. Introduce `j w hw`.

Take `⟨u, rfl⟩` from `hw`. Take `⟨j', hj'⟩` from `hT j`. Rewrite using `[hj', hv j', h.zero_right]`. Introduce `x y hx hy`. Rewrite using `[h.add_left, hx, hy, add_zero]`.
-/
theorem semiFam : SemiFam := by
  intro V _ _ _ φ hadd hsmul hherm hpos ι T hT
  have h : PosH φ := ⟨hadd, hsmul, hherm, hpos⟩
  refine ⟨fun v => ?_, fun v hv hvW => ?_⟩
  · have hv : v ∈ (⨆ i, LinearMap.range (T i)) ⊔ h.perp (⨆ i, LinearMap.range (T i)) := by
      rw [h.sup_perp]; trivial
    obtain ⟨w, hw, v₀, hv₀, hvw⟩ := Submodule.mem_sup.1 hv
    refine ⟨v₀, w, by rw [← hvw, add_comm], fun i => ?_, hw⟩
    obtain ⟨j, hj⟩ := hT i
    apply h.definite
    have hmem : T j (T i v₀) ∈ ⨆ i, LinearMap.range (T i) :=
      Submodule.mem_iSup_of_mem j (LinearMap.mem_range_self _ _)
    rw [hj, hherm (T j (T i v₀)) v₀, hv₀ _ hmem, star_zero]
  · apply h.definite
    refine Submodule.iSup_induction (motive := fun w => φ w v = 0) _ hvW ?_ (h.zero_left v) ?_
    · intro j w hw
      obtain ⟨u, rfl⟩ := hw
      obtain ⟨j', hj'⟩ := hT j
      rw [hj', hv j', h.zero_right]
    · intro x y hx hy
      rw [h.add_left, hx, hy, add_zero]

end PositivityTheory.Rg.Sw.LC
