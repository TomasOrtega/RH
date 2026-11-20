import Development.EtaleCohomology.WeilConjectures.ContinCut
import Mathlib.NumberTheory.Padics.ProperSpace

namespace LateralTheory.EWeil.ChevPf

open Topology

/- English proof (translation)
Introduce `l _ M _ _ _ K hK h0 N`. Take `⟨r, π, hπ⟩` from `Module.Finite.exists_fin' ℤ_[l] M`. Set `V : ℕ → Set (Fin r → ℤ_[l])` to `fun k => ((K k).comap π : Set (Fin r → ℤ_[l]))`. Establish `hc : ∀ k, IsCompact (V k)`. Introduce `k`.

Take `⟨s, g, hg⟩` from `Module.Finite.exists_fin' ℤ_[l] ((K k).comap π)`. Establish `: V k = Set.range (((K k).comap π).subtype.comp g)`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`.

Take `⟨a, ha⟩` from `hg ⟨z, hz⟩`. Conclude with `⟨a, by simp [ha]⟩`. Introduce and unpack `⟨a, rfl⟩`. Conclude with `(g a).2`. Rewrite using `[this]`.

Conclude with `isCompact_range (LinearMap.continuous_on_pi _)`. Establish `hdir : Directed (· ⊇ ·) V`. Introduce `a b`. Use `⟨max a b, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`.

Conclude with `hK (le_max_left a b) hz`. Introduce `z hz`. Conclude with `hK (le_max_right a b) hz`. Set `ε : ℝ` to `(l : ℝ) ^ (-(N : ℤ))`. Establish `hε : 0 < ε`.

Establish `: (0 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).pos`. Check the signs of the components of the expression. Set `U : Set (Fin r → ℤ_[l])` to `{z | ∃ c w, π c = 0 ∧ (∀ i, ‖w i‖ ≤ ε) ∧ z = c + w}`. Establish `hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x`. Introduce `x hx`.

Establish `hx0 : π x = 0` using `h0 _ (fun k => Set.mem_iInter.1 hx k)`. Use `Filter.mem_of_superset (Metric.ball_mem_nhds x hε) ?_` and prove the remaining obligations. Introduce `z hz`. Use `⟨x, z - x, hx0, fun i => ?_, by abel⟩` and prove the remaining obligations. Establish `h1 : dist (z i) (x i) ≤ dist z x` using `dist_le_pi_dist z x i`.

Rewrite `hz` using `[Metric.mem_ball]`. Rewrite using `[Pi.sub_apply, ← dist_eq_norm]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨k, hk⟩` from `exists_subset_nhds_of_isCompact hdir hc hU`. Use `⟨k, fun y hy => ?_⟩` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `hπ y`. Take `⟨c, w, hc0, hw, rfl⟩` from `hk (show x ∈ V k from hy)`. Establish `hu : ∀ i, ∃ u : ℤ_[l], w i = (l : ℤ_[l]) ^ N * u`. Introduce `i`. Use `(PadicInt.norm_le_pow_iff_mem_span_pow (w i) N).1 (hw i)` as an intermediate fact.

Take `⟨u, hu⟩` from `Ideal.mem_span_singleton'.1 this`. Conclude with `⟨u, by rw [← hu, mul_comm]⟩`. Use `choose u hu using hu`. Use `⟨π u, ?_⟩` and prove the remaining obligations. Establish `: w = (l : ℤ_[l]) ^ N • u` using `funext fun i => by simp [hu i]`.

Rewrite using `[map_add, hc0, zero_add, this, map_smul]`.
-/
theorem Chev_of : LateralTheory.EWeil.ContinCut.Chev := by
  intro l _ M _ _ _ K hK h0 N
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' ℤ_[l] M
  let V : ℕ → Set (Fin r → ℤ_[l]) := fun k => ((K k).comap π : Set (Fin r → ℤ_[l]))
  have hc : ∀ k, IsCompact (V k) := by
    intro k
    obtain ⟨s, g, hg⟩ := Module.Finite.exists_fin' ℤ_[l] ((K k).comap π)
    have : V k = Set.range (((K k).comap π).subtype.comp g) := by
      ext z
      constructor
      · intro hz
        obtain ⟨a, ha⟩ := hg ⟨z, hz⟩
        exact ⟨a, by simp [ha]⟩
      · rintro ⟨a, rfl⟩
        exact (g a).2
    rw [this]
    exact isCompact_range (LinearMap.continuous_on_pi _)
  have hdir : Directed (· ⊇ ·) V := by
    intro a b
    refine ⟨max a b, ?_, ?_⟩
    · intro z hz; exact hK (le_max_left a b) hz
    · intro z hz; exact hK (le_max_right a b) hz
  let ε : ℝ := (l : ℝ) ^ (-(N : ℤ))
  have hε : 0 < ε := by
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  let U : Set (Fin r → ℤ_[l]) :=
    {z | ∃ c w, π c = 0 ∧ (∀ i, ‖w i‖ ≤ ε) ∧ z = c + w}
  have hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x := by
    intro x hx
    have hx0 : π x = 0 := h0 _ (fun k => Set.mem_iInter.1 hx k)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x hε) ?_
    intro z hz
    refine ⟨x, z - x, hx0, fun i => ?_, by abel⟩
    have h1 : dist (z i) (x i) ≤ dist z x := dist_le_pi_dist z x i
    rw [Metric.mem_ball] at hz
    rw [Pi.sub_apply, ← dist_eq_norm]
    linarith
  obtain ⟨k, hk⟩ := exists_subset_nhds_of_isCompact hdir hc hU
  refine ⟨k, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := hπ y
  obtain ⟨c, w, hc0, hw, rfl⟩ := hk (show x ∈ V k from hy)
  have hu : ∀ i, ∃ u : ℤ_[l], w i = (l : ℤ_[l]) ^ N * u := by
    intro i
    have := (PadicInt.norm_le_pow_iff_mem_span_pow (w i) N).1 (hw i)
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨u, by rw [← hu, mul_comm]⟩
  choose u hu using hu
  refine ⟨π u, ?_⟩
  have : w = (l : ℤ_[l]) ^ N • u := funext fun i => by simp [hu i]
  rw [map_add, hc0, zero_add, this, map_smul]

end LateralTheory.EWeil.ChevPf
