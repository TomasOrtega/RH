import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori

/- English proof (translation)
Conclude with `IsLocalRing.surjective_units_map_of_local_ringHom _ IsLocalRing.residue_surjective inferInstance`.
-/
private theorem unitRes_surj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : Function.Surjective (unitRes k) := by
  exact IsLocalRing.surjective_units_map_of_local_ringHom _ IsLocalRing.residue_surjective inferInstance

/- English proof (translation)
Introduce `k _ _ _ _ s θ μ hθ hμ a b hab`. Establish `key : (∀ u, θ a (unitRes k u) = θ b (unitRes k u)) → False`. Introduce `h`. Apply `hab` to reduce the goal to its premises. Apply `hθ` to reduce the goal to its premises.

Use `MonoidHom.ext fun w => ?_` and prove the remaining obligations. Take `⟨u, rfl⟩` from `unitRes_surj k w`. Conclude with `h u`. Establish `hres : ∀ c u, UpperTheory.TNZ.res (μ c) u = θ c (unitRes k u)` using `fun c u => hμ c u`. Establish `hdiv : ∀ u, UpperTheory.TNZ.res (μ a / μ b) u = θ a (unitRes k u) / θ b (unitRes k u)`.

Introduce `u`. Use `show (μ a / μ b) (unitIncl k u) = _`. Rewrite using `[MonoidHom.div_apply, hμ a u, hμ b u]`. Use `⟨fun h => key fun u => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hres, ← hres, h]`.

Unfold `UpperTheory.TNZ.cc UpperTheory.TNZ.cond set S := {c : ℕ | ∀ u : (𝒪[k])ˣ, (u : 𝒪[k]) - 1 ∈ 𝓂[k] ^ c → UpperTheory.TNZ.res (μ a / μ b) u = 1} with hS`. Establish `h1 : 1 ∈ S`. Introduce `u hu`. Rewrite `hu` using `[pow_one]`. Establish `hr : unitRes k u = 1`.

Use `ext`. Simplify using `only [unitRes, Units.coe_map, MonoidHom.coe_coe, Units.val_one]`. Establish `hz : IsLocalRing.residue 𝒪[k] ((u : 𝒪[k]) - 1) = 0` using `(IsLocalRing.residue_eq_zero_iff _).2 hu`. Rewrite `hz` using `[map_sub, map_one, sub_eq_zero]`. Conclude with `hz`.

Rewrite using `[hdiv, hr, map_one, map_one, div_one]`. Establish `h0 : 0 ∉ S`. Introduce `h`. Apply `key` to reduce the goal to its premises. Introduce `u`.

Use `h u (by simp)` as an intermediate fact. Rewrite `this` using `[hdiv, div_eq_one]`. Conclude with `this`. Apply `le_antisymm (Nat.sInf_le h1)` to reduce the goal to its premises. Rewrite using `[Nat.one_le_iff_ne_zero]`.

Introduce `hz`. Break down `Nat.sInf_eq_zero.1 hz with h | h` into its components or cases. Conclude with `h0 h`. Rewrite `h1` using `[h]`. Conclude with `h1`.
-/
theorem UpperTheory.Gal.TypesAndIwahori.grpFacts :
    UpperTheory.Gal.TypesAndIwahori.GrpFacts := by
  intro k _ _ _ _ s θ μ hθ hμ a b hab
  have key : (∀ u, θ a (unitRes k u) = θ b (unitRes k u)) → False := by
    intro h
    apply hab
    apply hθ
    refine MonoidHom.ext fun w => ?_
    obtain ⟨u, rfl⟩ := unitRes_surj k w
    exact h u
  have hres : ∀ c u, UpperTheory.TNZ.res (μ c) u = θ c (unitRes k u) := fun c u => hμ c u
  have hdiv : ∀ u, UpperTheory.TNZ.res (μ a / μ b) u = θ a (unitRes k u) / θ b (unitRes k u) := by
    intro u
    show (μ a / μ b) (unitIncl k u) = _
    rw [MonoidHom.div_apply, hμ a u, hμ b u]
  refine ⟨fun h => key fun u => ?_, ?_⟩
  · rw [← hres, ← hres, h]
  · unfold UpperTheory.TNZ.cc UpperTheory.TNZ.cond
    set S := {c : ℕ | ∀ u : (𝒪[k])ˣ, (u : 𝒪[k]) - 1 ∈ 𝓂[k] ^ c → UpperTheory.TNZ.res (μ a / μ b) u = 1} with hS
    have h1 : 1 ∈ S := by
      intro u hu
      rw [pow_one] at hu
      have hr : unitRes k u = 1 := by
        ext
        simp only [unitRes, Units.coe_map, MonoidHom.coe_coe, Units.val_one]
        have hz : IsLocalRing.residue 𝒪[k] ((u : 𝒪[k]) - 1) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hu
        rw [map_sub, map_one, sub_eq_zero] at hz
        exact hz
      rw [hdiv, hr, map_one, map_one, div_one]
    have h0 : 0 ∉ S := by
      intro h
      apply key
      intro u
      have := h u (by simp)
      rw [hdiv, div_eq_one] at this
      exact this
    apply le_antisymm (Nat.sInf_le h1)
    rw [Nat.one_le_iff_ne_zero]
    intro hz
    rcases Nat.sInf_eq_zero.1 hz with h | h
    · exact h0 h
    · rw [h] at h1
      exact h1
