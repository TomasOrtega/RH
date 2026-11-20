import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SmoothRepIrreducibleSubcontainingVector

noncomputable section

namespace UpperTheory.NonzeroTypeTheory

namespace SubrepresentationTransport

variable {K : Type} [Group K] {m : ℕ}

def transport (V : Representation ℂ K (Fin m → ℂ)) (S : Submodule ℂ (Fin m → ℂ))
    (hS : ∀ k, ∀ s ∈ S, V k s ∈ S) {d : ℕ} (e : (Fin d → ℂ) ≃ₗ[ℂ] S) : Representation ℂ K (Fin d → ℂ) where
  toFun k := e.symm.toLinearMap ∘ₗ (V k).restrict (fun s hs => hS k s hs) ∘ₗ e.toLinearMap
  map_one' := by
    refine LinearMap.ext fun v => ?_
    apply e.injective
    apply Subtype.ext
    simp [LinearMap.restrict_apply]
  map_mul' a b := by
    refine LinearMap.ext fun v => ?_
    apply e.injective
    apply Subtype.ext
    simp [LinearMap.restrict_apply]

/- English proof (translation)
Simplify using `[transport, LinearMap.restrict_apply]`.
-/
lemma transport_apply (V : Representation ℂ K (Fin m → ℂ)) (S : Submodule ℂ (Fin m → ℂ))
    (hS : ∀ k, ∀ s ∈ S, V k s ∈ S) {d : ℕ} (e : (Fin d → ℂ) ≃ₗ[ℂ] S) (k : K) (v : Fin d → ℂ) :
    ((e (transport V S hS e k v) : S) : Fin m → ℂ) = V k (e v) := by
  simp [transport, LinearMap.restrict_apply]

end SubrepresentationTransport

open SubrepresentationTransport in
/- English proof (translation)
Introduce `K _ _ _ m V hV S hS0 hS hmin`. Use `set d := Module.finrank ℂ S`. Set `e : (Fin d → ℂ) ≃ₗ[ℂ] S` to `(Module.finBasis ℂ S).equivFun.symm`. Set `ξ` to `transport V S hS e`. Set `ι : (Fin d → ℂ) →ₗ[ℂ] (Fin m → ℂ)` to `S.subtype ∘ₗ e.toLinearMap`.

Establish `hι : ∀ v, ι v = ((e v : S) : Fin m → ℂ)` using `fun v => rfl`. Establish `hinj : Function.Injective ι` using `Subtype.val_injective.comp e.injective`. Establish `hint : ∀ k v, V k (ι v) = ι (ξ k v)`. Introduce `k v`. Rewrite using `[hι, hι]`.

Conclude with `(transport_apply V S hS e k v).symm`. Establish `hrange : LinearMap.range ι = S`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, rfl⟩`.

Conclude with `(e v).2`. Introduce `hx`. Conclude with `⟨e.symm ⟨x, hx⟩, by rw [hι]; simp⟩`. Use `⟨d, ξ, ι, hinj, hrange, hint, ?_, ?_⟩` and prove the remaining obligations. Establish `: Nontrivial S` using `Submodule.nontrivial_iff_ne_bot.mpr hS0`.

Establish `: Nontrivial (Fin d → ℂ)` using `e.toEquiv.nontrivial`. Establish `hne : (⊥ : Subrepresentation ξ) ≠ ⊤`. Introduce `h`. Establish `h'` using `congrArg Subrepresentation.toSubmodule h`. Conclude with `bot_ne_top h'`.

Establish `: Nontrivial (Subrepresentation ξ)` using `⟨⟨⊥, ⊤, hne⟩⟩`. Use `{ eq_bot_or_eq_top := ?_ }` and prove the remaining obligations. Introduce `W`. Establish `hle : W.toSubmodule.map ι ≤ S`. Rewrite using `[← hrange]`.

Conclude with `LinearMap.map_le_range`. Establish `hst : ∀ k, ∀ s ∈ W.toSubmodule.map ι, V k s ∈ W.toSubmodule.map ι`. Introduce and unpack `k s ⟨w, hw, rfl⟩`. Conclude with `⟨ξ k w, W.apply_mem_toSubmodule k hw, (hint k w).symm⟩`. Break down `hmin _ hle hst with h | h` into its components or cases.

Use `left`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Apply `Submodule.map_injective_of_injective hinj` to reduce the goal to its premises. Rewrite using `[h]`. Conclude with `(Submodule.map_bot ι).symm`.

Use `right`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Apply `Submodule.map_injective_of_injective hinj` to reduce the goal to its premises. Rewrite using `[h, ← hrange, LinearMap.range_eq_map]`. Both sides reduce to the same expression.

Introduce `v`. Establish `hset : {k : K | ξ k v = v} = {k : K | V k (ι v) = ι v}`. Use extensionality with `k`. Express the relevant statement in the definitionally equal form `ξ k v = v ↔ V k (ι v) = ι v`. Rewrite using `[hint]`.

Conclude with `hinj.eq_iff.symm`. Rewrite using `[hset]`. Conclude with `hV (ι v)`.
-/
theorem minimalSubrepresentation_holds : SmoothRepMinimalSubrepresentation := by
  intro K _ _ _ m V hV S hS0 hS hmin
  set d := Module.finrank ℂ S
  let e : (Fin d → ℂ) ≃ₗ[ℂ] S := (Module.finBasis ℂ S).equivFun.symm
  let ξ := transport V S hS e
  let ι : (Fin d → ℂ) →ₗ[ℂ] (Fin m → ℂ) := S.subtype ∘ₗ e.toLinearMap
  have hι : ∀ v, ι v = ((e v : S) : Fin m → ℂ) := fun v => rfl
  have hinj : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hint : ∀ k v, V k (ι v) = ι (ξ k v) := by
    intro k v
    rw [hι, hι]
    exact (transport_apply V S hS e k v).symm
  have hrange : LinearMap.range ι = S := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (e v).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by rw [hι]; simp⟩
  refine ⟨d, ξ, ι, hinj, hrange, hint, ?_, ?_⟩
  · have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr hS0
    have : Nontrivial (Fin d → ℂ) := e.toEquiv.nontrivial
    have hne : (⊥ : Subrepresentation ξ) ≠ ⊤ := by
      intro h
      have h' := congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top h'
    have : Nontrivial (Subrepresentation ξ) := ⟨⟨⊥, ⊤, hne⟩⟩
    refine { eq_bot_or_eq_top := ?_ }
    intro W
    have hle : W.toSubmodule.map ι ≤ S := by
      rw [← hrange]
      exact LinearMap.map_le_range
    have hst : ∀ k, ∀ s ∈ W.toSubmodule.map ι, V k s ∈ W.toSubmodule.map ι := by
      rintro k s ⟨w, hw, rfl⟩
      exact ⟨ξ k w, W.apply_mem_toSubmodule k hw, (hint k w).symm⟩
    rcases hmin _ hle hst with h | h
    · left
      apply Subrepresentation.toSubmodule_injective
      apply Submodule.map_injective_of_injective hinj
      rw [h]
      exact (Submodule.map_bot ι).symm
    · right
      apply Subrepresentation.toSubmodule_injective
      apply Submodule.map_injective_of_injective hinj
      rw [h, ← hrange, LinearMap.range_eq_map]
      rfl
  · intro v
    have hset : {k : K | ξ k v = v} = {k : K | V k (ι v) = ι v} := by
      ext k
      change ξ k v = v ↔ V k (ι v) = ι v
      rw [hint]
      exact hinj.eq_iff.symm
    rw [hset]
    exact hV (ι v)

end UpperTheory.NonzeroTypeTheory
