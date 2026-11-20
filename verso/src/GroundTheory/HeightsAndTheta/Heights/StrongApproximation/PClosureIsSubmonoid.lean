import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

/- English proof (translation)
Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by omega)`. Establish `hle : Fintype.card (E ≃ₐ[F] E) ≤ 2` using `h2 ▸ AlgEquiv.card_le`. Establish `hge : 2 ≤ Fintype.card (E ≃ₐ[F] E)` using `Fintype.one_lt_card_iff.2 ⟨c, 1, hc⟩`. Establish `hcard : Fintype.card (E ≃ₐ[F] E) = 2` using `le_antisymm hle hge`. Establish `hsq : c ^ 2 = 1` using `hcard ▸ pow_card_eq_one`.

Use `congrArg (fun g : E ≃ₐ[F] E => g x) hsq` as an intermediate fact. Simplify `this` using `[pow_two]`.
-/
theorem invol_of_quadratic {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E)
    (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E) : c (c x) = x := by
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hle : Fintype.card (E ≃ₐ[F] E) ≤ 2 := h2 ▸ AlgEquiv.card_le
  have hge : 2 ≤ Fintype.card (E ≃ₐ[F] E) :=
    Fintype.one_lt_card_iff.2 ⟨c, 1, hc⟩
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := le_antisymm hle hge
  have hsq : c ^ 2 = 1 := hcard ▸ pow_card_eq_one
  have := congrArg (fun g : E ≃ₐ[F] E => g x) hsq
  simpa [pow_two] using this

/- English proof (translation)
Simplify using `[sigA, inclA, Algebra.TensorProduct.map_tmul]`.
-/
theorem sigA_inclA_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) (x : E) : sigA c (inclA F E x) = inclA F E (c x) := by
  simp [sigA, inclA, Algebra.TensorProduct.map_tmul]

/- English proof (translation)
Take `⟨hdet, hJ⟩` from `hγ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h` using `(RingHom.map_det (inclA F E) γ).symm`. Rewrite `h` using `[hdet, map_one]`. Conclude with `h`.

Establish `hmap : (γ.map (inclA F E)).map (sigA c) = (γ.map c.toRingHom).map (inclA F E)`. Use extensionality with `i j`. Simplify using `[sigA_inclA_gen]`. Rewrite using `[hmap, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hJ]`.
-/
theorem map_mem_SU_AE {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) {γ : Matrix (Fin N) (Fin N) E}
    (hγ : γ ∈ SU c.toRingHom J) :
    γ.map (inclA F E) ∈ SU (sigA c) (J.map (inclA F E)) := by
  obtain ⟨hdet, hJ⟩ := hγ
  refine ⟨?_, ?_⟩
  · have h := (RingHom.map_det (inclA F E) γ).symm
    rw [hdet, map_one] at h
    exact h
  · have hmap : (γ.map (inclA F E)).map (sigA c) = (γ.map c.toRingHom).map (inclA F E) := by
      ext i j; simp [sigA_inclA_gen]
    rw [hmap, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hJ]

/- English proof (translation)
Introduce `F E _ _ _ _ _ c h2 hc N J hJ _ e f he hff hef _ _`. Establish `hσ : ∀ x, c.toRingHom (c.toRingHom x) = x` using `invol_of_quadratic c h2 hc`. Establish `hJ' : Jᵀ = J.map c.toRingHom` using `hJ`. Take `⟨-, -, -, hmat⟩` from `h₁ F E c h2 hc`. Take `⟨hmul, -, -, hclosed⟩` from `hmat N (J.map (inclA F E))`.

Take `⟨hde, hdf⟩` from `h₂ F E c h2 hc N J hJ e f he hff hef`. Use `set ι : Matrix (Fin N) (Fin N) E → Matrix (Fin N) (Fin N) (AE F E) := fun γ => γ.map (inclA F E)`. Establish `himg : ι '' SU c.toRingHom J ⊆ SU (sigA c) (J.map (inclA F E))`. Introduce and unpack `_ ⟨γ, hγ, rfl⟩`. Conclude with `map_mem_SU_AE c J hγ`.

Use `⟨closure_minimal himg hclosed, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `subset_closure` to reduce the goal to its premises. Conclude with `⟨1, one_mem_SU, by simp⟩`. Introduce `a ha b hb`. Use `map_mem_closure₂ hmul ha hb ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨γ, hγ, rfl⟩ _ ⟨δ, hδ, rfl⟩`. Conclude with `⟨γ * δ, mul_mem_SU hγ hδ, by simp [Matrix.map_mul]⟩`. Establish `hsub : ∀ {a b : Fin N → E}, hf c.toRingHom J a a = 0 → closure (ι '' eichAlong c.toRingHom J a b) ⊆ Cl c J` using `fun ha => closure_mono (Set.image_mono (eichAlong_sub hσ hJ' ha))`. Introduce and unpack `M (hM | hM)`. Conclude with `hsub he (hde hM)`.

Conclude with `hsub hff (hdf hM)`.
-/
theorem ClosureIsSubmonoid.proof (h₁ : AETopologicalRing.Statement) (h₂ : EichlerDense.Statement) :
    ClosureIsSubmonoid.Statement := by
  intro F E _ _ _ _ _ c h2 hc N J hJ _ e f he hff hef _ _
  have hσ : ∀ x, c.toRingHom (c.toRingHom x) = x := invol_of_quadratic c h2 hc
  have hJ' : Jᵀ = J.map c.toRingHom := hJ
  obtain ⟨-, -, -, hmat⟩ := h₁ F E c h2 hc
  obtain ⟨hmul, -, -, hclosed⟩ := hmat N (J.map (inclA F E))
  obtain ⟨hde, hdf⟩ := h₂ F E c h2 hc N J hJ e f he hff hef
  set ι : Matrix (Fin N) (Fin N) E → Matrix (Fin N) (Fin N) (AE F E) := fun γ => γ.map (inclA F E)
  have himg : ι '' SU c.toRingHom J ⊆ SU (sigA c) (J.map (inclA F E)) := by
    rintro _ ⟨γ, hγ, rfl⟩; exact map_mem_SU_AE c J hγ
  refine ⟨closure_minimal himg hclosed, ?_, ?_, ?_⟩
  · apply subset_closure
    exact ⟨1, one_mem_SU, by simp⟩
  · intro a ha b hb
    refine map_mem_closure₂ hmul ha hb ?_
    rintro _ ⟨γ, hγ, rfl⟩ _ ⟨δ, hδ, rfl⟩
    exact ⟨γ * δ, mul_mem_SU hγ hδ, by simp [Matrix.map_mul]⟩
  · have hsub : ∀ {a b : Fin N → E}, hf c.toRingHom J a a = 0 →
        closure (ι '' eichAlong c.toRingHom J a b) ⊆ Cl c J := fun ha =>
      closure_mono (Set.image_mono (eichAlong_sub hσ hJ' ha))
    rintro M (hM | hM)
    · exact hsub he (hde hM)
    · exact hsub hff (hdf hM)

end StrongApprox

end GroundTheory.Heights₂.Heights
