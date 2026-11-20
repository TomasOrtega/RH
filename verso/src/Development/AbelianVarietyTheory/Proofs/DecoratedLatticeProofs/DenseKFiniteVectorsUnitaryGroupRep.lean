import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspace

open scoped InnerProductSpace

namespace GlobalTheory.CompactRep

/- English proof (translation)
Set `N : Submodule ℂ H` to `{ carrier := {v : H | ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧ ∀ k, ∀ x ∈ S, π k x ∈ S} add_mem' := by`. Introduce and unpack `a b ⟨S, hS, ha, hSs⟩ ⟨T, hT, hb, hTs⟩`. Use `⟨S ⊔ T, inferInstance, Submodule.add_mem_sup ha hb, ?_⟩` and prove the remaining obligations. Introduce `k x hx`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hx`.

Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (hSs k y hy) (hTs k z hz)`. Use the proof step `zero_mem' := ⟨⊥, inferInstance, Submodule.zero_mem _, by`. Introduce `k x hx`. Rewrite `hx`, the goal using `[Submodule.mem_bot]`.

Rewrite using `[hx, map_zero]⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨S, hS, ha, hSs⟩`. Conclude with `⟨S, hS, S.smul_mem c ha, hSs⟩ }`. Establish `hNst : ∀ k, ∀ a ∈ N, π k a ∈ N`.

Introduce and unpack `k a ⟨S, hS, ha, hSs⟩`. Conclude with `⟨S, hS, hSs k a ha, hSs⟩`. Establish `hinner : ∀ k a b, ⟪π k a, π k b⟫_ℂ = ⟪a, b⟫_ℂ` using `fun k a b => (LinearIsometry.mk (π k).toLinearMap (hiso k)).inner_map_map a b`. Establish `hinv : ∀ k a, π k (π k⁻¹ a) = a`. Introduce `k a`.

Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]`. Establish `hOst : ∀ k, ∀ w ∈ Nᗮ, π k w ∈ Nᗮ`. Introduce `k w hw`. Rewrite `hw`, the goal using `[Submodule.mem_orthogonal]`. Introduce `a ha`.

Rewrite using `[← hinv k a, hinner]`. Conclude with `hw _ (hNst _ a ha)`. Establish `hbot : Nᗮ = ⊥`. Assume the negation of the conclusion as `hne`. Use `haveI : Nontrivial Nᗮ := Submodule.nontrivial_iff_ne_bot.2 hne`.

Set `ρ : K →* (Nᗮ →L[ℂ] Nᗮ)` to `{ toFun := fun k => ((π k).comp Nᗮ.subtypeL).codRestrict Nᗮ (fun w => hOst k w w.2) map_one' := by`. Use extensionality with `w`. Simplify using the standard rewrite rules. Use the proof step `map_mul' := by`. Introduce `k l`.

Use extensionality with `w`. Use `show π (k * l) w = π k (π l w)`. Rewrite using `[map_mul, ContinuousLinearMap.mul_apply] }`. Establish `hρ : ∀ k (w : Nᗮ), ((ρ k w : Nᗮ) : H) = π k w` using `fun k w => rfl`. Take `⟨S, hS0, hSf, hSs⟩` from `exists_finiteDimensional_invariant K Nᗮ ρ (fun k w => hiso k w) (fun w => (hcont w).subtype_mk _)`.

Apply `hS0` to reduce the goal to its premises. Rewrite using `[Submodule.eq_bot_iff]`. Introduce `w hw`. Establish `hwN : (w : H) ∈ N`. Use `⟨S.map Nᗮ.subtype, inferInstance, ⟨w, hw, rfl⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `k x ⟨y, hy, rfl⟩`. Conclude with `⟨ρ k y, hSs k y hy, rfl⟩`. Establish `h0 : ⟪(w : H), (w : H)⟫_ℂ = 0` using `(Submodule.mem_orthogonal _ _).1 w.2 _ hwN`. Conclude with `Subtype.ext (inner_self_eq_zero.1 h0)`. Conclude with `Submodule.dense_iff_topologicalClosure_eq_top.2 (Submodule.topologicalClosure_eq_top_iff.2 hbot)`.
-/
theorem dense_finite_vectors (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [SecondCountableTopology K] (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : K →* H →L[ℂ] H)
    (hiso : ∀ k x, ‖π k x‖ = ‖x‖) (hcont : ∀ x, Continuous fun k => π k x) :
    Dense {v : H | ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧
      ∀ k, ∀ x ∈ S, π k x ∈ S} := by
  let N : Submodule ℂ H :=
    { carrier := {v : H | ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧
        ∀ k, ∀ x ∈ S, π k x ∈ S}
      add_mem' := by
        rintro a b ⟨S, hS, ha, hSs⟩ ⟨T, hT, hb, hTs⟩
        refine ⟨S ⊔ T, inferInstance, Submodule.add_mem_sup ha hb, ?_⟩
        intro k x hx
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
        rw [map_add]
        exact Submodule.add_mem_sup (hSs k y hy) (hTs k z hz)
      zero_mem' := ⟨⊥, inferInstance, Submodule.zero_mem _, by
        intro k x hx
        rw [Submodule.mem_bot] at hx ⊢
        rw [hx, map_zero]⟩
      smul_mem' := by
        rintro c a ⟨S, hS, ha, hSs⟩
        exact ⟨S, hS, S.smul_mem c ha, hSs⟩ }
  have hNst : ∀ k, ∀ a ∈ N, π k a ∈ N := by
    rintro k a ⟨S, hS, ha, hSs⟩
    exact ⟨S, hS, hSs k a ha, hSs⟩
  have hinner : ∀ k a b, ⟪π k a, π k b⟫_ℂ = ⟪a, b⟫_ℂ := fun k a b =>
    (LinearIsometry.mk (π k).toLinearMap (hiso k)).inner_map_map a b
  have hinv : ∀ k a, π k (π k⁻¹ a) = a := by
    intro k a
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have hOst : ∀ k, ∀ w ∈ Nᗮ, π k w ∈ Nᗮ := by
    intro k w hw
    rw [Submodule.mem_orthogonal] at hw ⊢
    intro a ha
    rw [← hinv k a, hinner]
    exact hw _ (hNst _ a ha)
  have hbot : Nᗮ = ⊥ := by
    by_contra hne
    haveI : Nontrivial Nᗮ := Submodule.nontrivial_iff_ne_bot.2 hne
    let ρ : K →* (Nᗮ →L[ℂ] Nᗮ) :=
      { toFun := fun k => ((π k).comp Nᗮ.subtypeL).codRestrict Nᗮ (fun w => hOst k w w.2)
        map_one' := by
          ext w
          simp
        map_mul' := by
          intro k l
          ext w
          show π (k * l) w = π k (π l w)
          rw [map_mul, ContinuousLinearMap.mul_apply] }
    have hρ : ∀ k (w : Nᗮ), ((ρ k w : Nᗮ) : H) = π k w := fun k w => rfl
    obtain ⟨S, hS0, hSf, hSs⟩ := exists_finiteDimensional_invariant K Nᗮ ρ
      (fun k w => hiso k w) (fun w => (hcont w).subtype_mk _)
    apply hS0
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hwN : (w : H) ∈ N := by
      refine ⟨S.map Nᗮ.subtype, inferInstance, ⟨w, hw, rfl⟩, ?_⟩
      rintro k x ⟨y, hy, rfl⟩
      exact ⟨ρ k y, hSs k y hy, rfl⟩
    have h0 : ⟪(w : H), (w : H)⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 w.2 _ hwN
    exact Subtype.ext (inner_self_eq_zero.1 h0)
  exact Submodule.dense_iff_topologicalClosure_eq_top.2
    (Submodule.topologicalClosure_eq_top_iff.2 hbot)

/- English proof (translation)
Take `⟨⟨h1, hmul⟩, hiso, hcont⟩` from `hσ`. Establish `hemb : Topology.IsEmbedding (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k)` using `(Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))`. Use `haveI : SecondCountableTopology (Formalism.REAL.KG ε) := hemb.secondCountableTopology`. Establish `hU : ∀ k : Formalism.REAL.KG ε, Formalism.REAL.toMK k ∈ Formalism.MainNotions.S.UJset ε` using `fun k => k.1.2`.

Set `π : Formalism.REAL.KG ε →* (H →L[ℂ] H)` to `{ toFun := fun k => σ (Formalism.REAL.toMK k) map_one' := h1 map_mul' := fun k l => hmul _ (hU k) _ (hU l) }`. Establish `hd` using `dense_finite_vectors (Formalism.REAL.KG ε) H π (fun k x => hiso _ (hU k) x) (fun x => (hcont x).comp_continuous hemb.continuous hU)`. Use `hd.mono ?_` and prove the remaining obligations. Introduce and unpack `v ⟨S, hS, hv, hSs⟩`. Use `⟨S, hS, hv, ?_⟩` and prove the remaining obligations.

Introduce `g hg x hx`. Rewrite `hg` using `[← Formalism.REAL.range_toMK]`. Take `⟨k, rfl⟩` from `hg`. Conclude with `hSs k x hx`.
-/
theorem dense_isKFin (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) : Dense {v : H | Formalism.MainNotions.S.IsKFin ε σ v} := by
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hσ
  have hemb : Topology.IsEmbedding (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Formalism.REAL.KG ε) := hemb.secondCountableTopology
  have hU : ∀ k : Formalism.REAL.KG ε, Formalism.REAL.toMK k ∈ Formalism.MainNotions.S.UJset ε := fun k => k.1.2
  let π : Formalism.REAL.KG ε →* (H →L[ℂ] H) :=
    { toFun := fun k => σ (Formalism.REAL.toMK k)
      map_one' := h1
      map_mul' := fun k l => hmul _ (hU k) _ (hU l) }
  have hd := dense_finite_vectors (Formalism.REAL.KG ε) H π (fun k x => hiso _ (hU k) x)
    (fun x => (hcont x).comp_continuous hemb.continuous hU)
  refine hd.mono ?_
  rintro v ⟨S, hS, hv, hSs⟩
  refine ⟨S, hS, hv, ?_⟩
  intro g hg x hx
  rw [← Formalism.REAL.range_toMK] at hg
  obtain ⟨k, rfl⟩ := hg
  exact hSs k x hx

end GlobalTheory.CompactRep
