import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

/- English proof (translation)
Take `⟨W', ⟨hW's, hW'd⟩, hmax⟩` from `exists_maximal_of_wellFoundedGT (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ Disjoint W U) ⟨⊥, by intro g _ v hv; rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], disjoint_bot_right⟩`. Use `⟨W', hW's, hW'd, ?_⟩` and prove the remaining obligations. Rewrite using `[codisjoint_iff]`. Take `⟨C, hC, hUC⟩` from `hss (⨅ g : G, (W ⊔ W').comap (ρ g)) (by`. Introduce `g v hv`.

Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap] at hv ⊢`. Introduce `h`. Rewrite using `[hmul]`. Conclude with `hv _)`. Distinguish the cases in `htriv : C = ⊥`.

Establish `hU` using `hUC.sup_eq_top`. Rewrite `hU` using `[htriv, sup_bot_eq]`. Rewrite using `[eq_top_iff]`. Introduce `v _`. Establish `hv : v ∈ (⨅ g : G, (W ⊔ W').comap (ρ g))` using `hU ▸ Submodule.mem_top`.

Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap] at hv`. Use `hv 1` as an intermediate fact. Rewrite `this` using `[hone]`. Then use the resulting hypothesis. It suffices to derive a contradiction. Take `⟨S, ⟨hSs, hS0, hSC⟩, hmin⟩` from `exists_minimal_of_wellFoundedLT (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ U ≠ ⊥ ∧ U ≤ C) ⟨C, fun g _ v hv => hC g v hv, htriv, le_rfl⟩`.

Establish `hsup : ∀ n ∈ N, ∀ v ∈ W ⊔ W', ρ n v ∈ W ⊔ W'`. Introduce `n hn v hv`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp hv`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (hW n hn a ha) (hW's n hn b hb)`.

Establish `key : ∀ g : G, ∀ s ∈ S, ρ g s ∈ W ⊔ W'`. Introduce `g`. Distinguish the cases in `hA : S ⊓ (W ⊔ W').comap (ρ g) = ⊥`. Establish `hle : W' ⊔ S.map (ρ g) ≤ W'`. Use `hmax ⟨?_, ?_⟩ le_sup_left` and prove the remaining obligations.

Introduce `n hn v hv`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp hv`. Take `⟨s, hs, rfl⟩` from `Submodule.mem_map.mp hb`. Rewrite using `[map_add]`. Use `Submodule.add_mem_sup (hW's n hn a ha) ?_` and prove the remaining obligations.

Use `Submodule.mem_map.mpr ⟨ρ (g⁻¹ * n * g) s, hSs _ (hN.conj_mem' n hn g) s hs, ?_⟩` and prove the remaining obligations. Rewrite using `[hmul, hmul]`. Use `congr 2`. Use `group`. Rewrite using `[Submodule.disjoint_def]`.

Introduce `v hvW hv`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp hv`. Take `⟨s, hs, rfl⟩` from `Submodule.mem_map.mp hb`. Establish `h1 : ρ g s ∈ W ⊔ W'`. Use `(W ⊔ W').sub_mem (Submodule.mem_sup_left hvW) (Submodule.mem_sup_right ha)` as an intermediate fact.

Simplify using `using this`. Establish `h2 : s ∈ S ⊓ (W ⊔ W').comap (ρ g)` using `⟨hs, h1⟩`. Rewrite `h2` using `[hA, Submodule.mem_bot]`. Substitute `h2` using the available equality. Rewrite `hvW`, the goal using `[map_zero, add_zero]`.

Conclude with `Submodule.disjoint_def.mp hW'd a hvW ha`. Introduce `s hs`. Conclude with `Submodule.mem_sup_right (hle (Submodule.mem_sup_right (Submodule.mem_map_of_mem hs)))`. Establish `hle : S ≤ S ⊓ (W ⊔ W').comap (ρ g)`. Use `hmin ⟨?_, hA, inf_le_left.trans hSC⟩ inf_le_left` and prove the remaining obligations.

Introduce `n hn v hv`. Use `⟨hSs n hn v hv.1, ?_⟩` and prove the remaining obligations. Establish `h1 : ρ g v ∈ W ⊔ W'` using `hv.2`. Establish `h2` using `hsup _ (hN.conj_mem n hn g) _ h1`. Use `show ρ g (ρ n v) ∈ W ⊔ W'`.

Rewrite `h2`, the goal using `[hmul]`. Establish `: g * n * g⁻¹ * g = g * n` using `by group`. Rewrite `h2` using `[this]`. Then use the resulting hypothesis. Introduce `s hs`. Conclude with `(hle hs).2`.

Apply `hS0` to reduce the goal to its premises. Rewrite using `[eq_bot_iff, ← hUC.inf_eq_bot]`. Introduce `s hs`. Use `⟨?_, hSC hs⟩` and prove the remaining obligations. Simplify using `only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap]`.

Conclude with `fun g => key g s hs`.
-/
private theorem UpperTheory.semisimple_restriction_normal_subgroup {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : G → V →ₗ[K] V)
    (hmul : ∀ (a b : G) (v : V), ρ a (ρ b v) = ρ (a * b) v) (hone : ∀ v, ρ 1 v = v)
    (N : Subgroup G) (hN : N.Normal)
    (hss : ∀ W : Submodule K V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) →
      ∃ W' : Submodule K V, (∀ g, ∀ v ∈ W', ρ g v ∈ W') ∧ IsCompl W W')
    (W : Submodule K V) (hW : ∀ g ∈ N, ∀ v ∈ W, ρ g v ∈ W) :
    ∃ W' : Submodule K V, (∀ g ∈ N, ∀ v ∈ W', ρ g v ∈ W') ∧ IsCompl W W' := by
  obtain ⟨W', ⟨hW's, hW'd⟩, hmax⟩ := exists_maximal_of_wellFoundedGT
    (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ Disjoint W U)
    ⟨⊥, by intro g _ v hv; rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], disjoint_bot_right⟩
  refine ⟨W', hW's, hW'd, ?_⟩
  rw [codisjoint_iff]
  obtain ⟨C, hC, hUC⟩ := hss (⨅ g : G, (W ⊔ W').comap (ρ g)) (by
    intro g v hv
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv ⊢
    intro h
    rw [hmul]; exact hv _)
  by_cases htriv : C = ⊥
  · have hU := hUC.sup_eq_top
    rw [htriv, sup_bot_eq] at hU
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ (⨅ g : G, (W ⊔ W').comap (ρ g)) := hU ▸ Submodule.mem_top
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv
    have := hv 1
    rwa [hone] at this
  exfalso
  obtain ⟨S, ⟨hSs, hS0, hSC⟩, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ U ≠ ⊥ ∧ U ≤ C)
    ⟨C, fun g _ v hv => hC g v hv, htriv, le_rfl⟩
  have hsup : ∀ n ∈ N, ∀ v ∈ W ⊔ W', ρ n v ∈ W ⊔ W' := by
    intro n hn v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (hW n hn a ha) (hW's n hn b hb)
  have key : ∀ g : G, ∀ s ∈ S, ρ g s ∈ W ⊔ W' := by
    intro g
    by_cases hA : S ⊓ (W ⊔ W').comap (ρ g) = ⊥
    · have hle : W' ⊔ S.map (ρ g) ≤ W' := by
        refine hmax ⟨?_, ?_⟩ le_sup_left
        · intro n hn v hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hb
          rw [map_add]
          refine Submodule.add_mem_sup (hW's n hn a ha) ?_
          refine Submodule.mem_map.mpr ⟨ρ (g⁻¹ * n * g) s, hSs _ (hN.conj_mem' n hn g) s hs, ?_⟩
          rw [hmul, hmul]; congr 2; group
        · rw [Submodule.disjoint_def]
          intro v hvW hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hb
          have h1 : ρ g s ∈ W ⊔ W' := by
            have := (W ⊔ W').sub_mem (Submodule.mem_sup_left hvW) (Submodule.mem_sup_right ha)
            simpa using this
          have h2 : s ∈ S ⊓ (W ⊔ W').comap (ρ g) := ⟨hs, h1⟩
          rw [hA, Submodule.mem_bot] at h2
          subst h2
          rw [map_zero, add_zero] at hvW ⊢
          exact Submodule.disjoint_def.mp hW'd a hvW ha
      intro s hs
      exact Submodule.mem_sup_right (hle (Submodule.mem_sup_right (Submodule.mem_map_of_mem hs)))
    · have hle : S ≤ S ⊓ (W ⊔ W').comap (ρ g) := by
        refine hmin ⟨?_, hA, inf_le_left.trans hSC⟩ inf_le_left
        intro n hn v hv
        refine ⟨hSs n hn v hv.1, ?_⟩
        have h1 : ρ g v ∈ W ⊔ W' := hv.2
        have h2 := hsup _ (hN.conj_mem n hn g) _ h1
        show ρ g (ρ n v) ∈ W ⊔ W'
        rw [hmul] at h2 ⊢
        have : g * n * g⁻¹ * g = g * n := by group
        rwa [this] at h2
      intro s hs
      exact (hle hs).2
  apply hS0
  rw [eq_bot_iff, ← hUC.inf_eq_bot]
  intro s hs
  refine ⟨?_, hSC hs⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap]
  exact fun g => key g s hs

/- English proof (translation)
Introduce `Γ Γ' k _ _ _ n r φ hN hss W hW`. Take `⟨W', h1, h2⟩` from `UpperTheory.semisimple_restriction_normal_subgroup (fun g : Γ => Matrix.mulVecLin (r g : Matrix (Fin n) (Fin n) k)) (by`. Introduce `a b v`. Simplify using `only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, map_mul, Units.val_mul])`. Use the proof step `(by`.

Introduce `v`. Simplify using `only [Matrix.mulVecLin_apply, map_one, Units.val_one, Matrix.one_mulVec])`. Use the proof step `φ.range hN hss W (by`. Introduce and unpack `_ ⟨g, rfl⟩ v hv`. Conclude with `hW g v hv)`.

Conclude with `⟨W', fun g v hv => h1 (φ g) ⟨g, rfl⟩ v hv, h2⟩`.
-/
theorem UpperTheory.semisimpleModule_restriction_to_normal_subgroup :
    UpperTheory.V.Af.Sol.SsRes := by
  intro Γ Γ' k _ _ _ n r φ hN hss W hW
  obtain ⟨W', h1, h2⟩ := UpperTheory.semisimple_restriction_normal_subgroup
    (fun g : Γ => Matrix.mulVecLin (r g : Matrix (Fin n) (Fin n) k))
    (by
      intro a b v
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, map_mul, Units.val_mul])
    (by
      intro v
      simp only [Matrix.mulVecLin_apply, map_one, Units.val_one, Matrix.one_mulVec])
    φ.range hN hss W (by
      rintro _ ⟨g, rfl⟩ v hv
      exact hW g v hv)
  exact ⟨W', fun g v hv => h1 (φ g) ⟨g, rfl⟩ v hv, h2⟩
