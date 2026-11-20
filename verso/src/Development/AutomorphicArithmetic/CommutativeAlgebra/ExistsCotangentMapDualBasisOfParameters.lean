import Mathlib

open KaehlerDifferential

/- English proof (translation)
Introduce `R _ _ ev d t ψ hψ hsurj ht hloc`. Establish `key : ∀ χ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ), (∀ (b : R) (ω : Ω[R⁄ℂ]), χ (b • ω) = ev b • χ ω) → ∀ (u c : R) (g : Fin d → R), ev u = 0 → c * u = ∑ l, g l * t l → ev c • χ (D ℂ R u) = ∑ l, ev (g l) • χ (D ℂ R (t l))`. Introduce `χ hχ u c g hu hcu`. Establish `h` using `congrArg (fun x => χ (D ℂ R x)) hcu`. Simplify using `only [Derivation.leibniz, map_sum, map_add, hχ, hu, ht, zero_smul, add_zero] at h`.

Conclude with `h`. Use `set v : Fin d → (Fin d → ℂ) := fun l => ψ (D ℂ R (t l)) with hvdef`. Establish `hspan : ⊤ ≤ Submodule.span ℂ (Set.range v)`. Introduce `y hy`. Use `clear hy`.

Take `⟨ω, rfl⟩` from `hsurj y`. Establish `hω : ω ∈ Submodule.span R (Set.range (D ℂ R))`. Rewrite using `[KaehlerDifferential.span_range_derivation]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hω using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨u, rfl⟩` from `hx`. Use `set u' := u - algebraMap ℂ R (ev u) with hu'`. Establish `hDu : D ℂ R u = D ℂ R u'`. Rewrite using `[hu', map_sub, Derivation.map_algebraMap, sub_zero]`.

Establish `hev : ev u' = 0`. Rewrite using `[hu', map_sub, AlgHom.commutes]`. Simplify using the standard rewrite rules. Take `⟨c, g, hc, hcu⟩` from `hloc u' hev`. Establish `h` using `key ψ hψ u' c g hev hcu`.

Rewrite using `[hDu]`. Establish `: ψ (D ℂ R u') = (ev c)⁻¹ • ∑ l, ev (g l) • v l`. Rewrite using `[← h, smul_smul, inv_mul_cancel₀ hc, one_smul]`. Rewrite using `[this]`. Apply `Submodule.smul_mem` to reduce the goal to its premises.

Apply `Submodule.sum_mem` to reduce the goal to its premises. Introduce `l _`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`.

Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[hψ]`. Conclude with `Submodule.smul_mem _ _ hx`.

Establish `hli : LinearIndependent ℂ v` using `linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp)`. Use `set bs := Module.Basis.mk hli hspan with hbs`. Establish `hbv : ∀ l, ψ (D ℂ R (t l)) = bs l`. Introduce `l`. Rewrite using `[hbs, Module.Basis.mk_apply]`.

Establish `h2 : ∀ l, (bs.equivFun.toLinearMap ∘ₗ ψ) (D ℂ R (t l)) = Pi.single l 1`. Introduce `l`. Rewrite using `[LinearMap.comp_apply, LinearEquiv.coe_coe, hbv]`. Use extensionality with `j`. Rewrite using `[Module.Basis.equivFun_self]`.

Distinguish the cases in `hlj : l = j`. Substitute `hlj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hlj, Pi.single_apply, Ne.symm hlj]`. Use `⟨bs.equivFun.toLinearMap ∘ₗ ψ, ?_, h2, ?_, ?_⟩` and prove the remaining obligations.

Introduce `b ω`. Simplify using `[hψ]`. Introduce `ω hω`. Simplify using `using hω`. Introduce `u c g hu hc hcu l`.

Establish `h` using `key (bs.equivFun.toLinearMap ∘ₗ ψ) (by intro b ω; simp [hψ]) u c g hu hcu`. Simplify using `only [h2] at h`. Establish `h3` using `congrFun h l`. Simplify using `[Finset.sum_apply, Pi.single_apply] at h3`. Rewrite using `[← h3]`.

Both sides reduce to the same expression.
-/
theorem UpperTheory.exists_cotangent_map_dual_basis_of_parameters :
    ∀ {R : Type} [CommRing R] [Algebra ℂ R] (ev : R →ₐ[ℂ] ℂ) {d : ℕ} (t : Fin d → R) (ψ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ)), (∀ (b : R) (ω : Ω[R⁄ℂ]), ψ (b • ω) = ev b • ψ ω) → Function.Surjective ψ → (∀ l, ev (t l) = 0) → (∀ u : R, ev u = 0 → ∃ (c : R) (g : Fin d → R), ev c ≠ 0 ∧ c * u = ∑ l, g l * t l) → ∃ φ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ), (∀ (b : R) (ω : Ω[R⁄ℂ]), φ (b • ω) = ev b • φ ω) ∧ (∀ l, φ (D ℂ R (t l)) = Pi.single l 1) ∧ (∀ ω, φ ω = 0 → ψ ω = 0) ∧ ∀ (u c : R) (g : Fin d → R), ev u = 0 → ev c ≠ 0 → c * u = ∑ l, g l * t l → ∀ l, ev (g l) = ev c * φ (D ℂ R u) l := by
  intro R _ _ ev d t ψ hψ hsurj ht hloc
  have key : ∀ χ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ), (∀ (b : R) (ω : Ω[R⁄ℂ]), χ (b • ω) = ev b • χ ω) →
      ∀ (u c : R) (g : Fin d → R), ev u = 0 → c * u = ∑ l, g l * t l →
      ev c • χ (D ℂ R u) = ∑ l, ev (g l) • χ (D ℂ R (t l)) := by
    intro χ hχ u c g hu hcu
    have h := congrArg (fun x => χ (D ℂ R x)) hcu
    simp only [Derivation.leibniz, map_sum, map_add, hχ, hu, ht, zero_smul, add_zero] at h
    exact h
  set v : Fin d → (Fin d → ℂ) := fun l => ψ (D ℂ R (t l)) with hvdef
  have hspan : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    intro y hy
    clear hy
    obtain ⟨ω, rfl⟩ := hsurj y
    have hω : ω ∈ Submodule.span R (Set.range (D ℂ R)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      set u' := u - algebraMap ℂ R (ev u) with hu'
      have hDu : D ℂ R u = D ℂ R u' := by
        rw [hu', map_sub, Derivation.map_algebraMap, sub_zero]
      have hev : ev u' = 0 := by
        rw [hu', map_sub, AlgHom.commutes]
        simp
      obtain ⟨c, g, hc, hcu⟩ := hloc u' hev
      have h := key ψ hψ u' c g hev hcu
      rw [hDu]
      have : ψ (D ℂ R u') = (ev c)⁻¹ • ∑ l, ev (g l) • v l := by
        rw [← h, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [this]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      intro l _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [hψ]
      exact Submodule.smul_mem _ _ hx
  have hli : LinearIndependent ℂ v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp)
  set bs := Module.Basis.mk hli hspan with hbs
  have hbv : ∀ l, ψ (D ℂ R (t l)) = bs l := by
    intro l
    rw [hbs, Module.Basis.mk_apply]
  have h2 : ∀ l, (bs.equivFun.toLinearMap ∘ₗ ψ) (D ℂ R (t l)) = Pi.single l 1 := by
    intro l
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hbv]
    ext j
    rw [Module.Basis.equivFun_self]
    by_cases hlj : l = j
    · subst hlj
      simp
    · simp [hlj, Pi.single_apply, Ne.symm hlj]
  refine ⟨bs.equivFun.toLinearMap ∘ₗ ψ, ?_, h2, ?_, ?_⟩
  · intro b ω
    simp [hψ]
  · intro ω hω
    simpa using hω
  · intro u c g hu hc hcu l
    have h := key (bs.equivFun.toLinearMap ∘ₗ ψ) (by intro b ω; simp [hψ]) u c g hu hcu
    simp only [h2] at h
    have h3 := congrFun h l
    simp [Finset.sum_apply, Pi.single_apply] at h3
    rw [← h3]
    rfl
