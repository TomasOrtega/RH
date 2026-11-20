import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

/- English proof (translation)
Introduce `Ph A B _ _ _ π π' V _ hsup`. Establish `hdec : ∀ x, π' x = 1 → ∃ k, π k = 1 ∧ ∃ v ∈ V, k * v = x`. Introduce `x hx`. Establish `hx' : x ∈ π.ker ⊔ V`. Rewrite using `[hsup]`.

Conclude with `Subgroup.mem_sup_left (MonoidHom.mem_ker.2 hx)`. Take `⟨k, hk, v, hv, hkv⟩` from `Subgroup.mem_sup_of_normal_right.1 hx'`. Conclude with `⟨k, MonoidHom.mem_ker.1 hk, v, hv, hkv⟩`. Use `⟨fun a b g ⟨g0, g0', ha, hb, hV⟩ hg => ?_, fun k hk => ?_⟩` and prove the remaining obligations. Take `⟨k, hk, v, hv, hkv⟩` from `hdec (g0'⁻¹ * g) (by rw [map_mul, map_inv, hb, hg, inv_mul_cancel])`.

Use `⟨g0 * k, by rw [map_mul, ha, hk, mul_one], ?_⟩` and prove the remaining obligations. Establish `hg' : g = g0' * (k * v)` using `by rw [hkv, mul_inv_cancel_left]`. Rewrite using `[hg']`. Establish `hw : g0'⁻¹ * g0 ∈ V`. Use `V.inv_mem hV` as an intermediate fact.

Rewrite `this` using `[_root_.mul_inv_rev, inv_inv]`. Then use the resulting hypothesis. Establish `hconj : k⁻¹ * (g0'⁻¹ * g0) * k ∈ V`. Use `(inferInstance : V.Normal).conj_mem _ hw k⁻¹` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Establish `heq : (g0' * (k * v))⁻¹ * (g0 * k) = v⁻¹ * (k⁻¹ * (g0'⁻¹ * g0) * k)` using `by group`.

Rewrite using `[heq]`. Conclude with `V.mul_mem (V.inv_mem hv) hconj`. Take `⟨k', hk', v, hv, rfl⟩` from `hdec k hk`. Use `⟨k', hk', ?_⟩` and prove the remaining obligations. Establish `heq : (k' * v)⁻¹ * k' = v⁻¹` using `by group`.

Rewrite using `[heq]`. Conclude with `V.inv_mem hv`.
-/
theorem UpperTheory.V.Pa.Core.closeLift :
    ∀ (Ph A B : Type) [Group Ph] [Group A] [Group B] (π : Ph →* A) (π' : Ph →* B) (V : Subgroup Ph) [V.Normal], π.ker ⊔ V = π'.ker ⊔ V → (∀ a b g, Close π π' V a b → π' g = b → ∃ g', π g' = a ∧ g⁻¹ * g' ∈ V) ∧ ∀ k, π' k = 1 → ∃ k', π k' = 1 ∧ k⁻¹ * k' ∈ V := by
  intro Ph A B _ _ _ π π' V _ hsup
  have hdec : ∀ x, π' x = 1 → ∃ k, π k = 1 ∧ ∃ v ∈ V, k * v = x := by
    intro x hx
    have hx' : x ∈ π.ker ⊔ V := by
      rw [hsup]
      exact Subgroup.mem_sup_left (MonoidHom.mem_ker.2 hx)
    obtain ⟨k, hk, v, hv, hkv⟩ := Subgroup.mem_sup_of_normal_right.1 hx'
    exact ⟨k, MonoidHom.mem_ker.1 hk, v, hv, hkv⟩
  refine ⟨fun a b g ⟨g0, g0', ha, hb, hV⟩ hg => ?_, fun k hk => ?_⟩
  · obtain ⟨k, hk, v, hv, hkv⟩ := hdec (g0'⁻¹ * g) (by rw [map_mul, map_inv, hb, hg, inv_mul_cancel])
    refine ⟨g0 * k, by rw [map_mul, ha, hk, mul_one], ?_⟩
    have hg' : g = g0' * (k * v) := by rw [hkv, mul_inv_cancel_left]
    rw [hg']
    have hw : g0'⁻¹ * g0 ∈ V := by
      have := V.inv_mem hV
      rwa [_root_.mul_inv_rev, inv_inv] at this
    have hconj : k⁻¹ * (g0'⁻¹ * g0) * k ∈ V := by
      have := (inferInstance : V.Normal).conj_mem _ hw k⁻¹
      rwa [inv_inv] at this
    have heq : (g0' * (k * v))⁻¹ * (g0 * k) = v⁻¹ * (k⁻¹ * (g0'⁻¹ * g0) * k) := by group
    rw [heq]
    exact V.mul_mem (V.inv_mem hv) hconj
  · obtain ⟨k', hk', v, hv, rfl⟩ := hdec k hk
    refine ⟨k', hk', ?_⟩
    have heq : (k' * v)⁻¹ * k' = v⁻¹ := by group
    rw [heq]
    exact V.inv_mem hv
