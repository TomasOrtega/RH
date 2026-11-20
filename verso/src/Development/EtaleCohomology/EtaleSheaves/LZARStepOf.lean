import Development.EtaleCohomology.EtaleSheaves.NoetherianLocalChartOverlapFiniteComplement

namespace LateralTheory.E.LZARFacts

/- English proof (translation)
Introduce `A _ _ _ M _ _ N P hN`. Establish `: Module.Finite A N` using `Module.Finite.iff_fg.mpr hN`. Use `set I := IsLocalRing.maximalIdeal A`. Use `set Q : Submodule A N := P.comap N.subtype`. Take `⟨c, hc⟩` from `Ideal.exists_pow_inf_eq_pow_smul I Q`.

Use `⟨c + 1, by omega, ?_⟩` and prove the remaining obligations. Establish `hQ : I ^ (c + 1) • (⊤ : Submodule A N) ⊓ Q ≤ I • Q`. Rewrite using `[hc (c + 1) (by omega), show c + 1 - c = 1 by omega, pow_one]`. Conclude with `Submodule.smul_mono (le_refl _) inf_le_right`. Introduce `x ⟨hx, hxP⟩`.

Establish `hmap : I ^ (c + 1) • N = (I ^ (c + 1) • (⊤ : Submodule A N)).map N.subtype`. Rewrite using `[Submodule.map_smul'', Submodule.map_subtype_top]`. Rewrite `hx` using `[hmap]`. Take `⟨y, hy, rfl⟩` from `hx`. Establish `hyQ : y ∈ Q` using `hxP`.

Use `hQ ⟨hy, hyQ⟩` as an intermediate fact. Establish `h2 : (I • Q).map N.subtype ≤ I • P`. Rewrite using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono (le_refl _) (Submodule.map_comap_le _ _)`. Conclude with `h2 ⟨y, this, rfl⟩`.
-/
theorem LZARStep_of : LateralTheory.E.LZIdemSumNoetherian.LZARStep := by
  intro A _ _ _ M _ _ N P hN
  have : Module.Finite A N := Module.Finite.iff_fg.mpr hN
  set I := IsLocalRing.maximalIdeal A
  set Q : Submodule A N := P.comap N.subtype
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I Q
  refine ⟨c + 1, by omega, ?_⟩
  have hQ : I ^ (c + 1) • (⊤ : Submodule A N) ⊓ Q ≤ I • Q := by
    rw [hc (c + 1) (by omega), show c + 1 - c = 1 by omega, pow_one]
    exact Submodule.smul_mono (le_refl _) inf_le_right
  intro x ⟨hx, hxP⟩
  have hmap : I ^ (c + 1) • N = (I ^ (c + 1) • (⊤ : Submodule A N)).map N.subtype := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  rw [hmap] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyQ : y ∈ Q := hxP
  have := hQ ⟨hy, hyQ⟩
  have h2 : (I • Q).map N.subtype ≤ I • P := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono (le_refl _) (Submodule.map_comap_le _ _)
  exact h2 ⟨y, this, rfl⟩

end LateralTheory.E.LZARFacts
