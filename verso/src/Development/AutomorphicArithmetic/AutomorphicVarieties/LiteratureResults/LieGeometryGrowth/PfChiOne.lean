import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
open UpperTheory.V.Lit.Geo

open NumberField Formalism.L2.Host GroundTheory.Global in

/- English proof (translation)
Take `⟨D, hD, -, hxD⟩` from `IdeleGroup.exists_isCompact_normOneSubgroup E`. Establish `hc : Continuous fun z : IdeleGroup E => ((χ.1 z : ℂˣ) : ℂ)` using `Units.continuous_val.comp χ.2.1`. Take `⟨M, hM⟩` from `hD.exists_bound_of_continuousOn hc.continuousOn`. Establish `hb : ∀ z ∈ IdeleGroup.normOneSubgroup E, ‖((χ.1 z : ℂˣ) : ℂ)‖ ≤ M` using `fun z hz => by`. Take `⟨k, hk⟩` from `hxD z hz`.

Establish `h` using `hM _ hk`. Establish `h1 : χ.1 (IdeleGroup.diagonal E k) = 1` using `χ.2.2 k`. Establish `h2 : χ.1 (IdeleGroup.diagonal E k * z) = χ.1 z` using `(map_mul χ.1 _ _).trans (by rw [h1, one_mul])`. Rewrite `h` using `[h2]`. Then use the resulting hypothesis. Establish `hle : ∀ z ∈ IdeleGroup.normOneSubgroup E, ‖((χ.1 z : ℂˣ) : ℂ)‖ ≤ 1` using `fun z hz => by`.

Assume the negation of the conclusion as `h`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt M (not_le.1 h)`. Establish `h3` using `hb _ (pow_mem hz n)`. Establish `h4 : χ.1 (z ^ n) = χ.1 z ^ n` using `map_pow χ.1 z n`. Rewrite `h3` using `[h4, Units.val_pow_eq_pow_val, norm_pow]`.

Conclude with `(not_le.2 hn) h3`. Establish `h5` using `hle _ (inv_mem hy)`. Establish `h6 : χ.1 y⁻¹ = (χ.1 y)⁻¹` using `map_inv χ.1 y`. Rewrite `h5` using `[h6, Units.val_inv_eq_inv_val, norm_inv, inv_le_one₀ (norm_pos_iff.2 (Units.ne_zero _))]`. Conclude with `le_antisymm (hle _ hy) h5`.
-/
private theorem norm_of_normOne {E : Type} [Field E] [NumberField E] (χ : HChar E) {y : IdeleGroup E}
    (hy : y ∈ IdeleGroup.normOneSubgroup E) : ‖((χ.1 y : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup E
  have hc : Continuous fun z : IdeleGroup E => ((χ.1 z : ℂˣ) : ℂ) := Units.continuous_val.comp χ.2.1
  obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn hc.continuousOn
  have hb : ∀ z ∈ IdeleGroup.normOneSubgroup E, ‖((χ.1 z : ℂˣ) : ℂ)‖ ≤ M := fun z hz => by
    obtain ⟨k, hk⟩ := hxD z hz
    have h := hM _ hk
    have h1 : χ.1 (IdeleGroup.diagonal E k) = 1 := χ.2.2 k
    have h2 : χ.1 (IdeleGroup.diagonal E k * z) = χ.1 z :=
      (map_mul χ.1 _ _).trans (by rw [h1, one_mul])
    rwa [h2] at h
  have hle : ∀ z ∈ IdeleGroup.normOneSubgroup E, ‖((χ.1 z : ℂˣ) : ℂ)‖ ≤ 1 := fun z hz => by
    by_contra h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (not_le.1 h)
    have h3 := hb _ (pow_mem hz n)
    have h4 : χ.1 (z ^ n) = χ.1 z ^ n := map_pow χ.1 z n
    rw [h4, Units.val_pow_eq_pow_val, norm_pow] at h3
    exact (not_le.2 hn) h3
  have h5 := hle _ (inv_mem hy)
  have h6 : χ.1 y⁻¹ = (χ.1 y)⁻¹ := map_inv χ.1 y
  rw [h6, Units.val_inv_eq_inv_val, norm_inv, inv_le_one₀ (norm_pos_iff.2 (Units.ne_zero _))] at h5
  exact le_antisymm (hle _ hy) h5

/- English proof (translation)
Introduce `E _ _ _ a χ s _ g`. Conclude with `norm_of_normOne χ g.2`.
-/
theorem UpperTheory.V.Lit.Geo.Pf.chiOne :
    UpperTheory.V.Lit.Geo.Pf.ChiOne := by
  intro E _ _ _ a χ s _ g
  exact norm_of_normOne χ g.2
