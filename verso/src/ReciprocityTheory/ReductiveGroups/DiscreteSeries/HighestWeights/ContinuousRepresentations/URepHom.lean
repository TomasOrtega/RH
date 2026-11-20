import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement

noncomputable section

open Matrix Topology

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma urepHom_toMK_mul {ε : Fin n → Bool} (k k' : KG ε) : toMK (k * k') = toMK k * toMK k' := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma urepHom_toMK_one {ε : Fin n → Bool} : toMK (1 : KG ε) = 1 := rfl

/- English proof (translation)
Establish `hmem : ∀ k : KG ε, toMK k ∈ Kset ε` using `fun k => k.2`. Use `set a := σ (toMK k)`. Use `set c := σ (toMK k⁻¹)`. Establish `h1 : star a * a = 1` using `(ContinuousLinearMap.norm_map_iff_adjoint_comp_self a).1 (hσ.2.1 _ (hmem k))`. Establish `h2 : a * c = 1`.

Establish `e : toMK k * toMK k⁻¹ = 1`. Rewrite using `[← urepHom_toMK_mul, mul_inv_cancel, urepHom_toMK_one]`. Use `hσ.1.2 _ (hmem k) _ (hmem k⁻¹)` as an intermediate fact. Rewrite `this` using `[e, hσ.1.1]`. Conclude with `this.symm`.

Establish `h3 : a * star a = 1`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Unitary.mem_iff.2 ⟨h1, h3⟩`.
-/
lemma urepHom_mem_unitary {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (Kset ε) σ)
    (k : KG ε) : σ (toMK k) ∈ unitary (H →L[ℂ] H) := by
  have hmem : ∀ k : KG ε, toMK k ∈ Kset ε := fun k => k.2
  set a := σ (toMK k)
  set c := σ (toMK k⁻¹)

  have h1 : star a * a = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self a).1 (hσ.2.1 _ (hmem k))

  have h2 : a * c = 1 := by
    have e : toMK k * toMK k⁻¹ = 1 := by
      rw [← urepHom_toMK_mul, mul_inv_cancel, urepHom_toMK_one]
    have := hσ.1.2 _ (hmem k) _ (hmem k⁻¹)
    rw [e, hσ.1.1] at this
    exact this.symm
  have h3 : a * star a = 1 := by
    calc a * star a = a * star a * (a * c) := by rw [h2, mul_one]
      _ = a * (star a * a) * c := by noncomm_ring
      _ = 1 := by rw [h1, mul_one, h2]
  exact Unitary.mem_iff.2 ⟨h1, h3⟩

/- English proof (translation)
Introduce `n ε H _ _ _ σ hσ`. Establish `hmem : ∀ k : KG ε, toMK k ∈ Kset ε` using `fun k => k.2`. Use `⟨{ toFun := fun k => ⟨σ (toMK k), urepHom_mem_unitary hσ k⟩ map_one' := ?_ map_mul' := ?_ }, ?_, fun k => rfl⟩` and prove the remaining obligations. Apply `Subtype.ext show σ (toMK (1 : KG ε)) = 1` to reduce the goal to its premises. Rewrite using `[urepHom_toMK_one, hσ.1.1]`.

Introduce `k k'`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show σ (toMK (k * k')) = σ (toMK k) * σ (toMK k')`. Rewrite using `[urepHom_toMK_mul]`. Conclude with `hσ.1.2 _ (hmem k) _ (hmem k')`.

Establish `hc : Continuous (fun k : KG ε => toMK k)` using `by fun_prop`. Establish `hop : Continuous (fun k : KG ε => σ (toMK k))`. Use `continuous_clm_apply.2 fun v => ?_` and prove the remaining obligations. Conclude with `(hσ.2.2 v).comp_continuous hc hmem`. Conclude with `Continuous.subtype_mk hop _`.
-/
theorem uRepHom : URepHomStatement := by
  intro n ε H _ _ _ σ hσ
  have hmem : ∀ k : KG ε, toMK k ∈ Kset ε := fun k => k.2
  refine ⟨{ toFun := fun k => ⟨σ (toMK k), urepHom_mem_unitary hσ k⟩
            map_one' := ?_
            map_mul' := ?_ }, ?_, fun k => rfl⟩
  · apply Subtype.ext
    show σ (toMK (1 : KG ε)) = 1
    rw [urepHom_toMK_one, hσ.1.1]
  · intro k k'
    apply Subtype.ext
    show σ (toMK (k * k')) = σ (toMK k) * σ (toMK k')
    rw [urepHom_toMK_mul]
    exact hσ.1.2 _ (hmem k) _ (hmem k')
  · have hc : Continuous (fun k : KG ε => toMK k) := by
      fun_prop
    have hop : Continuous (fun k : KG ε => σ (toMK k)) := by
      refine continuous_clm_apply.2 fun v => ?_
      exact (hσ.2.2 v).comp_continuous hc hmem
    exact Continuous.subtype_mk hop _

end ReciprocityTheory.ChartRestriction.DS.HW
