import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc MeasureTheory
open scoped Pointwise ENNReal Classical NNReal

namespace GlobalTheory.ModuleUnits

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hM`. Take `⟨h1, h2, h3, h4, h5, hRc, hRo, hOc, hOo, -⟩` from `GlobalTheory.SgLoc.Top.model_topology M hM`. Use `hM.borel` as an intermediate fact. Use `hM.loc` as an intermediate fact. Use `hM.char0` as an intermediate fact.

Use `hM.haar.haar` as an intermediate fact. Establish `hreg : M.mu.Regular` using `inferInstance`. Establish `hO0 : M.mu (M.L.O : Set E) ≠ 0` using `hOo.measure_ne_zero M.mu ⟨0, M.L.O.zero_mem⟩`. Establish `hOt : M.mu (M.L.O : Set E) ≠ ∞` using `hOc.measure_lt_top.ne`. Establish `hmodK : ∀ u : Eˣ, M.modK u = (distribHaarChar E u : ℝ)`.

Introduce `u`. Establish `h` using `distribHaarChar_mul M.mu u (M.R : Set E)`. Rewrite `h` using `[hM.haar.volR, mul_one]`. Express the relevant statement in the definitionally equal form `(M.mu (u • (M.R : Set E))).toReal = _`. Rewrite using `[← h]`.

Both sides reduce to the same expression. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y hx hy`. Take `⟨u, rfl⟩` from `hx`. Take `⟨v, rfl⟩` from `hy`.

Rewrite using `[← Units.val_mul, hmodK, hmodK, hmodK, map_mul, NNReal.coe_mul]`. Introduce `x hx`. Take `⟨u, rfl⟩` from `hx`. Use `⟨by rw [hmodK]; exact NNReal.coe_pos.mpr distribHaarChar_pos, ?_⟩` and prove the remaining obligations. Establish `hcjO : ∀ z, z ∈ M.L.O → M.L.cj z ∈ M.L.O`.

Introduce `z hz`. Rewrite `hz`, the goal using `[M.L.O_def]`. Conclude with `hz.map ((M.L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])`. Establish `hcjO' : ∀ z, M.L.cj z ∈ M.L.O ↔ z ∈ M.L.O` using `fun z => ⟨fun h => by simpa [M.L.cj_cj] using hcjO _ h, hcjO z⟩`. Establish `: IsModuleTopology F E` using `M.L.top`.

Establish `hc1 : Continuous M.L.cj` using `IsModuleTopology.continuous_of_linearMap M.L.cj.toLinearMap`. Establish `hc2 : Continuous M.L.cj.symm` using `IsModuleTopology.continuous_of_linearMap M.L.cj.symm.toLinearMap`. Set `φ : E ≃ₜ+ E` to `{ M.L.cj.toAddEquiv with continuous_toFun := hc1, continuous_invFun := hc2 }`. Establish `hpre : ∀ X : Set E, addEquivAddHaarChar φ • M.mu (φ ⁻¹' X) = M.mu X` using `fun X => addEquivAddHaarChar_smul_preimage M.mu φ`. Establish `hφO : φ ⁻¹' (M.L.O : Set E) = M.L.O`.

Use extensionality with `z`. Conclude with `hcjO' z`. Establish `hc : (addEquivAddHaarChar φ : ℝ≥0∞) = 1`. Establish `h` using `hpre M.L.O`. Rewrite `h` using `[hφO]`.

Simplify using `only [ENNReal.smul_def, smul_eq_mul] at h`. Combine the equalities or inequalities in the displayed calculation. Set `w : Eˣ` to `Units.map (M.L.cj : E →* E) u`. Establish `hw : φ ⁻¹' (u • (M.L.O : Set E)) = w • (M.L.O : Set E)`. Use extensionality with `z`.

Rewrite using `[Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem]`. Express the relevant statement in the definitionally equal form `((u⁻¹ : Eˣ) : E) * M.L.cj z ∈ M.L.O ↔ ((w⁻¹ : Eˣ) : E) * z ∈ M.L.O`. Rewrite using `[← hcjO' (((w⁻¹ : Eˣ) : E) * z), map_mul]`. Simplify using `[w, M.L.cj_cj]`. Establish `hχ : distribHaarChar E w = distribHaarChar E u`.

Apply `distribHaarChar_eq_of_measure_smul_eq_mul hO0 hOt` to reduce the goal to its premises. Rewrite using `[← hw, distribHaarChar_mul M.mu u]`. Establish `h` using `hpre (u • (M.L.O : Set E))`. Simplify using `only [ENNReal.smul_def, smul_eq_mul, hc, one_mul] at h`. Conclude with `h`.

Rewrite using `[show M.L.cj (u : E) = (w : E) from rfl, hmodK, hmodK, hχ]`. Introduce and unpack `x hx ⟨y, hy, hxy⟩`. Set `u : Eˣ` to `⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩`. Establish `hset : u • (M.L.O : Set E) = M.L.O`. Use extensionality with `z`.

Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`. Express the relevant statement in the definitionally equal form `y * z ∈ M.L.O ↔ z ∈ M.L.O`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h'` using `M.L.O.mul_mem hx h`.

Rewrite `h'` using `[← mul_assoc, hxy, one_mul]`. Then use the resulting hypothesis. Introduce `h`. Conclude with `M.L.O.mul_mem hy h`. Establish `h1 : distribHaarChar E u = 1` using `distribHaarChar_eq_of_measure_smul_eq_mul hO0 hOt (by rw [hset]; simp)`. Rewrite using `[show x = (u : E) from rfl, hmodK, h1]`.

Simplify using the standard rewrite rules.
-/
theorem modK_units : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → (∀ x y : E, IsUnit x → IsUnit y → M.modK (x * y) = M.modK x * M.modK y) ∧ (∀ x : E, IsUnit x → 0 < M.modK x ∧ M.modK (M.L.cj x) = M.modK x) ∧ ∀ x : E, x ∈ M.L.O → (∃ y ∈ M.L.O, x * y = 1) → M.modK x = 1 := by
  intro F _ _ _ E _ _ _ _ M hM
  obtain ⟨h1, h2, h3, h4, h5, hRc, hRo, hOc, hOo, -⟩ := GlobalTheory.SgLoc.Top.model_topology M hM
  have := hM.borel
  have := hM.loc
  have := hM.char0
  have := hM.haar.haar
  have hreg : M.mu.Regular := inferInstance
  have hO0 : M.mu (M.L.O : Set E) ≠ 0 := hOo.measure_ne_zero M.mu ⟨0, M.L.O.zero_mem⟩
  have hOt : M.mu (M.L.O : Set E) ≠ ∞ := hOc.measure_lt_top.ne
  have hmodK : ∀ u : Eˣ, M.modK u = (distribHaarChar E u : ℝ) := by
    intro u
    have h := distribHaarChar_mul M.mu u (M.R : Set E)
    rw [hM.haar.volR, mul_one] at h
    change (M.mu (u • (M.R : Set E))).toReal = _
    rw [← h]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro x y hx hy
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    rw [← Units.val_mul, hmodK, hmodK, hmodK, map_mul, NNReal.coe_mul]
  · intro x hx
    obtain ⟨u, rfl⟩ := hx
    refine ⟨by rw [hmodK]; exact NNReal.coe_pos.mpr distribHaarChar_pos, ?_⟩
    have hcjO : ∀ z, z ∈ M.L.O → M.L.cj z ∈ M.L.O := by
      intro z hz
      rw [M.L.O_def] at hz ⊢
      exact hz.map ((M.L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])
    have hcjO' : ∀ z, M.L.cj z ∈ M.L.O ↔ z ∈ M.L.O := fun z =>
      ⟨fun h => by simpa [M.L.cj_cj] using hcjO _ h, hcjO z⟩
    have : IsModuleTopology F E := M.L.top
    have hc1 : Continuous M.L.cj := IsModuleTopology.continuous_of_linearMap M.L.cj.toLinearMap
    have hc2 : Continuous M.L.cj.symm :=
      IsModuleTopology.continuous_of_linearMap M.L.cj.symm.toLinearMap
    let φ : E ≃ₜ+ E := { M.L.cj.toAddEquiv with continuous_toFun := hc1, continuous_invFun := hc2 }
    have hpre : ∀ X : Set E, addEquivAddHaarChar φ • M.mu (φ ⁻¹' X) = M.mu X := fun X =>
      addEquivAddHaarChar_smul_preimage M.mu φ
    have hφO : φ ⁻¹' (M.L.O : Set E) = M.L.O := by
      ext z
      exact hcjO' z
    have hc : (addEquivAddHaarChar φ : ℝ≥0∞) = 1 := by
      have h := hpre M.L.O
      rw [hφO] at h
      simp only [ENNReal.smul_def, smul_eq_mul] at h
      calc _ = (addEquivAddHaarChar φ : ℝ≥0∞) * M.mu M.L.O / M.mu M.L.O :=
            (ENNReal.mul_div_cancel_right hO0 hOt).symm
        _ = 1 := by rw [h, ENNReal.div_self hO0 hOt]
    let w : Eˣ := Units.map (M.L.cj : E →* E) u
    have hw : φ ⁻¹' (u • (M.L.O : Set E)) = w • (M.L.O : Set E) := by
      ext z
      rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem]
      change ((u⁻¹ : Eˣ) : E) * M.L.cj z ∈ M.L.O ↔ ((w⁻¹ : Eˣ) : E) * z ∈ M.L.O
      rw [← hcjO' (((w⁻¹ : Eˣ) : E) * z), map_mul]
      simp [w, M.L.cj_cj]
    have hχ : distribHaarChar E w = distribHaarChar E u := by
      apply distribHaarChar_eq_of_measure_smul_eq_mul hO0 hOt
      rw [← hw, distribHaarChar_mul M.mu u]
      have h := hpre (u • (M.L.O : Set E))
      simp only [ENNReal.smul_def, smul_eq_mul, hc, one_mul] at h
      exact h
    rw [show M.L.cj (u : E) = (w : E) from rfl, hmodK, hmodK, hχ]
  · rintro x hx ⟨y, hy, hxy⟩
    let u : Eˣ := ⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩
    have hset : u • (M.L.O : Set E) = M.L.O := by
      ext z
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      change y * z ∈ M.L.O ↔ z ∈ M.L.O
      constructor
      · intro h
        have h' := M.L.O.mul_mem hx h
        rwa [← mul_assoc, hxy, one_mul] at h'
      · intro h
        exact M.L.O.mul_mem hy h
    have h1 : distribHaarChar E u = 1 :=
      distribHaarChar_eq_of_measure_smul_eq_mul hO0 hOt (by rw [hset]; simp)
    rw [show x = (u : E) from rfl, hmodK, h1]
    simp

end GlobalTheory.ModuleUnits
