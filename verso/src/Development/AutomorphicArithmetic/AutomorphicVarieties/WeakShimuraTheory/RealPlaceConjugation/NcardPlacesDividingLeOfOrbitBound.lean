import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

open scoped Pointwise in
/- English proof (translation)
Establish `key : ∀ A : ValuationSubring Ω, A.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ A`. Introduce `A`. Break down `eq_or_ne x 0 with h | h` into its components or cases. Simplify using `[h]`. Establish `e` using `(A.valuation).one_lt_val_iff (inv_ne_zero h)`.

Rewrite `e` using `[inv_inv]`. Rewrite using `[← e, ← not_le, A.valuation_le_one_iff]`. Simplify using `[h]`. Establish `mem : x⁻¹ ∈ v • B ↔ x⁻¹ ∈ B`. Establish `hv : v x⁻¹ = x⁻¹` using `by rw [map_inv₀, hx]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, hzx⟩`. Express the relevant statement in the definitionally equal form `v z = x⁻¹ at hzx`. Establish `hz' : z = x⁻¹` using `v.injective (hzx.trans hv.symm)`. Conclude with `hz' ▸ hz`.

Introduce `h`. Conclude with `⟨x⁻¹, h, hv⟩`. Rewrite using `[key, key, mem]`.
-/
private theorem val_smul_fix {Ω : Type} [Field Ω] [CharZero Ω] (B : ValuationSubring Ω) (v : G ℚ Ω) (x : Ω)
    (hx : v x = x) : (v • B).valuation x < 1 ↔ B.valuation x < 1 := by
  have key : ∀ A : ValuationSubring Ω, A.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ A := by
    intro A
    rcases eq_or_ne x 0 with h | h
    · simp [h]
    · have e := (A.valuation).one_lt_val_iff (inv_ne_zero h)
      rw [inv_inv] at e
      rw [← e, ← not_le, A.valuation_le_one_iff]
      simp [h]
  have mem : x⁻¹ ∈ v • B ↔ x⁻¹ ∈ B := by
    have hv : v x⁻¹ = x⁻¹ := by rw [map_inv₀, hx]
    constructor
    · rintro ⟨z, hz, hzx⟩
      change v z = x⁻¹ at hzx
      have hz' : z = x⁻¹ := v.injective (hzx.trans hv.symm)
      exact hz' ▸ hz
    · intro h
      exact ⟨x⁻¹, h, hv⟩
  rw [key, key, mem]

/- English proof (translation)
Introduce `Ω _ _ _ F _ V p n hp hV hO`. Take `⟨T, hT, hTp, hTA⟩` from `hO`. Establish `po : ∀ (w : HeightOneSpectrum (𝓞 F)) (y : 𝓞 F), (placeOf Ω w).valuation (algebraMap F Ω (y : F)) < 1 ↔ y ∈ w.asIdeal`. Introduce `w y`. Establish `h` using `isPlaceOver_placeOf Ω w`.

Unfold `IsPlaceOver at h`. Conclude with `h y`. Establish `fix : ∀ σ ∈ V, ∀ y : 𝓞 F, σ (algebraMap F Ω (y : F)) = algebraMap F Ω (y : F)`. Introduce `σ hσ y`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff F σ).1 (hV hσ) _ (by simp)`.

Use `open scoped Pointwise in`. Establish `hup : ∀ w ∈ plDvd F p, ∃ B ∈ T, ∃ σ ∈ V, σ • B = placeOf Ω w`. Introduce `w hw`. Apply `hTA` to reduce the goal to its premises. Establish `hw' : ((p : 𝓞 F)) ∈ w.asIdeal` using `hw`.

Simplify using `using (po w p).2 hw'`. Use `choose! f hfT σ hσV hσ using hup`. Establish `hinj : Set.InjOn f (plDvd F p)`. Introduce `w1 h1 w2 h2 he`. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises.

Use extensionality with `y`. Rewrite using `[← po w1 y, ← po w2 y, ← hσ w1 h1, ← hσ w2 h2, val_smul_fix _ _ _ (fix _ (hσV w1 h1) y), val_smul_fix _ _ _ (fix _ (hσV w2 h2) y), he]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Ws.ncard_placesDividing_le_of_orbitBound :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F] (V : Subgroup (G ℚ Ω)) (p n : ℕ), p ≠ 0 → V ≤ F.fixingSubgroup → OrbLe V p n → (plDvd F p).ncard ≤ n := by
  intro Ω _ _ _ F _ V p n hp hV hO
  obtain ⟨T, hT, hTp, hTA⟩ := hO
  have po : ∀ (w : HeightOneSpectrum (𝓞 F)) (y : 𝓞 F),
      (placeOf Ω w).valuation (algebraMap F Ω (y : F)) < 1 ↔ y ∈ w.asIdeal := by
    intro w y
    have h := isPlaceOver_placeOf Ω w
    unfold IsPlaceOver at h
    exact h y
  have fix : ∀ σ ∈ V, ∀ y : 𝓞 F, σ (algebraMap F Ω (y : F)) = algebraMap F Ω (y : F) := by
    intro σ hσ y
    exact (IntermediateField.mem_fixingSubgroup_iff F σ).1 (hV hσ) _ (by simp)
  open scoped Pointwise in
  have hup : ∀ w ∈ plDvd F p, ∃ B ∈ T, ∃ σ ∈ V, σ • B = placeOf Ω w := by
    intro w hw
    apply hTA
    have hw' : ((p : 𝓞 F)) ∈ w.asIdeal := hw
    simpa using (po w p).2 hw'
  choose! f hfT σ hσV hσ using hup
  have hinj : Set.InjOn f (plDvd F p) := by
    intro w1 h1 w2 h2 he
    apply HeightOneSpectrum.ext
    ext y
    rw [← po w1 y, ← po w2 y, ← hσ w1 h1, ← hσ w2 h2,
      val_smul_fix _ _ _ (fix _ (hσV w1 h1) y), val_smul_fix _ _ _ (fix _ (hσV w2 h2) y), he]
  calc (plDvd F p).ncard ≤ (T : Set (ValuationSubring Ω)).ncard :=
        Set.ncard_le_ncard_of_injOn f (fun w hw => hfT w hw) hinj T.finite_toSet
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ n := hT
